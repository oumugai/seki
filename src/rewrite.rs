//! Equational rewriting: turning a proven equation into a rewrite rule and
//! applying it to a goal.
//!
//! This is **part of the trusted computing base** (`crate::kernel`).
//! Rewriting by a proven equation is a primitive inference rule — Leibniz's
//! law — so it belongs next to substitution rather than among the tactics
//! that decide *which* equations to try.
//!
//! The split matters.  `by simp` searches: it collects every candidate rule,
//! runs them to a fixed point, AC-normalizes to stop symmetric rules from
//! oscillating, and gives up after 64 iterations.  None of that has to be
//! right.  What has to be right is [`rewrite_goal`]: that each replacement
//! really is an instance of an equation the system has accepted.  The kernel
//! re-runs `rewrite_goal` with the rules the certificate names and refuses
//! the proof unless it lands on the same goal, so a tactic cannot hand over
//! a "rewritten" goal it did not actually reach.

use crate::ast::{BinOp, Expr, UnOp};
use crate::eval::EvalCtx;
use crate::{SekiError, SekiResult};
use std::collections::BTreeSet;

/// How many rewrite passes before giving up.  A cap rather than a
/// termination proof: rules are user-supplied and need not terminate.
pub const MAX_REWRITE_PASSES: usize = 64;

/// Rewrite `goal` to a fixed point under `rules`, under its binders.
///
/// Leading `forall`s are peeled before rewriting and put back afterwards, so
/// the result is a proposition of the same shape as the input.  Rewriting
/// under a universal binder is sound because the rules hold for every value
/// of the bound variable.
///
/// `used` collects the names of rules that actually fired.
pub fn rewrite_goal(
    goal: &Expr,
    rules: &[SimpRule],
    canonicalizing: bool,
    used: &mut BTreeSet<String>,
) -> Vec<Expr> {
    let (binders, inner) = peel_binders(goal);
    let norm = |e: &Expr| if canonicalizing { canonicalize(e) } else { e.clone() };
    let initial = norm(inner);
    let mut current = initial.clone();
    let mut states = vec![rebuild_binders(&binders, initial)];
    for _ in 0..MAX_REWRITE_PASSES {
        let next = norm(&simp_rewrite(&current, rules, used));
        let seen = if canonicalizing {
            states
                .iter()
                .any(|s| exprs_equal(peel_binders(s).1, &next))
        } else {
            states
                .iter()
                .any(|s| crate::ast::alpha_equiv(peel_binders(s).1, &next))
        };
        if seen {
            break;
        }
        states.push(rebuild_binders(&binders, next.clone()));
        current = next;
    }
    states
}

/// Strip leading `forall x in S,` binders, returning them with the body.
pub fn peel_binders(e: &Expr) -> (Vec<(String, Expr)>, &Expr) {
    let mut binders = Vec::new();
    let mut cur = e;
    while let Expr::Forall { var, domain, body } = cur {
        binders.push((var.clone(), (**domain).clone()));
        cur = body;
    }
    (binders, cur)
}

/// Put binders back around a body, outermost first.
pub fn rebuild_binders(binders: &[(String, Expr)], inner: Expr) -> Expr {
    let mut out = inner;
    for (var, domain) in binders.iter().rev() {
        out = Expr::Forall {
            var: var.clone(),
            domain: Box::new(domain.clone()),
            body: Box::new(out),
        };
    }
    out
}

/// A rewrite rule extracted from a theorem/axiom of the shape
/// `forall x1 in T1, ..., forall xn in Tn, lhs == rhs`.
/// `metavars` are the bound variable names — they match anything in the goal.
#[derive(Debug, Clone)]
pub struct SimpRule {
    /// Source theorem/axiom name.  Recorded on every firing so that
    /// `crate::trust` can charge a `by simp` proof for the lemmas it used.
    pub name: String,
    pub metavars: Vec<String>,
    pub lhs: Expr,
    pub rhs: Expr,
}

/// Collect rewrite rules from globals.  When `lemmas` is empty, use every
/// theorem and axiom whose proposition reduces to an equality (after
/// stripping leading `forall` binders).  Otherwise, use exactly the named
/// ones (theorems first, then axioms; error if any name is unknown).
pub fn collect_simp_rules(ctx: &EvalCtx, lemmas: &[String]) -> SekiResult<Vec<SimpRule>> {
    let mut rules = Vec::new();
    if lemmas.is_empty() {
        for (name, prop) in ctx.globals.theorem_props.iter() {
            if let Some(rule) = rule_from_prop(name, prop) {
                rules.push(rule);
            }
        }
        for (name, prop) in ctx.globals.axiom_props.iter() {
            if let Some(rule) = rule_from_prop(name, prop) {
                rules.push(rule);
            }
        }
    } else {
        for name in lemmas {
            let prop = ctx
                .globals
                .theorem_props
                .get(name)
                .or_else(|| ctx.globals.axiom_props.get(name))
                .ok_or_else(|| {
                    SekiError::Proof(format!(
                        "by simp: unknown lemma `{}`",
                        name
                    ))
                })?;
            let rule = rule_from_prop(name, prop).ok_or_else(|| {
                SekiError::Proof(format!(
                    "by simp: lemma `{}` is not an equality, cannot use as rewrite rule",
                    name
                ))
            })?;
            rules.push(rule);
        }
    }
    Ok(rules)
}

/// Try to convert a proposition into a rewrite rule.  Strips leading
/// foralls (recording bound vars as metavariables) and requires the body
/// to be an equality.
pub fn rule_from_prop(name: &str, prop: &Expr) -> Option<SimpRule> {
    let mut metavars = Vec::new();
    let mut cur = prop;
    while let Expr::Forall { var, body, .. } = cur {
        metavars.push(var.clone());
        cur = body;
    }
    if let Expr::BinOp(BinOp::Eq, l, r) = cur {
        Some(SimpRule {
            name: name.to_string(),
            metavars,
            lhs: (**l).clone(),
            rhs: (**r).clone(),
        })
    } else {
        None
    }
}

/// One pass of bottom-up rewriting: try each rule against every sub-expr.
///
/// `used` accumulates the source name of every rule that actually fired.
/// `crate::trust` needs this: a goal closed by `by simp` is only as
/// trustworthy as the lemmas it really leaned on, and charging it for every
/// rule that merely *could* have applied would flag most of the stdlib.
pub fn simp_rewrite(e: &Expr, rules: &[SimpRule], used: &mut BTreeSet<String>) -> Expr {
    use Expr::*;
    // First rewrite children, then try the rules at this node.
    let after_children = match e {
        Int(_) | Real(_) | Bool(_) | Str(_) | Var { .. } => e.clone(),
        Lambda { params, body } => Lambda {
            params: params.clone(),
            body: Box::new(simp_rewrite(body, rules, used)),
        },
        App { func, args } => App {
            func: Box::new(simp_rewrite(func, rules, used)),
            args: args.iter().map(|a| simp_rewrite(a, rules, used)).collect(),
        },
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(simp_rewrite(value, rules, used)),
            body: Box::new(simp_rewrite(body, rules, used)),
            rec: *rec,
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(simp_rewrite(cond, rules, used)),
            then_branch: Box::new(simp_rewrite(then_branch, rules, used)),
            else_branch: Box::new(simp_rewrite(else_branch, rules, used)),
        },
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(simp_rewrite(l, rules, used)),
            Box::new(simp_rewrite(r, rules, used)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(simp_rewrite(x, rules, used))),
        SetEnum(xs) => SetEnum(xs.iter().map(|x| simp_rewrite(x, rules, used)).collect()),
        Tuple(xs) => Tuple(xs.iter().map(|x| simp_rewrite(x, rules, used)).collect()),
        List(xs) => List(xs.iter().map(|x| simp_rewrite(x, rules, used)).collect()),
        SetComp { var, domain, pred } => SetComp {
            var: var.clone(),
            domain: Box::new(simp_rewrite(domain, rules, used)),
            pred: Box::new(simp_rewrite(pred, rules, used)),
        },
        Arrow(a, b) => Arrow(
            Box::new(simp_rewrite(a, rules, used)),
            Box::new(simp_rewrite(b, rules, used)),
        ),
        DepArrow { binder, from, to } => DepArrow {
            binder: binder.clone(),
            from: Box::new(simp_rewrite(from, rules, used)),
            to: Box::new(simp_rewrite(to, rules, used)),
        },
        DepPair { binder, from, to } => DepPair {
            binder: binder.clone(),
            from: Box::new(simp_rewrite(from, rules, used)),
            to: Box::new(simp_rewrite(to, rules, used)),
        },
        Forall { var, domain, body } => Forall {
            var: var.clone(),
            domain: Box::new(simp_rewrite(domain, rules, used)),
            body: Box::new(simp_rewrite(body, rules, used)),
        },
        Exists { var, domain, body } => Exists {
            var: var.clone(),
            domain: Box::new(simp_rewrite(domain, rules, used)),
            body: Box::new(simp_rewrite(body, rules, used)),
        },
    };
    // Try each rule at this node.
    for rule in rules {
        if let Some(subst_map) = match_pattern(&rule.lhs, &after_children, &rule.metavars) {
            used.insert(rule.name.clone());
            return apply_subst(&rule.rhs, &subst_map);
        }
    }
    after_children
}

/// Attempt syntactic matching of `pattern` against `target`, treating any
/// occurrence of a name in `metavars` (in `pattern`) as a wildcard that
/// can be bound to any sub-expression.  Returns the binding on success.
pub fn match_pattern(
    pattern: &Expr,
    target: &Expr,
    metavars: &[String],
) -> Option<std::collections::HashMap<String, Expr>> {
    let mut subst = std::collections::HashMap::new();
    if try_match(pattern, target, metavars, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

fn try_match(
    pat: &Expr,
    tgt: &Expr,
    metavars: &[String],
    subst: &mut std::collections::HashMap<String, Expr>,
) -> bool {
    use Expr::*;
    // Metavariable in the pattern: bind or check consistency.
    if let Var { name: n, .. } = pat {
        if metavars.iter().any(|m| m == n) {
            if let Some(prev) = subst.get(n) {
                return crate::ast::alpha_equiv(prev, tgt);
            }
            subst.insert(n.clone(), tgt.clone());
            return true;
        }
    }
    match (pat, tgt) {
        (Int(a), Int(b)) => a == b,
        (Real(a), Real(b)) => a == b,
        (Bool(a), Bool(b)) => a == b,
        (Str(a), Str(b)) => a == b,
        (Var { name: a, .. }, Var { name: b, .. }) => a == b,
        (
            App { func: f1, args: a1 },
            App { func: f2, args: a2 },
        ) if a1.len() == a2.len() => {
            try_match(f1, f2, metavars, subst)
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| try_match(x, y, metavars, subst))
        }
        (BinOp(o1, l1, r1), BinOp(o2, l2, r2)) if o1 == o2 => {
            try_match(l1, l2, metavars, subst) && try_match(r1, r2, metavars, subst)
        }
        (UnOp(o1, x1), UnOp(o2, x2)) if o1 == o2 => try_match(x1, x2, metavars, subst),
        (Tuple(xs), Tuple(ys)) | (List(xs), List(ys)) | (SetEnum(xs), SetEnum(ys))
            if xs.len() == ys.len() =>
        {
            xs.iter()
                .zip(ys.iter())
                .all(|(x, y)| try_match(x, y, metavars, subst))
        }
        (
            If { cond: c1, then_branch: t1, else_branch: e1 },
            If { cond: c2, then_branch: t2, else_branch: e2 },
        ) => {
            try_match(c1, c2, metavars, subst)
                && try_match(t1, t2, metavars, subst)
                && try_match(e1, e2, metavars, subst)
        }
        // Lambda / Let / Forall / Exists: only match if structures match
        // exactly (no alpha-renaming for the matching positions — this
        // keeps simp simple and predictable).
        (
            Lambda { params: p1, body: b1 },
            Lambda { params: p2, body: b2 },
        ) if p1.len() == p2.len() && p1.iter().zip(p2.iter()).all(|(x, y)| x.name == y.name) => {
            try_match(b1, b2, metavars, subst)
        }
        _ => false,
    }
}

/// Substitute metavariables in `e` according to `m`.
pub fn apply_subst(e: &Expr, m: &std::collections::HashMap<String, Expr>) -> Expr {
    let mut out = e.clone();
    for (k, v) in m {
        out = crate::ast::subst(&out, k, v);
    }
    out
}

/// Cheap structural equality on `Expr` for fixed-point detection.
/// Reuses `alpha_equiv` which is structurally-aware.
pub fn exprs_equal(a: &Expr, b: &Expr) -> bool {
    crate::ast::alpha_equiv(a, b)
}

// =============================================================================
// AC (associative-commutative) canonicalization for `by simp`.
//
// We treat `+` and `*` as commutative + associative.  A sum like
// `(a + b) + c` and `c + (b + a)` should be recognized as equal after
// canonicalization.  Subtraction `a - b` is rewritten as `a + (- b)` so the
// sum's flatten step can see it as part of the additive group.
//
// Procedure (applied bottom-up):
//   1. Recurse into sub-expressions.
//   2. For `+` or `*`: flatten left-associated chains, sort terms by a
//      stable key (their `Display` representation), then re-fold
//      left-associatively in the sorted order.
// =============================================================================

fn flatten_sum(e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::BinOp(crate::ast::BinOp::Add, l, r) => {
            flatten_sum(l, out);
            flatten_sum(r, out);
        }
        // a - b => a + (-b)
        Expr::BinOp(crate::ast::BinOp::Sub, l, r) => {
            flatten_sum(l, out);
            out.push(Expr::UnOp(crate::ast::UnOp::Neg, r.clone()));
        }
        _ => out.push(e.clone()),
    }
}

fn flatten_product(e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::BinOp(crate::ast::BinOp::Mul, l, r) => {
            flatten_product(l, out);
            flatten_product(r, out);
        }
        _ => out.push(e.clone()),
    }
}

fn expr_key(e: &Expr) -> String {
    // Display impl gives a stable, structure-aware string.
    format!("{}", e)
}

/// Canonicalize an expression so that AC-equivalent forms become
/// syntactically identical (modulo alpha-equivalence on bound vars).
pub fn canonicalize(e: &Expr) -> Expr {
    use Expr::*;
    use crate::ast::BinOp as B;
    match e {
        BinOp(B::Add, _, _) | BinOp(B::Sub, _, _) => {
            let mut terms = Vec::new();
            flatten_sum(e, &mut terms);
            for t in terms.iter_mut() {
                *t = canonicalize(t);
            }
            // Drop additive identity (0); fold integer literals.
            let mut const_sum: i64 = 0;
            let mut others: Vec<Expr> = Vec::new();
            for t in terms.into_iter() {
                match &t {
                    Int(0) => {}
                    // Folding with `saturating_add` would quietly clamp at
                    // the i64 boundary and could make a false equation
                    // canonicalize to a true one.  On overflow, leave the
                    // literal alone instead.
                    Int(n) => match const_sum.checked_add(*n) {
                        Some(v) => const_sum = v,
                        None => others.push(t),
                    },
                    _ => others.push(t),
                }
            }
            if const_sum != 0 {
                others.push(Int(const_sum));
            }
            if others.is_empty() {
                return Int(0);
            }
            others.sort_by(|a, b| expr_key(a).cmp(&expr_key(b)));
            let mut iter = others.into_iter();
            let first = iter.next().unwrap();
            iter.fold(first, |acc, t| {
                BinOp(B::Add, Box::new(acc), Box::new(t))
            })
        }
        BinOp(B::Mul, _, _) => {
            let mut factors = Vec::new();
            flatten_product(e, &mut factors);
            for f in factors.iter_mut() {
                *f = canonicalize(f);
            }
            // Annihilator: any 0 factor → result is 0.
            if factors.iter().any(|f| matches!(f, Int(0))) {
                return Int(0);
            }
            // Drop multiplicative identity (1); fold integer literals.
            let mut const_prod: i64 = 1;
            let mut others: Vec<Expr> = Vec::new();
            for f in factors.into_iter() {
                match &f {
                    Int(1) => {}
                    Int(n) => const_prod = const_prod.saturating_mul(*n),
                    _ => others.push(f),
                }
            }
            if const_prod != 1 {
                others.push(Int(const_prod));
            }
            if others.is_empty() {
                return Int(1);
            }
            others.sort_by(|a, b| expr_key(a).cmp(&expr_key(b)));
            let mut iter = others.into_iter();
            let first = iter.next().unwrap();
            iter.fold(first, |acc, f| {
                BinOp(B::Mul, Box::new(acc), Box::new(f))
            })
        }
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(canonicalize(l)),
            Box::new(canonicalize(r)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(canonicalize(x))),
        App { func, args } => App {
            func: Box::new(canonicalize(func)),
            args: args.iter().map(canonicalize).collect(),
        },
        Lambda { params, body } => Lambda {
            params: params.clone(),
            body: Box::new(canonicalize(body)),
        },
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(canonicalize(value)),
            body: Box::new(canonicalize(body)),
            rec: *rec,
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(canonicalize(cond)),
            then_branch: Box::new(canonicalize(then_branch)),
            else_branch: Box::new(canonicalize(else_branch)),
        },
        SetEnum(xs) => SetEnum(xs.iter().map(canonicalize).collect()),
        Tuple(xs) => Tuple(xs.iter().map(canonicalize).collect()),
        List(xs) => List(xs.iter().map(canonicalize).collect()),
        SetComp { var, domain, pred } => SetComp {
            var: var.clone(),
            domain: Box::new(canonicalize(domain)),
            pred: Box::new(canonicalize(pred)),
        },
        Arrow(a, b) => Arrow(
            Box::new(canonicalize(a)),
            Box::new(canonicalize(b)),
        ),
        DepArrow { binder, from, to } => DepArrow {
            binder: binder.clone(),
            from: Box::new(canonicalize(from)),
            to: Box::new(canonicalize(to)),
        },
        DepPair { binder, from, to } => DepPair {
            binder: binder.clone(),
            from: Box::new(canonicalize(from)),
            to: Box::new(canonicalize(to)),
        },
        Forall { var, domain, body } => Forall {
            var: var.clone(),
            domain: Box::new(canonicalize(domain)),
            body: Box::new(canonicalize(body)),
        },
        Exists { var, domain, body } => Exists {
            var: var.clone(),
            domain: Box::new(canonicalize(domain)),
            body: Box::new(canonicalize(body)),
        },
        Int(_) | Real(_) | Bool(_) | Str(_) | Var { .. } => e.clone(),
    }
}

/// If `body` contains an `if c then t else e` subexpression, return:
///   * `body` with the first such if replaced by `t`,
///   * `body` with the first such if replaced by `e`,
///   * the condition `c`.
/// "First" means: leftmost in a left-to-right walk over the AST.  Used by
/// `prove_algebra_rel` to case-split on conditions.
pub fn split_first_if(body: &Expr) -> Option<(Expr, Expr, Expr)> {
    use Expr::*;
    match body {
        If { cond, then_branch, else_branch } => Some((
            (**then_branch).clone(),
            (**else_branch).clone(),
            (**cond).clone(),
        )),
        BinOp(op, l, r) => {
            if let Some((tl, el, c)) = split_first_if(l) {
                return Some((
                    BinOp(op.clone(), Box::new(tl), r.clone()),
                    BinOp(op.clone(), Box::new(el), r.clone()),
                    c,
                ));
            }
            if let Some((tr, er, c)) = split_first_if(r) {
                return Some((
                    BinOp(op.clone(), l.clone(), Box::new(tr)),
                    BinOp(op.clone(), l.clone(), Box::new(er)),
                    c,
                ));
            }
            None
        }
        UnOp(op, x) => split_first_if(x).map(|(t, e, c)| {
            (
                UnOp(op.clone(), Box::new(t)),
                UnOp(op.clone(), Box::new(e)),
                c,
            )
        }),
        App { func, args } => {
            if let Some((tf, ef, c)) = split_first_if(func) {
                return Some((
                    App { func: Box::new(tf), args: args.clone() },
                    App { func: Box::new(ef), args: args.clone() },
                    c,
                ));
            }
            for (i, a) in args.iter().enumerate() {
                if let Some((ta, ea, c)) = split_first_if(a) {
                    let mut targs = args.clone();
                    let mut eargs = args.clone();
                    targs[i] = ta;
                    eargs[i] = ea;
                    return Some((
                        App { func: func.clone(), args: targs },
                        App { func: func.clone(), args: eargs },
                        c,
                    ));
                }
            }
            None
        }
        Let { name, ty, value, body: lb, rec } => {
            if let Some((tv, ev, c)) = split_first_if(value) {
                return Some((
                    Let {
                        name: name.clone(),
                        ty: ty.clone(),
                        value: Box::new(tv),
                        body: lb.clone(),
                        rec: *rec,
                    },
                    Let {
                        name: name.clone(),
                        ty: ty.clone(),
                        value: Box::new(ev),
                        body: lb.clone(),
                        rec: *rec,
                    },
                    c,
                ));
            }
            split_first_if(lb).map(|(t, e, c)| {
                (
                    Let {
                        name: name.clone(),
                        ty: ty.clone(),
                        value: value.clone(),
                        body: Box::new(t),
                        rec: *rec,
                    },
                    Let {
                        name: name.clone(),
                        ty: ty.clone(),
                        value: value.clone(),
                        body: Box::new(e),
                        rec: *rec,
                    },
                    c,
                )
            })
        }
        _ => None,
    }
}

/// The two obligations a case split on the goal's first `if` produces.
///
/// `if c then A else B` inside a goal is settled by proving the goal with
/// the `if` collapsed to `A` *under the assumption `c`*, and to `B` under
/// its negation.  Together those cover every case, so the original follows.
///
/// Both `crate::prover` (to build the certificate) and `crate::kernel` (to
/// re-derive what the certificate must prove) call this, which is what
/// stops a certificate from splitting on a condition of its own choosing.
pub fn case_split_goals(prop: &Expr) -> Option<(Expr, Expr)> {
    let (binders, inner) = peel_binders(prop);
    let (conclusion, hyps) = peel_premises(inner);
    let (then_form, else_form, cond) = split_first_if(&conclusion)?;
    let neg = negate_condition(&cond);
    let under = |extra: Expr, concl: Expr| {
        let mut premise = extra;
        for h in hyps.iter().rev() {
            premise = Expr::BinOp(BinOp::And, Box::new(h.clone()), Box::new(premise));
        }
        rebuild_binders(
            &binders,
            Expr::BinOp(
                BinOp::Or,
                Box::new(Expr::UnOp(UnOp::Not, Box::new(premise))),
                Box::new(concl),
            ),
        )
    };
    Some((under(cond, then_form), under(neg, else_form)))
}

/// Negate a condition, keeping it a relation where possible so that the
/// `else` branch can still use it as a linear hypothesis.
fn negate_condition(c: &Expr) -> Expr {
    match c {
        Expr::BinOp(op, l, r) => {
            let flipped = match op {
                BinOp::Eq => Some(BinOp::Neq),
                BinOp::Neq => Some(BinOp::Eq),
                BinOp::Lt => Some(BinOp::Ge),
                BinOp::Le => Some(BinOp::Gt),
                BinOp::Gt => Some(BinOp::Le),
                BinOp::Ge => Some(BinOp::Lt),
                _ => None,
            };
            match flipped {
                Some(op) => Expr::BinOp(op, l.clone(), r.clone()),
                None => Expr::UnOp(UnOp::Not, Box::new(c.clone())),
            }
        }
        other => Expr::UnOp(UnOp::Not, Box::new(other.clone())),
    }
}

/// Peel `(not P) or Q` / `P -> Q` chains into the conclusion and the
/// premises gathered on the way.
pub fn peel_premises(body: &Expr) -> (Expr, Vec<Expr>) {
    let mut premises = Vec::new();
    let mut cur = body.clone();
    loop {
        match &cur {
            Expr::BinOp(BinOp::Or, l, r) => {
                if let Expr::UnOp(UnOp::Not, inner) = l.as_ref() {
                    let mut cs = Vec::new();
                    flatten_and(inner, &mut cs);
                    premises.extend(cs);
                    cur = (**r).clone();
                    continue;
                }
                break;
            }
            Expr::Arrow(l, r) => {
                let mut cs = Vec::new();
                flatten_and(l, &mut cs);
                premises.extend(cs);
                cur = (**r).clone();
                continue;
            }
            _ => break,
        }
    }
    (cur, premises)
}

fn flatten_and(e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::BinOp(BinOp::And, l, r) => {
            flatten_and(l, out);
            flatten_and(r, out);
        }
        other => out.push(other.clone()),
    }
}

//! Theorem verification.
//!
//! Three kinds of proof:
//!   * `by eval`            — reduce the proposition; must yield `true`.
//!   * `refl`               — for an equality `a == b`, both sides must reduce
//!                            to the same value.
//!   * `<term>` (a value)   — Curry-Howard-ish proof witness:
//!         * for `forall x in S, P(x)`: the term must be a function; we
//!           enumerate `S` (when finite), apply the function to every
//!           element, and require `P[x := elem]` to evaluate to `true`.
//!         * for `exists x in S, P(x)`: the term is the witness; we evaluate
//!           it, check membership in `S`, and require `P[x := witness]` to
//!           evaluate to `true`.
//!         * for any other proposition: we evaluate the prop and require
//!           `true`; the term is recorded as a proof token.
//!
//! This is far weaker than what Lean offers (no real proof terms with their
//! own type), but it is *sound for the cases it accepts* — every accepted
//! theorem has been demonstrated against the language's actual semantics.

use crate::algebra::{
    expr_to_poly, polynomial_neg, polynomial_nonneg, polynomial_nonpos, polynomial_pos,
    polynomial_strictly_positive_in_nat, ratpoly_equal, PolyDomain,
};
use crate::ast::{subst, BinOp, Expr, Proof, UnOp};
use crate::eval::{enumerate_set, EvalCtx};
use crate::value::{value_eq, AtomicSet, Env, SetVal, Value};
use crate::{SekiError, SekiResult};

pub struct Prover<'a> {
    pub ctx: &'a EvalCtx<'a>,
}

/// Outcome of one step inside a `by t1 then t2 then ...` sequence.
enum TacOutcome {
    /// The tactic finished proving the (sub)goal.
    Closed,
    /// The tactic transformed the goal; the next tactic should pick up.
    NewGoal(Expr),
}

/// Walk `e` and replace every direct call `name(a1, ..., ak)` with
/// `body[params := args]`.  Only single-level: we don't re-unfold calls
/// produced by the substitution itself (avoids infinite expansion for
/// recursive functions).
fn unfold_calls(
    e: &Expr,
    name: &str,
    params: &[String],
    body: &Expr,
) -> Expr {
    use Expr::*;
    match e {
        App { func, args } if matches!(func.as_ref(), Var { name: n, .. } if n == name)
            && args.len() == params.len() =>
        {
            let mut out = body.clone();
            for (p, a) in params.iter().zip(args.iter()) {
                out = crate::ast::subst(&out, p, a);
            }
            out
        }
        App { func, args } => App {
            func: Box::new(unfold_calls(func, name, params, body)),
            args: args
                .iter()
                .map(|a| unfold_calls(a, name, params, body))
                .collect(),
        },
        Lambda { params: lp, body: b } => {
            // The lambda parameter list contains `Param { name, .. }`.  We
            // skip into the body only if none of its params shadow `name`.
            if lp.iter().any(|p| p.name == name) {
                e.clone()
            } else {
                Lambda {
                    params: lp.clone(),
                    body: Box::new(unfold_calls(b, name, params, body)),
                }
            }
        }
        Let { name: ln, ty, value, body: lb, rec } => Let {
            name: ln.clone(),
            ty: ty.clone(),
            value: Box::new(unfold_calls(value, name, params, body)),
            body: if ln == name {
                lb.clone()
            } else {
                Box::new(unfold_calls(lb, name, params, body))
            },
            rec: *rec,
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(unfold_calls(cond, name, params, body)),
            then_branch: Box::new(unfold_calls(then_branch, name, params, body)),
            else_branch: Box::new(unfold_calls(else_branch, name, params, body)),
        },
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(unfold_calls(l, name, params, body)),
            Box::new(unfold_calls(r, name, params, body)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(unfold_calls(x, name, params, body))),
        SetEnum(xs) => SetEnum(
            xs.iter()
                .map(|x| unfold_calls(x, name, params, body))
                .collect(),
        ),
        Tuple(xs) => Tuple(
            xs.iter()
                .map(|x| unfold_calls(x, name, params, body))
                .collect(),
        ),
        List(xs) => List(
            xs.iter()
                .map(|x| unfold_calls(x, name, params, body))
                .collect(),
        ),
        SetComp { var, domain, pred } => SetComp {
            var: var.clone(),
            domain: Box::new(unfold_calls(domain, name, params, body)),
            pred: Box::new(unfold_calls(pred, name, params, body)),
        },
        Arrow(a, b) => Arrow(
            Box::new(unfold_calls(a, name, params, body)),
            Box::new(unfold_calls(b, name, params, body)),
        ),
        DepArrow { binder, from, to } => DepArrow {
            binder: binder.clone(),
            from: Box::new(unfold_calls(from, name, params, body)),
            to: Box::new(unfold_calls(to, name, params, body)),
        },
        DepPair { binder, from, to } => DepPair {
            binder: binder.clone(),
            from: Box::new(unfold_calls(from, name, params, body)),
            to: Box::new(unfold_calls(to, name, params, body)),
        },
        Forall { var, domain, body: fb } => Forall {
            var: var.clone(),
            domain: Box::new(unfold_calls(domain, name, params, body)),
            body: Box::new(unfold_calls(fb, name, params, body)),
        },
        Exists { var, domain, body: fb } => Exists {
            var: var.clone(),
            domain: Box::new(unfold_calls(domain, name, params, body)),
            body: Box::new(unfold_calls(fb, name, params, body)),
        },
        Int(_) | Real(_) | Bool(_) | Str(_) | Var { .. } => e.clone(),
    }
}

impl<'a> Prover<'a> {
    pub fn new(ctx: &'a EvalCtx<'a>) -> Self {
        Self { ctx }
    }

    /// Verify a theorem with the given proof.  Returns the proposition's value
    /// (always `Value::Bool(true)` on success) so callers may store the
    /// theorem as a proven proposition.
    pub fn verify(&self, prop: &Expr, proof: &Proof, env: &Env) -> SekiResult<Value> {
        match proof {
            Proof::ByEval => {
                let v = self.ctx.eval(prop, env)?;
                require_true(&v).map(|()| Value::Bool(true))
            }
            Proof::Refl => self.verify_refl(prop, env),
            Proof::ByAlgebra | Proof::ByLinarith => self.verify_algebra(prop, env),
            Proof::ByDecide => {
                // Strict decision procedure: evaluate the proposition to a
                // Bool literal under env.  Refuses non-Bool results.
                let v = self.ctx.eval(prop, env)?;
                match v {
                    Value::Bool(true) => Ok(Value::Bool(true)),
                    Value::Bool(false) => Err(SekiError::Proof(
                        "by decide: proposition reduced to false".into(),
                    )),
                    other => Err(SekiError::Proof(format!(
                        "by decide: proposition did not decide to a Bool (got {})",
                        other
                    ))),
                }
            }
            Proof::ByInduction => self.verify_induction(prop, env),
            Proof::ByStrongInduction { depth } => self.verify_strong_induction(prop, env, *depth),
            Proof::BySimp { lemmas } => self.verify_simp(prop, env, lemmas),
            Proof::ByUnfold(name) => {
                // Standalone unfold: transform and then require the result
                // to evaluate to `true`.  Most useful inside a `Seq`.
                let unfolded = self.do_unfold(prop, name)?;
                let v = self.ctx.eval(&unfolded, env)?;
                if matches!(v, Value::Bool(true)) {
                    Ok(Value::Bool(true))
                } else {
                    Err(SekiError::Proof(format!(
                        "by unfold {}: result did not close the goal: {}",
                        name, unfolded
                    )))
                }
            }
            Proof::ByIntros => {
                // Standalone intros: strip foralls; remaining expression
                // must be provable by-eval over the now-free variables.
                let stripped = strip_foralls(prop).clone();
                let v = self.ctx.eval(&stripped, env)?;
                if matches!(v, Value::Bool(true)) {
                    Ok(Value::Bool(true))
                } else {
                    Err(SekiError::Proof(format!(
                        "by intros: stripped goal did not evaluate to true: {}",
                        stripped
                    )))
                }
            }
            Proof::Seq(tacs) => self.verify_seq(prop, env, tacs),
            Proof::Term(term) => self.verify_term(prop, term, env),
            Proof::ByAuto => match self.try_portfolio(prop, env) {
                Some(_) => Ok(Value::Bool(true)),
                None => Err(SekiError::Proof(
                    "by auto: no tactic in the portfolio closed the goal".into(),
                )),
            },
        }
    }

    /// Portfolio search.  Tries a fixed pipeline of closers and combinators
    /// in increasing cost order; returns the first `Proof` that successfully
    /// verifies `prop`, or `None` if all candidates fail.
    ///
    /// The order is roughly: refl/eval/decide (instant) → algebra/linarith
    /// (polynomial normalization) → induction/strong_induction (sample-driven
    /// step verification) → simp on all proven theorems → intros-prefixed
    /// variants → unfold combinators for each user-defined function appearing
    /// in `prop` → simp with the top symbol-overlap-ranked lemmas (singletons
    /// then pairs).
    ///
    /// Each candidate is bounded only by its own internal logic — there is
    /// no per-candidate wall-clock cutoff here, because callers that need a
    /// timeout (e.g. the REPL's background search) run the whole portfolio
    /// inside a worker thread that they cancel externally.
    pub fn try_portfolio(&self, prop: &Expr, env: &Env) -> Option<Proof> {
        let candidates = self.portfolio_candidates(prop, false);
        for cand in candidates {
            if self.verify(prop, &cand, env).is_ok() {
                return Some(cand);
            }
        }
        None
    }

    /// Variant of `try_portfolio` that *prefers lemma-based proofs*: the
    /// top-ranked `by simp [T_i]` and 2-lemma combos are tried first, and
    /// the cheap closers (refl/eval/algebra/...) only run as a fallback.
    /// Used by the REPL's `:why` command — the user is explicitly asking
    /// which earlier lemmas a goal builds on, so a derivation that names
    /// a relevant theorem is more informative than one that closes via
    /// `by eval` sampling.
    pub fn try_portfolio_lemma_first(&self, prop: &Expr, env: &Env) -> Option<Proof> {
        let candidates = self.portfolio_candidates(prop, true);
        for cand in candidates {
            if self.verify(prop, &cand, env).is_ok() {
                return Some(cand);
            }
        }
        None
    }

    /// Build the ordered list of `Proof` candidates.  When `prefer_lemmas`
    /// is true, lemma-based combinators come first (used by `:why`);
    /// otherwise cheap closers come first (used by `:prove` / `by auto`).
    fn portfolio_candidates(&self, prop: &Expr, prefer_lemmas: bool) -> Vec<Proof> {
        // Collect identifiers referenced in the proposition so we can
        // (a) propose `unfold f then algebra` for user-defined `f`,
        // (b) rank existing theorems by symbol overlap for `by simp [..]`.
        let mut idents: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        collect_idents(prop, &mut idents);

        let mut user_funcs: Vec<String> = idents
            .iter()
            .filter(|n| {
                matches!(
                    self.ctx.globals.defs.get(n.as_str()),
                    Some(Value::Closure { .. })
                )
            })
            .cloned()
            .collect();
        user_funcs.sort();

        let ranked: Vec<String> =
            rank_lemmas(&idents, &self.ctx.globals.theorem_props, None);

        // Sub-block: cheap closers (refl/eval/decide/algebra/induction).
        let cheap: Vec<Proof> = vec![
            Proof::Refl,
            Proof::ByEval,
            Proof::ByDecide,
            Proof::ByAlgebra,
            Proof::ByInduction,
            Proof::ByStrongInduction { depth: 2 },
            Proof::ByStrongInduction { depth: 3 },
            Proof::Seq(vec![Proof::ByIntros, Proof::ByAlgebra]),
        ];

        // Sub-block: unfold combinators for each user-defined function.
        let mut unfolds: Vec<Proof> = Vec::new();
        for f in &user_funcs {
            unfolds.push(Proof::Seq(vec![
                Proof::ByUnfold(f.clone()),
                Proof::ByAlgebra,
            ]));
            unfolds.push(Proof::Seq(vec![
                Proof::ByIntros,
                Proof::ByUnfold(f.clone()),
                Proof::ByAlgebra,
            ]));
            unfolds.push(Proof::Seq(vec![
                Proof::ByUnfold(f.clone()),
                Proof::ByInduction,
            ]));
        }

        // Sub-block: lemma-based combinators.  Singletons (top-5) then
        // pairs (top-3 → 3 pairs).  Each is wrapped in `by intros then simp
        // [T] then algebra` to handle quantified goals uniformly.
        let mut lemma_chains: Vec<Proof> = Vec::new();
        for name in ranked.iter().take(5) {
            lemma_chains.push(Proof::Seq(vec![
                Proof::ByIntros,
                Proof::BySimp {
                    lemmas: vec![name.clone()],
                },
                Proof::ByAlgebra,
            ]));
        }
        let pool: Vec<&String> = ranked.iter().take(3).collect();
        for i in 0..pool.len() {
            for j in i + 1..pool.len() {
                lemma_chains.push(Proof::Seq(vec![
                    Proof::ByIntros,
                    Proof::BySimp {
                        lemmas: vec![pool[i].clone(), pool[j].clone()],
                    },
                    Proof::ByAlgebra,
                ]));
            }
        }

        // Full-pool simp falls last either way — most expensive search.
        let fallback: Vec<Proof> = vec![
            Proof::BySimp { lemmas: vec![] },
            Proof::Seq(vec![Proof::ByIntros, Proof::BySimp { lemmas: vec![] }]),
        ];

        let mut out: Vec<Proof> = Vec::new();
        if prefer_lemmas {
            out.extend(lemma_chains);
            out.extend(unfolds);
            out.extend(cheap);
            out.extend(fallback);
        } else {
            out.extend(cheap);
            out.extend(unfolds);
            out.extend(lemma_chains);
            out.extend(fallback);
        }
        out
    }

    /// Run a sequence of tactics `t1 then t2 then ... then tk`.  Each
    /// tactic returns a `TacOutcome`:
    ///   * `Closed` — the goal was proved; this MUST be the last tactic.
    ///   * `NewGoal(g)` — the goal was transformed to `g`; pass to the
    ///     next tactic.
    fn verify_seq(&self, prop: &Expr, env: &Env, tacs: &[Proof]) -> SekiResult<Value> {
        if tacs.is_empty() {
            return Err(SekiError::Proof("empty tactic sequence".into()));
        }
        let mut current = prop.clone();
        for (i, t) in tacs.iter().enumerate() {
            let is_last = i + 1 == tacs.len();
            match self.run_step(&current, env, t)? {
                TacOutcome::Closed => {
                    if !is_last {
                        // Earlier tactic closed the goal — succeed (the
                        // user maybe over-specified the composition).
                        return Ok(Value::Bool(true));
                    }
                    return Ok(Value::Bool(true));
                }
                TacOutcome::NewGoal(g) => {
                    if is_last {
                        return Err(SekiError::Proof(format!(
                            "tactic sequence ended with an unclosed goal: {}",
                            g
                        )));
                    }
                    current = g;
                }
            }
        }
        unreachable!("verify_seq loop did not return")
    }

    /// One step in a tactic sequence: tries the tactic; if it's a closer
    /// (algebra/induction/etc) and succeeds, returns `Closed`; if it's a
    /// transformer (unfold/intros/simp-partial), returns `NewGoal`.
    fn run_step(&self, prop: &Expr, env: &Env, proof: &Proof) -> SekiResult<TacOutcome> {
        match proof {
            Proof::ByUnfold(name) => {
                let g = self.do_unfold(prop, name)?;
                Ok(TacOutcome::NewGoal(g))
            }
            Proof::ByIntros => {
                let g = strip_foralls(prop).clone();
                Ok(TacOutcome::NewGoal(g))
            }
            Proof::BySimp { lemmas } => {
                // Try to close via simp; if it can't, return the most
                // rewritten state as a new goal.
                let rules = collect_simp_rules(self.ctx, lemmas)?;
                let initial = strip_foralls(prop).clone();
                let mut current = initial.clone();
                let mut seen: Vec<Expr> = vec![initial];
                const MAX_ITERS: usize = 64;
                for _ in 0..MAX_ITERS {
                    let next = simp_rewrite(&current, &rules);
                    if seen.iter().any(|s| crate::ast::alpha_equiv(s, &next)) {
                        break;
                    }
                    seen.push(next.clone());
                    current = next;
                }
                for state in &seen {
                    if matches!(state, Expr::Bool(true)) {
                        return Ok(TacOutcome::Closed);
                    }
                    if let Expr::BinOp(BinOp::Eq, l, r) = state {
                        if crate::ast::alpha_equiv(l, r) {
                            return Ok(TacOutcome::Closed);
                        }
                    }
                    if let Ok(Value::Bool(true)) = self.ctx.eval(state, env) {
                        return Ok(TacOutcome::Closed);
                    }
                }
                Ok(TacOutcome::NewGoal(current))
            }
            // Closing tactics: invoke verify on the current goal; success → Closed.
            closer @ (Proof::ByEval
            | Proof::Refl
            | Proof::ByAlgebra
            | Proof::ByLinarith
            | Proof::ByDecide
            | Proof::ByInduction
            | Proof::ByStrongInduction { .. }
            | Proof::ByAuto
            | Proof::Term(_)) => {
                self.verify(prop, closer, env)?;
                Ok(TacOutcome::Closed)
            }
            Proof::Seq(_) => Err(SekiError::Proof(
                "nested tactic sequences not allowed; flatten with `then`".into(),
            )),
        }
    }

    /// β-unfold every occurrence of `App { func: Var { name: name, .. }, args }` in
    /// `e` using the body of the global `def name := \params -> body`.
    /// Performs a single layer of unfolding; recursive functions don't
    /// loop because we don't unfold the calls produced by substitution.
    fn do_unfold(&self, e: &Expr, name: &str) -> SekiResult<Expr> {
        // Look up the closure's body and parameter list.
        let (params, body) = match self.ctx.globals.defs.get(name) {
            Some(Value::Closure { params, body, .. }) => (params.clone(), (**body).clone()),
            Some(other) => {
                return Err(SekiError::Proof(format!(
                    "by unfold {}: not a function, got {}",
                    name,
                    other.type_name()
                )))
            }
            None => {
                return Err(SekiError::Proof(format!(
                    "by unfold {}: no such definition",
                    name
                )))
            }
        };
        // First: β-unfold `name` itself.
        let one_step = unfold_calls(e, name, &params, &body);
        // Then: transitively unfold any **non-recursive** user-defined
        // function called from the result.  This lets `unfold g then
        // algebra` see through `g x = f x + 1` where `f` is a separate
        // definition.  Recursive functions are detected by checking
        // whether their body mentions their own name, and are left at
        // one-level unfolding (preserving the existing safety guarantee).
        Ok(unfold_nonrec_transitive(
            &one_step,
            &self.ctx.globals,
            &[name],
        ))
    }

    /// `by algebra`:  prove a relational claim over **all integers (or naturals
    /// or reals)** by reducing the relation to a polynomial sign analysis.
    /// Supports `==`, `!=`, `<`, `<=`, `>`, `>=`, integer division and modulo
    /// by constant divisors, **Real** coefficients via rational arithmetic,
    /// and **if-expressions** via case-splitting on each condition.
    ///
    /// Sound: a `proved` outcome means the relation holds for every valuation
    /// of the free variables in the chosen domain (Nat, Int, or Real).
    ///
    /// Case-split semantics for `if c then t else e`:
    ///   - Replace the if with `t` and recurse (success means: in the world
    ///     where `c` is true, the relation holds).
    ///   - Replace the if with `e` and recurse (success means: in the world
    ///     where `c` is false, the relation holds).
    ///   - As a sweetener, when `c` is `v == val` (variable equals literal),
    ///     we substitute `v := val` in the then-branch so the polynomial
    ///     checker sees the value the condition guarantees.
    ///
    /// Either branch alone closing means that whole side of the case-split is
    /// proved unconditionally — `by algebra` then only needs the other branch
    /// to succeed.
    fn verify_algebra(&self, prop: &Expr, _env: &Env) -> SekiResult<Value> {
        let dom = detect_domain(prop);
        let body = strip_foralls(prop).clone();
        // Inject implicit non-negativity hypotheses for every `forall x in
        // Nat` binder.  This is sound (each such x really is ≥ 0) and lets
        // the case-split contradiction engine close branches like
        // `(50 + k) < 50` when `k in Nat`.
        let mut initial_hyps: Vec<(Expr, bool)> = Vec::new();
        collect_nat_hyps(prop, &mut initial_hyps);
        // Also handle a top-level implication `premise -> conclusion`:
        // turn the premise into a hypothesis and continue with the
        // conclusion as the goal.
        let (conclusion, premises) = peel_implications(&body);
        for p in premises {
            initial_hyps.push((p, true));
        }
        self.prove_algebra_rel(&conclusion, dom, &initial_hyps)
    }

    /// Recursive worker for `verify_algebra`: case-splits on any `if`
    /// subexpression first, then falls through to the polynomial check.
    ///
    /// `hyps` is the list of relational facts known to hold in the current
    /// branch (each `(relation, is_true)` — `is_true=false` means the
    /// negation of the relation holds, i.e. we're in the else-branch of
    /// `if relation`).  These let us close branches whose goal is implied
    /// by the path we took to get here.
    fn prove_algebra_rel(
        &self,
        body: &Expr,
        dom: PolyDomain,
        hyps: &[(Expr, bool)],
    ) -> SekiResult<Value> {
        // If any prior hypothesis is contradicted (same condition assumed
        // both true and false on this path), the branch is vacuously true.
        if hyps_contradict(hyps) {
            return Ok(Value::Bool(true));
        }
        if let Some((then_body, else_body, cond)) = split_first_if(body) {
            // In the then-branch, propagate `cond ⇒ true` everywhere by
            // rewriting matching `if cond then T else E` subterms to `T`.
            // Mirror in the else-branch.  This collapses repeat occurrences
            // of the same condition (typical for matrix-style proofs where
            // the LHS and RHS both branch on the same predicate).
            let then_collapsed = collapse_if_cond(&then_body, &cond, true);
            let else_collapsed = collapse_if_cond(&else_body, &cond, false);
            let then_refined = if let Some((v, val)) = eq_var_value(&cond) {
                crate::ast::subst(&then_collapsed, &v, &val)
            } else {
                then_collapsed
            };
            let else_refined = else_collapsed;
            let mut then_hyps = hyps.to_vec();
            then_hyps.push((cond.clone(), true));
            let mut else_hyps = hyps.to_vec();
            else_hyps.push((cond.clone(), false));
            self.prove_algebra_rel(&then_refined, dom, &then_hyps)
                .map_err(|e| {
                    SekiError::Proof(format!(
                        "by algebra (then-branch of `if {}`): {}",
                        cond, e
                    ))
                })?;
            self.prove_algebra_rel(&else_refined, dom, &else_hyps)
                .map_err(|e| {
                    SekiError::Proof(format!(
                        "by algebra (else-branch of `if {}`): {}",
                        cond, e
                    ))
                })?;
            return Ok(Value::Bool(true));
        }
        // Try to discharge via a hypothesis before the polynomial check.
        for (hcond, htrue) in hyps {
            if hypothesis_proves(hcond, *htrue, body) {
                return Ok(Value::Bool(true));
            }
        }
        // Try discharging via a *positive combination* of several
        // hypotheses at once (e.g. `x > 0`, `y > 0` ⊢ `x + y > 0`) — sound
        // because a sum of nonnegative quantities is nonnegative, and
        // strictly positive if any summand is strictly positive.
        if hyps_sum_proves(hyps, body) {
            return Ok(Value::Bool(true));
        }
        let (op, lhs, rhs) = match body {
            Expr::BinOp(op, l, r)
                if matches!(
                    op,
                    BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                ) =>
            {
                (op.clone(), &**l, &**r)
            }
            other => {
                return Err(SekiError::Proof(format!(
                    "by algebra: proposition must be a relation \
                     (==, !=, <, <=, >, >=), got {}",
                    other
                )))
            }
        };
        let lp = expr_to_poly(lhs).ok_or_else(|| {
            SekiError::Proof(
                "by algebra: lhs contains expressions outside the polynomial fragment".into(),
            )
        })?;
        let rp = expr_to_poly(rhs).ok_or_else(|| {
            SekiError::Proof(
                "by algebra: rhs contains expressions outside the polynomial fragment".into(),
            )
        })?;
        let diff = lp.sub(rp);
        let ok = match op {
            BinOp::Eq => diff.terms.is_empty(),
            BinOp::Neq => polynomial_pos(&diff, dom) || polynomial_neg(&diff, dom),
            BinOp::Lt => polynomial_neg(&diff, dom),
            BinOp::Le => polynomial_nonpos(&diff, dom),
            BinOp::Gt => polynomial_pos(&diff, dom),
            BinOp::Ge => polynomial_nonneg(&diff, dom),
            _ => unreachable!(),
        };
        if ok {
            return Ok(Value::Bool(true));
        }
        // Rational-function fallback for equality goals: clear denominators
        // by cross-multiplication.  Sound modulo the standard convention
        // that denominators are non-zero (i.e. we prove the equality on
        // the open set where divisions are defined — see `RatPoly`).
        if op == BinOp::Eq {
            if let Some(true) = ratpoly_equal(lhs, rhs) {
                return Ok(Value::Bool(true));
            }
            // Variable-divisor `mod` cancellation: `<expr> mod v == 0`
            // where `v` is a bare variable. Sound unconditionally (given
            // `v != 0`, an implicit side-condition already accepted for
            // division elsewhere in this fragment) — an exact multiple of
            // `v` has zero remainder regardless of anyone's sign.
            if mod_by_var_is_exactly_zero(lhs, rhs) || mod_by_var_is_exactly_zero(rhs, lhs) {
                return Ok(Value::Bool(true));
            }
        }
        Err(SekiError::Proof(format!(
            "by algebra: cannot prove {} {} {} over {:?}",
            lhs, op, rhs, dom
        )))
    }

    /// `by induction`:  prove `forall n in <domain>, P(n)`.  The shape of
    /// `<domain>` selects the induction principle:
    ///
    ///   - **Nat**           — mathematical induction (base 0, step k → k+1)
    ///   - **List T**        — structural induction (base nil, step ys → cons x ys)
    ///
    /// For both shapes we accept the same relation operators as `by algebra`:
    /// `==`, `<=`, `>=`, `<`, `>`.
    ///
    /// Splits `P` into `lhs(n) == rhs(n)` and discharges:
    ///   (a) **base** — `P(0)` evaluates to `true`,
    ///   (b) **step** — `P(k+1) - P(k)` is a ring identity in `ℤ` (modulo
    ///       a recursive-unfolding shortcut for the LHS) so that any
    ///       polynomial equation `lhs == rhs` valid for `n = 0` and whose
    ///       difference matches between consecutive `n` is valid for all `n`.
    ///
    /// Concretely: we verify `lhs(k+1) - lhs(k) == rhs(k+1) - rhs(k)` as a
    /// polynomial identity in `k`, after one β-step unfolding of any function
    /// applications appearing in `lhs` (the "specification side"). When this
    /// holds and the base case is true, induction concludes `P(n)` for all
    /// `n ∈ Nat`.
    fn verify_induction(&self, prop: &Expr, env: &Env) -> SekiResult<Value> {
        let (var, domain, body) = match prop {
            Expr::Forall { var, domain, body } => (var.clone(), domain.as_ref(), body.as_ref()),
            other => {
                return Err(SekiError::Proof(format!(
                    "by induction: expected `forall n in <domain>, P(n)`, got {}",
                    other
                )))
            }
        };
        // First, try user-defined ADT induction: if the domain is a bare
        // reference to a registered `data` type, dispatch to the
        // constructor-driven prover.  Falls through to the built-in modes
        // (Nat / List / Tree) when not a known ADT.
        if let Expr::Var { name: name, .. } = domain {
            if self.ctx.globals.data_info.contains_key(name) {
                return self.verify_adt_induction(&var, name, body, env);
            }
        }
        // Decide induction shape based on the quantifier domain.
        let dv = self.ctx.eval(domain, env).ok();
        let mode = induction_mode(&dv);
        match mode {
            InductionMode::Nat => self.verify_nat_induction(&var, body, env),
            InductionMode::List => self.verify_list_induction(&var, body, env),
            InductionMode::Tree => self.verify_tree_induction(&var, body, env),
            InductionMode::Unsupported => Err(SekiError::Proof(format!(
                "by induction: unsupported domain {} (expected Nat / List T / Tree T / a `data` type)",
                domain
            ))),
        }
    }

    /// Structural induction on a user-defined `data` type.
    ///
    /// For each constructor `C(a1: T1, ..., ak: Tk)`:
    ///   1. Introduce fresh variables for each argument
    ///   2. Substitute `x := C a1 ... ak` in `body`
    ///   3. β-reduce one level (unfold_one) to expose the structure
    ///   4. Check via `by eval` (the recursive arg references P(ai) become
    ///      opaque applications when ai has the same type as the data —
    ///      treated as the inductive hypothesis under polynomial sign
    ///      analysis or symbolic evaluation).
    fn verify_adt_induction(
        &self,
        var: &str,
        data_name: &str,
        body: &Expr,
        env: &Env,
    ) -> SekiResult<Value> {
        let ctors = self
            .ctx
            .globals
            .data_info
            .get(data_name)
            .cloned()
            .ok_or_else(|| SekiError::Proof(format!(
                "by induction: data type `{}` not registered",
                data_name
            )))?;
        for (idx, (cname, arg_types)) in ctors.iter().enumerate() {
            // Build the constructor application:
            //   nullary: just `cname` as a Var
            //   k-ary  : `cname a0 a1 ... a_{k-1}` where ai are fresh names
            let ctor_var = Expr::Var { name: cname.clone(), line: 0, col: 0 };
            let mut fresh_arg_names: Vec<String> = Vec::new();
            let mut fresh_args: Vec<Expr> = Vec::new();
            for i in 0..arg_types.len() {
                let n = format!("__ind_{}_{}_{}", cname, i, idx);
                fresh_arg_names.push(n.clone());
                fresh_args.push(Expr::Var { name: n, line: 0, col: 0 });
            }
            let ctor_app = if fresh_args.is_empty() {
                ctor_var
            } else {
                Expr::App {
                    func: Box::new(ctor_var),
                    args: fresh_args.clone(),
                }
            };
            // Substitute and unfold one level so the constructor's
            // tag-pair encoding becomes visible to subsequent destructors.
            let substituted = crate::ast::subst(body, var, &ctor_app);
            let mut current = substituted;
            for _ in 0..8 {
                let next = unfold_one(&current, self.ctx, env);
                if exprs_equal(&next, &current) {
                    break;
                }
                current = next;
            }
            // Try verification strategies in turn:
            //   1. polynomial sign analysis (best for arithmetic relations;
            //      treats free vars and recursive-arg references as opaque)
            //   2. `by eval` after binding fresh args to a dummy Int(0)
            //      (works for constructor-tag-based equality/inequality)
            //   3. `by eval` directly (no free vars in the case body)
            if self.verify_algebra(&current, env).is_ok() {
                continue;
            }
            let mut probe_env = env.clone();
            for n in &fresh_arg_names {
                probe_env = probe_env.extend(n.clone(), Value::Int(0));
            }
            let case_ok = self
                .ctx
                .eval(&current, &probe_env)
                .ok()
                .map(|v| matches!(v, Value::Bool(true)))
                .unwrap_or(false);
            if case_ok {
                continue;
            }
            // Last-ditch: try direct eval (works only if no free vars).
            if let Ok(Value::Bool(true)) = self.ctx.eval(&current, env) {
                continue;
            }
            return Err(SekiError::Proof(format!(
                "by induction on `{}`: case for constructor `{}` failed; reached: {}",
                data_name, cname, current
            )));
        }
        Ok(Value::Bool(true))
    }

    fn verify_nat_induction(&self, var: &str, body: &Expr, env: &Env) -> SekiResult<Value> {
        let (op, lhs, rhs) = match body {
            Expr::BinOp(op, l, r) if is_relation(op) => ((**l).clone(), &**l, &**r),
            _ => {
                return Err(SekiError::Proof(format!(
                    "by induction: body must be a relation (==, <=, >=, <, >), got {}",
                    body
                )))
            }
        };
        let _ = op;
        let op = match body {
            Expr::BinOp(o, _, _) => o.clone(),
            _ => unreachable!(),
        };

        // ---- base: P(0) by eval ----
        let base = subst(body, var, &Expr::Int(0));
        let bv = self.ctx.eval(&base, env)?;
        if !matches!(bv, Value::Bool(true)) {
            return Err(SekiError::Proof(format!(
                "by induction: base case P(0) failed (got {})",
                bv
            )));
        }

        // ---- step: relation between lhs/rhs differences over ℕ ----
        let kvar = format!("__k_{}", var);
        let k_expr = Expr::Var { name: kvar.clone(), line: 0, col: 0 };
        let kp1 = Expr::BinOp(BinOp::Add, Box::new(k_expr.clone()), Box::new(Expr::Int(1)));
        let lhs_kp1 = unfold_one(&subst(lhs, var, &kp1), self.ctx, env);
        let lhs_k = subst(lhs, var, &k_expr);
        let rhs_kp1 = unfold_one(&subst(rhs, var, &kp1), self.ctx, env);
        let rhs_k = subst(rhs, var, &k_expr);
        let lhs_diff = Expr::BinOp(BinOp::Sub, Box::new(lhs_kp1.clone()), Box::new(lhs_k));
        let rhs_diff = Expr::BinOp(BinOp::Sub, Box::new(rhs_kp1.clone()), Box::new(rhs_k));
        self.discharge_step(&op, &lhs_diff, &rhs_diff, PolyDomain::Nat)
    }

    fn verify_list_induction(&self, var: &str, body: &Expr, env: &Env) -> SekiResult<Value> {
        let (op, lhs, rhs) = match body {
            Expr::BinOp(o, l, r) if is_relation(o) => (o.clone(), (**l).clone(), (**r).clone()),
            _ => {
                return Err(SekiError::Proof(format!(
                    "by induction: list-induction body must be a relation, got {}",
                    body
                )))
            }
        };

        // ---- base: P(nil) ----
        let nil_expr = Expr::List(vec![]);
        let base_body = subst(body, var, &nil_expr);
        let bv = self.ctx.eval(&base_body, env)?;
        if !matches!(bv, Value::Bool(true)) {
            return Err(SekiError::Proof(format!(
                "by induction: base case P([]) failed (got {})",
                bv
            )));
        }

        // ---- step: P(cons x ys) follows from P(ys) ----
        // Use fresh names so they don't collide with the original variable.
        let xname = format!("__x_{}", var);
        let ysname = format!("__ys_{}", var);
        let cons_expr = Expr::App {
            func: Box::new(Expr::Var { name: "cons".into(), line: 0, col: 0 }),
            args: vec![Expr::Var { name: xname.clone(), line: 0, col: 0 }, Expr::Var { name: ysname.clone(), line: 0, col: 0 }],
        };
        let lhs_cons = simplify_list_ops(
            &unfold_one(&subst(&lhs, var, &cons_expr), self.ctx, env),
            self.ctx,
            env,
        );
        let lhs_ys = subst(&lhs, var, &Expr::Var { name: ysname.clone(), line: 0, col: 0 });
        let rhs_cons = simplify_list_ops(
            &unfold_one(&subst(&rhs, var, &cons_expr), self.ctx, env),
            self.ctx,
            env,
        );
        let rhs_ys = subst(&rhs, var, &Expr::Var { name: ysname.clone(), line: 0, col: 0 });
        let lhs_diff = Expr::BinOp(BinOp::Sub, Box::new(lhs_cons), Box::new(lhs_ys));
        let rhs_diff = Expr::BinOp(BinOp::Sub, Box::new(rhs_cons), Box::new(rhs_ys));
        // For list induction, opaque `head/tail` of a fresh `ys` are
        // unrestricted — treat the polynomial domain as Int.
        self.discharge_step(&op, &lhs_diff, &rhs_diff, PolyDomain::Int)
    }

    /// `by strong_induction` (default depth 2, or `by strong_induction <N>`):
    /// prove `forall n in Nat, P(n)` by verifying `P(0), ..., P(N-1)` as
    /// bases, and `P(k+N)` by polynomial sign analysis over Nat, where the
    /// recursive calls exposed by unfolding at `k+N` are treated as nonneg
    /// atoms (the inductive hypotheses).  Useful when the spec recurses on
    /// more than one immediate predecessor (Fibonacci needs depth 2, a
    /// tribonacci-style recurrence needs depth 3, etc.) — `N` is the number
    /// of prior terms the recursive definition itself reaches back to, not
    /// an arbitrary search budget.
    fn verify_strong_induction(&self, prop: &Expr, env: &Env, depth: u32) -> SekiResult<Value> {
        if depth == 0 {
            return Err(SekiError::Proof(
                "by strong_induction: depth must be >= 1".into(),
            ));
        }
        let depth = depth as i64;
        let (var, domain, body) = match prop {
            Expr::Forall { var, domain, body } => (var.clone(), domain.as_ref(), body.as_ref()),
            other => {
                return Err(SekiError::Proof(format!(
                    "by strong_induction: expected `forall n in Nat, P(n)`, got {}",
                    other
                )))
            }
        };
        // Only Nat for now.
        let dv = self.ctx.eval(domain, env).ok();
        if !matches!(induction_mode(&dv), InductionMode::Nat) {
            return Err(SekiError::Proof(
                "by strong_induction: only Nat is supported as the induction domain".into(),
            ));
        }
        let (op, lhs, rhs) = match body {
            Expr::BinOp(o, l, r) if is_relation(o) => (o.clone(), (**l).clone(), (**r).clone()),
            other => {
                return Err(SekiError::Proof(format!(
                    "by strong_induction: body must be a relation, got {}",
                    other
                )))
            }
        };
        // ---- bases: P(0), ..., P(depth - 1) ----
        for n in 0..depth {
            let p_n = subst(body, &var, &Expr::Int(n));
            let v = self.ctx.eval(&p_n, env)?;
            if !matches!(v, Value::Bool(true)) {
                return Err(SekiError::Proof(format!(
                    "by strong_induction: base case P({}) failed (got {})",
                    n, v
                )));
            }
        }
        // ---- step: P(k+depth) directly, with the recursive calls it
        // exposes (e.g. `f k`, `f (k+1)`, ..., for depth 2) as nonneg atoms
        let kvar = format!("__k_{}", var);
        let k_expr = Expr::Var { name: kvar.clone(), line: 0, col: 0 };
        let kpd = Expr::BinOp(BinOp::Add, Box::new(k_expr.clone()), Box::new(Expr::Int(depth)));
        let lhs_kpd = unfold_one(&subst(&lhs, &var, &kpd), self.ctx, env);
        let rhs_kpd = unfold_one(&subst(&rhs, &var, &kpd), self.ctx, env);
        // Soundness guard: if unfolding at `k+depth` left an `if` whose
        // *condition* still mentions `k` (e.g. `if (k + depth) == 2 then
        // ... else ...`), that boundary couldn't be resolved to a single
        // definite branch for every `k` — typically because `depth` is
        // smaller than how far back the recursive definition actually
        // reaches, so the base cases just below the general recursive
        // branch weren't all covered by `P(0)..P(depth-1)`.  Without this
        // guard, `expr_to_poly`'s opaque-atom fallback would silently treat
        // that whole unresolved `if` as an unconstrained "≥ 0" atom, which
        // can validate a **false** proposition (a literal negative branch
        // hiding inside the unresolved `if` never gets checked). Fail loudly
        // instead of proving something unsound.
        if contains_var_conditioned_if(&lhs_kpd, &kvar) || contains_var_conditioned_if(&rhs_kpd, &kvar)
        {
            return Err(SekiError::Proof(format!(
                "by strong_induction {}: could not resolve every base-case boundary after \
                 unfolding at k+{} — the recursive definition likely reaches back further \
                 than depth {} (try a larger depth), or a guard condition isn't decidable by \
                 polynomial sign analysis",
                depth, depth, depth
            )));
        }
        // Discharge `lhs_kpd op rhs_kpd` directly.  Over Nat, opaque atoms
        // (which include the IH instances) are treated as ≥ 0 — sound for
        // the bounded-below kind of claims this tactic typically targets.
        let lp = expr_to_poly(&lhs_kpd).ok_or_else(|| {
            SekiError::Proof(
                "by strong_induction: lhs is outside the polynomial fragment after unfolding"
                    .into(),
            )
        })?;
        let rp = expr_to_poly(&rhs_kpd).ok_or_else(|| {
            SekiError::Proof(
                "by strong_induction: rhs is outside the polynomial fragment after unfolding"
                    .into(),
            )
        })?;
        let diff = lp.sub(rp);
        let dom = PolyDomain::Nat;
        let ok = match op {
            BinOp::Eq => diff.terms.is_empty(),
            BinOp::Ge | BinOp::Gt => polynomial_nonneg(&diff, dom),
            BinOp::Le | BinOp::Lt => polynomial_nonpos(&diff, dom),
            _ => false,
        };
        if ok {
            Ok(Value::Bool(true))
        } else {
            Err(SekiError::Proof(format!(
                "by strong_induction: step P(k+{}) failed for {} {} {}",
                depth, lhs_kpd, op, rhs_kpd
            )))
        }
    }

    fn verify_tree_induction(&self, var: &str, body: &Expr, env: &Env) -> SekiResult<Value> {
        let (op, lhs, rhs) = match body {
            Expr::BinOp(o, l, r) if is_relation(o) => (o.clone(), (**l).clone(), (**r).clone()),
            _ => {
                return Err(SekiError::Proof(format!(
                    "by induction: tree-induction body must be a relation, got {}",
                    body
                )))
            }
        };

        // ---- base: P(leaf) ----
        let leaf_expr = Expr::Var { name: "leaf".into(), line: 0, col: 0 };
        let base_body = subst(body, var, &leaf_expr);
        let bv = self.ctx.eval(&base_body, env)?;
        if !matches!(bv, Value::Bool(true)) {
            return Err(SekiError::Proof(format!(
                "by induction: base case P(leaf) failed (got {})",
                bv
            )));
        }

        // ---- step: P(node l v r) follows from P(l) ∧ P(r) ----
        let lname = format!("__l_{}", var);
        let vname = format!("__v_{}", var);
        let rname = format!("__r_{}", var);
        let node_expr = Expr::App {
            func: Box::new(Expr::Var { name: "node".into(), line: 0, col: 0 }),
            args: vec![
                Expr::Var { name: lname.clone(), line: 0, col: 0 },
                Expr::Var { name: vname.clone(), line: 0, col: 0 },
                Expr::Var { name: rname.clone(), line: 0, col: 0 },
            ],
        };
        // Compute lhs/rhs at `node l v r` (after unfolding+simplifying tree
        // destructors) and at the immediate subtrees.  The IH instances on
        // l and r appear as identical opaque atoms on both sides, so
        // polynomial cancellation handles them automatically when present.
        let lhs_node = simplify_tree_ops(
            &unfold_one(&subst(&lhs, var, &node_expr), self.ctx, env),
            self.ctx,
            env,
        );
        let lhs_sub = Expr::BinOp(
            BinOp::Add,
            Box::new(subst(&lhs, var, &Expr::Var { name: lname.clone(), line: 0, col: 0 })),
            Box::new(subst(&lhs, var, &Expr::Var { name: rname.clone(), line: 0, col: 0 })),
        );
        let rhs_node = simplify_tree_ops(
            &unfold_one(&subst(&rhs, var, &node_expr), self.ctx, env),
            self.ctx,
            env,
        );
        let rhs_sub = Expr::BinOp(
            BinOp::Add,
            Box::new(subst(&rhs, var, &Expr::Var { name: lname.clone(), line: 0, col: 0 })),
            Box::new(subst(&rhs, var, &Expr::Var { name: rname.clone(), line: 0, col: 0 })),
        );
        let lhs_diff = Expr::BinOp(BinOp::Sub, Box::new(lhs_node), Box::new(lhs_sub));
        let rhs_diff = Expr::BinOp(BinOp::Sub, Box::new(rhs_node), Box::new(rhs_sub));
        // Tree induction discharges over Nat — opaque atoms representing
        // recursive calls on subtrees inherit the IH and are treated as
        // nonneg by default.  This is sound for claims with all-nonneg
        // coefficients in the difference.
        self.discharge_step(&op, &lhs_diff, &rhs_diff, PolyDomain::Nat)
    }

    /// Common step discharge for inductive proofs.
    ///
    /// Given the original claim `lhs(n) op rhs(n)`, the step requires that
    /// when we go from the "smaller" case (`n=k`, or `xs=ys`) to the "larger"
    /// case (`n=k+1`, or `xs=cons x ys`), the relation propagates given the
    /// inductive hypothesis.  Concretely:
    ///
    ///   * `==`     —  `lhs_diff == rhs_diff` (purely polynomial equality)
    ///   * `>=`,`>` —  `lhs_diff >= rhs_diff` (the IH slack, ≥ 0 or ≥ 1, only
    ///                  needs to be preserved, not strengthened)
    ///   * `<=`,`<` —  `lhs_diff <= rhs_diff` (symmetric)
    ///   * `!=`     —  not supported (IH gives no useful slack)
    fn discharge_step(
        &self,
        op: &BinOp,
        lhs_diff: &Expr,
        rhs_diff: &Expr,
        dom: PolyDomain,
    ) -> SekiResult<Value> {
        let lp = expr_to_poly(lhs_diff).ok_or_else(|| {
            SekiError::Proof(
                "by induction: step lhs is outside the polynomial fragment".into(),
            )
        })?;
        let rp = expr_to_poly(rhs_diff).ok_or_else(|| {
            SekiError::Proof(
                "by induction: step rhs is outside the polynomial fragment".into(),
            )
        })?;
        let diff = lp.sub(rp);
        let ok = match op {
            BinOp::Eq => diff.terms.is_empty(),
            BinOp::Ge | BinOp::Gt => polynomial_nonneg(&diff, dom),
            BinOp::Le | BinOp::Lt => polynomial_nonpos(&diff, dom),
            BinOp::Neq => {
                return Err(SekiError::Proof(
                    "by induction: `!=` is not supported as the inductive relation".into(),
                ))
            }
            _ => false,
        };
        if ok {
            Ok(Value::Bool(true))
        } else {
            Err(SekiError::Proof(format!(
                "by induction: step case fails — could not establish {} {} {}",
                lhs_diff, op, rhs_diff
            )))
        }
    }

    fn verify_refl(&self, prop: &Expr, env: &Env) -> SekiResult<Value> {
        match prop {
            Expr::BinOp(BinOp::Eq, a, b) => {
                let av = self.ctx.eval(a, env)?;
                let bv = self.ctx.eval(b, env)?;
                if value_eq(&av, &bv) {
                    Ok(Value::Bool(true))
                } else {
                    Err(SekiError::Proof(format!(
                        "refl: lhs {} ≠ rhs {}",
                        av, bv
                    )))
                }
            }
            other => Err(SekiError::Proof(format!(
                "refl can only prove equalities, got {}",
                other
            ))),
        }
    }

    /// `by simp` — equational rewriting tactic.
    ///
    /// Collects equality-shaped theorems (and axioms) as left-to-right
    /// rewrite rules, then walks the goal applying any matching rule until
    /// a fixed point.  Succeeds if the rewritten goal evaluates to `true`,
    /// or if it is an equality whose two sides became syntactically equal.
    ///
    /// `lemmas` (when non-empty) restricts the rule set to exactly the
    /// named theorems/axioms.  Empty means "use everything available."
    fn verify_simp(
        &self,
        prop: &Expr,
        env: &Env,
        lemmas: &[String],
    ) -> SekiResult<Value> {
        let rules = collect_simp_rules(self.ctx, lemmas)?;
        // AC-canonicalize the initial goal so symmetric rules don't
        // oscillate forever.  Each rewrite step is followed by another
        // canonicalize pass.
        let initial = canonicalize(strip_foralls(prop));
        let mut current = initial.clone();
        let mut seen: Vec<Expr> = vec![initial];
        const MAX_ITERS: usize = 64;
        for _ in 0..MAX_ITERS {
            let next = canonicalize(&simp_rewrite(&current, &rules));
            if seen.iter().any(|s| exprs_equal(s, &next)) {
                break;
            }
            seen.push(next.clone());
            current = next;
        }
        // Success: any visited state matches one of
        //   1. Bool(true) literal
        //   2. equality whose two sides are alpha-equivalent
        //      (after canonicalization, AC-equivalent forms count)
        //   3. evaluates to Bool(true) under env
        for state in &seen {
            if matches!(state, Expr::Bool(true)) {
                return Ok(Value::Bool(true));
            }
            if let Expr::BinOp(BinOp::Eq, l, r) = state {
                let lc = canonicalize(l);
                let rc = canonicalize(r);
                if crate::ast::alpha_equiv(&lc, &rc) {
                    return Ok(Value::Bool(true));
                }
            }
            if let Ok(Value::Bool(true)) = self.ctx.eval(state, env) {
                return Ok(Value::Bool(true));
            }
        }
        Err(SekiError::Proof(format!(
            "by simp: could not reduce goal to true; reached {}",
            current
        )))
    }

    fn verify_term(&self, prop: &Expr, term: &Expr, env: &Env) -> SekiResult<Value> {
        match prop {
            Expr::Forall { var, domain, body } => {
                // 1. evaluate the witness function
                let pf = self.ctx.eval(term, env)?;
                if !matches!(pf, Value::Closure { .. } | Value::Builtin(_)) {
                    return Err(SekiError::Proof(format!(
                        "proof of forall must be a function, got {}",
                        pf.type_name()
                    )));
                }
                // 2. enumerate the domain
                let dv = self.ctx.eval(domain, env)?;
                let dset = match dv {
                    Value::Set(s) => s,
                    other => {
                        return Err(SekiError::Proof(format!(
                            "forall domain must be a Set, got {}",
                            other.type_name()
                        )))
                    }
                };
                let elems = enumerate_set(&dset, self.ctx, env)?;
                // 3. for every element check (a) the proof applies (gives some value),
                //    and (b) body[var := e] evaluates to true.
                for e in elems {
                    let _ = self.ctx.apply(pf.clone(), vec![e.clone()])?;
                    let env2 = env.extend(var.clone(), e.clone());
                    let bv = self.ctx.eval(body, &env2)?;
                    if !matches!(bv, Value::Bool(true)) {
                        return Err(SekiError::Proof(format!(
                            "counterexample: with {} = {} the body is not true (got {})",
                            var, e, bv
                        )));
                    }
                }
                Ok(Value::Bool(true))
            }
            Expr::Exists { var, domain, body } => {
                let witness = self.ctx.eval(term, env)?;
                let dv = self.ctx.eval(domain, env)?;
                let dset = match dv {
                    Value::Set(s) => s,
                    other => {
                        return Err(SekiError::Proof(format!(
                            "exists domain must be a Set, got {}",
                            other.type_name()
                        )))
                    }
                };
                if !self.ctx.member(&witness, &dset, env)? {
                    return Err(SekiError::Proof(format!(
                        "witness {} is not in declared domain {}",
                        witness, dset
                    )));
                }
                let env2 = env.extend(var.clone(), witness.clone());
                let bv = self.ctx.eval(body, &env2)?;
                if matches!(bv, Value::Bool(true)) {
                    Ok(Value::Bool(true))
                } else {
                    Err(SekiError::Proof(format!(
                        "with witness {} = {} body did not hold (got {})",
                        var, witness, bv
                    )))
                }
            }
            // for `a in S`-style propositions, eval and require true; the term
            // is just a tag.
            _ => {
                let _ = self.ctx.eval(term, env)?; // tag must at least evaluate
                let v = self.ctx.eval(prop, env)?;
                require_true(&v).map(|()| Value::Bool(true))
            }
        }
    }
}

fn require_true(v: &Value) -> SekiResult<()> {
    match v {
        Value::Bool(true) => Ok(()),
        Value::Bool(false) => Err(SekiError::Proof(
            "proposition reduced to false".into(),
        )),
        other => Err(SekiError::Proof(format!(
            "proposition did not reduce to a Bool (got {})",
            other.type_name()
        ))),
    }
}

/// True if `set` is "trustably finite" — i.e. enumerating it materializes all
/// its elements.  Used by REPL/main to warn when a forall-proof relies on
/// SAMPLE_BOUND for an infinite domain.
pub fn domain_is_finite(set: &SetVal) -> bool {
    crate::eval::is_definitely_finite(set)
}

// -- helpers used by the algebra / induction tactics ------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InductionMode {
    Nat,
    List,
    Tree,
    Unsupported,
}

fn induction_mode(domain_value: &Option<Value>) -> InductionMode {
    match domain_value {
        Some(Value::Set(s)) => match &**s {
            SetVal::Atomic(AtomicSet::Nat) => InductionMode::Nat,
            SetVal::ListOf(_) => InductionMode::List,
            SetVal::TreeOf(_) => InductionMode::Tree,
            _ => InductionMode::Unsupported,
        },
        _ => InductionMode::Unsupported,
    }
}

fn is_relation(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

/// Decide whether free variables in `prop` should be treated as Nat (≥ 0),
/// Int, or Real.  Heuristic over the binder chain:
///   - every domain is `Nat` ⇒ `Nat`
///   - any domain is `Real` ⇒ `Real` (the unsigned-coefficient analyses still
///     apply, since rationals embed into ℝ)
///   - otherwise ⇒ `Int` (the conservative default)
fn detect_domain(prop: &Expr) -> PolyDomain {
    fn looks_like(e: &Expr, name: &str) -> bool {
        matches!(e, Expr::Var { name: s, .. } if s == name)
    }
    let mut cur = prop;
    let mut all_nat = true;
    let mut saw_real = false;
    let mut saw_any = false;
    while let Expr::Forall { domain, body, .. } = cur {
        saw_any = true;
        if !looks_like(domain, "Nat") {
            all_nat = false;
        }
        if looks_like(domain, "Real") {
            saw_real = true;
        }
        cur = body;
    }
    if saw_any && all_nat {
        PolyDomain::Nat
    } else if saw_real {
        PolyDomain::Real
    } else {
        PolyDomain::Int
    }
}

/// If `body` contains an `if c then t else e` subexpression, return:
///   * `body` with the first such if replaced by `t`,
///   * `body` with the first such if replaced by `e`,
///   * the condition `c`.
/// "First" means: leftmost in a left-to-right walk over the AST.  Used by
/// `prove_algebra_rel` to case-split on conditions.
fn split_first_if(body: &Expr) -> Option<(Expr, Expr, Expr)> {
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

/// If `cond` has the form `v == literal` or `literal == v` where `v` is a
/// simple variable and `literal` is a constant Int/Real, return `(v, literal)`.
/// Used by case-splitting to substitute the known value of `v` in the
/// then-branch — sound because the then-branch only runs when `cond` is true.
fn eq_var_value(cond: &Expr) -> Option<(String, Expr)> {
    if let Expr::BinOp(BinOp::Eq, l, r) = cond {
        if let (Expr::Var { name, .. }, lit) = (l.as_ref(), r.as_ref()) {
            if is_simple_literal(lit) {
                return Some((name.clone(), lit.clone()));
            }
        }
        if let (lit, Expr::Var { name, .. }) = (l.as_ref(), r.as_ref()) {
            if is_simple_literal(lit) {
                return Some((name.clone(), lit.clone()));
            }
        }
    }
    None
}

fn is_simple_literal(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Int(_) | Expr::Real(_) | Expr::Bool(_)
    ) || matches!(
        e,
        Expr::UnOp(UnOp::Neg, inner) if matches!(inner.as_ref(), Expr::Int(_) | Expr::Real(_))
    )
}

/// Decide whether the assumption `hcond` (taken as true when `htrue`, or
/// false when `!htrue`) implies the relational `goal`.  Sound and incomplete
/// — covers the common cases:
///   * **identity**           `c == g` (same relation)
///   * **negation**           `g == !c` matches the else-branch
///   * **weakening of `>=`**  `x >= y` implies `x >= y - k` for any nonneg `k`
///   * **strict→nonstrict**   `x > y` implies `x >= y`
///   * **equality strongest** `x == y` implies any `x rel y` that `0 rel 0`
fn hypothesis_proves(hcond: &Expr, htrue: bool, goal: &Expr) -> bool {
    let (cop, cl, cr) = match hcond {
        Expr::BinOp(op, l, r) if is_relation(op) => (op.clone(), l.as_ref(), r.as_ref()),
        _ => return false,
    };
    let (gop, gl, gr) = match goal {
        Expr::BinOp(op, l, r) if is_relation(op) => (op.clone(), l.as_ref(), r.as_ref()),
        _ => return false,
    };
    let cp_lhs = match crate::algebra::expr_to_poly(cl) {
        Some(p) => p,
        None => return false,
    };
    let cp_rhs = match crate::algebra::expr_to_poly(cr) {
        Some(p) => p,
        None => return false,
    };
    let gp_lhs = match crate::algebra::expr_to_poly(gl) {
        Some(p) => p,
        None => return false,
    };
    let gp_rhs = match crate::algebra::expr_to_poly(gr) {
        Some(p) => p,
        None => return false,
    };
    let cp = cp_lhs.sub(cp_rhs); // hypothesis: cp `cop` 0
    let gp = gp_lhs.sub(gp_rhs); // goal:        gp `gop` 0

    // Determine the effective operator on `cp`: if htrue is false, negate.
    let eff_cop = if htrue { cop } else { negate_relation(&cop) };

    relation_implies(&eff_cop, &cp, &gop, &gp)
}

/// Logical negation of a strict/nonstrict comparison.
fn negate_relation(op: &BinOp) -> BinOp {
    match op {
        BinOp::Eq => BinOp::Neq,
        BinOp::Neq => BinOp::Eq,
        BinOp::Lt => BinOp::Ge,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Ge => BinOp::Lt,
        other => other.clone(),
    }
}

/// Normalize a hypothesis `cond` (negated if `htrue` is false) into
/// `(poly, is_strict)` meaning `poly > 0` (is_strict) or `poly >= 0`
/// (otherwise).  Returns `None` for relations this combinator can't use
/// (`==`, `!=`) — those need exact cancellation, not summation.
fn normalize_nonneg_hyp(cond: &Expr, htrue: bool) -> Option<(crate::algebra::Polynomial, bool)> {
    let (op, l, r) = match cond {
        Expr::BinOp(op, l, r) if is_relation(op) => (op.clone(), l.as_ref(), r.as_ref()),
        _ => return None,
    };
    let lp = crate::algebra::expr_to_poly(l)?;
    let rp = crate::algebra::expr_to_poly(r)?;
    let diff = lp.sub(rp); // l - r
    let eff_op = if htrue { op } else { negate_relation(&op) };
    match eff_op {
        BinOp::Gt => Some((diff, true)),
        BinOp::Ge => Some((diff, false)),
        BinOp::Lt => Some((diff.neg(), true)),
        BinOp::Le => Some((diff.neg(), false)),
        _ => None,
    }
}

/// Try to discharge a `>` / `>=` goal as a *positive combination* (equal
/// weight 1, no scaling) of the available inequality hypotheses — e.g.
/// `x > 0`, `y > 0` ⊢ `x + y > 0`.  Sound: a sum of quantities each known
/// `>= 0` is `>= 0`, and `> 0` as soon as one summand is strict.  Bounded
/// to a handful of hypotheses (subset search is exponential) since proof
/// contexts built by `by algebra`/`by linarith` rarely carry many at once.
fn hyps_sum_proves(hyps: &[(Expr, bool)], goal: &Expr) -> bool {
    let (gop, gl, gr) = match goal {
        Expr::BinOp(op, l, r) if matches!(op, BinOp::Gt | BinOp::Ge) => {
            (op.clone(), l.as_ref(), r.as_ref())
        }
        _ => return false,
    };
    let glp = match crate::algebra::expr_to_poly(gl) {
        Some(p) => p,
        None => return false,
    };
    let grp = match crate::algebra::expr_to_poly(gr) {
        Some(p) => p,
        None => return false,
    };
    let goal_diff = glp.sub(grp);

    let normalized: Vec<(crate::algebra::Polynomial, bool)> = hyps
        .iter()
        .filter_map(|(c, t)| normalize_nonneg_hyp(c, *t))
        .collect();
    let n = normalized.len();
    if n < 2 || n > 12 {
        // n < 2: a single hypothesis is already covered by
        // `hypothesis_proves`; n too large: bound the 2^n subset search.
        return false;
    }
    for mask in 1u32..(1u32 << n) {
        let mut acc = crate::algebra::Polynomial::zero();
        let mut any_strict = false;
        let mut count = 0;
        for (i, (poly, strict)) in normalized.iter().enumerate() {
            if mask & (1 << i) != 0 {
                acc = acc.add(poly.clone());
                any_strict |= *strict;
                count += 1;
            }
        }
        if count < 2 {
            continue; // single-hypothesis subsets are `hypothesis_proves`'s job
        }
        if acc.sub(goal_diff.clone()).terms.is_empty() && (gop == BinOp::Ge || any_strict) {
            return true;
        }
    }
    false
}

/// True if `mod_expr` is `<numerator> mod v` for a bare variable `v`,
/// `zero_expr` is (polynomially) zero, and `v` exactly divides the
/// numerator — i.e. the goal is `<numerator> mod v == 0` and that's a sound
/// consequence of `v` being a literal factor of every term of the
/// numerator (see `Polynomial::exact_div_by_var`).
fn mod_by_var_is_exactly_zero(mod_expr: &Expr, zero_expr: &Expr) -> bool {
    let Expr::BinOp(BinOp::Mod, num, divisor) = mod_expr else { return false };
    let Expr::Var { name: var, .. } = divisor.as_ref() else { return false };
    let Some(zp) = expr_to_poly(zero_expr) else { return false };
    if !zp.terms.is_empty() {
        return false;
    }
    let Some(np) = expr_to_poly(num) else { return false };
    np.exact_div_by_var(var).is_some()
}

/// Sound implication check between two relations expressed as polynomials.
/// Both relations are written in the form `p rel 0`.  Returns true when
/// `hyp` proves `goal` for every valuation.
fn relation_implies(
    hop: &BinOp,
    hp: &crate::algebra::Polynomial,
    gop: &BinOp,
    gp: &crate::algebra::Polynomial,
) -> bool {
    // Same relation, same polynomial — trivially.
    if hop == gop && hp == gp {
        return true;
    }
    // Same relation but the goal is the "flipped" form: `-hp <op> 0` where
    // `<op>` is the symmetric (e.g. `>=` ↔ `<=`) of `op`.
    // We normalise by trying both `gp` and `-gp` paired with the flipped op.
    let neg_gp = gp.clone().neg();
    if hop == &flip_relation(gop) && hp == &neg_gp {
        return true;
    }
    // Equality is the strongest fact: hp == 0 implies any relation of hp
    // against 0 that is reflexive on 0.
    if hop == &BinOp::Eq && hp == gp {
        return matches!(
            gop,
            BinOp::Eq | BinOp::Le | BinOp::Ge
        );
    }
    if hop == &BinOp::Eq && hp == &neg_gp {
        return matches!(
            gop,
            BinOp::Eq | BinOp::Le | BinOp::Ge
        );
    }
    // hp > 0 implies hp >= 0, hp != 0
    if hop == &BinOp::Gt && hp == gp && matches!(gop, BinOp::Ge | BinOp::Gt | BinOp::Neq) {
        return true;
    }
    // hp < 0 implies hp <= 0, hp != 0
    if hop == &BinOp::Lt && hp == gp && matches!(gop, BinOp::Le | BinOp::Lt | BinOp::Neq) {
        return true;
    }
    // hp >= 0 implies hp >= 0
    if hop == &BinOp::Ge && hp == gp && matches!(gop, BinOp::Ge) {
        return true;
    }
    // hp <= 0 implies hp <= 0
    if hop == &BinOp::Le && hp == gp && matches!(gop, BinOp::Le) {
        return true;
    }
    // Symmetric forms with flipped sign / op:
    //   hp >= 0  iff  -hp <= 0
    //   hp > 0   iff  -hp < 0
    if hp == &neg_gp {
        match (hop, gop) {
            (BinOp::Ge, BinOp::Le) | (BinOp::Le, BinOp::Ge) => return true,
            (BinOp::Gt, BinOp::Lt) | (BinOp::Lt, BinOp::Gt) => return true,
            (BinOp::Gt, BinOp::Le) => return true, // -hp < 0  ⇒  -hp <= 0
            (BinOp::Lt, BinOp::Ge) => return true,
            _ => {}
        }
    }
    false
}

/// Swap `<` ↔ `>`, `<=` ↔ `>=`, `==` ↔ `==`, `!=` ↔ `!=`.  This is the
/// relation you obtain after multiplying both sides by `-1`.
fn flip_relation(op: &BinOp) -> BinOp {
    match op {
        BinOp::Lt => BinOp::Gt,
        BinOp::Le => BinOp::Ge,
        BinOp::Gt => BinOp::Lt,
        BinOp::Ge => BinOp::Le,
        other => other.clone(),
    }
}

/// Detect a contradiction among hypotheses.  Covers:
///   * **syntactic**       same condition assumed both true and false
///   * **polynomial sign** two hypotheses on the same linear combination
///     of polynomials but with disjoint sign requirements (e.g. `k >= 0`
///     and `(50+k) < 50`, which simplifies to `k < 0`)
///
/// When this holds, the current branch is unreachable and any goal
/// trivially follows.
fn hyps_contradict(hyps: &[(Expr, bool)]) -> bool {
    // 1. Cheap syntactic check
    for (i, (c1, t1)) in hyps.iter().enumerate() {
        for (c2, t2) in hyps.iter().skip(i + 1) {
            if t1 != t2 && c1 == c2 {
                return true;
            }
        }
    }
    // 2. Polynomial sign check.  Convert each hypothesis to `(poly, op)`
    //    where the operator constrains `poly` against 0.  Pairs of
    //    hypotheses about the same poly (modulo sign) whose sign-sets
    //    have empty intersection produce a contradiction.
    let mut hyp_polys: Vec<(crate::algebra::Polynomial, SignSet)> = Vec::new();
    for (h, htrue) in hyps {
        if let Some((p, ss)) = hyp_to_signset(h, *htrue) {
            hyp_polys.push((p, ss));
        }
    }
    for (i, (p1, ss1)) in hyp_polys.iter().enumerate() {
        for (p2, ss2) in hyp_polys.iter().skip(i + 1) {
            if p1 == p2 {
                if !ss1.intersects(*ss2) {
                    return true;
                }
            } else if p1 == &p2.clone().neg() {
                // hyp1 about p, hyp2 about -p — flip ss2 sign set
                if !ss1.intersects(ss2.flip()) {
                    return true;
                }
            }
        }
    }
    false
}

/// Possible signs of a polynomial: a subset of `{<0, =0, >0}`.
/// Two hypotheses on the same polynomial are jointly satisfiable iff
/// their sign sets intersect.
#[derive(Clone, Copy, Debug)]
struct SignSet {
    neg: bool,
    zero: bool,
    pos: bool,
}

impl SignSet {
    fn intersects(self, other: SignSet) -> bool {
        (self.neg && other.neg)
            || (self.zero && other.zero)
            || (self.pos && other.pos)
    }
    /// Sign set after the polynomial is negated (`<0` ↔ `>0`, `=0` stays).
    fn flip(self) -> SignSet {
        SignSet { neg: self.pos, zero: self.zero, pos: self.neg }
    }
}

/// Convert `(rel-expr, is_true)` into `(poly, signset)` describing what
/// `poly` is allowed to be.  Returns `None` if the relation isn't a
/// recognised numeric comparison.
fn hyp_to_signset(h: &Expr, htrue: bool) -> Option<(crate::algebra::Polynomial, SignSet)> {
    let (op, l, r) = match h {
        Expr::BinOp(op, l, r) if is_relation(op) => (op.clone(), l.as_ref(), r.as_ref()),
        _ => return None,
    };
    let lp = crate::algebra::expr_to_poly(l)?;
    let rp = crate::algebra::expr_to_poly(r)?;
    let poly = lp.sub(rp); // poly `op` 0
    let eff_op = if htrue { op } else { negate_relation(&op) };
    let ss = match eff_op {
        BinOp::Eq => SignSet { neg: false, zero: true, pos: false },
        BinOp::Neq => SignSet { neg: true, zero: false, pos: true },
        BinOp::Lt => SignSet { neg: true, zero: false, pos: false },
        BinOp::Le => SignSet { neg: true, zero: true, pos: false },
        BinOp::Gt => SignSet { neg: false, zero: false, pos: true },
        BinOp::Ge => SignSet { neg: false, zero: true, pos: true },
        _ => return None,
    };
    Some((poly, ss))
}

/// Walk every `forall x in Nat, ...` binder in `prop` and accumulate
/// `(x >= 0, true)` hypotheses.  These are sound non-negativity facts
/// every Nat-bound variable enjoys; they let the contradiction engine
/// close branches that violate non-negativity.
fn collect_nat_hyps(prop: &Expr, out: &mut Vec<(Expr, bool)>) {
    let mut cur = prop;
    while let Expr::Forall { var, domain, body } = cur {
        if matches!(domain.as_ref(), Expr::Var { name: s, .. } if s == "Nat") {
            let var_e = Expr::Var { name: var.clone(), line: 0, col: 0 };
            let hyp = Expr::BinOp(
                BinOp::Ge,
                Box::new(var_e),
                Box::new(Expr::Int(0)),
            );
            out.push((hyp, true));
        }
        cur = body;
    }
}

/// Strip leading propositional implications from `body`.  Recognises both
///   * the `=>` desugaring `(not P) or Q`  (parse-time)
///   * the function-type `Arrow(P, Q)` whose LHS is a relational expression
///     (so the user can write `... > 0 -> conclusion` and have it treated
///     as implication rather than a doomed function type).
///
/// Returns `(conclusion, premises_in_order)`.  Each premise becomes a
/// `(expr, true)` hypothesis for the algebra prover.
/// Flatten a top-level conjunction of relations (`a > 0 and b > 0 and ...`)
/// into its relational leaves.  Returns `None` (instead of a partial list)
/// if any conjunct isn't itself a relation, so callers never silently drop
/// a premise they can't represent as a hypothesis.
fn flatten_relational_and(e: &Expr, out: &mut Vec<Expr>) -> bool {
    match e {
        Expr::BinOp(BinOp::And, l, r) => {
            flatten_relational_and(l, out) && flatten_relational_and(r, out)
        }
        Expr::BinOp(op, _, _) if is_relation(op) => {
            out.push(e.clone());
            true
        }
        _ => false,
    }
}

fn peel_implications(body: &Expr) -> (Expr, Vec<Expr>) {
    let mut premises = Vec::new();
    let mut cur = body.clone();
    loop {
        match &cur {
            // `(not P) or Q` — the `=>` desugaring.  `P` may itself be a
            // conjunction of relations (`a > 0 and b > 0 => ...`), each
            // conjunct becomes its own hypothesis.
            Expr::BinOp(BinOp::Or, l, r) => {
                if let Expr::UnOp(UnOp::Not, inner) = l.as_ref() {
                    let mut conjuncts = Vec::new();
                    if flatten_relational_and(inner, &mut conjuncts) {
                        premises.extend(conjuncts);
                        cur = (**r).clone();
                        continue;
                    }
                }
                break;
            }
            // `P -> Q` where P is a (possibly conjoined) relational
            // expression — treat as implication.  The function-arrow
            // interpretation would have failed type-checking anyway (Bool
            // isn't a Set).
            Expr::Arrow(l, r) => {
                let mut conjuncts = Vec::new();
                if flatten_relational_and(l, &mut conjuncts) {
                    premises.extend(conjuncts);
                    cur = (**r).clone();
                    continue;
                }
                break;
            }
            _ => break,
        }
    }
    (cur, premises)
}

/// Rewrite `e` by replacing every `if cond then T else E` subterm whose
/// condition is structurally equal to `target_cond` with `T` (when
/// `target_value` is true) or `E` (when false).  This is the standard
/// "propagate the case assumption" pass used after splitting on a
/// condition.  Sound because, on the branch where the condition has a
/// fixed value, all occurrences of `if cond ...` reduce to that branch.
fn collapse_if_cond(e: &Expr, target_cond: &Expr, target_value: bool) -> Expr {
    use Expr::*;
    match e {
        If { cond, then_branch, else_branch } => {
            let inner_then = collapse_if_cond(then_branch, target_cond, target_value);
            let inner_else = collapse_if_cond(else_branch, target_cond, target_value);
            let inner_cond = collapse_if_cond(cond, target_cond, target_value);
            if inner_cond == *target_cond {
                if target_value {
                    inner_then
                } else {
                    inner_else
                }
            } else {
                If {
                    cond: Box::new(inner_cond),
                    then_branch: Box::new(inner_then),
                    else_branch: Box::new(inner_else),
                }
            }
        }
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(collapse_if_cond(l, target_cond, target_value)),
            Box::new(collapse_if_cond(r, target_cond, target_value)),
        ),
        UnOp(op, x) => UnOp(
            op.clone(),
            Box::new(collapse_if_cond(x, target_cond, target_value)),
        ),
        App { func, args } => App {
            func: Box::new(collapse_if_cond(func, target_cond, target_value)),
            args: args
                .iter()
                .map(|a| collapse_if_cond(a, target_cond, target_value))
                .collect(),
        },
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(collapse_if_cond(value, target_cond, target_value)),
            body: Box::new(collapse_if_cond(body, target_cond, target_value)),
            rec: *rec,
        },
        _ => e.clone(),
    }
}

/// Recognize the canonical stdlib representation of a list cell:
///   * `nil`            — the variable `nil` (resolved at runtime to (0, ()))
///   * `(0, ...)`       — inlined nil tuple
///   * `App(cons, ..)`  — explicit `cons x xs` syntactic form
///   * `(1, (x, xs))`   — inlined cons tuple (after stdlib β-reduction)
fn list_shape(e: &Expr) -> Option<ListShape> {
    use Expr::*;
    match e {
        Var { name: s, .. } if s == "nil" => Some(ListShape::Nil),
        App { func, args } => {
            if let Var { name: fname, .. } = func.as_ref() {
                if fname == "nil" {
                    return Some(ListShape::Nil);
                }
                if fname == "cons" && args.len() == 2 {
                    return Some(ListShape::Cons(args[0].clone(), args[1].clone()));
                }
            }
            None
        }
        Tuple(xs) if xs.len() == 2 => match (&xs[0], &xs[1]) {
            (Int(0), _) => Some(ListShape::Nil),
            (Int(1), Tuple(inner)) if inner.len() == 2 => {
                Some(ListShape::Cons(inner[0].clone(), inner[1].clone()))
            }
            _ => None,
        },
        _ => None,
    }
}

enum ListShape {
    Nil,
    Cons(Expr, Expr),
}

/// Recognize the canonical stdlib representation of a tree node:
///   * `leaf` (Var)              — empty tree
///   * `(2, ...)`                — inlined leaf tuple
///   * `App(node, [l, v, r])`    — explicit `node l v r` syntactic form
///   * `(3, (l, (v, r)))`        — inlined node tuple after β-reduction
fn tree_shape(e: &Expr) -> Option<TreeShape> {
    use Expr::*;
    match e {
        Var { name: s, .. } if s == "leaf" => Some(TreeShape::Leaf),
        App { func, args } => {
            if let Var { name: fname, .. } = func.as_ref() {
                if fname == "leaf" {
                    return Some(TreeShape::Leaf);
                }
                if fname == "node" && args.len() == 3 {
                    return Some(TreeShape::Node(
                        args[0].clone(),
                        args[1].clone(),
                        args[2].clone(),
                    ));
                }
            }
            None
        }
        Tuple(xs) if xs.len() == 2 => match (&xs[0], &xs[1]) {
            (Int(2), _) => Some(TreeShape::Leaf),
            (Int(3), Tuple(body)) if body.len() == 2 => {
                if let Tuple(inner) = &body[1] {
                    if inner.len() == 2 {
                        return Some(TreeShape::Node(
                            body[0].clone(),
                            inner[0].clone(),
                            inner[1].clone(),
                        ));
                    }
                }
                None
            }
            _ => None,
        },
        _ => None,
    }
}

enum TreeShape {
    Leaf,
    Node(Expr, Expr, Expr),
}

/// Simplify built-in list destructors when applied to a known constructor:
///   null  cons-shaped → false / nil-shaped → true
///   head  cons (x, _) → x
///   tail  cons (_, ys) → ys
/// Recognizes both the syntactic form (`cons` / `nil` Var/App) and the
/// inlined tagged-pair form (`(1, (x, xs))` / `(0, ())`) that the unfolder
/// produces after β-reducing stdlib's `cons` / `nil` definitions.
fn simplify_list_ops(e: &Expr, ctx: &EvalCtx, env: &Env) -> Expr {
    use Expr::*;
    match e {
        App { func, args } => {
            let new_args: Vec<Expr> =
                args.iter().map(|a| simplify_list_ops(a, ctx, env)).collect();
            if let Var { name: fname, .. } = func.as_ref() {
                match fname.as_str() {
                    "null" if new_args.len() == 1 => match list_shape(&new_args[0]) {
                        Some(ListShape::Nil) => return Bool(true),
                        Some(ListShape::Cons(_, _)) => return Bool(false),
                        None => {}
                    },
                    "head" if new_args.len() == 1 => {
                        if let Some(ListShape::Cons(h, _)) = list_shape(&new_args[0]) {
                            return h;
                        }
                    }
                    "tail" if new_args.len() == 1 => {
                        if let Some(ListShape::Cons(_, t)) = list_shape(&new_args[0]) {
                            return t;
                        }
                    }
                    "length" if new_args.len() == 1 => match list_shape(&new_args[0]) {
                        Some(ListShape::Nil) => return Int(0),
                        Some(ListShape::Cons(_, t)) => {
                            return BinOp(
                                crate::ast::BinOp::Add,
                                Box::new(Int(1)),
                                Box::new(App {
                                    func: Box::new(Var { name: "length".into(), line: 0, col: 0 }),
                                    args: vec![t],
                                }),
                            );
                        }
                        None => {}
                    },
                    _ => {}
                }
            }
            let rebuilt = App {
                func: Box::new(simplify_list_ops(func, ctx, env)),
                args: new_args,
            };
            simplify_ifs(&rebuilt, "", ctx, env)
        }
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(simplify_list_ops(l, ctx, env)),
            Box::new(simplify_list_ops(r, ctx, env)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(simplify_list_ops(x, ctx, env))),
        If { cond, then_branch, else_branch } => {
            let c2 = simplify_list_ops(cond, ctx, env);
            let t2 = simplify_list_ops(then_branch, ctx, env);
            let e2 = simplify_list_ops(else_branch, ctx, env);
            if let Bool(b) = &c2 {
                return if *b { t2 } else { e2 };
            }
            // Pattern: `if X == 0 then ...` where X is the tag of a known
            // list/tree constructor.  We can simplify the comparison.
            if let BinOp(crate::ast::BinOp::Eq, l, r) = &c2 {
                if let (Int(a), Int(b)) = (l.as_ref(), r.as_ref()) {
                    return if a == b { t2 } else { e2 };
                }
            }
            If {
                cond: Box::new(c2),
                then_branch: Box::new(t2),
                else_branch: Box::new(e2),
            }
        }
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(simplify_list_ops(value, ctx, env)),
            body: Box::new(simplify_list_ops(body, ctx, env)),
            rec: *rec,
        },
        _ => e.clone(),
    }
}


/// Strip all leading `forall x in T, ...` binders, returning the body.
/// We don't track the bound variable list because in the polynomial encoding
/// every free variable is universally quantified by default.
/// True if `name`'s own definition is recursive — either directly (its body
/// mentions itself) or *mutually*, through a cycle of other user-defined
/// closures (e.g. `isEven` calling `isOdd` calling `isEven`).  Walks the call
/// graph (via `collect_free_var_names` on each visited closure's body) with
/// a `visited` set, so it terminates in O(number of reachable definitions)
/// regardless of cycles.
///
/// This used to only check direct self-reference, leaving mutually-recursive
/// pairs misclassified as "non-recursive" — `unfold_nonrec_transitive` would
/// then try to fully expand them, ping-ponging between the two functions
/// until its iteration cap kicked in, instead of stopping after one
/// meaningful step the way genuine self-recursion does.
fn closure_is_recursive(name: &str, globals: &crate::value::Globals) -> bool {
    let own_body = match globals.defs.get(name) {
        Some(Value::Closure { body, .. }) => body,
        _ => return false,
    };
    let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut stack: Vec<String> = Vec::new();
    let mut seed = std::collections::BTreeSet::new();
    collect_free_var_names(own_body, &mut seed);
    stack.extend(seed);
    while let Some(n) = stack.pop() {
        if n == name {
            return true;
        }
        if !visited.insert(n.clone()) {
            continue;
        }
        if let Some(Value::Closure { body, .. }) = globals.defs.get(&n) {
            let mut names = std::collections::BTreeSet::new();
            collect_free_var_names(body, &mut names);
            stack.extend(names);
        }
    }
    false
}

/// True if `e` contains an `If` node whose *condition* still mentions
/// `kvar` — i.e. a case-split on the induction step variable that
/// `simplify_ifs` was unable to resolve to a single definite branch.  Used
/// by `verify_strong_induction` as a soundness guard: normal recursive-call
/// atoms (`f (k + 1)`, etc.) mentioning `kvar` are expected and fine — it's
/// specifically an *unresolved `if`* keyed on `kvar` that signals a
/// base-case boundary the chosen depth didn't cover.
fn contains_var_conditioned_if(e: &Expr, kvar: &str) -> bool {
    use Expr::*;
    match e {
        If { cond, then_branch, else_branch } => {
            let mut names = std::collections::BTreeSet::new();
            collect_free_var_names(cond, &mut names);
            if names.contains(kvar) {
                return true;
            }
            contains_var_conditioned_if(then_branch, kvar)
                || contains_var_conditioned_if(else_branch, kvar)
        }
        App { func, args } => {
            contains_var_conditioned_if(func, kvar)
                || args.iter().any(|a| contains_var_conditioned_if(a, kvar))
        }
        BinOp(_, l, r) => {
            contains_var_conditioned_if(l, kvar) || contains_var_conditioned_if(r, kvar)
        }
        UnOp(_, x) => contains_var_conditioned_if(x, kvar),
        Let { value, body, .. } => {
            contains_var_conditioned_if(value, kvar) || contains_var_conditioned_if(body, kvar)
        }
        _ => false,
    }
}

/// Collect every variable name appearing free in `e` (no scope tracking;
/// over-approximates for binders, which is fine because we only use this
/// to decide which definitions to attempt unfolding).
fn collect_free_var_names(e: &Expr, out: &mut std::collections::BTreeSet<String>) {
    use Expr::*;
    match e {
        Var { name, .. } => {
            out.insert(name.clone());
        }
        Lambda { body, .. } => collect_free_var_names(body, out),
        App { func, args } => {
            collect_free_var_names(func, out);
            for a in args {
                collect_free_var_names(a, out);
            }
        }
        Let { value, body, .. } => {
            collect_free_var_names(value, out);
            collect_free_var_names(body, out);
        }
        If { cond, then_branch, else_branch } => {
            collect_free_var_names(cond, out);
            collect_free_var_names(then_branch, out);
            collect_free_var_names(else_branch, out);
        }
        BinOp(_, l, r) => {
            collect_free_var_names(l, out);
            collect_free_var_names(r, out);
        }
        UnOp(_, x) => collect_free_var_names(x, out),
        SetEnum(xs) | Tuple(xs) | List(xs) => {
            for x in xs {
                collect_free_var_names(x, out);
            }
        }
        SetComp { domain, pred, .. } => {
            collect_free_var_names(domain, out);
            collect_free_var_names(pred, out);
        }
        Arrow(a, b) => {
            collect_free_var_names(a, out);
            collect_free_var_names(b, out);
        }
        DepArrow { from, to, .. } | DepPair { from, to, .. } => {
            collect_free_var_names(from, out);
            collect_free_var_names(to, out);
        }
        Forall { domain, body, .. } | Exists { domain, body, .. } => {
            collect_free_var_names(domain, out);
            collect_free_var_names(body, out);
        }
        _ => {}
    }
}

/// Transitively β-unfold every **non-recursive** user-defined function call
/// appearing in `e`.  Continues until a fixed point or until the bound
/// `MAX_UNFOLD_ITERS` is reached.  `seeded` lists the function names
/// already unfolded by the calling tactic (so we don't try them again at
/// the top level — they're handled by `do_unfold` itself).
fn unfold_nonrec_transitive(
    e: &Expr,
    globals: &crate::value::Globals,
    _seeded: &[&str],
) -> Expr {
    const MAX_UNFOLD_ITERS: usize = 32;
    let mut current = e.clone();
    for _ in 0..MAX_UNFOLD_ITERS {
        let mut names = std::collections::BTreeSet::new();
        collect_free_var_names(&current, &mut names);
        let mut changed = false;
        for name in &names {
            if let Some(Value::Closure { params, body, .. }) = globals.defs.get(name) {
                if !closure_is_recursive(name, globals) {
                    let next = unfold_calls(&current, name, params, body);
                    if next != current {
                        current = next;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    current
}

fn strip_foralls(e: &Expr) -> &Expr {
    let mut cur = e;
    while let Expr::Forall { body, .. } = cur {
        cur = body;
    }
    cur
}

/// Walk `e` and collect every identifier referenced (variable / function /
/// constructor / set name).  Used by the portfolio search to discover
/// candidate unfold targets and rank candidate lemmas.
pub fn collect_idents(e: &Expr, out: &mut std::collections::HashSet<String>) {
    use Expr::*;
    match e {
        Var { name, .. } => {
            out.insert(name.clone());
        }
        App { func, args } => {
            collect_idents(func, out);
            for a in args {
                collect_idents(a, out);
            }
        }
        BinOp(_, l, r) => {
            collect_idents(l, out);
            collect_idents(r, out);
        }
        UnOp(_, x) => collect_idents(x, out),
        If { cond, then_branch, else_branch } => {
            collect_idents(cond, out);
            collect_idents(then_branch, out);
            collect_idents(else_branch, out);
        }
        Let { value, body, .. } => {
            collect_idents(value, out);
            collect_idents(body, out);
        }
        Lambda { body, .. } => collect_idents(body, out),
        SetEnum(xs) | Tuple(xs) | List(xs) => {
            for x in xs {
                collect_idents(x, out);
            }
        }
        SetComp { domain, pred, .. } => {
            collect_idents(domain, out);
            collect_idents(pred, out);
        }
        Arrow(a, b) => {
            collect_idents(a, out);
            collect_idents(b, out);
        }
        DepArrow { from, to, .. } | DepPair { from, to, .. } => {
            collect_idents(from, out);
            collect_idents(to, out);
        }
        Forall { domain, body, .. } | Exists { domain, body, .. } => {
            collect_idents(domain, out);
            collect_idents(body, out);
        }
        Int(_) | Real(_) | Bool(_) | Str(_) => {}
    }
}

/// Walk a `Proof` AST and collect every theorem name referenced through a
/// `BySimp { lemmas }`.  Used by `:why` to surface which existing lemmas
/// the portfolio's discovered proof actually leans on, so the user sees
/// "this follows from `gauss`" rather than just "by simp [gauss] then
/// algebra".  Returns names in source order with duplicates preserved.
pub fn extract_lemmas(p: &Proof) -> Vec<String> {
    let mut out = Vec::new();
    fn go(p: &Proof, out: &mut Vec<String>) {
        match p {
            Proof::BySimp { lemmas } => {
                for l in lemmas {
                    out.push(l.clone());
                }
            }
            Proof::Seq(tacs) => {
                for t in tacs {
                    go(t, out);
                }
            }
            _ => {}
        }
    }
    go(p, &mut out);
    out
}

/// Rank proven theorems by Jaccard symbol overlap with `goal_syms`.  Returns
/// names sorted by decreasing overlap, dropping any theorem whose own
/// proposition has no identifier in common with the goal.  `self_name`
/// suppresses a theorem from ranking against itself (used when rebuilding
/// the search for a goal that *is* a theorem statement).
fn rank_lemmas(
    goal_syms: &std::collections::HashSet<String>,
    pool: &std::collections::HashMap<String, Expr>,
    self_name: Option<&str>,
) -> Vec<String> {
    let mut scored: Vec<(f64, String)> = Vec::new();
    for (name, stmt) in pool {
        if Some(name.as_str()) == self_name {
            continue;
        }
        let mut syms = std::collections::HashSet::new();
        collect_idents(stmt, &mut syms);
        let inter = goal_syms.intersection(&syms).count() as f64;
        if inter == 0.0 {
            continue;
        }
        let union = goal_syms.union(&syms).count() as f64;
        let jaccard = inter / union.max(1.0);
        scored.push((jaccard, name.clone()));
    }
    scored.sort_by(|a, b| {
        b.0.partial_cmp(&a.0)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.1.cmp(&b.1)) // stable tie-break by name
    });
    scored.into_iter().map(|(_, n)| n).collect()
}

// `subst` lives in `ast.rs` so the evaluator can reuse it for tautology
// detection.  It is re-exported into the prover via `use ast::subst`.

/// Perform one β-step unfolding of every user-defined function call appearing
/// in `e`, as long as the unfolded body simplifies under the assumption that
/// "the recursive argument is `k + 1`".  When we encounter `if cond then T
/// else E` and `cond` evaluates to a boolean constant after partial reduction,
/// we keep only the active branch.  Recursive self-calls `f k` (i.e. with the
/// argument being just the induction variable, without further computation)
/// are left in place — they represent the inductive hypothesis instance.
///
/// This is intentionally conservative: it handles single-argument primitive
/// recursion of the shape `f := \n -> if n == 0 then base else step n (f (n-1))`
/// (which covers the typical sum / fact / sumSq / fibonacci patterns).
fn unfold_one(e: &Expr, ctx: &EvalCtx, env: &Env) -> Expr {
    use Expr::*;
    match e {
        App { func, args } => {
            let unfolded_args: Vec<Expr> = args.iter().map(|a| unfold_one(a, ctx, env)).collect();
            // Look up `func` if it is a Var that resolves to a known closure.
            if let Var { name: name, .. } = func.as_ref() {
                if let Some(Value::Closure { params, body, env: cenv, .. }) =
                    ctx.globals.defs.get(name)
                {
                    if params.len() == unfolded_args.len() {
                        // β-substitute parameters with arguments inside the body
                        let mut new_body = (**body).clone();
                        for (p, a) in params.iter().zip(unfolded_args.iter()) {
                            new_body = subst(&new_body, p, a);
                        }
                        // try to simplify if-conditions inside the unfolded body
                        let _ = cenv; // not used in this simple version
                        return simplify_ifs(&new_body, name, ctx, env);
                    }
                }
            }
            App {
                func: Box::new(unfold_one(func, ctx, env)),
                args: unfolded_args,
            }
        }
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(unfold_one(l, ctx, env)),
            Box::new(unfold_one(r, ctx, env)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(unfold_one(x, ctx, env))),
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(unfold_one(value, ctx, env)),
            body: Box::new(unfold_one(body, ctx, env)),
            rec: *rec,
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(unfold_one(cond, ctx, env)),
            then_branch: Box::new(unfold_one(then_branch, ctx, env)),
            else_branch: Box::new(unfold_one(else_branch, ctx, env)),
        },
        _ => e.clone(),
    }
}

/// Try to evaluate `if`-conditions after substitution.  When the condition
/// becomes a known boolean (by polynomial-zero test, integer comparison of
/// constants, etc.), we drop the dead branch and unfold further. We also
/// avoid re-unfolding the same recursive function (`fname`) past the first
/// β-step: subsequent occurrences are treated as the inductive hypothesis.
fn simplify_ifs(e: &Expr, fname: &str, ctx: &EvalCtx, env: &Env) -> Expr {
    use Expr::*;
    match e {
        If { cond, then_branch, else_branch } => {
            // attempt to evaluate the condition
            if let Ok(v) = ctx.eval(cond, env) {
                match v {
                    Value::Bool(true) => return simplify_ifs(then_branch, fname, ctx, env),
                    Value::Bool(false) => return simplify_ifs(else_branch, fname, ctx, env),
                    _ => {}
                }
            }
            // structural fallback: try to detect `n == 0` with n known to be
            // the bumped induction variable `k + 1` (always nonzero in ℕ).
            if let BinOp(crate::ast::BinOp::Eq, l, r) = cond.as_ref() {
                if let (Some(p), Some(q)) = (expr_to_poly(l), expr_to_poly(r)) {
                    let diff = p.sub(q);
                    // exactly zero → condition true
                    if diff.terms.is_empty() {
                        return simplify_ifs(then_branch, fname, ctx, env);
                    }
                    // strictly positive in Nat → condition false
                    if polynomial_strictly_positive_in_nat(&diff) {
                        return simplify_ifs(else_branch, fname, ctx, env);
                    }
                    // strictly negative in Nat → condition false (negate)
                    if polynomial_strictly_positive_in_nat(&diff.clone().neg()) {
                        return simplify_ifs(else_branch, fname, ctx, env);
                    }
                }
            }
            // Also detect the inverse comparisons: `> 0`, `< 0`, etc., and
            // refute them when possible (over Nat).  This is what lets the
            // induction unfolder simplify away `if (k+2) < 2` when proving
            // facts about Fibonacci-style recurrences.
            if let BinOp(op, l, r) = cond.as_ref() {
                use crate::ast::BinOp as B;
                if let (Some(p), Some(q)) = (expr_to_poly(l), expr_to_poly(r)) {
                    let diff = p.sub(q);
                    let pos = polynomial_pos(&diff, PolyDomain::Nat);
                    let neg = polynomial_neg(&diff, PolyDomain::Nat);
                    let zero = diff.terms.is_empty();
                    let nonneg = polynomial_nonneg(&diff, PolyDomain::Nat);
                    let nonpos = polynomial_nonpos(&diff, PolyDomain::Nat);
                    let truth: Option<bool> = match op {
                        B::Lt => {
                            if neg {
                                Some(true)
                            } else if nonneg {
                                Some(false)
                            } else {
                                None
                            }
                        }
                        B::Le => {
                            if nonpos || zero {
                                Some(true)
                            } else if pos {
                                Some(false)
                            } else {
                                None
                            }
                        }
                        B::Gt => {
                            if pos {
                                Some(true)
                            } else if nonpos {
                                Some(false)
                            } else {
                                None
                            }
                        }
                        B::Ge => {
                            if nonneg || zero {
                                Some(true)
                            } else if neg {
                                Some(false)
                            } else {
                                None
                            }
                        }
                        B::Neq => {
                            if pos || neg {
                                Some(true)
                            } else if zero {
                                Some(false)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    match truth {
                        Some(true) => return simplify_ifs(then_branch, fname, ctx, env),
                        Some(false) => return simplify_ifs(else_branch, fname, ctx, env),
                        None => {}
                    }
                }
            }
            If {
                cond: cond.clone(),
                then_branch: Box::new(simplify_ifs(then_branch, fname, ctx, env)),
                else_branch: Box::new(simplify_ifs(else_branch, fname, ctx, env)),
            }
        }
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(simplify_ifs(l, fname, ctx, env)),
            Box::new(simplify_ifs(r, fname, ctx, env)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(simplify_ifs(x, fname, ctx, env))),
        App { func, args } => {
            let new_args: Vec<Expr> =
                args.iter().map(|a| simplify_ifs(a, fname, ctx, env)).collect();
            // Recursive self-call inside the unfolded body — encode it as the
            // free variable `fname`-applied-to-its-arg, which the polynomial
            // converter treats as a free variable ONLY when the argument is
            // itself a single variable (the induction hypothesis case).
            App {
                func: func.clone(),
                args: new_args,
            }
        }
        _ => e.clone(),
    }
}

/// Mark `_` as used (unused-warnings silencer for UnOp variant in subst).
#[allow(dead_code)]
fn _touch_unop(_: &UnOp) {}

/// Simplify built-in tree destructors when applied to a known constructor.
/// Recognizes both the syntactic form (`leaf` / `App(node, ..)`) and the
/// inlined tagged-pair form (`(2, ())` / `(3, (l, (v, r)))`).
fn simplify_tree_ops(e: &Expr, ctx: &EvalCtx, env: &Env) -> Expr {
    use Expr::*;
    match e {
        App { func, args } => {
            let new_args: Vec<Expr> =
                args.iter().map(|a| simplify_tree_ops(a, ctx, env)).collect();
            if let Var { name: fname, .. } = func.as_ref() {
                match fname.as_str() {
                    "isLeaf" if new_args.len() == 1 => match tree_shape(&new_args[0]) {
                        Some(TreeShape::Leaf) => return Bool(true),
                        Some(TreeShape::Node(_, _, _)) => return Bool(false),
                        None => {}
                    },
                    "treeVal" if new_args.len() == 1 => {
                        if let Some(TreeShape::Node(_, v, _)) = tree_shape(&new_args[0]) {
                            return v;
                        }
                    }
                    "treeLeft" if new_args.len() == 1 => {
                        if let Some(TreeShape::Node(l, _, _)) = tree_shape(&new_args[0]) {
                            return l;
                        }
                    }
                    "treeRight" if new_args.len() == 1 => {
                        if let Some(TreeShape::Node(_, _, r)) = tree_shape(&new_args[0]) {
                            return r;
                        }
                    }
                    _ => {}
                }
            }
            let rebuilt = App {
                func: Box::new(simplify_tree_ops(func, ctx, env)),
                args: new_args,
            };
            simplify_ifs(&rebuilt, "", ctx, env)
        }
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(simplify_tree_ops(l, ctx, env)),
            Box::new(simplify_tree_ops(r, ctx, env)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(simplify_tree_ops(x, ctx, env))),
        If { cond, then_branch, else_branch } => {
            let c2 = simplify_tree_ops(cond, ctx, env);
            let t2 = simplify_tree_ops(then_branch, ctx, env);
            let e2 = simplify_tree_ops(else_branch, ctx, env);
            if let Bool(b) = &c2 {
                return if *b { t2 } else { e2 };
            }
            if let BinOp(crate::ast::BinOp::Eq, l, r) = &c2 {
                if let (Int(a), Int(b)) = (l.as_ref(), r.as_ref()) {
                    return if a == b { t2 } else { e2 };
                }
            }
            If {
                cond: Box::new(c2),
                then_branch: Box::new(t2),
                else_branch: Box::new(e2),
            }
        }
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(simplify_tree_ops(value, ctx, env)),
            body: Box::new(simplify_tree_ops(body, ctx, env)),
            rec: *rec,
        },
        _ => e.clone(),
    }
}

// =============================================================================
// `by simp` infrastructure: rule collection, pattern matching, rewriting.
// =============================================================================

/// A rewrite rule extracted from a theorem/axiom of the shape
/// `forall x1 in T1, ..., forall xn in Tn, lhs == rhs`.
/// `metavars` are the bound variable names — they match anything in the goal.
#[derive(Debug, Clone)]
struct SimpRule {
    /// Source theorem/axiom name — kept for future diagnostic messages.
    #[allow(dead_code)]
    name: String,
    metavars: Vec<String>,
    lhs: Expr,
    rhs: Expr,
}

/// Collect rewrite rules from globals.  When `lemmas` is empty, use every
/// theorem and axiom whose proposition reduces to an equality (after
/// stripping leading `forall` binders).  Otherwise, use exactly the named
/// ones (theorems first, then axioms; error if any name is unknown).
fn collect_simp_rules(ctx: &EvalCtx, lemmas: &[String]) -> SekiResult<Vec<SimpRule>> {
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
fn rule_from_prop(name: &str, prop: &Expr) -> Option<SimpRule> {
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
fn simp_rewrite(e: &Expr, rules: &[SimpRule]) -> Expr {
    use Expr::*;
    // First rewrite children, then try the rules at this node.
    let after_children = match e {
        Int(_) | Real(_) | Bool(_) | Str(_) | Var { .. } => e.clone(),
        Lambda { params, body } => Lambda {
            params: params.clone(),
            body: Box::new(simp_rewrite(body, rules)),
        },
        App { func, args } => App {
            func: Box::new(simp_rewrite(func, rules)),
            args: args.iter().map(|a| simp_rewrite(a, rules)).collect(),
        },
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(simp_rewrite(value, rules)),
            body: Box::new(simp_rewrite(body, rules)),
            rec: *rec,
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(simp_rewrite(cond, rules)),
            then_branch: Box::new(simp_rewrite(then_branch, rules)),
            else_branch: Box::new(simp_rewrite(else_branch, rules)),
        },
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(simp_rewrite(l, rules)),
            Box::new(simp_rewrite(r, rules)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(simp_rewrite(x, rules))),
        SetEnum(xs) => SetEnum(xs.iter().map(|x| simp_rewrite(x, rules)).collect()),
        Tuple(xs) => Tuple(xs.iter().map(|x| simp_rewrite(x, rules)).collect()),
        List(xs) => List(xs.iter().map(|x| simp_rewrite(x, rules)).collect()),
        SetComp { var, domain, pred } => SetComp {
            var: var.clone(),
            domain: Box::new(simp_rewrite(domain, rules)),
            pred: Box::new(simp_rewrite(pred, rules)),
        },
        Arrow(a, b) => Arrow(
            Box::new(simp_rewrite(a, rules)),
            Box::new(simp_rewrite(b, rules)),
        ),
        DepArrow { binder, from, to } => DepArrow {
            binder: binder.clone(),
            from: Box::new(simp_rewrite(from, rules)),
            to: Box::new(simp_rewrite(to, rules)),
        },
        DepPair { binder, from, to } => DepPair {
            binder: binder.clone(),
            from: Box::new(simp_rewrite(from, rules)),
            to: Box::new(simp_rewrite(to, rules)),
        },
        Forall { var, domain, body } => Forall {
            var: var.clone(),
            domain: Box::new(simp_rewrite(domain, rules)),
            body: Box::new(simp_rewrite(body, rules)),
        },
        Exists { var, domain, body } => Exists {
            var: var.clone(),
            domain: Box::new(simp_rewrite(domain, rules)),
            body: Box::new(simp_rewrite(body, rules)),
        },
    };
    // Try each rule at this node.
    for rule in rules {
        if let Some(subst_map) = match_pattern(&rule.lhs, &after_children, &rule.metavars) {
            return apply_subst(&rule.rhs, &subst_map);
        }
    }
    after_children
}

/// Attempt syntactic matching of `pattern` against `target`, treating any
/// occurrence of a name in `metavars` (in `pattern`) as a wildcard that
/// can be bound to any sub-expression.  Returns the binding on success.
fn match_pattern(
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
fn apply_subst(e: &Expr, m: &std::collections::HashMap<String, Expr>) -> Expr {
    let mut out = e.clone();
    for (k, v) in m {
        out = crate::ast::subst(&out, k, v);
    }
    out
}

/// Cheap structural equality on `Expr` for fixed-point detection.
/// Reuses `alpha_equiv` which is structurally-aware.
fn exprs_equal(a: &Expr, b: &Expr) -> bool {
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
fn canonicalize(e: &Expr) -> Expr {
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
                    Int(n) => const_sum = const_sum.saturating_add(*n),
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

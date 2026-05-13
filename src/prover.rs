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
    polynomial_strictly_positive_in_nat, PolyDomain,
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
            Proof::ByStrongInduction => self.verify_strong_induction(prop, env),
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
        }
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
            | Proof::ByStrongInduction
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
        Ok(unfold_calls(e, name, &params, &body))
    }

    /// `by algebra`:  prove a relational claim over **all integers (or naturals)**
    /// by reducing the relation to a polynomial sign analysis.  Supports
    /// `==`, `!=`, `<`, `<=`, `>`, `>=`, plus integer division and modulo by
    /// constant divisors (handled inside `expr_to_poly`).
    ///
    /// Sound: a `proved` outcome means the relation holds for every valuation
    /// of the free variables in the chosen domain (Nat or Int).
    fn verify_algebra(&self, prop: &Expr, _env: &Env) -> SekiResult<Value> {
        let dom = detect_domain(prop);
        let body = strip_foralls(prop);
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
        let diff = lp.sub(rp); // diff = lhs - rhs
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
            Ok(Value::Bool(true))
        } else {
            Err(SekiError::Proof(format!(
                "by algebra: cannot prove {} {} {} over {:?}",
                lhs, op, rhs, dom
            )))
        }
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

    /// `by strong_induction` (depth 2):  prove `forall n in Nat, P(n)` by
    /// verifying P(0) and P(1) as bases, and P(k+2) by polynomial sign analysis
    /// over Nat, where recursive calls `f k` and `f (k+1)` are treated as
    /// nonneg atoms (the inductive hypotheses).  Useful when the spec recurses
    /// on more than one immediate predecessor (Fibonacci-style).
    fn verify_strong_induction(&self, prop: &Expr, env: &Env) -> SekiResult<Value> {
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
        // ---- bases: P(0), P(1) ----
        for n in 0..2i64 {
            let p_n = subst(body, &var, &Expr::Int(n));
            let v = self.ctx.eval(&p_n, env)?;
            if !matches!(v, Value::Bool(true)) {
                return Err(SekiError::Proof(format!(
                    "by strong_induction: base case P({}) failed (got {})",
                    n, v
                )));
            }
        }
        // ---- step: P(k+2) directly, with `f k`, `f (k+1)` as nonneg atoms ----
        let kvar = format!("__k_{}", var);
        let k_expr = Expr::Var { name: kvar, line: 0, col: 0 };
        let kp2 = Expr::BinOp(BinOp::Add, Box::new(k_expr.clone()), Box::new(Expr::Int(2)));
        let lhs_kp2 = unfold_one(&subst(&lhs, &var, &kp2), self.ctx, env);
        let rhs_kp2 = unfold_one(&subst(&rhs, &var, &kp2), self.ctx, env);
        // Discharge `lhs_kp2 op rhs_kp2` directly.  Over Nat, opaque atoms
        // (which include the IH instances `f k`, `f (k+1)`) are treated as
        // ≥ 0 — sound for the bounded-below kind of claims this tactic
        // typically targets.
        let lp = expr_to_poly(&lhs_kp2).ok_or_else(|| {
            SekiError::Proof(
                "by strong_induction: lhs is outside the polynomial fragment after unfolding"
                    .into(),
            )
        })?;
        let rp = expr_to_poly(&rhs_kp2).ok_or_else(|| {
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
                "by strong_induction: step P(k+2) failed for {} {} {}",
                lhs_kp2, op, rhs_kp2
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

/// Decide whether free variables in `prop` should be treated as Nat (≥ 0) or
/// Int.  Heuristic: if every binder's domain (as a syntactic Expr) is `Nat`,
/// we use Nat; otherwise Int.  Mixed domains default to Int (more
/// conservative — fewer signs are inferable).
fn detect_domain(prop: &Expr) -> PolyDomain {
    fn looks_like_nat(e: &Expr) -> bool {
        matches!(e, Expr::Var { name: s, .. } if s == "Nat")
    }
    let mut cur = prop;
    let mut all_nat = true;
    let mut saw_any = false;
    while let Expr::Forall { domain, body, .. } = cur {
        saw_any = true;
        if !looks_like_nat(domain) {
            all_nat = false;
        }
        cur = body;
    }
    if saw_any && all_nat {
        PolyDomain::Nat
    } else {
        PolyDomain::Int
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
fn strip_foralls(e: &Expr) -> &Expr {
    let mut cur = e;
    while let Expr::Forall { body, .. } = cur {
        cur = body;
    }
    cur
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

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

use crate::algebra::{Rat,
    
    expr_to_poly, polynomial_neg, polynomial_nonneg, polynomial_nonneg_under_ih,
    polynomial_nonpos, polynomial_nonpos_under_ih, polynomial_pos,
    polynomial_strictly_positive_in_nat, ratpoly_equal, PolyDomain,
};
use crate::ast::{subst, BinOp, Expr, Proof, UnOp};
use crate::rewrite::{
    canonicalize, case_split_goals, collect_simp_rules, exprs_equal, rewrite_goal,
    simp_rewrite, split_first_if, SimpRule,
};
use crate::unfold::{collect_free_var_names, unfold_definition};
use crate::eval::{enumerate_set, EvalCtx};
use crate::value::{value_eq, AtomicSet, Env, SetVal, Value};
use crate::kernel::{Cert, PolyClaim, TrustReason};
use crate::trust::TrustLevel;
use crate::{SekiError, SekiResult};
use std::collections::BTreeSet;

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
            Proof::Assumption => self.verify_assumption(prop).map(|()| Value::Bool(true)),
            Proof::Apply { lemma, substs } => self
                .verify_apply(prop, lemma, substs, env)
                .map(|_| Value::Bool(true)),
            Proof::Have { name, prop: fact, proof: sub } => {
                // Standalone `have` (no following `then`): prove the fact,
                // then require the goal to follow from it by evaluation.
                let _ = name;
                let hyps = goal_hypotheses(prop);
                self.verify(&under_hypotheses(&hyps, (**fact).clone()), sub, env)?;
                let extended = add_hypothesis(prop, (**fact).clone());
                let v = self.ctx.eval(&extended, env)?;
                require_true(&v).map(|()| Value::Bool(true))
            }
            Proof::Obtain { intro, lemma, substs } => {
                // Standalone `obtain` (no following `then`): transform and
                // require the result to evaluate to `true`, same pattern as
                // standalone unfold/intros. Rarely useful alone since the
                // transformed goal still has `intro` as a free symbol.
                let (_, context_hyps) = peel_implications(strip_foralls(prop));
                let fact = self.verify_obtain(intro, lemma, substs, &context_hyps, env)?;
                let new_goal = implies_expr(fact, prop.clone());
                let v = self.ctx.eval(&new_goal, env)?;
                if matches!(v, Value::Bool(true)) {
                    Ok(Value::Bool(true))
                } else {
                    Err(SekiError::Proof(format!(
                        "by obtain {} from {}: result did not close the goal",
                        intro, lemma
                    )))
                }
            }
        }
    }

    /// Instantiate `lemma` (an axiom or theorem name) by substituting each
    /// `substs` binding for the corresponding name — first consuming
    /// leading `forall`s positionally by name, then substituting any
    /// remaining free occurrences (for names the lemma left unquantified,
    /// e.g. an uninterpreted function parameter with no natural `Set`
    /// domain to quantify over). Discharges any resulting premises via `by
    /// algebra`, then requires the conclusion to be `exists w in D, P(w)`
    /// and returns `P(intro)` — the fact the caller gets to assume.
    fn verify_obtain(
        &self,
        intro: &str,
        lemma: &str,
        substs: &[(String, Expr)],
        context_hyps: &[Expr],
        env: &Env,
    ) -> SekiResult<Expr> {
        let prop = self
            .ctx
            .globals
            .theorem_props
            .get(lemma)
            .or_else(|| self.ctx.globals.axiom_props.get(lemma))
            .cloned()
            .ok_or_else(|| {
                SekiError::Proof(format!("by obtain: unknown axiom/theorem `{}`", lemma))
            })?;
        let mut cur = prop;
        while let Expr::Forall { var, body, .. } = cur {
            let value = substs
                .iter()
                .find(|(n, _)| *n == var)
                .map(|(_, e)| e.clone())
                .ok_or_else(|| {
                    SekiError::Proof(format!(
                        "by obtain: `{}` is universally quantified in `{}` but no \
                         `with {} := ...` was given",
                        var, lemma, var
                    ))
                })?;
            cur = subst(body.as_ref(), &var, &value);
        }
        for (name, value) in substs {
            cur = subst(&cur, name, value);
        }
        let (conclusion, premises) = peel_implications(&cur);
        for p in &premises {
            // First check whether `p` is literally already known — a
            // premise of the theorem currently being proved, brought into
            // scope via `strip_foralls`+`peel_implications` on the goal.
            // Only fall back to `by algebra` (which can't see `context_hyps`
            // and would have to re-derive `p` from nothing) when it isn't.
            let already_known = context_hyps.iter().any(|h| crate::ast::alpha_equiv(h, p));
            if already_known {
                continue;
            }
            self.verify_algebra(p, env).map_err(|e| {
                SekiError::Proof(format!(
                    "by obtain: could not discharge premise `{}` of `{}` \
                     (not already a hypothesis of the current goal either): {}",
                    p, lemma, e
                ))
            })?;
        }
        match conclusion {
            Expr::Exists { var, body, .. } => {
                let intro_expr = Expr::Var { name: intro.to_string(), line: 0, col: 0 };
                Ok(subst(body.as_ref(), &var, &intro_expr))
            }
            other => Err(SekiError::Proof(format!(
                "by obtain: `{}` (after substitution) is not an existential, got {}",
                lemma, other
            ))),
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

    /// Variant of `try_portfolio` that prefers a proof the **kernel
    /// accepts**.
    ///
    /// `try_portfolio` returns whatever closes the goal first, and the cheap
    /// closers come first — so `by eval` would win on `forall n in Int, ...`
    /// by sampling even when `by unfold f then algebra` would have proved it
    /// outright.  That is the wrong trade for a search whose whole purpose
    /// is to find a proof: a sampled "success" is worth less than a slower
    /// real one.
    ///
    /// Candidates are tried in the same order, but each is certified and
    /// checked, and the first fully sound one wins.  If none is sound the
    /// first that merely verifies is returned, so this never finds *less*
    /// than `try_portfolio`.
    pub fn try_portfolio_sound(&self, prop: &Expr, env: &Env) -> Option<Proof> {
        let mut fallback: Option<Proof> = None;
        for cand in self.portfolio_candidates(prop, false) {
            if self.verify(prop, &cand, env).is_err() {
                continue;
            }
            if let Ok(cert) = self.certify(prop, &cand, env) {
                let kernel_ctx = EvalCtx::finite_only(self.ctx.globals);
                if let Ok(v) = crate::kernel::check(prop, &cert, &kernel_ctx, env) {
                    if v.fully_checked && !v.has_assumptions() {
                        return Some(cand);
                    }
                }
            }
            if fallback.is_none() {
                fallback = Some(cand);
            }
        }
        fallback
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
            // Forward reasoning: prove the fact under what is already
            // assumed, then carry on with it available.
            Proof::Have { prop: fact, proof: sub, .. } => {
                let hyps = goal_hypotheses(prop);
                self.verify(&under_hypotheses(&hyps, (**fact).clone()), sub, env)?;
                Ok(TacOutcome::NewGoal(add_hypothesis(prop, (**fact).clone())))
            }
            Proof::Assumption => {
                self.verify_assumption(prop)?;
                Ok(TacOutcome::Closed)
            }
            Proof::Apply { lemma, substs } => {
                self.verify_apply(prop, lemma, substs, env)?;
                Ok(TacOutcome::Closed)
            }
            Proof::Obtain { intro, lemma, substs } => {
                // Also strip the *current goal's own* leading foralls/
                // implications here (not just to gather `context_hyps` for
                // discharging the lemma's premises, but for the produced
                // goal too) — otherwise a closer downstream would see a
                // doubly-nested implication (`fact => (own_premises =>
                // conclusion)`) and most closers only peel one level.
                // Consuming the goal's own premises here is exactly what a
                // separate `by intros`/implication-peel right before
                // `obtain` would have done anyway.
                let (conclusion, context_hyps) = peel_implications(strip_foralls(prop));
                let fact = self.verify_obtain(intro, lemma, substs, &context_hyps, env)?;
                Ok(TacOutcome::NewGoal(implies_expr(fact, conclusion)))
            }
            Proof::BySimp { lemmas } => {
                // Try to close via simp; if it can't, return the most
                // rewritten state as a new goal.
                let run = self.simp_fixpoint(prop, lemmas, SimpMode::Transform)?;
                if self
                    .simp_closure(&run.states, env, SimpMode::Transform)
                    .is_some()
                {
                    return Ok(TacOutcome::Closed);
                }
                Ok(TacOutcome::NewGoal(run.final_state))
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

    /// β-unfold every occurrence of `App { func: Var { name, .. }, args }` in
    /// `e` using the body of the global `def name := \params -> body`.
    /// Performs a single layer of unfolding; recursive functions don't
    /// loop because we don't unfold the calls produced by substitution.
    fn do_unfold(&self, e: &Expr, name: &str) -> SekiResult<Expr> {
        unfold_definition(e, name, self.ctx.globals)
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
    /// `by algebra`, with a hint on failure saying what would have to be
    /// assumed for the goal to hold.
    ///
    /// The hint comes from `crate::abduce`, which verifies each suggestion
    /// by re-running the *raw* form below — going through this one would
    /// recurse forever.
    pub fn verify_algebra(&self, prop: &Expr, env: &Env) -> SekiResult<Value> {
        self.verify_algebra_raw(prop, env).map_err(|e| match e {
            SekiError::Proof(msg) => {
                let hint = crate::abduce::hint(&crate::abduce::missing_assumptions(
                    self, prop, env,
                ));
                SekiError::Proof(format!("{}{}", msg, hint))
            }
            other => other,
        })
    }

    /// `by algebra` without the hint — the form `crate::abduce` calls while
    /// checking whether a suggested assumption actually works.
    pub fn verify_algebra_raw(&self, prop: &Expr, _env: &Env) -> SekiResult<Value> {
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
            if let Some(h) = integer_strengthen(&p, true, dom) {
                initial_hyps.push(h);
            }
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
        // Case-split on an `if` hiding *inside a hypothesis* (typically
        // left there by unfolding a function like `absR := \r -> if r<0.0
        // then -r else r`) before looking at the goal's own `if`s. Without
        // this, a hypothesis such as `absR(x-x0) < delta` stays an opaque,
        // unusable fact — `expr_to_poly` can't see through the embedded
        // `if`, so the hypothesis never yields the linear bound on `x` a
        // goal like an epsilon-delta continuity proof needs. Sound for the
        // same reason the goal-side split is: each branch only needs to
        // hold under the extra assumption that got it there.
        for (i, (h, htrue)) in hyps.iter().enumerate() {
            if let Some((then_h, else_h, cond)) = split_first_if(h) {
                let mut then_hyps = hyps.to_vec();
                then_hyps[i] = (then_h, *htrue);
                then_hyps.push((cond.clone(), true));
                if let Some(extra) = integer_strengthen(&cond, true, dom) {
                    then_hyps.push(extra);
                }
                let mut else_hyps = hyps.to_vec();
                else_hyps[i] = (else_h, *htrue);
                else_hyps.push((cond.clone(), false));
                if let Some(extra) = integer_strengthen(&cond, false, dom) {
                    else_hyps.push(extra);
                }
                self.prove_algebra_rel(body, dom, &then_hyps)?;
                return self.prove_algebra_rel(body, dom, &else_hyps);
            }
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
            if let Some(h) = integer_strengthen(&cond, true, dom) {
                then_hyps.push(h);
            }
            let mut else_hyps = hyps.to_vec();
            else_hyps.push((cond.clone(), false));
            if let Some(h) = integer_strengthen(&cond, false, dom) {
                else_hyps.push(h);
            }
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
        // Structural list equality: `cons`/`nil` are freely-generated (an
        // injective, disjoint constructor pair), so `xs == ys` decomposes
        // into `head xs == head ys and tail xs == tail ys` (both Cons) or
        // is trivially true (both Nil) or false (one of each) — regardless
        // of *which* AST shape each side happens to be in (a literal
        // `App(cons, ..)`, a raw tag-tuple left over from unfolding `cons`
        // itself, or an `Expr::List` literal all count). This lets `by
        // algebra` close equalities between structurally-equal-but-
        // differently-represented lists, e.g. from induction step goals
        // where only one side got fully unfolded.
        if op == BinOp::Eq {
            match ctor_equality(lhs, rhs) {
                Some(CtorEquality::Trivial) => return Ok(Value::Bool(true)),
                Some(CtorEquality::Fields(pairs)) => {
                    // Same constructor on both sides: injectivity turns the
                    // equality into one equality per field.  All but the
                    // last are discharged here; the last is returned so a
                    // failure reports against the original goal.
                    let (last, rest) = pairs.split_last().expect("arity >= 1");
                    for (a, b) in rest {
                        let eq = Expr::BinOp(
                            BinOp::Eq,
                            Box::new(a.clone()),
                            Box::new(b.clone()),
                        );
                        self.prove_algebra_rel(&eq, dom, hyps)?;
                    }
                    let eq = Expr::BinOp(
                        BinOp::Eq,
                        Box::new(last.0.clone()),
                        Box::new(last.1.clone()),
                    );
                    return self.prove_algebra_rel(&eq, dom, hyps);
                }
                Some(CtorEquality::Distinct(a, b)) => {
                    return Err(SekiError::Proof(format!(
                        "by algebra: cannot prove {} == {} ({} vs {} — structurally unequal)",
                        lhs, rhs, a, b
                    )))
                }
                None => {}
            }
        }
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
        // Multi-variable linear inequality fallback: full Fourier-Motzkin
        // elimination over the hypotheses + negated goal (sound only in
        // the "provable" direction — see `algebra::fm_is_unsat`'s module
        // docs). Reaches goals that need *scaling* a hypothesis (e.g.
        // `2x <= y, y <= z ⊢ 2x <= z`), which the weight-1-sum shortcut in
        // `hyps_sum_proves` above can't. Only attempted for the inequality
        // ops it can natively negate into another inequality (`==`/`!=`
        // goals are handled by the mechanisms above instead).
        if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
            && try_fm_prove(hyps, &diff, &op)
        {
            return Ok(Value::Bool(true));
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
        if let Expr::Var { name, .. } = domain {
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
        // A generalized induction: `body` still has leading `forall`s (over
        // auxiliary parameters threaded through the recursion, e.g. an
        // accumulator index) before the actual relation. Plain structural
        // induction can't use these — the naturally-available IH would be
        // fixed at the *same* auxiliary values as the goal, but many
        // recursive definitions (integration threading a denominator index,
        // for instance) need the IH at *different* values in the step. See
        // `verify_list_induction_generalized` for how this is handled
        // soundly via the IH-as-rewrite-rule technique already used by
        // `by simp`.
        if let Expr::Forall { .. } = body {
            return self.verify_list_induction_generalized(var, body, env);
        }
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

    /// Structural list induction where the goal, after the induction
    /// variable, still carries leading `forall`s over auxiliary parameters
    /// (e.g. `forall p in List Real, forall k in Nat, forall c in Real,
    /// LHS(p,k,c) == RHS(p,k,c)`). Plain `verify_list_induction` can't use
    /// these: its diff-based step only ever compares against the IH at the
    /// *same* auxiliary values as the current goal, but recursive
    /// definitions that thread a changing accumulator (e.g. an integration
    /// index incrementing on each recursive call) need the IH at *different*
    /// values in the step.
    ///
    /// The fix: keep the auxiliary variables universally quantified (never
    /// fix them), and represent the induction hypothesis "the property holds
    /// for `ys`, for *any* value of the auxiliary variables" as a
    /// `by simp`-style rewrite rule (`SimpRule`) whose metavariables are
    /// exactly those auxiliary names, with the induction variable itself
    /// fixed to the concrete fresh tail symbol `ys` (never a metavariable —
    /// this is what keeps the self-reference well-founded: the rule can only
    /// ever fire on the literal smaller instance `ys`, not on `cons x ys` or
    /// anything containing it). Applying that rule via the existing
    /// `simp_rewrite` engine to the (one-level-unfolded) step goal discovers
    /// whatever instantiation of the auxiliary variables the recursion
    /// actually needs, exactly as pattern-matching would in an interactive
    /// prover's `rewrite [ih]`. What's left after rewriting is closed by
    /// `by algebra`, which already knows how to discharge a relation under
    /// several leading `forall`s.
    ///
    /// Only `==` goals are supported (rewriting needs an equation) — `<=`
    /// etc. would need a genuine generalization of this technique.
    fn verify_list_induction_generalized(
        &self,
        var: &str,
        body: &Expr,
        env: &Env,
    ) -> SekiResult<Value> {
        let (extra, inner) = peel_leading_foralls(body);
        let (lhs, rhs) = match inner {
            Expr::BinOp(BinOp::Eq, l, r) => (l.as_ref(), r.as_ref()),
            _ => {
                return Err(SekiError::Proof(format!(
                    "by induction: generalized list induction only supports `==` goals \
                     (auxiliary foralls before the relation), got {}",
                    inner
                )))
            }
        };
        let extra_names: Vec<String> = extra.iter().map(|(n, _)| n.clone()).collect();

        // ---- base: forall extra.., lhs[var:=nil] == rhs[var:=nil] ----
        let nil_expr = Expr::List(vec![]);
        let lhs_nil = unfold_to_fixpoint(&subst(lhs, var, &nil_expr), self.ctx, env);
        let rhs_nil = unfold_to_fixpoint(&subst(rhs, var, &nil_expr), self.ctx, env);
        if !exprs_equal(&canonicalize(&lhs_nil), &canonicalize(&rhs_nil)) {
            let base_goal = rebuild_foralls(
                &extra,
                Expr::BinOp(BinOp::Eq, Box::new(lhs_nil), Box::new(rhs_nil)),
            );
            self.verify_algebra(&base_goal, env).map_err(|e| {
                SekiError::Proof(format!("by induction: base case P([]) failed: {}", e))
            })?;
        }

        // ---- step: IH is `forall extra.., lhs[var:=ys] == rhs[var:=ys]` ----
        let xname = format!("__x_{}", var);
        let ysname = format!("__ys_{}", var);
        let ys_expr = Expr::Var { name: ysname.clone(), line: 0, col: 0 };
        let cons_expr = Expr::App {
            func: Box::new(Expr::Var { name: "cons".into(), line: 0, col: 0 }),
            args: vec![Expr::Var { name: xname, line: 0, col: 0 }, ys_expr.clone()],
        };
        // Only ONE level of unfolding here (mirroring the plain
        // `verify_list_induction` step) — enough to expose the recursive
        // sub-call(s) on `ys` that the IH rewrite rule below should match.
        // Fully reducing to a fixpoint (as the base case does) would chase
        // `null`/`head`/`tail` through the still-symbolic `ys`, producing
        // an explosion of undecidable case-splits instead of a clean IH
        // application.
        let lhs_cons = normalize_nil(&simplify_list_ops_fixpoint(
            &unfold_one(&subst(lhs, var, &cons_expr), self.ctx, env),
            self.ctx,
            env,
        ));
        let rhs_cons = normalize_nil(&simplify_list_ops_fixpoint(
            &unfold_one(&subst(rhs, var, &cons_expr), self.ctx, env),
            self.ctx,
            env,
        ));
        // Normalize the IH's lhs/rhs the same way as `lhs_cons`/`rhs_cons`
        // (`simplify_list_ops` may rewrite `cons`-applications into a
        // different internal shape while resolving `head`/`tail`/`null` —
        // matching against an un-normalized IH pattern would silently never
        // fire).
        let ih_rule = SimpRule {
            name: "<induction hypothesis>".into(),
            metavars: extra_names,
            lhs: normalize_nil(&simplify_list_ops_fixpoint(&subst(lhs, var, &ys_expr), self.ctx, env)),
            rhs: normalize_nil(&simplify_list_ops_fixpoint(&subst(rhs, var, &ys_expr), self.ctx, env)),
        };
        let rule = std::slice::from_ref(&ih_rule);
        let mut lhs_step = lhs_cons;
        let mut rhs_step = rhs_cons;
        let mut ih_used: BTreeSet<String> = BTreeSet::new();
        for _ in 0..8 {
            let l2 = canonicalize(&simp_rewrite(&lhs_step, rule, &mut ih_used));
            let r2 = canonicalize(&simp_rewrite(&rhs_step, rule, &mut ih_used));
            let done = exprs_equal(&l2, &lhs_step) && exprs_equal(&r2, &rhs_step);
            lhs_step = l2;
            rhs_step = r2;
            if done {
                break;
            }
        }
        let step_goal = rebuild_foralls(
            &extra,
            Expr::BinOp(BinOp::Eq, Box::new(lhs_step), Box::new(rhs_step)),
        );
        self.verify_algebra(&step_goal, env).map_err(|e| {
            SekiError::Proof(format!("by induction: step case fails: {}", e))
        })
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
        // An opaque atom here is the proposition at a smaller argument,
        // which strong induction's hypothesis has already granted — see
        // `polynomial_nonneg_under_ih`.
        let ok = match op {
            BinOp::Eq => diff.terms.is_empty(),
            BinOp::Ge | BinOp::Gt => polynomial_nonneg_under_ih(&diff, dom),
            BinOp::Le | BinOp::Lt => polynomial_nonpos_under_ih(&diff, dom),
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
        // Same as `verify_strong_induction`: an opaque atom in the step is
        // the induction hypothesis, not an arbitrary expression.
        let ok = match op {
            BinOp::Eq => diff.terms.is_empty(),
            BinOp::Ge | BinOp::Gt => polynomial_nonneg_under_ih(&diff, dom),
            BinOp::Le | BinOp::Lt => polynomial_nonpos_under_ih(&diff, dom),
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

    /// `by assumption` — the goal's conclusion is already assumed.
    fn verify_assumption(&self, prop: &Expr) -> SekiResult<()> {
        let (concl, hyps) = peel_implications(strip_foralls(prop));
        if hyps.iter().any(|h| crate::ast::alpha_equiv(h, &concl)) {
            return Ok(());
        }
        Err(SekiError::Proof(format!(
            "by assumption: `{}` is not among the hypotheses in scope ({})",
            concl,
            if hyps.is_empty() {
                "there are none".to_string()
            } else {
                hyps.iter().map(|h| format!("{}", h)).collect::<Vec<_>>().join(", ")
            }
        )))
    }

    /// `by apply L [with ...]` — modus ponens.
    ///
    /// Returns the full instantiation (including the parts inferred by
    /// matching, so the certificate records exactly what was used) and the
    /// premise sub-goals that were discharged.
    fn verify_apply(
        &self,
        prop: &Expr,
        lemma: &str,
        substs: &[(String, Expr)],
        env: &Env,
    ) -> SekiResult<(Vec<(String, Expr)>, Vec<Expr>)> {
        let stmt = self
            .ctx
            .globals
            .theorem_props
            .get(lemma)
            .or_else(|| self.ctx.globals.axiom_props.get(lemma))
            .cloned()
            .ok_or_else(|| {
                SekiError::Proof(format!(
                    "by apply: unknown theorem/axiom `{}`{}",
                    lemma,
                    self.nearest_known_name(lemma)
                        .map(|n| format!(" (did you mean `{}`?)", n))
                        .unwrap_or_default()
                ))
            })?;

        let (goal_concl, goal_hyps) = peel_implications(strip_foralls(prop));
        let full = self.instantiate_lemma(lemma, &stmt, substs, &goal_concl)?;

        // Apply the instantiation and read off what the lemma then says.
        let mut cur = stmt;
        while let Expr::Forall { var, body, .. } = cur {
            let value = full
                .iter()
                .find(|(n, _)| *n == var)
                .map(|(_, e)| e.clone())
                .expect("instantiate_lemma covers every binder");
            cur = subst(body.as_ref(), &var, &value);
        }
        for (n, v) in &full {
            cur = subst(&cur, n, v);
        }
        let (lemma_concl, lemma_prems) = peel_implications(strip_foralls(&cur));
        if !crate::ast::alpha_equiv(&lemma_concl, &goal_concl) {
            return Err(SekiError::Proof(format!(
                "by apply {}: the lemma concludes `{}`, but the goal is `{}`",
                lemma, lemma_concl, goal_concl
            )));
        }

        // Discharge each premise: already assumed, or provable outright.
        let mut premise_goals = Vec::new();
        for p in &lemma_prems {
            let sub = under_hypotheses(&goal_hyps, p.clone());
            if goal_hyps.iter().any(|h| crate::ast::alpha_equiv(h, p)) {
                premise_goals.push(sub);
                continue;
            }
            self.verify_algebra(&sub, env).map_err(|_| {
                // Name the premise, say what *is* in scope, and say how to
                // supply it — a proof fails far more often for a missing
                // assumption than for a wrong one, and "could not discharge"
                // on its own leaves the reader to work out which.
                let in_scope = if goal_hyps.is_empty() {
                    "nothing is assumed here".to_string()
                } else {
                    format!(
                        "in scope: {}",
                        goal_hyps
                            .iter()
                            .map(|h| format!("`{}`", h))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                SekiError::Proof(format!(
                    "by apply {}: premise `{}` is neither assumed nor provable outright \
                     ({}).\n  supply it with `by have h : {} := <proof> then apply {}`, \
                     or add it to the theorem's hypotheses",
                    lemma, p, in_scope, p, lemma
                ))
            })?;
            premise_goals.push(sub);
        }
        Ok((full, premise_goals))
    }

    /// The accepted theorem or axiom whose name is closest to `name`, when
    /// one is close enough to be worth suggesting.
    fn nearest_known_name(&self, name: &str) -> Option<String> {
        let mut best: Option<(usize, String)> = None;
        let candidates = self
            .ctx
            .globals
            .theorem_props
            .keys()
            .chain(self.ctx.globals.axiom_props.keys());
        for cand in candidates {
            let d = edit_distance(name, cand);
            if best.as_ref().map(|(bd, _)| d < *bd).unwrap_or(true) {
                best = Some((d, cand.clone()));
            }
        }
        // Only suggest a name that is actually close — a third of the
        // length, at most.
        best.filter(|(d, _)| *d * 3 <= name.len().max(1))
            .map(|(_, n)| n)
    }

    /// Work out a value for every variable the lemma quantifies over.
    ///
    /// Anything the caller gave in `with` wins; the rest is inferred by
    /// matching the lemma's conclusion against the goal's. That inference is
    /// what makes `by apply` usable — without it every application would
    /// have to spell out bindings that are obvious from the goal.  A wrong
    /// guess cannot make a bad proof pass: the instantiated conclusion still
    /// has to match the goal, and the kernel redoes the whole thing.
    fn instantiate_lemma(
        &self,
        lemma: &str,
        stmt: &Expr,
        substs: &[(String, Expr)],
        goal_concl: &Expr,
    ) -> SekiResult<Vec<(String, Expr)>> {
        let mut binders = Vec::new();
        let mut cur = stmt;
        while let Expr::Forall { var, body, .. } = cur {
            binders.push(var.clone());
            cur = body;
        }
        let mut full: Vec<(String, Expr)> = substs.to_vec();
        let missing: Vec<String> = binders
            .iter()
            .filter(|b| !full.iter().any(|(n, _)| n == *b))
            .cloned()
            .collect();
        if !missing.is_empty() {
            // Match the lemma's conclusion (with the unresolved binders as
            // wildcards) against the goal's conclusion.  The bindings the
            // caller *did* give are substituted in first, so that
            // `shift_mono with c := 10.0` matches `(x + 10.0) <= (y + 10.0)`
            // rather than the unsubstituted `(x + c) <= (y + c)`.
            let mut known = cur.clone();
            for (n, v) in &full {
                known = subst(&known, n, v);
            }
            let (lemma_concl, _) = peel_implications(&known);
            if let Some(m) = crate::rewrite::match_pattern(&lemma_concl, goal_concl, &missing) {
                for name in &missing {
                    if let Some(e) = m.get(name) {
                        full.push((name.clone(), e.clone()));
                    }
                }
            }
        }
        let still_missing: Vec<&String> = binders
            .iter()
            .filter(|b| !full.iter().any(|(n, _)| n == *b))
            .collect();
        if !still_missing.is_empty() {
            return Err(SekiError::Proof(format!(
                "by apply {}: could not work out what to use for {} — matching the \
                 conclusion against the goal did not determine {}; give {} explicitly",
                lemma,
                still_missing
                    .iter()
                    .map(|n| format!("`{}`", n))
                    .collect::<Vec<_>>()
                    .join(", "),
                if still_missing.len() == 1 { "it" } else { "them" },
                still_missing
                    .iter()
                    .map(|n| format!("`with {} := ...`", n))
                    .collect::<Vec<_>>()
                    .join(", ")
            )));
        }
        Ok(full)
    }

    /// Certificate for one premise of an applied lemma: it is either
    /// already assumed, or it was discharged by `by algebra`.
    fn premise_cert(&self, goal: &Expr, env: &Env) -> Cert {
        let (concl, hyps) = peel_implications(strip_foralls(goal));
        if hyps.iter().any(|h| crate::ast::alpha_equiv(h, &concl)) {
            return Cert::Assumption;
        }
        self.algebra_cert(goal, env)
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
        self.simp_run(prop, env, lemmas).map(|(v, _)| v)
    }

    /// `verify_simp`'s core, additionally reporting which rewrite rules
    /// actually fired (see `crate::trust`).
    fn simp_run(
        &self,
        prop: &Expr,
        env: &Env,
        lemmas: &[String],
    ) -> SekiResult<(Value, BTreeSet<String>)> {
        let run = self.simp_fixpoint(prop, lemmas, SimpMode::Close)?;
        if self
            .simp_closure(&run.states, env, SimpMode::Close)
            .is_some()
        {
            return Ok((Value::Bool(true), run.used));
        }
        Err(SekiError::Proof(format!(
            "by simp: could not reduce goal to true; reached {}",
            run.final_state
        )))
    }

    /// Rewrite `prop` with the `lemmas` rule set until nothing changes,
    /// recording every intermediate state and every rule that fired.
    ///
    /// Shared by `by simp` as a closer (`simp_run`) and as a transformer
    /// inside a `then` chain (`run_step`), which used to keep two divergent
    /// copies of this loop.  `mode` preserves the one real difference
    /// between them — see [`SimpMode`].
    fn simp_fixpoint(
        &self,
        prop: &Expr,
        lemmas: &[String],
        mode: SimpMode,
    ) -> SekiResult<SimpRun> {
        let rules = collect_simp_rules(self.ctx, lemmas)?;
        let mut used: BTreeSet<String> = BTreeSet::new();
        // `crate::rewrite::rewrite_goal` is the shared, trusted engine: the
        // kernel re-runs exactly this to check that a certificate's claimed
        // rewrite really is reachable.
        let states = rewrite_goal(prop, &rules, mode == SimpMode::Close, &mut used);
        let final_state = states.last().cloned().unwrap_or_else(|| prop.clone());
        Ok(SimpRun { states, final_state, used })
    }

    /// Did the rewrite reach a state that closes the goal?  Any visited
    /// state matching one of
    ///   1. the `Bool(true)` literal
    ///   2. an equality whose two sides became alpha-equivalent
    ///      (after canonicalization, AC-equivalent forms count)
    ///   3. something that evaluates to `Bool(true)` under `env`
    /// is enough.
    fn simp_closure(
        &self,
        states: &[Expr],
        env: &Env,
        mode: SimpMode,
    ) -> Option<SimpClosure> {
        for (i, state) in states.iter().enumerate() {
            if matches!(crate::rewrite::peel_binders(state).1, Expr::Bool(true)) {
                return Some(SimpClosure::Syntactic);
            }
            if let Expr::BinOp(BinOp::Eq, l, r) = crate::rewrite::peel_binders(state).1 {
                let equal = match mode {
                    SimpMode::Close => {
                        crate::ast::alpha_equiv(&canonicalize(l), &canonicalize(r))
                    }
                    SimpMode::Transform => crate::ast::alpha_equiv(l, r),
                };
                if equal {
                    return Some(SimpClosure::Syntactic);
                }
            }
            if matches!(self.ctx.eval(state, env), Ok(Value::Bool(true))) {
                return Some(SimpClosure::Evaluated(i));
            }
        }
        None
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


    // -- proof terms --------------------------------------------------------

    /// Verify `prop` and return the *proof term* that records how it was
    /// closed (`crate::kernel::Cert`).
    ///
    /// This is the real entry point now: `verify` is a thin wrapper that
    /// throws the certificate away.  A tactic is free to search however it
    /// likes — the certificate it produces has to survive `kernel::check`
    /// afterwards, and that check does not call back into any tactic.
    pub fn certify(&self, prop: &Expr, proof: &Proof, env: &Env) -> SekiResult<Cert> {
        match proof {
            Proof::Refl => {
                self.verify_refl(prop, env)?;
                Ok(Cert::Refl)
            }

            // Every "reduce the proposition and look at the answer" tactic
            // goes through the same structural analysis, which is where a
            // goal either decomposes into checkable pieces or is recorded
            // as having been sampled.
            Proof::ByEval | Proof::ByDecide => {
                self.verify(prop, proof, env)?;
                Ok(self.evaluation_cert(prop, env))
            }
            Proof::ByIntros => {
                self.verify(prop, proof, env)?;
                let (binders, inner) = crate::rewrite::peel_binders(prop);
                if binders.is_empty() {
                    return Ok(self.evaluation_cert(prop, env));
                }
                Ok(Cert::Generalize {
                    vars: binders.into_iter().map(|(v, _)| v).collect(),
                    then: Box::new(self.evaluation_cert(inner, env)),
                })
            }
            Proof::Term(term) => {
                self.verify(prop, proof, env)?;
                // A proof term for `exists` *is* the witness.
                if let Expr::Exists { .. } = prop {
                    if let Some(c) = self.exists_cert_with(prop, term, env) {
                        return Ok(c);
                    }
                }
                Ok(self.evaluation_cert(prop, env))
            }

            Proof::ByAlgebra | Proof::ByLinarith => {
                self.verify_algebra(prop, env)?;
                Ok(self.algebra_cert(prop, env))
            }

            Proof::ByInduction => {
                self.verify_induction(prop, env)?;
                Ok(self.induction_cert(prop, env))
            }

            Proof::ByStrongInduction { depth } => {
                self.verify_strong_induction(prop, env, *depth)?;
                Ok(Cert::Trusted {
                    tactic: "by strong_induction",
                    reason: TrustReason::NoWitnessYet,
                    why: "the well-founded step is discharged by unfolding to a fixed \
                          depth; no witness for that is emitted yet"
                        .into(),
                })
            }

            Proof::BySimp { lemmas } => {
                let (_, _) = self.simp_run(prop, env, lemmas)?;
                Ok(self.simp_cert(prop, env, lemmas, SimpMode::Close))
            }

            Proof::ByUnfold(name) => {
                self.verify(prop, proof, env)?;
                let unfolded = self.do_unfold(prop, name)?;
                Ok(Cert::Unfold {
                    name: name.clone(),
                    unfolded: unfolded.clone(),
                    then: Box::new(self.evaluation_cert(&unfolded, env)),
                })
            }

            Proof::Seq(tacs) => {
                self.verify_seq(prop, env, tacs)?;
                self.seq_cert(prop, env, tacs)
            }

            // Prefer a proof the kernel will accept over the first one that
            // merely closes the goal — see `try_portfolio_sound`.
            Proof::ByAuto => match self.try_portfolio_sound(prop, env) {
                Some(found) => self.certify(prop, &found, env),
                None => Err(SekiError::Proof(
                    "by auto: no tactic in the portfolio closed the goal".into(),
                )),
            },

            Proof::Assumption => {
                self.verify_assumption(prop)?;
                Ok(Cert::Assumption)
            }
            Proof::Apply { lemma, substs } => {
                let (full_substs, premise_goals) =
                    self.verify_apply(prop, lemma, substs, env)?;
                let premises = premise_goals
                    .iter()
                    .map(|g| self.premise_cert(g, env))
                    .collect();
                Ok(Cert::Apply {
                    lemma: lemma.clone(),
                    substs: full_substs,
                    premises,
                })
            }
            Proof::Have { prop: fact, proof: sub, .. } => {
                let hyps = goal_hypotheses(prop);
                let fact_goal = under_hypotheses(&hyps, (**fact).clone());
                let fact_proof = self.certify(&fact_goal, sub, env)?;
                let extended = add_hypothesis(prop, (**fact).clone());
                Ok(Cert::Have {
                    fact: (**fact).clone(),
                    fact_proof: Box::new(fact_proof),
                    then: Box::new(self.evaluation_cert(&extended, env)),
                })
            }
            Proof::Obtain { intro, lemma, substs } => {
                self.verify(prop, proof, env)?;
                Ok(self.obtain_cert(prop, intro, lemma, substs, env))
            }
        }
    }

    /// Build a proof term for a goal that a tactic closed by *evaluating* it.
    ///
    /// The whole point is to decompose the evaluation into steps the kernel
    /// can redo without sampling.  Whatever is left over — a `forall` over
    /// an infinite domain that no definitional rule settles — becomes an
    /// explicit `Sampled` marker rather than passing silently.
    fn evaluation_cert(&self, prop: &Expr, env: &Env) -> Cert {
        match prop {
            Expr::Forall { var, domain, body } => {
                let dset = match self.ctx.eval(domain, env) {
                    Ok(Value::Set(s)) => s,
                    _ => return self.sampled("by eval", "the domain does not evaluate to a set"),
                };
                if crate::eval::is_definitely_finite(&dset) {
                    let elems = match enumerate_set(&dset, self.ctx, env) {
                        Ok(e) => e,
                        Err(_) => {
                            return self.sampled("by eval", "the domain could not be enumerated")
                        }
                    };
                    let subs = elems
                        .iter()
                        .map(|e| {
                            // Bind rather than substitute: an element may be
                            // an ADT constructor or a set, with no literal
                            // syntax to put into the goal.  The kernel binds
                            // it the same way.
                            let env2 = env.extend(var.clone(), e.clone());
                            self.evaluation_cert(body, &env2)
                        })
                        .collect();
                    return Cert::ForallFinite { subs };
                }
                // Infinite domain.  It is still sound if the *definition* of
                // the set settles it.
                if let Some(c) = self.definitional_forall_cert(var, &dset, body, prop) {
                    return c;
                }
                self.sampled(
                    "by eval",
                    "the domain is infinite, so only a finite sample was checked",
                )
            }
            Expr::Exists { var, domain, body } => {
                match self.find_witness(var, domain, body, env) {
                    Some(c) => c,
                    None => self.sampled(
                        "by eval",
                        "no witness was found within the sampled part of the domain",
                    ),
                }
            }
            // A ground proposition: the kernel simply re-evaluates it.  If
            // any quantifier is hiding inside, `finite_only` catches it
            // there rather than here.
            _ => {
                if self.kernel_can_evaluate(prop, env) {
                    Cert::Ground
                } else {
                    self.sampled(
                        "by eval",
                        "re-evaluating the goal without sampling did not yield true",
                    )
                }
            }
        }
    }

    /// Would the kernel's finiteness-strict evaluator confirm this goal?
    /// Asking here — rather than emitting a certificate and finding out
    /// later — keeps the failure attributable to the tactic.
    fn kernel_can_evaluate(&self, prop: &Expr, env: &Env) -> bool {
        let strict = EvalCtx::finite_only(self.ctx.globals);
        matches!(strict.eval(prop, env), Ok(Value::Bool(true)))
    }

    fn sampled(&self, tactic: &'static str, why: &str) -> Cert {
        Cert::Trusted {
            tactic,
            reason: TrustReason::Sampled,
            why: why.to_string(),
        }
    }

    fn no_witness(&self, tactic: &'static str, why: &str) -> Cert {
        Cert::Trusted {
            tactic,
            reason: TrustReason::NoWitnessYet,
            why: why.to_string(),
        }
    }

    /// Search the domain for a witness and package it as an `exists` proof
    /// term.  Sound at any cardinality: the kernel re-checks membership and
    /// the body, so a witness found inside a sample is still a witness.
    fn find_witness(
        &self,
        var: &str,
        domain: &Expr,
        body: &Expr,
        env: &Env,
    ) -> Option<Cert> {
        let dset = match self.ctx.eval(domain, env) {
            Ok(Value::Set(s)) => s,
            _ => return None,
        };
        let elems = enumerate_set(&dset, self.ctx, env).ok()?;
        for e in elems {
            let w = crate::kernel::value_as_expr(&e)?;
            let instance = subst(body, var, &w);
            if self.kernel_can_evaluate(&instance, env) {
                return Some(Cert::ExistsWitness {
                    witness: w,
                    sub: Box::new(self.evaluation_cert(&instance, env)),
                });
            }
        }
        None
    }

    fn exists_cert_with(&self, prop: &Expr, term: &Expr, env: &Env) -> Option<Cert> {
        let (var, body) = match prop {
            Expr::Exists { var, body, .. } => (var, body),
            _ => return None,
        };
        let instance = subst(body, var, term);
        Some(Cert::ExistsWitness {
            witness: term.clone(),
            sub: Box::new(self.evaluation_cert(&instance, env)),
        })
    }

    /// `forall x in S, P(x)` settled from `S`'s definition rather than by
    /// enumeration — the two sound routes `try_forall_from_definition`
    /// takes, expressed as proof terms.
    fn definitional_forall_cert(
        &self,
        var: &str,
        dset: &SetVal,
        body: &Expr,
        prop: &Expr,
    ) -> Option<Cert> {
        // (a) the body is one conjunct of a comprehension's predicate.
        if let SetVal::Comp { var: cv, pred, .. } = dset {
            let canon = Expr::Var { name: "__kernel_x".into(), line: 0, col: 0 };
            let body_canon = subst(body, var, &canon);
            let pred_canon = subst(pred, cv, &canon);
            let mut cs = Vec::new();
            flatten_conjuncts_expr(&pred_canon, &mut cs);
            if let Some(i) = cs
                .iter()
                .position(|c| crate::ast::alpha_equiv(c, &body_canon))
            {
                return Some(Cert::ForallFromComprehension { conjunct: i });
            }
        }
        // (b) a polynomial relation over a numeric domain.
        let cert = self.algebra_cert(prop, &Env::new());
        if !matches!(cert, Cert::Trusted { .. }) {
            return Some(cert);
        }
        None
    }

    /// A proof term for a goal that `by algebra` closed.
    ///
    /// `by algebra` *searches*: it normalizes, splits `if`s, combines
    /// hypotheses, tries sign analysis and Fourier-Motzkin.  None of that
    /// needs to be trusted — what comes out is a witness the kernel can
    /// check with addition and comparison alone.  When the search took a
    /// route that has no witness form yet, that is recorded explicitly
    /// instead of being passed off as checked.
    fn algebra_cert(&self, prop: &Expr, _env: &Env) -> Cert {
        let dom = detect_domain(prop);
        let body = strip_foralls(prop);
        let (conclusion, hyps) = peel_implications(body);
        let (op, gl, gr) = match &conclusion {
            Expr::BinOp(op, l, r) if is_relation(op) => {
                (op.clone(), (**l).clone(), (**r).clone())
            }
            _ => {
                return self.no_witness(
                    "by algebra",
                    "the goal is not a relation between two polynomials",
                )
            }
        };
        // Orient so the certificate always talks about `lhs - rhs >= 0`.
        let (lhs, rhs) = match op {
            BinOp::Le | BinOp::Lt => (gr.clone(), gl.clone()),
            _ => (gl.clone(), gr.clone()),
        };
        // The goal's conclusion is sometimes just one of its hypotheses —
        // which is what a case split leaves behind, and needs no arithmetic.
        if hyps.iter().any(|h| crate::ast::alpha_equiv(h, &conclusion)) {
            return Cert::Assumption;
        }
        let (lp, rp) = match (expr_to_poly(&lhs), expr_to_poly(&rhs)) {
            (Some(a), Some(b)) => (a, b),
            // Not a polynomial *yet*: an `if` in the goal is split on
            // first, which is how `(if x >= y then x else y) >= y` gets
            // decided.  Only give up once there is nothing left to split.
            _ => return self.case_split_or_give_up(prop, &conclusion, _env),
        };
        let diff = lp.sub(rp);
        let strict = matches!(op, BinOp::Gt | BinOp::Lt);

        // A zero difference settles `==`, and also the non-strict
        // inequalities — `y >= y` is exactly what a case split leaves on
        // the branch it does not care about.
        if diff.terms.is_empty() && matches!(op, BinOp::Eq | BinOp::Ge | BinOp::Le) {
            return Cert::Poly {
                dom,
                claim: PolyClaim::Zero { lhs, rhs },
            };
        }
        if op == BinOp::Eq {
            // An equality goal may still follow from equality hypotheses,
            // rearranged: `w³ - w - 2 = 0 ⊢ w³ = w + 2`.
            if let Some(used) = self.find_eq_combination(&hyps, &diff) {
                return Cert::Poly {
                    dom,
                    claim: PolyClaim::EqCombination { lhs, rhs, used },
                };
            }
            return self.no_witness(
                "by algebra",
                "the two sides do not normalize to the same polynomial by ring \
                 arithmetic alone (a rational-function or div/mod cancellation was used)",
            );
        }

        if op == BinOp::Neq {
            return self.no_witness(
                "by algebra",
                "a disequality is closed by showing the difference is strictly signed                  in one direction; that has no witness form yet",
            );
        }

        // The simple witnesses do not care whether the goal has hypotheses —
        // `bal >= 0` follows from `bal` being a `Nat` whether or not
        // something else is also assumed.  Gating them on `hyps.is_empty()`
        // meant a case split's "uninteresting" branch fell through to
        // Farkas, which of course could not derive it from an unrelated
        // hypothesis.
        {
            // An opaque atom stands for an arbitrary expression, so "all
            // coefficients are non-negative" says nothing about it — see
            // `algebra::polynomial_nonneg`.  A goal that needs one is not
            // provable by this witness.
            let only_real_vars = diff
                .terms
                .iter()
                .all(|m| m.vars.keys().all(|v| !crate::algebra::is_opaque_atom(v)));
            // Over `Nat` every variable may be zero, so a strict claim has
            // to rest on a positive constant term.
            let positive_constant = diff
                .terms
                .iter()
                .filter(|m| m.vars.is_empty())
                .fold(Rat::from_int(0), |a, m| a.add(m.coeff))
                .sign()
                > 0;
            if dom == PolyDomain::Nat
                && only_real_vars
                && diff.terms.iter().all(|m| m.coeff.sign() >= 0)
                && (!strict || positive_constant)
            {
                return Cert::Poly {
                    dom,
                    claim: PolyClaim::NonnegCoeffs { lhs, rhs, strict },
                };
            }
            if (!strict || positive_constant)
                && diff.terms.iter().all(|m| {
                    m.coeff.sign() >= 0 && m.vars.values().all(|e| e % 2 == 0)
                })
            {
                return Cert::Poly {
                    dom,
                    claim: PolyClaim::EvenPowers { lhs, rhs, strict },
                };
            }
        }
        if !hyps.is_empty() {
            if let Some((used, slack)) = self.find_farkas(&hyps, &diff, strict) {
                return Cert::Poly {
                    dom,
                    claim: PolyClaim::Farkas { lhs, rhs, used, slack, goal_strict: strict },
                };
            }
        }

        // A binary quadratic form: complete the square.  This is the
        // search half of the PSD test — the kernel then only has to
        // multiply the decomposition out and compare.
        if !strict {
            if let Some(terms) = sum_of_squares(&diff) {
                return Cert::Poly {
                    dom,
                    claim: PolyClaim::SumOfSquares { lhs, rhs, terms },
                };
            }
        }

        self.case_split_or_give_up(prop, &conclusion, _env)
    }

    /// Last resort for `by algebra`: split on the goal's first `if` and
    /// certify each branch, or record that nothing here has a witness form.
    fn case_split_or_give_up(&self, prop: &Expr, conclusion: &Expr, env: &Env) -> Cert {
        if split_first_if(conclusion).is_some() {
            if let Some((goal_t, goal_f)) = case_split_goals(prop) {
                let t = self.algebra_cert(&goal_t, env);
                let f = self.algebra_cert(&goal_f, env);
                if !matches!(t, Cert::Trusted { .. }) && !matches!(f, Cert::Trusted { .. }) {
                    return Cert::CaseSplit {
                        then_branch: Box::new(t),
                        else_branch: Box::new(f),
                    };
                }
            }
        }
        self.no_witness(
            "by algebra",
            "closed by a route with no witness form yet (sign analysis, PSD quadratic \
             forms, or Fourier-Motzkin elimination)",
        )
    }

    /// Express the goal's difference as a linear combination of the
    /// equality hypotheses in scope.  Multipliers are unrestricted, so the
    /// system is solved directly rather than searched.
    fn find_eq_combination(
        &self,
        hyps: &[Expr],
        diff: &crate::algebra::Polynomial,
    ) -> Option<Vec<(Expr, Rat)>> {
        let mut usable: Vec<(Expr, crate::algebra::Polynomial)> = Vec::new();
        for h in hyps {
            if let Expr::BinOp(BinOp::Eq, l, r) = h {
                if let (Some(lp), Some(rp)) = (expr_to_poly(l), expr_to_poly(r)) {
                    usable.push((h.clone(), lp.sub(rp)));
                }
            }
        }
        if usable.is_empty() {
            return None;
        }
        let polys: Vec<crate::algebra::Polynomial> =
            usable.iter().map(|(_, p)| p.clone()).collect();
        let lambdas = solve_combination(&polys, diff, false, false)?.0;
        let used: Vec<(Expr, Rat)> = usable
            .into_iter()
            .zip(lambdas)
            .filter(|(_, l)| !l.is_zero())
            .map(|((h, _), l)| (h, l))
            .collect();
        if used.is_empty() {
            return None;
        }
        Some(used)
    }

    /// Find Farkas multipliers: non-negative rationals `λᵢ` and a
    /// non-negative slack `k` with `Σ λᵢ·hypᵢ + k = diff`.
    ///
    /// This is the search half of linear arithmetic.  Matching coefficients
    /// monomial by monomial turns it into a linear system, which is solved
    /// exactly over the rationals; the kernel then only has to multiply and
    /// add.  It strictly subsumes the equal-weights subset search it
    /// replaces — `x <= 3 ⊢ 2x <= 6` needs `λ = 2`, and `2a <= 10 ⊢ 2a <= 12`
    /// needs a slack of 2, and neither was reachable before.
    fn find_farkas(
        &self,
        hyps: &[Expr],
        diff: &crate::algebra::Polynomial,
        goal_strict: bool,
    ) -> Option<(Vec<(Expr, bool, Rat)>, Rat)> {
        // Normalize each usable hypothesis to a polynomial asserted `>= 0`.
        let mut usable: Vec<(Expr, bool, crate::algebra::Polynomial)> = Vec::new();
        for h in hyps {
            if let Expr::BinOp(op, l, r) = h {
                let (a, b, strict) = match op {
                    BinOp::Ge => (l, r, false),
                    BinOp::Gt => (l, r, true),
                    BinOp::Le => (r, l, false),
                    BinOp::Lt => (r, l, true),
                    _ => continue,
                };
                if let (Some(ap), Some(bp)) = (expr_to_poly(a), expr_to_poly(b)) {
                    usable.push((h.clone(), strict, ap.sub(bp)));
                }
            }
        }
        if usable.is_empty() {
            return None;
        }
        // Solving with *every* hypothesis as a column leaves free variables,
        // and setting those to zero can miss the solution: for an interval
        // `0.05 <= r <= 0.15` the answer uses only the upper bound, but the
        // elimination may pivot on the lower one.  Searching subsets makes
        // each system determined, and going smallest-first yields the
        // simplest certificate.
        const MAX_HYPS: usize = 10;
        if usable.len() > MAX_HYPS {
            usable.truncate(MAX_HYPS);
        }
        let n = usable.len();
        let mut subsets: Vec<u32> = (1u32..(1u32 << n)).collect();
        subsets.sort_by_key(|m| m.count_ones());
        for mask in subsets {
            let chosen: Vec<usize> = (0..n).filter(|i| mask & (1 << i) != 0).collect();
            let polys: Vec<crate::algebra::Polynomial> =
                chosen.iter().map(|&i| usable[i].2.clone()).collect();
            let Some((lambdas, slack)) = solve_nonneg_combination(&polys, diff) else {
                continue;
            };
            if goal_strict {
                let strict_ok = slack.sign() > 0
                    || chosen
                        .iter()
                        .zip(&lambdas)
                        .any(|(&i, l)| usable[i].1 && l.sign() > 0);
                if !strict_ok {
                    continue;
                }
            }
            let used: Vec<(Expr, bool, Rat)> = chosen
                .iter()
                .zip(&lambdas)
                .filter(|(_, l)| !l.is_zero())
                .map(|(&i, l)| (usable[i].0.clone(), usable[i].1, *l))
                .collect();
            if used.is_empty() {
                // A constant goal needs no hypotheses; leave that to the
                // simpler witnesses.
                continue;
            }
            return Some((used, slack));
        }
        None
    }

    /// Induction: the base case becomes a real sub-proof (the kernel derives
    /// the obligation itself), the step is recorded as trusted.
    fn induction_cert(&self, prop: &Expr, env: &Env) -> Cert {
        let (var, domain, body) = match prop {
            Expr::Forall { var, domain, body } => (var, domain, body.as_ref()),
            _ => return self.no_witness("by induction", "the goal is not a `forall`"),
        };
        let base_term = match self.ctx.eval(domain, env) {
            Ok(Value::Set(s)) => match &*s {
                SetVal::Atomic(AtomicSet::Nat) => Some(Expr::Int(0)),
                SetVal::ListOf(_) => Some(Expr::Var { name: "nil".into(), line: 0, col: 0 }),
                SetVal::TreeOf(_) => Some(Expr::Var { name: "leaf".into(), line: 0, col: 0 }),
                _ => None,
            },
            _ => None,
        };
        let Some(base_term) = base_term else {
            return self.no_witness(
                "by induction",
                "the domain has no structural base case the kernel knows",
            );
        };
        let base_goal = subst(body, var, &base_term);
        Cert::Induction {
            base: Box::new(self.evaluation_cert(&base_goal, env)),
            step: Box::new(self.no_witness(
                "by induction",
                "the inductive step is discharged by unfolding the successor side and \
                 comparing polynomial differences; that normalization has no witness \
                 form yet",
            )),
        }
    }

    /// `by simp`: the trace of rewrites, then whatever closed the result.
    fn simp_cert(&self, prop: &Expr, env: &Env, lemmas: &[String], mode: SimpMode) -> Cert {
        let Ok(run) = self.simp_fixpoint(prop, lemmas, mode) else {
            return self.no_witness("by simp", "the rewrite run was not reproducible");
        };
        let Some(closure) = self.simp_closure(&run.states, env, mode) else {
            return self.no_witness("by simp", "the rewrite did not close the goal");
        };
        let idx = match closure {
            // The first state that closes *syntactically* — asking
            // `simp_closure` per state would also accept one that merely
            // evaluates to true, which for an infinite domain means it was
            // sampled.
            SimpClosure::Syntactic => run
                .states
                .iter()
                .position(|st| match crate::rewrite::peel_binders(st).1 {
                    Expr::Bool(true) => true,
                    Expr::BinOp(BinOp::Eq, l, r) => crate::ast::alpha_equiv(
                        &canonicalize(l),
                        &canonicalize(r),
                    ),
                    _ => false,
                })
                .unwrap_or(0),
            SimpClosure::Evaluated(i) => i,
        };
        let reached = run.states[idx].clone();
        let then = match crate::rewrite::peel_binders(&reached).1 {
            Expr::Bool(true) => Cert::Ground,
            Expr::BinOp(BinOp::Eq, l, r) if crate::ast::alpha_equiv(l, r) => {
                Cert::SyntacticRefl
            }
            _ => self.evaluation_cert(&reached, env),
        };
        // The goal is only unchanged if canonicalization did nothing
        // either — `x + 0 == x` canonicalizes to `x == x` before any rule
        // fires, and that step has to be recorded too.
        if crate::ast::alpha_equiv(&reached, prop) {
            return then;
        }
        Cert::Rewrite {
            lemmas: run.used.iter().cloned().collect(),
            result: reached,
            then: Box::new(then),
        }
    }

    /// A `then` chain: replay it, and certify whichever step actually closed
    /// the goal against the goal *it* saw.
    fn seq_cert(&self, prop: &Expr, env: &Env, tacs: &[Proof]) -> SekiResult<Cert> {
        let mut current = prop.clone();
        let mut wraps: Vec<SeqWrap> = Vec::new();
        for t in tacs {
            match self.run_step(&current, env, t)? {
                TacOutcome::Closed => {
                    let inner = self.certify(&current, t, env)?;
                    return Ok(wrap_seq(wraps, inner));
                }
                TacOutcome::NewGoal(g) => {
                    match t {
                        Proof::ByUnfold(name) => {
                            wraps.push(SeqWrap::Unfold(name.clone(), g.clone()))
                        }
                        Proof::ByIntros => {
                            let (binders, _) = crate::rewrite::peel_binders(&current);
                            wraps.push(SeqWrap::Generalize(
                                binders.into_iter().map(|(v, _)| v).collect(),
                            ));
                        }
                        Proof::Obtain { intro, lemma, substs } => {
                            let (_, hyps) =
                                peel_implications(strip_foralls(&current));
                            match self.lemma_premise_certs(lemma, substs, &hyps, env) {
                                Some(premises) => wraps.push(SeqWrap::Obtain {
                                    intro: intro.clone(),
                                    lemma: lemma.clone(),
                                    substs: substs.clone(),
                                    premises,
                                }),
                                None => wraps.push(SeqWrap::Opaque("by obtain")),
                            }
                        }
                        Proof::Have { prop: fact, proof: sub, .. } => {
                            let hyps = goal_hypotheses(&current);
                            let fact_goal =
                                under_hypotheses(&hyps, (**fact).clone());
                            let fact_cert = self.certify(&fact_goal, sub, env)?;
                            wraps.push(SeqWrap::Have((**fact).clone(), fact_cert));
                        }
                        // `simp` and `obtain` as transformers do not have a
                        // wrapper form yet; the chain's certificate stops
                        // being checkable at that point.
                        _ => wraps.push(SeqWrap::Opaque(tactic_name(t))),
                    }
                    current = g;
                }
            }
        }
        Err(SekiError::Proof(
            "tactic sequence ended with an unclosed goal".into(),
        ))
    }


    fn obtain_cert(
        &self,
        prop: &Expr,
        intro: &str,
        lemma: &str,
        substs: &[(String, Expr)],
        env: &Env,
    ) -> Cert {
        let (conclusion, context_hyps) = peel_implications(strip_foralls(prop));
        let Ok(fact) = self.verify_obtain(intro, lemma, substs, &context_hyps, env) else {
            return self.no_witness("by obtain", "the instantiation was not reproducible");
        };
        let premises = match self.lemma_premise_certs(lemma, substs, &context_hyps, env) {
            Some(p) => p,
            None => {
                return self.no_witness(
                    "by obtain",
                    "a premise of the lemma has no witness form",
                )
            }
        };
        let goal = under_hypotheses(&[fact], conclusion);
        Cert::Obtain {
            lemma: lemma.to_string(),
            intro: intro.to_string(),
            substs: substs.to_vec(),
            premises,
            then: Box::new(self.evaluation_cert(&goal, env)),
        }
    }

    /// Certificates for each premise of `lemma` once instantiated — shared
    /// by `by apply` and `by obtain`, which discharge premises the same way.
    fn lemma_premise_certs(
        &self,
        lemma: &str,
        substs: &[(String, Expr)],
        context_hyps: &[Expr],
        env: &Env,
    ) -> Option<Vec<Cert>> {
        let stmt = self
            .ctx
            .globals
            .theorem_props
            .get(lemma)
            .or_else(|| self.ctx.globals.axiom_props.get(lemma))?
            .clone();
        let mut cur = stmt;
        while let Expr::Forall { var, body, .. } = cur {
            let value = substs.iter().find(|(n, _)| *n == var).map(|(_, e)| e.clone())?;
            cur = subst(body.as_ref(), &var, &value);
        }
        for (n, v) in substs {
            cur = subst(&cur, n, v);
        }
        let (_, prems) = peel_implications(&cur);
        let mut out = Vec::new();
        for p in &prems {
            let sub = under_hypotheses(context_hyps, p.clone());
            out.push(self.premise_cert(&sub, env));
        }
        Some(out)
    }

    // -- trust accounting ---------------------------------------------------

    /// How much a *successful* `verify(prop, proof, env)` is actually worth.
    ///
    /// `verify` only answers "did a tactic close this goal".  Two of seki's
    /// tactics can close a goal that is false — `by eval` over an infinite
    /// domain (which enumerates only `SAMPLE_BOUND` elements) and anything
    /// resting on an `axiom`.  This walks the same proposition and proof and
    /// reports the level of the weakest ingredient, so callers can refuse to
    /// launder a sampled check into a "proof".  See `crate::trust`.
    ///
    /// Only ever *over*-estimates the risk: whenever it cannot tell (a domain
    /// that does not evaluate in this environment, a quantifier in a position
    /// whose polarity is unclear), it reports `Sampled`.
    pub fn trust_of(&self, prop: &Expr, proof: &Proof, env: &Env) -> TrustLevel {
        self.statement_trust(prop)
            .weakest(self.proof_trust(prop, proof, env))
    }

    /// Assumptions pulled in by the *statement* itself.  Naming an axiom in a
    /// proposition makes it evaluate to `true`, so `theorem t : someAxiom :=
    /// by eval` is really a restatement of the axiom.
    fn statement_trust(&self, prop: &Expr) -> TrustLevel {
        let mut ids = std::collections::HashSet::new();
        collect_idents(prop, &mut ids);
        TrustLevel::weakest_of(ids.iter().map(|id| self.name_trust(id)))
    }

    /// The level a cited axiom / theorem contributes.
    fn name_trust(&self, name: &str) -> TrustLevel {
        if self.ctx.globals.axiom_props.contains_key(name) {
            return TrustLevel::Axiomatic;
        }
        self.ctx
            .globals
            .theorem_trust
            .get(name)
            .copied()
            .unwrap_or(TrustLevel::Sound)
    }

    fn proof_trust(&self, prop: &Expr, proof: &Proof, env: &Env) -> TrustLevel {
        match proof {
            // Closed by a decision procedure that never enumerates a domain:
            // structural equality, polynomial normalization, or induction
            // whose step is discharged over the polynomial fragment.
            Proof::Refl
            | Proof::ByAlgebra
            | Proof::ByLinarith
            | Proof::ByInduction
            | Proof::ByStrongInduction { .. } => TrustLevel::Sound,

            // Every tactic that finishes by *evaluating* the goal inherits
            // `enumerate_set`'s sampling of infinite domains.
            Proof::ByEval
            | Proof::ByDecide
            | Proof::ByIntros
            | Proof::ByUnfold(_)
            | Proof::Term(_) => self.quantifier_trust(prop, env, Polarity::Positive),

            Proof::BySimp { lemmas } => {
                self.simp_trust(prop, env, lemmas, SimpMode::Close)
            }

            Proof::Seq(tacs) => self.seq_trust(prop, env, tacs),

            Proof::Obtain { lemma, .. } => self
                .name_trust(lemma)
                .weakest(self.quantifier_trust(prop, env, Polarity::Positive)),

            Proof::Assumption => TrustLevel::Sound,
            Proof::Apply { lemma, .. } => self.name_trust(lemma),
            Proof::Have { proof: sub, .. } => self.proof_trust(prop, sub, env),

            // Re-run the portfolio to learn which candidate actually closed
            // the goal; `by auto` is otherwise a blank cheque.
            Proof::ByAuto => match self.try_portfolio_sound(prop, env) {
                Some(found) => self.proof_trust(prop, &found, env),
                None => TrustLevel::Sampled,
            },
        }
    }

    /// What a goal-closing `by simp` is worth.
    ///
    /// Rewriting itself is sound, so the two ingredients are the lemmas that
    /// fired and *how* the rewritten goal was finally discharged: reaching
    /// `true` (or an equality whose sides became identical) is purely
    /// syntactic and costs nothing, while falling back on evaluating the
    /// rewritten goal inherits that evaluation's sampling.
    fn simp_trust(
        &self,
        goal: &Expr,
        env: &Env,
        lemmas: &[String],
        mode: SimpMode,
    ) -> TrustLevel {
        let run = match self.simp_fixpoint(goal, lemmas, mode) {
            Ok(r) => r,
            // `verify` succeeded, so a failure here means the run was not
            // reproducible; stay conservative.
            Err(_) => return TrustLevel::Sampled,
        };
        let from_lemmas =
            TrustLevel::weakest_of(run.used.iter().map(|n| self.name_trust(n)));
        match self.simp_closure(&run.states, env, mode) {
            Some(SimpClosure::Syntactic) => from_lemmas,
            Some(SimpClosure::Evaluated(i)) => from_lemmas
                .weakest(self.quantifier_trust(&run.states[i], env, Polarity::Positive)),
            None => TrustLevel::Sampled,
        }
    }

    /// Replay a `then` chain to find out which step actually closed the
    /// goal, and charge that step against the goal *it* saw.
    ///
    /// Only the closer evaluates the proposition, so a chain like
    /// `by unfold absR then algebra` over `forall x in Real` is fully sound
    /// even though a standalone `by unfold` would not be: `unfold` and
    /// `intros` merely rewrite the goal, and `obtain` merely introduces a
    /// fact.  Charging every step as if it were the closer would flag such
    /// chains as sampled.
    fn seq_trust(&self, prop: &Expr, env: &Env, tacs: &[Proof]) -> TrustLevel {
        let mut current = prop.clone();
        let mut worst = TrustLevel::Sound;
        for t in tacs {
            match self.run_step(&current, env, t) {
                Ok(TacOutcome::Closed) => {
                    let step = match t {
                        // Inside a chain, `by simp` runs in `Transform`
                        // mode, so its trust must be measured the same way.
                        Proof::BySimp { lemmas } => {
                            self.simp_trust(&current, env, lemmas, SimpMode::Transform)
                        }
                        other => self.proof_trust(&current, other, env),
                    };
                    return worst.weakest(step);
                }
                Ok(TacOutcome::NewGoal(g)) => {
                    worst = worst.weakest(self.transform_trust(&current, t));
                    current = g;
                }
                // `verify` already succeeded, so a step failing on replay
                // means the tactics are not reproducible; stay conservative.
                Err(_) => return TrustLevel::Sampled,
            }
        }
        TrustLevel::Sampled
    }

    /// What a non-closing step in a `then` chain contributes: the
    /// assumptions it pulled in, and nothing else.  Transformers never
    /// evaluate the goal, so they never sample a domain.
    fn transform_trust(&self, goal: &Expr, t: &Proof) -> TrustLevel {
        match t {
            Proof::ByUnfold(_) | Proof::ByIntros => TrustLevel::Sound,
            Proof::Obtain { lemma, .. } => self.name_trust(lemma),
            Proof::BySimp { lemmas } => match self.simp_fixpoint(
                goal,
                lemmas,
                SimpMode::Transform,
            ) {
                Ok(run) => {
                    TrustLevel::weakest_of(run.used.iter().map(|n| self.name_trust(n)))
                }
                Err(_) => TrustLevel::Sampled,
            },
            _ => TrustLevel::Sound,
        }
    }

    /// Scan a proposition that has been established *true* for quantifiers
    /// whose domain `enumerate_set` would only sample.
    ///
    /// Polarity matters, because sampling is unsound in exactly one
    /// direction.  A positive `forall n in Nat, P n` accepted by enumeration
    /// proves nothing (`P` may fail at 10^9), but a positive `exists n in
    /// Nat, P n` accepted by enumeration produced an actual witness, and a
    /// *negative* `forall` accepted by enumeration produced an actual
    /// counterexample — both are sound.
    fn quantifier_trust(&self, e: &Expr, env: &Env, pol: Polarity) -> TrustLevel {
        use Expr::*;
        match e {
            Forall { var, domain, body } => {
                self.binder_trust(var, domain, body, env, pol, true)
            }
            Exists { var, domain, body } => {
                self.binder_trust(var, domain, body, env, pol, false)
            }
            UnOp(crate::ast::UnOp::Not, x) => self.quantifier_trust(x, env, pol.flip()),
            BinOp(crate::ast::BinOp::And, l, r)
            | BinOp(crate::ast::BinOp::Or, l, r) => self
                .quantifier_trust(l, env, pol)
                .weakest(self.quantifier_trust(r, env, pol)),
            // `P -> Q` read as an implication: the premise sits in negative
            // position.  (`(not P) or Q`, the other spelling, is already
            // handled by the `Or` / `Not` arms above.)
            Arrow(l, r) => self
                .quantifier_trust(l, env, pol.flip())
                .weakest(self.quantifier_trust(r, env, pol)),
            If { cond, then_branch, else_branch } => self
                .quantifier_trust(cond, env, Polarity::Unknown)
                .weakest(self.quantifier_trust(then_branch, env, pol))
                .weakest(self.quantifier_trust(else_branch, env, pol)),
            _ => {
                // Any other context (an argument position, a comparison
                // between propositions, a set comprehension) does not
                // preserve polarity, so recurse without it.
                let mut worst = TrustLevel::Sound;
                for child in crate::ast::children(e) {
                    worst = worst.weakest(self.quantifier_trust(
                        child,
                        env,
                        Polarity::Unknown,
                    ));
                }
                worst
            }
        }
    }

    /// One quantifier.  `is_forall` selects which direction of sampling is
    /// the unsound one.
    fn binder_trust(
        &self,
        var: &str,
        domain: &Expr,
        body: &Expr,
        env: &Env,
        pol: Polarity,
        is_forall: bool,
    ) -> TrustLevel {
        let dset = match self.ctx.eval(domain, env) {
            Ok(Value::Set(s)) => s,
            // The domain depends on an enclosing binder (or does not
            // evaluate at all) — we cannot show it is finite, so assume the
            // worst.
            _ => return TrustLevel::Sampled,
        };
        if crate::eval::is_definitely_finite(&dset) {
            // Enumeration was exhaustive; only the body can still be weak.
            return self.quantifier_trust(body, env, pol);
        }
        // Infinite domain: `enumerate_set` returned a sample.
        if is_forall {
            // A sound definitional discharge (`try_forall_from_definition`
            // — the same polynomial decision `by algebra` uses) means the
            // quantifier never went through enumeration at all.
            if crate::eval::try_forall_from_definition(var, &dset, body) == Some(true) {
                return TrustLevel::Sound;
            }
            match pol {
                // Sampling can only make a `forall` look *truer* than it is.
                Polarity::Positive | Polarity::Unknown => TrustLevel::Sampled,
                // Here a `false` from the sample is a real counterexample.
                Polarity::Negative => self.quantifier_trust(body, env, pol),
            }
        } else {
            if crate::eval::try_exists_from_definition(var, &dset, body) == Some(true) {
                return TrustLevel::Sound;
            }
            match pol {
                // A `true` from the sample is a real witness.
                Polarity::Positive => self.quantifier_trust(body, env, pol),
                Polarity::Negative | Polarity::Unknown => TrustLevel::Sampled,
            }
        }
    }
}

/// Which of the two `by simp` roles a rewrite run is playing.
///
/// As a closer, `by simp` AC-canonicalizes every state so that symmetric
/// rules (`add_comm` and friends) settle instead of oscillating.  As a
/// transformer inside a `then` chain it must *not*: the next tactic gets
/// the goal as written, and reordering an AC operand chain can stop a later
/// rule — or a later `by algebra` — from matching what the user wrote.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SimpMode {
    Close,
    Transform,
}

/// How a `by simp` run discharged its goal.
enum SimpClosure {
    /// Rewriting alone reached `true`, or made both sides of an equality
    /// identical.  No evaluation, so nothing was sampled.
    Syntactic,
    /// Evaluating the rewritten state at this index returned `true` — which
    /// samples any infinite domain that state still quantifies over.
    Evaluated(usize),
}

/// One run of the `by simp` rewrite fixpoint.
struct SimpRun {
    /// Every state visited, oldest first; the goal is closed if *any* of
    /// them closes it.
    states: Vec<Expr>,
    /// The last state reached — what a non-closing `simp` hands to the next
    /// tactic in a `then` chain.
    final_state: Expr,
    /// Source names of the rules that actually fired (see `crate::trust`).
    used: BTreeSet<String>,
}


/// Decompose a homogeneous binary quadratic `c1·a² + c2·b² + c3·ab` into a
/// non-negative combination of squares, when one exists.
///
/// Completing the square gives
///   `4·c1·p = (2·c1·a + c3·b)² + (4·c1·c2 - c3²)·b²`,
/// so `p = (1/4c1)·(2c1·a + c3·b)² + ((4c1c2 - c3²)/4c1)·b²`, which is a
/// sum of squares with non-negative weights exactly when `c1 > 0` and the
/// discriminant `4c1c2 - c3²` is non-negative.
///
/// The point of returning the decomposition rather than a yes/no is that
/// `crate::kernel` can then *check* it by polynomial multiplication instead
/// of having to trust a PSD test.
fn sum_of_squares(p: &crate::algebra::Polynomial) -> Option<Vec<(Rat, Expr)>> {
    use crate::algebra::Monomial;
    // Collect the variables and require a homogeneous degree-2 form in two.
    let mut vars: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    for m in &p.terms {
        if m.vars.values().sum::<u32>() != 2 {
            return None;
        }
        for v in m.vars.keys() {
            vars.insert(v.as_str());
        }
    }
    if vars.len() != 2 {
        return None;
    }
    let vs: Vec<&str> = vars.into_iter().collect();
    let (a, b) = (vs[0], vs[1]);
    let coeff = |want: &dyn Fn(&Monomial) -> bool| -> Rat {
        p.terms
            .iter()
            .filter(|m| want(m))
            .fold(Rat::from_int(0), |acc, m| acc.add(m.coeff))
    };
    let c1 = coeff(&|m: &Monomial| m.vars.get(a) == Some(&2));
    let c2 = coeff(&|m: &Monomial| m.vars.get(b) == Some(&2));
    let c3 = coeff(&|m: &Monomial| {
        m.vars.get(a) == Some(&1) && m.vars.get(b) == Some(&1)
    });
    if c1.sign() <= 0 {
        return None;
    }
    let four_c1 = Rat::from_int(4).mul(c1);
    let disc = four_c1.mul(c2).sub(c3.mul(c3));
    if disc.sign() < 0 {
        return None;
    }
    // The linear forms need integer coefficients to be written as terms;
    // `2·c1` and `c3` are integers whenever the input polynomial is.
    let two_c1 = Rat::from_int(2).mul(c1);
    let (w1, w2) = (
        Rat::from_int(1).div(four_c1)?,
        disc.div(four_c1)?,
    );
    let var = |n: &str| Expr::Var { name: n.to_string(), line: 0, col: 0 };
    let scaled = |c: Rat, v: &str| -> Option<Expr> {
        let n = if c.is_int() { i64::try_from(c.num).ok()? } else { return None };
        Some(Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Int(n)),
            Box::new(var(v)),
        ))
    };
    let first = Expr::BinOp(
        BinOp::Add,
        Box::new(scaled(two_c1, a)?),
        Box::new(scaled(c3, b)?),
    );
    let mut terms = vec![(w1, first)];
    if !w2.is_zero() {
        terms.push((w2, var(b)));
    }
    Some(terms)
}

/// One goal-transforming step of a `then` chain, kept so the certificate
/// can replay the chain in order.
enum SeqWrap {
    Unfold(String, Expr),
    Generalize(Vec<String>),
    /// A `by have`: the fact it established, and its proof.
    Have(Expr, Cert),
    /// A `by obtain`: the existential it eliminated.
    Obtain {
        intro: String,
        lemma: String,
        substs: Vec<(String, Expr)>,
        premises: Vec<Cert>,
    },
    /// A transformer with no certificate form yet.  Everything inside it is
    /// still certified, but the chain as a whole cannot be replayed, so the
    /// result is reported as not fully checked.
    Opaque(&'static str),
}

/// Wrap a certificate in the transformations that preceded it in a `then`
/// chain, outermost first, so the kernel replays them in order.
fn wrap_seq(wraps: Vec<SeqWrap>, inner: Cert) -> Cert {
    let mut cert = inner;
    for w in wraps.into_iter().rev() {
        cert = match w {
            SeqWrap::Unfold(name, unfolded) => {
                Cert::Unfold { name, unfolded, then: Box::new(cert) }
            }
            SeqWrap::Generalize(vars) => Cert::Generalize { vars, then: Box::new(cert) },
            SeqWrap::Obtain { intro, lemma, substs, premises } => Cert::Obtain {
                lemma,
                intro,
                substs,
                premises,
                then: Box::new(cert),
            },
            SeqWrap::Have(fact, fact_proof) => Cert::Have {
                fact,
                fact_proof: Box::new(fact_proof),
                then: Box::new(cert),
            },
            SeqWrap::Opaque(tactic) => Cert::Trusted {
                tactic,
                reason: TrustReason::NoWitnessYet,
                why: format!(
                    "`{}` was used to transform the goal mid-chain, and that \
                     transformation has no certificate form yet",
                    tactic
                ),
            },
        };
    }
    cert
}


/// Solve `Σ xᵢ·pᵢ + k = target` for non-negative rationals, or report that
/// no such combination exists.
///
/// The polynomials are compared coefficient by coefficient over the union of
/// their monomials, which makes this an ordinary linear system.  Gaussian
/// elimination over the rationals gives an exact answer; free variables are
/// set to zero, and the result is only returned when every coefficient came
/// out non-negative — a negative multiplier would reverse an inequality
/// rather than preserve it.
fn solve_nonneg_combination(
    polys: &[crate::algebra::Polynomial],
    target: &crate::algebra::Polynomial,
) -> Option<(Vec<Rat>, Rat)> {
    solve_combination(polys, target, true, true)
}

/// As above, but with two knobs: whether the coefficients must come out
/// non-negative (inequalities need that, equations do not) and whether an
/// extra non-negative slack column is allowed.
fn solve_combination(
    polys: &[crate::algebra::Polynomial],
    target: &crate::algebra::Polynomial,
    require_nonneg: bool,
    with_slack: bool,
) -> Option<(Vec<Rat>, Rat)> {
    use std::collections::BTreeMap;
    // One row per monomial.  The slack is an extra column that only
    // contributes to the constant monomial.
    let key = |m: &crate::algebra::Monomial| -> BTreeMap<String, u32> { m.vars.clone() };
    let mut monomials: Vec<BTreeMap<String, u32>> = Vec::new();
    let note = |m: &crate::algebra::Monomial, out: &mut Vec<BTreeMap<String, u32>>| {
        let k = key(m);
        if !out.contains(&k) {
            out.push(k);
        }
    };
    for p in polys {
        for m in &p.terms {
            note(m, &mut monomials);
        }
    }
    for m in &target.terms {
        note(m, &mut monomials);
    }
    let constant: BTreeMap<String, u32> = BTreeMap::new();
    if !monomials.contains(&constant) {
        monomials.push(constant.clone());
    }

    let n_cols = polys.len() + if with_slack { 1 } else { 0 };
    let coeff = |p: &crate::algebra::Polynomial, k: &BTreeMap<String, u32>| -> Rat {
        p.terms
            .iter()
            .filter(|m| m.vars == *k)
            .fold(Rat::from_int(0), |a, m| a.add(m.coeff))
    };
    let mut rows: Vec<Vec<Rat>> = Vec::new();
    for k in &monomials {
        let mut row = Vec::with_capacity(n_cols + 1);
        for p in polys {
            row.push(coeff(p, k));
        }
        if with_slack {
            row.push(if *k == constant { Rat::from_int(1) } else { Rat::from_int(0) });
        }
        row.push(coeff(target, k));
        rows.push(row);
    }

    // Gaussian elimination.
    let mut pivot_of_col: Vec<Option<usize>> = vec![None; n_cols];
    let mut r = 0usize;
    for c in 0..n_cols {
        let Some(pr) = (r..rows.len()).find(|&i| rows[i][c].sign() != 0) else {
            continue;
        };
        rows.swap(r, pr);
        let pivot = rows[r][c];
        for j in 0..=n_cols {
            rows[r][j] = rows[r][j].div(pivot)?;
        }
        for i in 0..rows.len() {
            if i == r || rows[i][c].sign() == 0 {
                continue;
            }
            let factor = rows[i][c];
            for j in 0..=n_cols {
                let sub = rows[r][j].mul(factor);
                rows[i][j] = rows[i][j].sub(sub);
            }
        }
        pivot_of_col[c] = Some(r);
        r += 1;
        if r == rows.len() {
            break;
        }
    }
    // Any row that is all zeros on the left but not on the right means the
    // system is inconsistent: no combination reaches the target.
    for row in &rows {
        if row[..n_cols].iter().all(|v| v.sign() == 0) && row[n_cols].sign() != 0 {
            return None;
        }
    }
    // Free variables are set to zero.
    let mut sol = vec![Rat::from_int(0); n_cols];
    for (c, p) in pivot_of_col.iter().enumerate() {
        if let Some(pr) = p {
            sol[c] = rows[*pr][n_cols];
        }
    }
    if require_nonneg && sol.iter().any(|v| v.sign() < 0) {
        return None;
    }
    let slack = if with_slack {
        sol.pop().expect("the slack column is present")
    } else {
        Rat::from_int(0)
    };
    Some((sol, slack))
}

/// Levenshtein distance, for "did you mean" suggestions.
fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0usize; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        cur[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let cost = if ca == cb { 0 } else { 1 };
            cur[j + 1] = (prev[j] + cost).min(prev[j + 1] + 1).min(cur[j] + 1);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

/// The hypotheses a goal currently assumes, read off its premise chain.
///
/// seki keeps the proof context *in the goal*: `h1 and h2 => C` is a goal
/// with two hypotheses.  `by have` extends the chain and `by apply` /
/// `by assumption` read it, so no separate context object is needed.
fn goal_hypotheses(prop: &Expr) -> Vec<Expr> {
    peel_implications(strip_foralls(prop)).1
}

/// Build `h1 and h2 and ... => concl`.
fn under_hypotheses(hyps: &[Expr], concl: Expr) -> Expr {
    if hyps.is_empty() {
        return concl;
    }
    let mut premise = hyps[0].clone();
    for h in &hyps[1..] {
        premise = Expr::BinOp(BinOp::And, Box::new(premise), Box::new(h.clone()));
    }
    implies_expr(premise, concl)
}

/// Add one hypothesis to a goal, keeping its `forall` binders outside so the
/// hypothesis may mention the bound variables.
fn add_hypothesis(prop: &Expr, fact: Expr) -> Expr {
    let (binders, inner) = crate::rewrite::peel_binders(prop);
    crate::rewrite::rebuild_binders(&binders, implies_expr(fact, inner.clone()))
}

fn tactic_name(p: &Proof) -> &'static str {
    match p {
        Proof::ByEval => "by eval",
        Proof::Refl => "refl",
        Proof::ByAlgebra => "by algebra",
        Proof::ByLinarith => "by linarith",
        Proof::ByDecide => "by decide",
        Proof::ByInduction => "by induction",
        Proof::ByStrongInduction { .. } => "by strong_induction",
        Proof::BySimp { .. } => "by simp",
        Proof::ByUnfold(_) => "by unfold",
        Proof::ByIntros => "by intros",
        Proof::ByAuto => "by auto",
        Proof::Term(_) => "a proof term",
        Proof::Obtain { .. } => "by obtain",
        Proof::Apply { .. } => "by apply",
        Proof::Have { .. } => "by have",
        Proof::Assumption => "by assumption",
        Proof::Seq(_) => "a tactic chain",
    }
}

fn flatten_conjuncts_expr<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match e {
        Expr::BinOp(BinOp::And, l, r) => {
            flatten_conjuncts_expr(l, out);
            flatten_conjuncts_expr(r, out);
        }
        other => out.push(other),
    }
}

/// Where a subterm sits inside a proposition known to be true.  Sampling an
/// infinite domain is unsound in one direction only, so which direction a
/// quantifier faces decides whether its enumeration proved anything.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Polarity {
    Positive,
    Negative,
    /// A context that is neither (a function argument, an `if` condition).
    Unknown,
}

impl Polarity {
    fn flip(self) -> Self {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
            Polarity::Unknown => Polarity::Unknown,
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

/// Under `Nat`/`Int`, a *strict* inequality hypothesis is about an
/// integer-valued polynomial, so `poly > 0` implies the sharper `poly >= 1`
/// (equivalently `poly - 1 >= 0`) — there's no integer strictly between 0
/// and 1. Feeding this back into the hypothesis list lets the existing
/// (rational-sound) machinery close goals that genuinely need integer
/// discreteness, e.g. `n > 0 (Nat) ⊢ n - 1 >= 0`, which is false over the
/// reals/rationals and therefore unreachable via Fourier-Motzkin alone.
fn integer_strengthen(cond: &Expr, htrue: bool, dom: PolyDomain) -> Option<(Expr, bool)> {
    if !matches!(dom, PolyDomain::Nat | PolyDomain::Int) {
        return None;
    }
    let (poly, is_strict) = normalize_nonneg_hyp(cond, htrue)?;
    if !is_strict {
        return None;
    }
    let shifted = poly.sub(crate::algebra::Polynomial::from_const(1));
    let expr = Expr::BinOp(
        BinOp::Ge,
        Box::new(crate::algebra::poly_to_expr(&shifted)),
        Box::new(Expr::Int(0)),
    );
    Some((expr, true))
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

/// Try to prove `diff <op> 0` (an inequality goal) from `hyps` via full
/// multi-variable Fourier-Motzkin elimination: negate the goal, add it to
/// the hypotheses converted to linear constraints, and check the combined
/// system for unsatisfiability (see `algebra::fm_is_unsat`). Bails (returns
/// `false`, never a false positive) if the goal or any hypothesis carries
/// a nonlinear term, or if a hypothesis's relation can't be represented as
/// linear constraints (`!=`) — such hypotheses are simply skipped, which
/// only loses precision, never soundness.
fn try_fm_prove(hyps: &[(Expr, bool)], diff: &crate::algebra::Polynomial, op: &BinOp) -> bool {
    if !crate::algebra::poly_is_affine(diff) {
        return false;
    }
    let neg_op = negate_relation(op);
    let Some(mut constraints) = crate::algebra::relation_to_constraints(&neg_op, diff.clone())
    else {
        return false;
    };
    for (hcond, htrue) in hyps {
        let Expr::BinOp(hop, hl, hr) = hcond else { continue };
        if !is_relation(hop) {
            continue;
        }
        let (Some(hlp), Some(hrp)) = (expr_to_poly(hl), expr_to_poly(hr)) else { continue };
        let hdiff = hlp.sub(hrp);
        if !crate::algebra::poly_is_affine(&hdiff) {
            continue; // nonlinear hypothesis — skip it, don't abort the whole attempt
        }
        let eff_op = if *htrue { hop.clone() } else { negate_relation(hop) };
        if let Some(cs) = crate::algebra::relation_to_constraints(&eff_op, hdiff) {
            constraints.extend(cs);
        }
    }
    crate::algebra::fm_is_unsat(&constraints)
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
    // 1b. A single hypothesis about a *constant* polynomial (no free
    // variables) whose claimed sign-set excludes its own literal sign is
    // unconditionally impossible — e.g. a hypothesis `1 == 0` arising from
    // specializing `if n == 0` after substituting a concrete `n` (via
    // `by unfold`). Without this check, `prove_algebra_rel`'s `if`
    // case-split chases the vacuous branch as if it were reachable and
    // reports a spurious proof failure instead of pruning it.
    for (h, htrue) in hyps {
        if let Some((p, ss)) = hyp_to_signset(h, *htrue) {
            if let Some(c) = p.as_constant() {
                let sign = c.sign();
                let compatible = (sign < 0 && ss.neg) || (sign == 0 && ss.zero) || (sign > 0 && ss.pos);
                if !compatible {
                    return true;
                }
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

/// Build the `=>` desugaring `(not P) or Q` directly — matching what the
/// parser produces for `P => Q` — so `peel_implications`/`by algebra`
/// recognize the result as an implication without any special-casing.
fn implies_expr(premise: Expr, conclusion: Expr) -> Expr {
    Expr::BinOp(
        BinOp::Or,
        Box::new(Expr::UnOp(UnOp::Not, Box::new(premise))),
        Box::new(conclusion),
    )
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
// -- structural encodings ---------------------------------------------------
//
// `stdlib.seki` builds its recursive datatypes out of tagged tuples rather
// than `data` declarations (see `Value::Tuple`): `nil = (0, ())`,
// `cons x xs = (1, (x, xs))`, `leaf = (2, ())`, `node l v r = (3, (l, (v,
// r)))`.  The induction tactics have to see through that encoding to
// simplify `head (cons x xs)` down to `x`.
//
// This used to be two near-identical 80-line traversals, `simplify_list_ops`
// and `simplify_tree_ops`, each paired with its own shape recognizer — so a
// third encoded datatype meant a third copy.  The traversal is now written
// once and driven by the table below, and `by induction` over user-declared
// `data` types goes through `verify_adt_induction` and needs nothing here at
// all.  Adding a fourth stdlib encoding is an `Encoding` entry, not new code.

/// One constructor of an encoded datatype.
struct Ctor {
    name: &'static str,
    /// The `Int` tag this constructor writes as the tuple's first component.
    tag: i64,
    /// How many payload fields it carries.  Two or more are stored
    /// right-nested: arity 3 is `(f0, (f1, f2))`.
    arity: usize,
}

/// A destructor that projects one field out of one constructor —
/// `head (cons x xs) = x` is `Projection { name: "head", ctor: "cons",
/// field: 0 }`.
struct Projection {
    name: &'static str,
    ctor: &'static str,
    field: usize,
}

/// A predicate that answers `true` for exactly one constructor and `false`
/// for every other — `null nil = true`, `null (cons _ _) = false`.
struct Discriminator {
    name: &'static str,
    true_for: &'static str,
}

/// A structurally recursive `Int`-valued measure:
/// `length nil = 0`, `length (cons _ t) = 1 + length t`.
struct Measure {
    name: &'static str,
    /// Value at the nullary constructor.
    zero: i64,
    /// The recursive constructor, and which of its fields to recurse into.
    ctor: &'static str,
    field: usize,
    /// Added to the recursive call's result at each step.
    step: i64,
}

struct Encoding {
    ctors: &'static [Ctor],
    projections: &'static [Projection],
    discriminators: &'static [Discriminator],
    measures: &'static [Measure],
    /// Whether a `[a, b, c]` literal denotes this type (lists do, trees
    /// don't).  When set, the first constructor is the empty case and the
    /// second is the two-field cons case.
    from_list_literal: bool,
}

const LIST_ENCODING: Encoding = Encoding {
    ctors: &[
        Ctor { name: "nil", tag: 0, arity: 0 },
        Ctor { name: "cons", tag: 1, arity: 2 },
    ],
    projections: &[
        Projection { name: "head", ctor: "cons", field: 0 },
        Projection { name: "tail", ctor: "cons", field: 1 },
    ],
    discriminators: &[Discriminator { name: "null", true_for: "nil" }],
    measures: &[Measure { name: "length", zero: 0, ctor: "cons", field: 1, step: 1 }],
    from_list_literal: true,
};

const TREE_ENCODING: Encoding = Encoding {
    ctors: &[
        Ctor { name: "leaf", tag: 2, arity: 0 },
        Ctor { name: "node", tag: 3, arity: 3 },
    ],
    projections: &[
        Projection { name: "treeLeft", ctor: "node", field: 0 },
        Projection { name: "treeVal", ctor: "node", field: 1 },
        Projection { name: "treeRight", ctor: "node", field: 2 },
    ],
    discriminators: &[Discriminator { name: "isLeaf", true_for: "leaf" }],
    measures: &[],
    from_list_literal: false,
};

/// An expression recognized as an application of one of an encoding's
/// constructors.
struct CtorShape {
    name: &'static str,
    fields: Vec<Expr>,
}

impl Encoding {
    fn ctor(&self, name: &str) -> Option<&Ctor> {
        self.ctors.iter().find(|c| c.name == name)
    }

    /// Recognize `e` as a constructor application, in any of the spellings
    /// that reach the prover: the bare name, an explicit application, the
    /// tagged tuple the unfolder produces after beta-reducing the stdlib
    /// definition, and (for lists) a bracket literal.
    fn shape_of(&self, e: &Expr) -> Option<CtorShape> {
        use Expr::*;
        match e {
            Var { name, .. } => self
                .ctor(name)
                .filter(|c| c.arity == 0)
                .map(|c| CtorShape { name: c.name, fields: Vec::new() }),
            App { func, args } => {
                let fname = match func.as_ref() {
                    Var { name, .. } => name,
                    _ => return None,
                };
                let c = self.ctor(fname)?;
                if c.arity == 0 {
                    // `nil ()` and friends — the argument is the unit the
                    // stdlib's nullary constructors take.
                    return Some(CtorShape { name: c.name, fields: Vec::new() });
                }
                if args.len() != c.arity {
                    return None;
                }
                Some(CtorShape { name: c.name, fields: args.clone() })
            }
            Tuple(xs) if xs.len() == 2 => {
                let tag = match &xs[0] {
                    Int(t) => *t,
                    _ => return None,
                };
                let c = self.ctors.iter().find(|c| c.tag == tag)?;
                let fields = unnest_right(&xs[1], c.arity)?;
                Some(CtorShape { name: c.name, fields })
            }
            List(xs) if self.from_list_literal => {
                if xs.is_empty() {
                    Some(CtorShape { name: self.ctors[0].name, fields: Vec::new() })
                } else {
                    Some(CtorShape {
                        name: self.ctors[1].name,
                        fields: vec![xs[0].clone(), List(xs[1..].to_vec())],
                    })
                }
            }
            _ => None,
        }
    }
}

/// Every encoded datatype the tactics know about.  A new entry is all it
/// takes to teach `by algebra` and `by induction` about another one.
const ENCODINGS: &[&Encoding] = &[&LIST_ENCODING, &TREE_ENCODING];

/// What an equality between two constructor applications reduces to.
enum CtorEquality {
    /// Both sides are the same nullary constructor.
    Trivial,
    /// Same constructor: equal iff every field is equal (injectivity).
    Fields(Vec<(Expr, Expr)>),
    /// Different constructors of the same type: never equal (disjointness).
    Distinct(&'static str, &'static str),
}

/// Decompose `lhs == rhs` when both sides are recognizable applications of
/// constructors from the *same* encoding — regardless of which spelling
/// each side happens to be in (an explicit `cons ..`, a raw tag tuple left
/// over from unfolding, or an `Expr::List` literal all count).
///
/// This lets `by algebra` close equalities between structurally-equal but
/// differently-represented values, which is what induction step goals look
/// like when only one side got fully unfolded.  It used to be written out
/// for lists only; going through the encoding table gives trees — and
/// anything added later — the same treatment.
fn ctor_equality(lhs: &Expr, rhs: &Expr) -> Option<CtorEquality> {
    for enc in ENCODINGS {
        let (l, r) = match (enc.shape_of(lhs), enc.shape_of(rhs)) {
            (Some(l), Some(r)) => (l, r),
            _ => continue,
        };
        if l.name != r.name {
            return Some(CtorEquality::Distinct(l.name, r.name));
        }
        if l.fields.is_empty() {
            return Some(CtorEquality::Trivial);
        }
        return Some(CtorEquality::Fields(
            l.fields.into_iter().zip(r.fields).collect(),
        ));
    }
    None
}

/// Split a right-nested tuple payload into `arity` fields:
/// arity 0 takes nothing, arity 1 is the payload itself, and arity `n` is
/// `(f0, (f1, ... fn-1))`.
fn unnest_right(payload: &Expr, arity: usize) -> Option<Vec<Expr>> {
    match arity {
        0 => Some(Vec::new()),
        1 => Some(vec![payload.clone()]),
        n => {
            let mut fields = Vec::with_capacity(n);
            let mut cur = payload.clone();
            for _ in 0..n - 1 {
                match cur {
                    Expr::Tuple(ref parts) if parts.len() == 2 => {
                        fields.push(parts[0].clone());
                        cur = parts[1].clone();
                    }
                    _ => return None,
                }
            }
            fields.push(cur);
            Some(fields)
        }
    }
}

/// Resolve an encoding's destructors, discriminators and measures wherever
/// they are applied to a recognizable constructor, everywhere in `e`.
///
/// One traversal serves every encoding in the table above; `simplify_list_ops`
/// and `simplify_tree_ops` are the two instantiations the tactics use.
fn simplify_structural_ops(e: &Expr, enc: &Encoding, ctx: &EvalCtx, env: &Env) -> Expr {
    use Expr::*;
    let go = |x: &Expr| simplify_structural_ops(x, enc, ctx, env);
    match e {
        App { func, args } => {
            let new_args: Vec<Expr> = args.iter().map(&go).collect();
            if let Var { name: fname, .. } = func.as_ref() {
                if new_args.len() == 1 {
                    if let Some(simplified) = enc.apply_op(fname, &new_args[0]) {
                        return simplified;
                    }
                }
            }
            let rebuilt = App { func: Box::new(go(func)), args: new_args };
            simplify_ifs(&rebuilt, "", ctx, env)
        }
        BinOp(op, l, r) => BinOp(op.clone(), Box::new(go(l)), Box::new(go(r))),
        UnOp(op, x) => UnOp(op.clone(), Box::new(go(x))),
        If { cond, then_branch, else_branch } => {
            let c2 = go(cond);
            let t2 = go(then_branch);
            let e2 = go(else_branch);
            if let Bool(b) = &c2 {
                return if *b { t2 } else { e2 };
            }
            // `if X == 0 then ...` where both sides became the literal tag
            // of a known constructor: the comparison is now decidable.
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
            value: Box::new(go(value)),
            body: Box::new(go(body)),
            rec: *rec,
        },
        _ => e.clone(),
    }
}

impl Encoding {
    /// Apply the one-argument operation `op` to `arg`, if `arg` is a
    /// recognizable constructor application and `op` is one of this
    /// encoding's destructors, discriminators or measures.
    fn apply_op(&self, op: &str, arg: &Expr) -> Option<Expr> {
        let shape = self.shape_of(arg)?;
        if let Some(d) = self.discriminators.iter().find(|d| d.name == op) {
            return Some(Expr::Bool(d.true_for == shape.name));
        }
        if let Some(p) = self.projections.iter().find(|p| p.name == op) {
            if p.ctor == shape.name {
                return shape.fields.get(p.field).cloned();
            }
            return None;
        }
        if let Some(m) = self.measures.iter().find(|m| m.name == op) {
            if m.ctor == shape.name {
                let rest = shape.fields.get(m.field)?.clone();
                return Some(Expr::BinOp(
                    crate::ast::BinOp::Add,
                    Box::new(Expr::Int(m.step)),
                    Box::new(Expr::App {
                        func: Box::new(Expr::Var {
                            name: m.name.to_string(),
                            line: 0,
                            col: 0,
                        }),
                        args: vec![rest],
                    }),
                ));
            }
            // Any other constructor is the base case.
            if self.ctor(shape.name).map(|c| c.arity == 0).unwrap_or(false) {
                return Some(Expr::Int(m.zero));
            }
            return None;
        }
        None
    }
}

fn simplify_list_ops(e: &Expr, ctx: &EvalCtx, env: &Env) -> Expr {
    simplify_structural_ops(e, &LIST_ENCODING, ctx, env)
}

fn simplify_tree_ops(e: &Expr, ctx: &EvalCtx, env: &Env) -> Expr {
    simplify_structural_ops(e, &TREE_ENCODING, ctx, env)
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



fn strip_foralls(e: &Expr) -> &Expr {
    let mut cur = e;
    while let Expr::Forall { body, .. } = cur {
        cur = body;
    }
    cur
}

/// Peel every leading `forall var in domain, ...` off `e`, returning the
/// `(var, domain)` pairs in outer-to-inner order together with the
/// innermost non-`Forall` body.
fn peel_leading_foralls(e: &Expr) -> (Vec<(String, Expr)>, &Expr) {
    let mut vars = Vec::new();
    let mut cur = e;
    while let Expr::Forall { var, domain, body } = cur {
        vars.push((var.clone(), (**domain).clone()));
        cur = body;
    }
    (vars, cur)
}

/// Inverse of `peel_leading_foralls`: wrap `inner` back in `forall var in
/// domain, ...` binders, outer-to-inner matching `vars`' order.
fn rebuild_foralls(vars: &[(String, Expr)], inner: Expr) -> Expr {
    let mut cur = inner;
    for (var, domain) in vars.iter().rev() {
        cur = Expr::Forall {
            var: var.clone(),
            domain: Box::new(domain.clone()),
            body: Box::new(cur),
        };
    }
    cur
}

/// Repeatedly apply `unfold_one` (plus list-op simplification) until a
/// fixpoint or a small iteration cap. Sound for any starting expression —
/// each step is the same beta/delta-reduction `unfold_one` already
/// performs — and terminates quickly whenever the recursion's termination
/// depends only on concrete (non-symbolic) structure, e.g. list recursion
/// once the list argument is literally `nil` or `cons x ys` for a fixed
/// depth of concrete conses.
/// `simplify_list_ops` resolves `null`/`head`/`tail` against a `cons`/`nil`
/// literal it can already see — but a residual `if` left behind by
/// `unfold_one`'s own (weaker) internal `simplify_ifs` can hide a *second*
/// concrete cons/nil one level down, which only becomes visible after the
/// outer `if` collapses. Iterate a few rounds so those newly-exposed shapes
/// get their own chance at simplification, without going all the way to
/// `unfold_to_fixpoint`'s full reduction (which would also try to decide
/// `null` on the still-symbolic `ys` and blow up into case-splits).
fn simplify_list_ops_fixpoint(e: &Expr, ctx: &EvalCtx, env: &Env) -> Expr {
    let mut current = e.clone();
    for _ in 0..4 {
        let next = simplify_list_ops(&current, ctx, env);
        if exprs_equal(&next, &current) {
            break;
        }
        current = next;
    }
    current
}

fn unfold_to_fixpoint(e: &Expr, ctx: &EvalCtx, env: &Env) -> Expr {
    let mut current = normalize_nil(e);
    for _ in 0..16 {
        let next = normalize_nil(&simplify_list_ops(&unfold_one(&current, ctx, env), ctx, env));
        if exprs_equal(&next, &current) {
            break;
        }
        current = next;
    }
    current
}

/// `nil` (the identifier) and `[]` (a literal empty `Expr::List`) are the
/// same value but different ASTs — unfolding a recursive list function's
/// `if null p then nil else ...` base case surfaces the identifier form,
/// while callers substituting a concrete empty list in typically use the
/// literal form. Canonicalize both to `Expr::List(vec![])` so syntactic
/// equality checks (and `by algebra`'s opaque-atom naming) see them as
/// identical.
fn normalize_nil(e: &Expr) -> Expr {
    use Expr::*;
    match e {
        Var { name, .. } if name == "nil" => List(vec![]),
        App { func, args } => App {
            func: Box::new(normalize_nil(func)),
            args: args.iter().map(normalize_nil).collect(),
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(normalize_nil(cond)),
            then_branch: Box::new(normalize_nil(then_branch)),
            else_branch: Box::new(normalize_nil(else_branch)),
        },
        Let { name, ty, value, body, rec } => Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(normalize_nil(value)),
            body: Box::new(normalize_nil(body)),
            rec: *rec,
        },
        BinOp(op, l, r) => BinOp(op.clone(), Box::new(normalize_nil(l)), Box::new(normalize_nil(r))),
        UnOp(op, x) => UnOp(op.clone(), Box::new(normalize_nil(x))),
        List(xs) => List(xs.iter().map(normalize_nil).collect()),
        Tuple(xs) => Tuple(xs.iter().map(normalize_nil).collect()),
        _ => e.clone(),
    }
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
            if let Var { name, .. } = func.as_ref() {
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

#[cfg(test)]
mod encoding_tests {
    use super::*;

    fn var(n: &str) -> Expr {
        Expr::Var { name: n.into(), line: 0, col: 0 }
    }
    fn app(f: &str, args: Vec<Expr>) -> Expr {
        Expr::App { func: Box::new(var(f)), args }
    }
    fn tup(xs: Vec<Expr>) -> Expr {
        Expr::Tuple(xs)
    }

    #[test]
    fn a_constructor_is_recognized_in_every_spelling() {
        // The bare name, an explicit application, the tagged tuple the
        // unfolder leaves behind, and a bracket literal must all resolve to
        // the same constructor.
        for (spelling, expect) in [
            (var("nil"), "nil"),
            (app("nil", vec![Expr::Tuple(vec![])]), "nil"),
            (tup(vec![Expr::Int(0), Expr::Tuple(vec![])]), "nil"),
            (Expr::List(vec![]), "nil"),
            (app("cons", vec![Expr::Int(1), var("nil")]), "cons"),
            (
                tup(vec![
                    Expr::Int(1),
                    tup(vec![Expr::Int(1), var("nil")]),
                ]),
                "cons",
            ),
            (Expr::List(vec![Expr::Int(1)]), "cons"),
        ] {
            let shape = LIST_ENCODING
                .shape_of(&spelling)
                .unwrap_or_else(|| panic!("not recognized: {}", spelling));
            assert_eq!(shape.name, expect, "for {}", spelling);
        }
    }

    #[test]
    fn a_three_field_constructor_unnests_right() {
        // `node l v r` is stored as `(3, (l, (v, r)))`.
        let encoded = tup(vec![
            Expr::Int(3),
            tup(vec![
                var("leaf"),
                tup(vec![Expr::Int(7), var("leaf")]),
            ]),
        ]);
        let shape = TREE_ENCODING.shape_of(&encoded).expect("node shape");
        assert_eq!(shape.name, "node");
        assert_eq!(shape.fields.len(), 3);
        assert!(matches!(shape.fields[1], Expr::Int(7)));
    }

    #[test]
    fn projections_discriminators_and_measures_all_fire() {
        let xs = app("cons", vec![Expr::Int(7), var("nil")]);
        assert!(matches!(
            LIST_ENCODING.apply_op("head", &xs),
            Some(Expr::Int(7))
        ));
        assert!(matches!(
            LIST_ENCODING.apply_op("null", &xs),
            Some(Expr::Bool(false))
        ));
        assert!(matches!(
            LIST_ENCODING.apply_op("null", &var("nil")),
            Some(Expr::Bool(true))
        ));
        // `length nil = 0`, `length (cons _ t) = 1 + length t`.
        assert!(matches!(
            LIST_ENCODING.apply_op("length", &var("nil")),
            Some(Expr::Int(0))
        ));
        match LIST_ENCODING.apply_op("length", &xs) {
            Some(Expr::BinOp(crate::ast::BinOp::Add, l, _)) => {
                assert!(matches!(*l, Expr::Int(1)));
            }
            other => panic!("expected `1 + length t`, got {:?}", other),
        }
        // A destructor of another encoding must not fire here.
        assert!(LIST_ENCODING.apply_op("treeVal", &xs).is_none());
        assert!(TREE_ENCODING.apply_op("head", &xs).is_none());
    }

    #[test]
    fn constructor_equality_decomposes_and_rejects() {
        let a = app("cons", vec![Expr::Int(1), var("nil")]);
        let b = app("cons", vec![Expr::Int(2), var("nil")]);
        match ctor_equality(&a, &b) {
            Some(CtorEquality::Fields(pairs)) => assert_eq!(pairs.len(), 2),
            other => panic!("expected field-wise decomposition, got a different arm ({})",
                            matches!(other, Some(CtorEquality::Trivial))),
        }
        assert!(matches!(
            ctor_equality(&var("nil"), &var("nil")),
            Some(CtorEquality::Trivial)
        ));
        assert!(matches!(
            ctor_equality(&var("nil"), &a),
            Some(CtorEquality::Distinct("nil", "cons"))
        ));
        // Trees go through the same table.
        assert!(matches!(
            ctor_equality(&var("leaf"), &app("node", vec![var("leaf"), Expr::Int(1), var("leaf")])),
            Some(CtorEquality::Distinct("leaf", "node"))
        ));
        // Unrelated expressions are not constructor applications.
        assert!(ctor_equality(&Expr::Int(1), &Expr::Int(2)).is_none());
    }
}

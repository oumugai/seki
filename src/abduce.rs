//! Working backwards: what would have to be assumed for a goal to hold.
//!
//! A failed proof usually means a *missing assumption*, not a wrong claim.
//! "cannot prove `100 - 200r > 0` over Real" is true and unhelpful; what the
//! author wants to know is that it holds exactly when `r < 1/2`.  For a model
//! whose parameters are estimates, that answer is often more valuable than
//! the proof would have been — it is the sensitivity of the conclusion.
//!
//! This is a *search*, so nothing here is trusted: a suggestion is only
//! offered after it has been checked to actually work, by adding it as a
//! hypothesis and re-running the prover.  A suggestion that does not close
//! the goal is worse than none, so none is given.
//!
//! What it currently finds: the bound on a single variable that makes a
//! linear goal hold.  Missing premises of an applied lemma are reported by
//! `by apply` itself, which knows them exactly.

use crate::algebra::{expr_to_poly, Polynomial, Rat};
use crate::ast::{BinOp, Expr};
use crate::eval::EvalCtx;
use crate::prover::Prover;
use crate::value::Env;

/// An assumption that would make the goal provable, together with the goal
/// it was derived from.
#[derive(Debug, Clone)]
pub struct Suggestion {
    /// The assumption to add.
    pub assumption: Expr,
    /// The variable it constrains, when it constrains one.
    pub variable: Option<String>,
}

/// Assumptions that would let `prop` be proved, each verified to work.
///
/// Returns an empty vector when nothing was found — which is the common
/// case for goals outside the linear fragment, and is reported as silence
/// rather than as a guess.
pub fn missing_assumptions(prover: &Prover, prop: &Expr, env: &Env) -> Vec<Suggestion> {
    let mut out = Vec::new();
    let Some((diff, strict)) = goal_difference(prop) else {
        return out;
    };
    let (conclusion, _) =
        crate::rewrite::peel_premises(crate::rewrite::peel_binders(prop).1);
    for var in single_variable_bounds(&diff, strict) {
        // A "suggestion" that restates the goal tells the author nothing:
        // `n >= 5` holds given `n >= 5`.  Say nothing instead.
        if crate::ast::alpha_equiv(&var.assumption, &conclusion) {
            continue;
        }
        // And only offer what actually works.
        let candidate = with_assumption(prop, var.assumption.clone());
        if prover.verify_algebra_raw(&candidate, env).is_ok() {
            out.push(var);
        }
    }
    out
}

/// Format suggestions as a hint to append to a failure message.
pub fn hint(suggestions: &[Suggestion]) -> String {
    if suggestions.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = suggestions
        .iter()
        .map(|s| format!("`{}`", s.assumption))
        .collect();
    format!(
        "\n  it would hold given {} — add it as a hypothesis \
         (`... => <goal>`) or tighten an existing one",
        parts.join(" or ")
    )
}

/// The polynomial a goal asserts is non-negative, and whether strictly.
fn goal_difference(prop: &Expr) -> Option<(Polynomial, bool)> {
    let (concl, _) = crate::rewrite::peel_premises(crate::rewrite::peel_binders(prop).1);
    let (op, l, r) = match &concl {
        Expr::BinOp(op, l, r) => (op.clone(), (**l).clone(), (**r).clone()),
        _ => return None,
    };
    let (lhs, rhs, strict) = match op {
        BinOp::Ge => (l, r, false),
        BinOp::Gt => (l, r, true),
        BinOp::Le => (r, l, false),
        BinOp::Lt => (r, l, true),
        _ => return None,
    };
    Some((expr_to_poly(&lhs)?.sub(expr_to_poly(&rhs)?), strict))
}

/// For `c·v + k ≥ 0` in a single variable, the bound on `v`.
fn single_variable_bounds(diff: &Polynomial, strict: bool) -> Vec<Suggestion> {
    let mut vars: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    for m in &diff.terms {
        for v in m.vars.keys() {
            vars.insert(v.as_str());
        }
    }
    // One variable, appearing linearly: anything else needs a different
    // shape of answer than a bound.
    if vars.len() != 1 {
        return Vec::new();
    }
    let var = vars.into_iter().next().expect("one variable");
    if var.starts_with("__atom_") {
        // An opaque subterm is not something the author can bound.
        return Vec::new();
    }
    let mut coeff = Rat::from_int(0);
    let mut constant = Rat::from_int(0);
    for m in &diff.terms {
        match m.vars.get(var) {
            Some(1) if m.vars.len() == 1 => coeff = coeff.add(m.coeff),
            Some(_) => return Vec::new(), // non-linear
            None if m.vars.is_empty() => constant = constant.add(m.coeff),
            None => return Vec::new(),
        }
    }
    if coeff.sign() == 0 {
        return Vec::new();
    }
    // c·v + k ≥ 0  ⟺  v ≥ -k/c  (c > 0)  or  v ≤ -k/c  (c < 0)
    let Some(bound) = constant.neg().div(coeff) else {
        return Vec::new();
    };
    let op = match (coeff.sign() > 0, strict) {
        (true, false) => BinOp::Ge,
        (true, true) => BinOp::Gt,
        (false, false) => BinOp::Le,
        (false, true) => BinOp::Lt,
    };
    vec![Suggestion {
        assumption: Expr::BinOp(
            op,
            Box::new(Expr::Var { name: var.to_string(), line: 0, col: 0 }),
            Box::new(rat_to_expr(bound)),
        ),
        variable: Some(var.to_string()),
    }]
}

fn rat_to_expr(r: Rat) -> Expr {
    if r.den == 1 {
        return Expr::Int(r.num as i64);
    }
    Expr::BinOp(
        BinOp::Div,
        Box::new(Expr::Int(r.num as i64)),
        Box::new(Expr::Int(r.den as i64)),
    )
}

/// `prop` with one more hypothesis, keeping its binders outside.
fn with_assumption(prop: &Expr, extra: Expr) -> Expr {
    let (binders, inner) = crate::rewrite::peel_binders(prop);
    let implied = Expr::BinOp(
        BinOp::Or,
        Box::new(Expr::UnOp(crate::ast::UnOp::Not, Box::new(extra))),
        Box::new(inner.clone()),
    );
    crate::rewrite::rebuild_binders(&binders, implied)
}

/// Convenience for callers that only have globals.
pub fn suggestions_for(prop: &Expr, globals: &crate::value::Globals) -> Vec<Suggestion> {
    let ctx = EvalCtx::new(globals);
    let prover = Prover::new(&ctx);
    missing_assumptions(&prover, prop, &Env::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::make_prelude;

    fn prop_of(src: &str) -> Expr {
        let decls = crate::parse_program(src).expect("parse");
        match decls.into_iter().next().expect("one decl").decl {
            crate::ast::Decl::Expr(e) => e,
            other => panic!("expected an expression, got {:?}", other),
        }
    }

    fn suggest(src: &str) -> Vec<String> {
        let g = make_prelude();
        suggestions_for(&prop_of(src), &g)
            .into_iter()
            .map(|s| format!("{}", s.assumption))
            .collect()
    }

    #[test]
    fn a_linear_goal_yields_the_bound_that_makes_it_hold() {
        assert_eq!(
            suggest("forall r in Real, (100.0 - 200.0 * r) > 0.0"),
            vec!["(r < (1 / 2))"]
        );
    }

    #[test]
    fn a_hypothesis_that_is_not_tight_enough_still_gets_the_real_bound() {
        assert_eq!(
            suggest("forall r in Real, r <= 0.6 => (100.0 - 200.0 * r) > 0.0"),
            vec!["(r < (1 / 2))"]
        );
    }

    #[test]
    fn restating_the_goal_is_not_a_suggestion() {
        // `n >= 5` holds given `n >= 5` — true, and useless.
        assert!(suggest("forall n in Nat, n >= 5").is_empty());
    }

    #[test]
    fn nothing_is_offered_outside_the_linear_fragment() {
        assert!(suggest("forall x in Real, forall y in Real, x * y >= 0.0").is_empty());
        assert!(suggest("forall x in Real, x * x * x >= 0.0").is_empty());
    }

    #[test]
    fn a_goal_that_already_holds_needs_nothing() {
        // `x * x >= 0` is provable outright, so there is no missing
        // assumption to find.
        let g = make_prelude();
        let prop = prop_of("forall x in Real, x * x >= 0.0");
        let ctx = EvalCtx::new(&g);
        let prover = Prover::new(&ctx);
        assert!(prover.verify_algebra_raw(&prop, &Env::new()).is_ok());
    }
}

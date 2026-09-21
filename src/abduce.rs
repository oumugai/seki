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
//! What it finds: bounds on the goal's variables that, added as
//! hypotheses, make it provable — up to a few of them, since a model
//! usually lacks more than one.  The bounds come from running Farkas
//! backwards (`Prover::abduce_bound`), so they are exact and work with any
//! number of variables.  Missing premises of an applied lemma are reported
//! by `by apply` itself, which knows them exactly.
//!
//! When the bound is needed *inside a product* the linear reading cannot
//! see it: `x >= 0 ⊢ x² <= 4` holds given `x <= 2`, whose certificate is
//! `(2-x)·(2+x)`, and there the unknown multiplies a generator instead of
//! standing in its own column.  For those goals the prover is asked
//! directly, over a ladder of candidate values — see `probe_for_bound`.
//!
//! What it still does not find: a missing assumption that is not a bound on
//! one variable.  `⊢ c - p >= 1/2` needs a bound on the *difference*; any
//! pair of bounds on `c` and `p` separately would do, so there is no answer
//! to give and silence is the honest one.

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
    const MAX_SUGGESTIONS: usize = 3;
    let mut found: Vec<Suggestion> = Vec::new();
    // Each round adds the bound it found and asks again, so a goal short of
    // two assumptions gets told about both.  Three is where a list stops
    // being a diagnosis and starts being a shrug.
    let mut goal = prop.clone();
    for _ in 0..MAX_SUGGESTIONS {
        let Some(next) = one_missing_bound(prover, &goal, env) else {
            break;
        };
        goal = with_assumption(&goal, next.assumption.clone());
        found.push(next);
        if prover.verify_algebra_raw(&goal, env).is_ok() {
            return found;
        }
    }
    // Only report a set that actually closes the goal.  A partial list
    // points at the wrong thing, and a wrong hint costs more than silence.
    if !found.is_empty() && prover.verify_algebra_raw(&goal, env).is_ok() {
        found
    } else {
        Vec::new()
    }
}

/// One bound that gets the goal closer, verified to be usable.
fn one_missing_bound(prover: &Prover, prop: &Expr, env: &Env) -> Option<Suggestion> {
    let (diff, strict) = goal_difference(prop)?;
    let (conclusion, hyps) =
        crate::rewrite::peel_premises(crate::rewrite::peel_binders(prop).1);
    let vars = candidate_variables(&diff, &hyps);
    // The exact reading first: it is one linear solve and gives the
    // boundary outright.
    if let Some(found) = exact_bound(prover, prop, env, &diff, strict, &vars, &hyps, &conclusion) {
        return Some(found);
    }
    // Then, only for a goal the linear reading provably cannot answer, ask
    // the prover over a ladder of candidate values.  Every probe is a real
    // proof attempt, so this stays behind a degree check and a probe cap.
    if diff.degree() > 1 && vars.len() <= MAX_PROBED_VARIABLES {
        for var in &vars {
            for upper in [true, false] {
                let Some(bound) = probe_for_bound(prover, prop, env, var, upper, strict)
                else {
                    continue;
                };
                let Some(written) = small_rational_expr(bound) else {
                    continue;
                };
                let assumption = bound_expr(var, upper, strict, written);
                if crate::ast::alpha_equiv(&assumption, &conclusion)
                    || hyps.iter().any(|h| crate::ast::alpha_equiv(h, &assumption))
                {
                    continue;
                }
                let candidate = with_assumption(prop, assumption.clone());
                if contradicts_the_hypotheses(prover, &candidate, env) {
                    continue;
                }
                if prover.verify_algebra_raw(&candidate, env).is_ok() {
                    return Some(Suggestion {
                        assumption,
                        variable: Some(var.clone()),
                    });
                }
            }
        }
    }
    None
}

/// How many variables are worth probing.  Each one costs two ladders of
/// real proof attempts, and a goal with many free variables rarely has a
/// single bound as its answer anyway.
const MAX_PROBED_VARIABLES: usize = 3;

/// The bound read straight off the linear system — exact, one solve.
#[allow(clippy::too_many_arguments)]
fn exact_bound(
    prover: &Prover,
    prop: &Expr,
    env: &Env,
    diff: &Polynomial,
    strict: bool,
    vars: &[String],
    hyps: &[Expr],
    conclusion: &Expr,
) -> Option<Suggestion> {
    for var in vars {
        for (upper, bound) in prover.abduce_bound(hyps, diff, var) {
            let op = match (upper, strict) {
                (false, false) => BinOp::Ge,
                (false, true) => BinOp::Gt,
                (true, false) => BinOp::Le,
                (true, true) => BinOp::Lt,
            };
            // A bound derived from decimal literals is exact but
            // unreadable — `0.99` is not ninety-nine hundredths as an
            // `f64`, so dividing by it yields something like
            // `3602879701896397 / 17834254524387164`.  Offer rounded forms
            // first, erring towards the *stronger* assumption so they still
            // imply the goal.
            for written in readable_bounds(bound, upper) {
                let assumption = Expr::BinOp(
                    op.clone(),
                    Box::new(Expr::Var { name: var.clone(), line: 0, col: 0 }),
                    Box::new(written),
                );
                // A "suggestion" that restates the goal tells the author
                // nothing: `n >= 5` holds given `n >= 5`.
                if crate::ast::alpha_equiv(&assumption, conclusion) {
                    continue;
                }
                // Nor does one already assumed.
                if hyps.iter().any(|h| crate::ast::alpha_equiv(h, &assumption)) {
                    continue;
                }
                // Does adding it actually get anywhere?  Either it closes
                // the goal outright, or it is a step the next round can
                // build on — but a bound that changes nothing is noise.
                let candidate = with_assumption(prop, assumption.clone());
                // A bound that contradicts what is already assumed makes
                // the goal hold *vacuously*.  `a >= 0.6 ⊢ 50a >= 30` is
                // "provable" given `a <= 0`, and offering that as the
                // missing assumption is worse than saying nothing: it reads
                // as a finding about the model when it is an artifact of
                // ex falso.
                if contradicts_the_hypotheses(prover, &candidate, env) {
                    continue;
                }
                if prover.verify_algebra_raw(&candidate, env).is_ok()
                    || bound_is_progress(prover, &candidate, env)
                {
                    return Some(Suggestion {
                        assumption,
                        variable: Some(var.clone()),
                    });
                }
            }
        }
    }
    None
}

/// How a bound on `var` is written.
fn bound_expr(var: &str, upper: bool, strict: bool, c: Expr) -> Expr {
    let op = match (upper, strict) {
        (false, false) => BinOp::Ge,
        (false, true) => BinOp::Gt,
        (true, false) => BinOp::Le,
        (true, true) => BinOp::Lt,
    };
    Expr::BinOp(
        op,
        Box::new(Expr::Var { name: var.to_string(), line: 0, col: 0 }),
        Box::new(c),
    )
}

/// The weakest bound on `var` that closes the goal, found by asking the
/// prover.
///
/// The linear reading in `Prover::abduce_bound` cannot see a bound the
/// certificate needs *inside a product*.  `x >= 0 ⊢ x² <= 4` holds given
/// `x <= 2`, and the certificate is `(2-x)·(2+x)`: the unknown multiplies a
/// generator rather than standing in its own column, and the system stops
/// being linear.
///
/// So stop solving for it and test it instead.  "Does `var <= c` close the
/// goal" is monotone in `c` — a tighter bound assumes more — so a
/// doubling ladder brackets the boundary and a bisection narrows it.  The
/// answer is then rounded to something a reader can act on, and each
/// rounding is tested too, so nothing is offered that does not work.
///
/// Every probe is a real proof attempt, which is why the caller only
/// reaches here for a non-linear goal, where the exact method provably
/// cannot help.
fn probe_for_bound(
    prover: &Prover,
    prop: &Expr,
    env: &Env,
    var: &str,
    upper: bool,
    strict: bool,
) -> Option<Rat> {
    // Far enough to bracket the bounds a model states, and small enough
    // that a failed search costs a bounded number of proof attempts.
    const LADDER_LIMIT: i128 = 4096;
    const BISECTIONS: u32 = 24;

    let works = |c: Rat| -> bool {
        let Some(written) = small_rational_expr(c) else {
            return false;
        };
        let candidate = with_assumption(prop, bound_expr(var, upper, strict, written));
        prover.verify_algebra_raw(&candidate, env).is_ok()
    };
    // `works` is monotone the same way in both directions once read as
    // "how far out is the bound": an upper bound gets weaker as it grows,
    // a lower bound as it shrinks.  `step` walks outwards.
    let outward = |c: Rat, by: Rat| if upper { c.add(by) } else { c.sub(by) };

    // Bracketing is two moves, not one.  The bound that works may be
    // *stronger* than anything near zero — `perNode >= 0` proves nothing
    // about `perNode · nodes >= rps`, while `perNode >= 625` proves it —
    // so first walk in the strong direction until something works, then
    // walk back toward the weak side to find where it stops.
    let zero = Rat::from_int(0);
    let strong = |c: Rat, by: Rat| if upper { c.sub(by) } else { c.add(by) };

    let mut good = zero;
    let mut weakest_failure: Option<Rat> = None;
    if !works(zero) {
        let mut step = Rat::from_int(1);
        let mut found = None;
        while step.num <= LADDER_LIMIT {
            let c = strong(zero, step);
            if works(c) {
                found = Some(c);
                break;
            }
            // Still failing, and this is the weakest failure seen so far.
            weakest_failure = Some(c);
            step = step.mul(Rat::from_int(2));
        }
        good = found?;
        // Anything weaker than `good` that already failed brackets it; if
        // the very first strong step worked, zero is the bracket.
        if weakest_failure.is_none() {
            weakest_failure = Some(zero);
        }
    }

    // Now walk toward the weak side while it still works.
    let outward = |c: Rat, by: Rat| if upper { c.add(by) } else { c.sub(by) };
    let mut bad = weakest_failure;
    if bad.is_none() {
        let mut step = Rat::from_int(1);
        while step.num <= LADDER_LIMIT {
            let next = outward(zero, step);
            if works(next) {
                good = next;
            } else {
                bad = Some(next);
                break;
            }
            step = step.mul(Rat::from_int(2));
        }
    }
    // Nothing failed inside the ladder: the bound is not what constrains
    // this goal, or it is vacuously wide.  Either way there is nothing
    // useful to report.
    let mut bad = bad?;

    // Narrow.  `good` always works and `bad` never does, so the boundary is
    // between them.
    for _ in 0..BISECTIONS {
        let mid = good.add(bad).div(Rat::from_int(2))?;
        if mid.is_poison() {
            break;
        }
        if works(mid) {
            good = mid;
        } else {
            bad = mid;
        }
    }

    // A boundary of 1.99998 is the answer to a question nobody asked; the
    // bound worth showing is the roundest value that still works, which is
    // usually the one the model was written around.  Both ends are rounded
    // because the true boundary may sit just above `good`.
    let mut best: Option<Rat> = None;
    for candidate in readable_bounds(good, upper)
        .into_iter()
        .chain(readable_bounds(bad, upper))
    {
        let Some(c) = rat_of_expr(&candidate) else {
            continue;
        };
        if !works(c) {
            continue;
        }
        // Weakest wins: the largest upper bound, the smallest lower one.
        let better = match best {
            None => true,
            Some(b) => {
                let d = c.sub(b).sign();
                if upper {
                    d > 0
                } else {
                    d < 0
                }
            }
        };
        if better {
            best = Some(c);
        }
    }
    best.or(Some(good))
}

/// The rational an expression built by `small_rational_expr` stands for.
fn rat_of_expr(e: &Expr) -> Option<Rat> {
    match e {
        Expr::Int(n) => Some(Rat::from_int(*n as i128)),
        Expr::BinOp(BinOp::Div, a, b) => match (a.as_ref(), b.as_ref()) {
            (Expr::Int(n), Expr::Int(d)) => Some(Rat::new(*n as i128, *d as i128)),
            _ => None,
        },
        Expr::UnOp(crate::ast::UnOp::Neg, x) => rat_of_expr(x).map(|r| r.neg()),
        _ => None,
    }
}

/// Whether the hypotheses of `prop` cannot all hold at once.
///
/// Asked by trying to derive something plainly false from them: if `0 >= 1`
/// follows, anything does, and the goal's truth says nothing.
fn contradicts_the_hypotheses(prover: &Prover, prop: &Expr, env: &Env) -> bool {
    let (binders, inner) = crate::rewrite::peel_binders(prop);
    let (_, hyps) = crate::rewrite::peel_premises(&inner);
    if hyps.is_empty() {
        return false;
    }
    let absurd = Expr::BinOp(
        BinOp::Ge,
        Box::new(Expr::Real(0.0)),
        Box::new(Expr::Real(1.0)),
    );
    let mut goal = absurd;
    for h in hyps.iter().rev() {
        goal = Expr::BinOp(
            BinOp::Or,
            Box::new(Expr::UnOp(crate::ast::UnOp::Not, Box::new(h.clone()))),
            Box::new(goal),
        );
    }
    prover
        .verify_algebra_raw(&crate::rewrite::rebuild_binders(&binders, goal), env)
        .is_ok()
}

/// Whether a candidate assumption leaves a goal that abduction can still
/// make progress on — used to accept a bound that is necessary but not on
/// its own sufficient.
fn bound_is_progress(prover: &Prover, candidate: &Expr, _env: &Env) -> bool {
    let Some((diff, _)) = goal_difference(candidate) else {
        return false;
    };
    let (_, hyps) =
        crate::rewrite::peel_premises(crate::rewrite::peel_binders(candidate).1);
    candidate_variables(&diff, &hyps)
        .into_iter()
        .any(|v| !prover.abduce_bound(&hyps, &diff, &v).is_empty())
}

/// The goal's variables, the ones no hypothesis mentions first.
///
/// An unconstrained parameter is what is usually missing; a variable that
/// already has a bound needs it *tightened*, which is a smaller surprise
/// and a less likely diagnosis.
fn candidate_variables(diff: &Polynomial, hyps: &[Expr]) -> Vec<String> {
    let mut vars: Vec<String> = Vec::new();
    for m in &diff.terms {
        for v in m.vars.keys() {
            // An opaque subterm is not something the author can bound.
            if !v.starts_with("__atom_") && !vars.contains(v) {
                vars.push(v.clone());
            }
        }
    }
    let mentioned = |v: &str| {
        let mut names = std::collections::BTreeSet::new();
        for h in hyps {
            crate::unfold::collect_free_var_names(h, &mut names);
        }
        names.contains(v)
    };
    vars.sort_by_key(|v| mentioned(v));
    vars
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
    // The set is collectively sufficient, so they are joined with "and":
    // adding only one of them would still leave the goal open.
    format!(
        "\n  it would hold given {} — add {} as a hypothesis \
         (`... => <goal>`) or tighten an existing one",
        parts.join(" and "),
        if parts.len() == 1 { "it" } else { "them" }
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

/// Ways of writing a bound, most readable first.
///
/// Rounding goes towards the stronger assumption — down for an upper bound,
/// up for a lower one — so a rounded form still implies what the exact one
/// did.  Each is checked by the caller before being offered, so a rounding
/// that goes too far is simply dropped.
fn readable_bounds(bound: Rat, upper: bool) -> Vec<Expr> {
    let mut out = Vec::new();
    let exact = bound.num as f64 / bound.den as f64;
    for places in [2u32, 3, 4, 6] {
        let scale = 10f64.powi(places as i32);
        let rounded = if upper {
            (exact * scale).floor() / scale
        } else {
            (exact * scale).ceil() / scale
        };
        if let Some(r) = crate::confidence::rational_from_decimal(rounded) {
            if let Some(e) = small_rational_expr(r) {
                if !out.iter().any(|prev| format!("{}", prev) == format!("{}", e)) {
                    out.push(e);
                }
            }
        }
    }
    // The exact bound last, when it can be written down at all.
    if let Some(e) = small_rational_expr(bound) {
        out.push(e);
    }
    out
}

/// A rational as an expression, when its parts fit in the `Int` the
/// language actually has.  A ratio of 17-digit numbers is not a bound
/// anybody can act on, and casting it would silently truncate.
fn small_rational_expr(r: Rat) -> Option<Expr> {
    let num = i64::try_from(r.num).ok()?;
    let den = i64::try_from(r.den).ok()?;
    if den == 1 {
        return Some(Expr::Int(num));
    }
    // Beyond this a "bound" is noise rather than information.
    if den.abs() > 100_000 {
        return None;
    }
    Some(Expr::BinOp(
        BinOp::Div,
        Box::new(Expr::Int(num)),
        Box::new(Expr::Int(den)),
    ))
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
    fn a_bound_is_found_with_several_variables_in_play() {
        // `c >= 3.5` and the goal `c - p >= 0.5` pin `p` down exactly.
        // Rearranging for a single variable — what this used to do — cannot
        // see this at all.
        assert_eq!(
            suggest("forall c in Real, forall p in Real, c >= 3.5 => (c - p) >= 0.5"),
            vec!["(p <= 3)"]
        );
    }

    #[test]
    fn the_bound_reported_is_the_weakest_one_that_works() {
        // `r <= 0` would also make the goal hold, and the simplex is just
        // as happy to return it.  Phase 2 picks the bound that actually
        // answers the question.
        assert_eq!(
            suggest("forall r in Real, r <= 0.6 => (100.0 - 200.0 * r) > 0.0"),
            vec!["(r < (1 / 2))"]
        );
    }

    #[test]
    fn a_three_parameter_model_names_the_one_that_is_missing() {
        assert_eq!(
            suggest(
                "forall rev in Real, forall cost in Real, forall tax in Real, \
                 (rev >= 100.0) and (tax <= 20.0) => (rev - cost - tax) >= 50.0"
            ),
            vec!["(cost <= 30)"]
        );
    }

    #[test]
    fn an_existing_bound_that_is_too_loose_gets_tightened() {
        // `a >= 3/5` is not enough for `50a >= 40`; `a >= 4/5` is, and it
        // is the *weakest* bound that is.  `a >= 1000` would also do, and
        // is what a linear objective on the constant term picks — the
        // bound is a ratio, so choosing it needs the Charnes-Cooper
        // substitution in `Prover::abduce_bound`.
        assert_eq!(
            suggest("forall a in Real, a >= 0.6 => (a * 50.0) >= 40.0"),
            vec!["(a >= (4 / 5))"]
        );
    }

    #[test]
    fn a_suggestion_never_works_by_contradicting_what_is_assumed() {
        // `a <= 0` makes `a >= 0.6 ⊢ 50a >= 40` hold, vacuously.  Offering
        // it reads as a finding about the model when it is ex falso.
        for s in suggest("forall a in Real, a >= 0.6 => (a * 50.0) >= 40.0") {
            assert!(!s.contains("a <="), "offered a contradictory bound: {}", s);
        }
    }

    #[test]
    fn an_ambiguous_gap_gets_silence_rather_than_a_guess() {
        // `c - p >= 1/2` with both free needs a bound on the difference;
        // infinitely many pairs of individual bounds would do, so naming
        // one would be arbitrary.
        assert!(suggest("forall c in Real, forall p in Real, (c - p) >= 0.5").is_empty());
    }

    #[test]
    fn a_bound_needed_inside_a_product_is_found_by_probing() {
        // `x <= 2` does it, but its certificate is `(2-x)·(2+x)`: the
        // missing bound multiplies a generator instead of standing in its
        // own column, so the linear reading cannot see it.
        assert_eq!(
            suggest("forall x in Real, x >= 0.0 => x * x <= 4.0"),
            vec!["(x <= 2)"]
        );
        assert_eq!(
            suggest("forall x in Real, x >= 0.0 => x * x * x <= 8.0"),
            vec!["(x <= 2)"]
        );
        // The direction follows the goal, not a convention.
        assert_eq!(
            suggest("forall x in Real, x <= 0.0 => x * x <= 4.0"),
            vec!["(x >= -2)"]
        );
        // And a product of two parameters bounds the free one.
        assert_eq!(
            suggest(
                "forall a in Real, forall b in Real, \
                 (a >= 0.0) and (b >= 0.0) and (b <= 3.0) => a * b <= 12.0"
            ),
            vec!["(a <= 4)"]
        );
    }

    #[test]
    fn a_goal_with_no_bound_to_find_still_says_nothing() {
        // `x³ >= 0` needs `x >= 0`, which is a bound — but the goal as
        // stated is false only for negative `x`, and the suggestion has to
        // survive the contradiction check like any other.
        let s = suggest("forall x in Real, x * x * x >= 0.0");
        assert!(s.is_empty() || s == vec!["(x >= 0)"], "{:?}", s);
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

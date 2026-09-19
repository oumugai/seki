//! How much a conclusion's assumptions warrant it.
//!
//! # Why this is not in the kernel
//!
//! `crate::kernel` answers a yes/no question — was every step of the proof
//! re-established from primitives — and the value of that answer comes from
//! its being binary.  Letting a probability into it would turn `Sound` into
//! a continuous quantity and dissolve the whole trust story.
//!
//! So this layer sits *on top of* the proof term and changes nothing about
//! it.  The hard part is already done: a `Verdict` names, transitively,
//! every assumption a conclusion rests on.  All that is added here is
//! arithmetic over that set.
//!
//! An axiom carrying `with confidence c` is still an axiom — the theorem
//! that uses it is still `TrustLevel::Axiomatic`.  Confidence is a *second,
//! orthogonal* report: "how was this checked" and "how much do its
//! assumptions warrant it" are genuinely different questions.
//!
//! # Why the bound is not a product
//!
//! Multiplying confidences assumes the assumptions are independent, and
//! facts derived from the same source usually are not.  `0.9 × 0.9 = 0.81`
//! looks precise and means nothing.
//!
//! The conclusion needs *all* of its assumptions to hold, so the guaranteed
//! bound is Fréchet's, which assumes nothing about the joint distribution:
//!
//! ```text
//! P(A₁ ∧ … ∧ Aₙ) ≥ max(0, Σ P(Aᵢ) − (n−1))
//! ```
//!
//! This is not merely conservative — for an assumption written as an
//! implication it is *exact*.  `with confidence q` on `axiom r : A => B`
//! states `P(A → B) ≥ q`, and from `P(A) ≥ p`,
//!
//! ```text
//! P(B) ≥ P(A ∧ B) = P(A) − P(A ∧ ¬B) ≥ p − (1 − q) = p + q − 1
//! ```
//!
//! which is the bound above.  Chaining uncertain rules — the shape an
//! LLM-extracted fact takes — therefore composes correctly with no
//! independence assumption anywhere.

use crate::algebra::Rat;
use crate::kernel::Verdict;
use crate::value::Globals;

/// Read a confidence written as a decimal as the rational the author meant.
///
/// `f64_to_rat` is exact, which is right for `by algebra` — `0.1` really is
/// not one tenth and a proof had better not pretend otherwise.  A confidence
/// is different: `0.9` is a number the author chose, not a measurement, and
/// combining exact-f64 versions of it produces `0.7000000000000001` in a
/// report meant for a person to read.
///
/// So the simplest rational within a hair of the literal is used instead.
/// Anything that does not round cleanly is left exact.
pub fn rational_from_decimal(f: f64) -> Option<Rat> {
    if !f.is_finite() {
        return None;
    }
    const TOLERANCE: f64 = 1e-9;
    for den in 1i128..=100_000 {
        let num = (f * den as f64).round();
        if num.abs() > i128::MAX as f64 {
            break;
        }
        if (num / den as f64 - f).abs() < TOLERANCE {
            return Some(Rat::new(num as i128, den));
        }
    }
    crate::algebra::f64_to_rat(f)
}

/// What can be said about a conclusion given the confidence of the
/// assumptions it rests on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Confidence {
    /// Nothing the conclusion rests on carries a confidence: either it rests
    /// on nothing at all, or only on axioms asserted outright.
    Unqualified,
    /// A guaranteed lower bound, and the assumptions it came from.
    Bounded {
        lower: Rat,
        /// `(axiom name, its confidence)`, sorted by name.
        from: Vec<(String, Rat)>,
    },
}

impl Confidence {
    /// The bound, or `1` when the conclusion carries no uncertain
    /// assumption.
    pub fn lower_bound(&self) -> Rat {
        match self {
            Confidence::Unqualified => Rat::from_int(1),
            Confidence::Bounded { lower, .. } => *lower,
        }
    }

    /// Is this conclusion warranted to at least `threshold`?
    pub fn meets(&self, threshold: Rat) -> bool {
        // `a >= b`  ⟺  `a - b >= 0`
        self.lower_bound().sub(threshold).sign() >= 0
    }

    /// One line for an audit listing.
    pub fn describe(&self) -> String {
        match self {
            Confidence::Unqualified => String::new(),
            Confidence::Bounded { lower, from } => format!(
                "confidence >= {} (from {})",
                lower,
                from.iter()
                    .map(|(n, c)| format!("`{}` {}", n, c))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

/// Read the confidence of a conclusion off what the kernel concluded.
///
/// Every uncertain assumption named in the verdict contributes; the bound is
/// Fréchet's, so nothing about independence is assumed.
pub fn of_verdict(verdict: &Verdict, globals: &Globals) -> Confidence {
    let mut from: Vec<(String, Rat)> = Vec::new();
    for name in assumed_axioms(verdict) {
        if let Some(c) = globals.axiom_confidence.get(&name) {
            from.push((name, *c));
        }
    }
    if from.is_empty() {
        return Confidence::Unqualified;
    }
    from.sort_by(|a, b| a.0.cmp(&b.0));
    from.dedup_by(|a, b| a.0 == b.0);
    Confidence::Bounded { lower: frechet_lower_bound(&from), from }
}

/// `max(0, Σ pᵢ − (n − 1))`.
fn frechet_lower_bound(from: &[(String, Rat)]) -> Rat {
    let n = from.len() as i128;
    let sum = from
        .iter()
        .fold(Rat::from_int(0), |acc, (_, p)| acc.add(*p));
    let bound = sum.sub(Rat::from_int(n - 1));
    if bound.sign() < 0 {
        Rat::from_int(0)
    } else {
        bound
    }
}

/// The axiom names a verdict records as assumptions.
///
/// `Verdict::assumptions` holds human-readable lines; the axiom ones are
/// written by `crate::kernel` as ``axiom `name` ``.
fn assumed_axioms(verdict: &Verdict) -> Vec<String> {
    verdict
        .assumptions
        .iter()
        .filter_map(|a| {
            let rest = a.strip_prefix("axiom `")?;
            let end = rest.find('`')?;
            Some(rest[..end].to_string())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Verdict;

    fn verdict_on(axioms: &[&str]) -> Verdict {
        Verdict {
            fully_checked: true,
            trusted_steps: Vec::new(),
            assumptions: axioms
                .iter()
                .map(|a| format!("axiom `{}`", a))
                .collect(),
        }
    }

    fn globals_with(cs: &[(&str, (i128, i128))]) -> Globals {
        let mut g = Globals::new();
        for (n, (num, den)) in cs {
            g.axiom_confidence
                .insert((*n).to_string(), Rat::new(*num, *den));
        }
        g
    }

    #[test]
    fn a_decimal_confidence_reads_as_the_rational_it_means() {
        assert_eq!(rational_from_decimal(0.9), Some(Rat::new(9, 10)));
        assert_eq!(rational_from_decimal(0.85), Some(Rat::new(17, 20)));
        assert_eq!(rational_from_decimal(1.0), Some(Rat::from_int(1)));
        assert_eq!(rational_from_decimal(0.0), Some(Rat::from_int(0)));
        // And the arithmetic then stays clean.
        let a = rational_from_decimal(0.9).unwrap();
        let b = rational_from_decimal(0.8).unwrap();
        assert_eq!(a.add(b).sub(Rat::from_int(1)), Rat::new(7, 10));
    }

    #[test]
    fn a_conclusion_with_no_uncertain_assumption_is_unqualified() {
        let g = globals_with(&[]);
        assert_eq!(
            of_verdict(&verdict_on(&[]), &g),
            Confidence::Unqualified
        );
        // A classical axiom with no confidence does not qualify it either.
        assert_eq!(
            of_verdict(&verdict_on(&["ivt"]), &g),
            Confidence::Unqualified
        );
    }

    #[test]
    fn one_assumption_passes_its_own_confidence_through() {
        let g = globals_with(&[("llm", (85, 100))]);
        let c = of_verdict(&verdict_on(&["llm"]), &g);
        assert_eq!(c.lower_bound(), Rat::new(85, 100));
    }

    #[test]
    fn two_assumptions_combine_by_frechet_not_by_product() {
        // 0.9 and 0.8: the product would be 0.72, which assumes
        // independence.  The guaranteed bound is 0.9 + 0.8 - 1 = 0.7.
        let g = globals_with(&[("a", (9, 10)), ("b", (8, 10))]);
        let c = of_verdict(&verdict_on(&["a", "b"]), &g);
        assert_eq!(c.lower_bound(), Rat::new(7, 10));
    }

    #[test]
    fn enough_weak_assumptions_warrant_nothing() {
        // Three assumptions at 0.5 guarantee max(0, 1.5 - 2) = 0 — which is
        // the honest answer, and what a product (0.125) would hide.
        let g = globals_with(&[("a", (1, 2)), ("b", (1, 2)), ("c", (1, 2))]);
        let c = of_verdict(&verdict_on(&["a", "b", "c"]), &g);
        assert_eq!(c.lower_bound(), Rat::from_int(0));
        assert!(!c.meets(Rat::new(1, 100)));
    }

    #[test]
    fn the_same_assumption_twice_is_counted_once() {
        let g = globals_with(&[("a", (9, 10))]);
        let c = of_verdict(&verdict_on(&["a", "a"]), &g);
        assert_eq!(c.lower_bound(), Rat::new(9, 10));
    }

    #[test]
    fn a_threshold_is_compared_exactly() {
        let g = globals_with(&[("a", (9, 10))]);
        let c = of_verdict(&verdict_on(&["a"]), &g);
        assert!(c.meets(Rat::new(9, 10)));
        assert!(!c.meets(Rat::new(901, 1000)));
    }
}

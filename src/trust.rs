//! How much a verified theorem is actually worth.
//!
//! `Prover::verify` answers a yes/no question: did some tactic close this
//! goal?  That is not the same as "is this theorem true", because two of
//! seki's tactics are deliberately incomplete in a direction that can accept
//! a false statement:
//!
//!   * `by eval` (and `by decide`, and the trailing eval of `by simp` /
//!     `by unfold` / `by intros`) enumerates a quantifier's domain.  For an
//!     infinite domain — `Nat`, `Int`, `Real` — `enumerate_set` returns a
//!     *sample* bounded by `SAMPLE_BOUND`, so `forall n in Nat, P(n)` is
//!     accepted whenever `P` holds on `0..200`.
//!   * `axiom` declares a proposition true without proof, and `by simp` /
//!     `by obtain` propagate axioms into other theorems.
//!
//! `docs/spec/06-soundness.md` §6.6 told users to audit for this by hand.
//! This module makes it a machine check instead: every theorem carries the
//! trust level of its *weakest* ingredient, and `--strict` refuses to accept
//! anything below `Sound`.
//!
//! The levels form a lattice ordered by decreasing trust, so combining
//! ingredients is `max` (see [`TrustLevel::weakest`]).

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TrustLevel {
    /// Machine-checked with no appeal to sampling or to an unproven
    /// assumption.  `refl`, `by algebra`, `by linarith`, `by induction`,
    /// `by strong_induction`, and `by eval` over a *finite* domain.
    Sound,
    /// Sound *relative to* one or more `axiom` declarations.  The proof
    /// itself is valid; its conclusion is only as true as the axioms the
    /// user asserted.
    Axiomatic,
    /// A tactic closed the goal by a route that emits no checkable witness,
    /// so `crate::kernel` could not re-establish it.  The proposition is
    /// probably true; nothing here proves it independently.
    Unchecked,
    /// Checked on a finite sample of an infinite domain.  **This can accept
    /// a false proposition** — see `docs/spec/06-soundness.md` §6.0.
    Sampled,
}

impl TrustLevel {
    /// Read a level off what the kernel concluded.
    ///
    /// The certificate *is* the evidence, so the level is derived from the
    /// kernel's verdict rather than computed by a second analysis that
    /// could disagree with it.
    pub fn from_verdict(v: &crate::kernel::Verdict) -> Self {
        if v.is_sampled() {
            return TrustLevel::Sampled;
        }
        if !v.fully_checked {
            return TrustLevel::Unchecked;
        }
        if v.has_assumptions() {
            return TrustLevel::Axiomatic;
        }
        TrustLevel::Sound
    }
}

impl TrustLevel {
    /// Combine two ingredients of one proof: the result is only as
    /// trustworthy as the weaker of the two.
    pub fn weakest(self, other: Self) -> Self {
        self.max(other)
    }

    /// Combine an iterator of ingredients; an empty iterator is `Sound`.
    pub fn weakest_of(levels: impl IntoIterator<Item = Self>) -> Self {
        levels
            .into_iter()
            .fold(TrustLevel::Sound, TrustLevel::weakest)
    }

    /// Nothing in the proof can accept a false proposition.
    pub fn is_sound(self) -> bool {
        self == TrustLevel::Sound
    }

    /// Short suffix shown after `theorem foo ✓ proved`.  `Sound` prints
    /// nothing — the unmarked case is the good one, so a clean file stays
    /// clean.
    pub fn marker(self) -> &'static str {
        match self {
            TrustLevel::Sound => "",
            TrustLevel::Axiomatic => "  [axiomatic]",
            TrustLevel::Unchecked => "  [unchecked — no proof term]",
            TrustLevel::Sampled => "  [sampled — NOT a proof]",
        }
    }

    /// Why a `--strict` run rejected this theorem.
    pub fn rejection_reason(self) -> Option<&'static str> {
        match self {
            TrustLevel::Sound => None,
            TrustLevel::Axiomatic => Some(
                "it depends on an `axiom`, which is asserted without proof",
            ),
            TrustLevel::Unchecked => Some(
                "the tactic that closed it emits no proof term, so the kernel could \
                 not re-establish it independently",
            ),
            TrustLevel::Sampled => Some(
                "it quantifies over an infinite domain but was only checked on a \
                 finite sample, so it is not a proof (see docs/spec/06-soundness.md §6.0)",
            ),
        }
    }
}

impl fmt::Display for TrustLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            TrustLevel::Sound => "sound",
            TrustLevel::Axiomatic => "axiomatic",
            TrustLevel::Unchecked => "unchecked",
            TrustLevel::Sampled => "sampled",
        };
        f.write_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn weakest_link_wins() {
        assert_eq!(
            TrustLevel::Sound.weakest(TrustLevel::Sampled),
            TrustLevel::Sampled
        );
        assert_eq!(
            TrustLevel::Axiomatic.weakest(TrustLevel::Sampled),
            TrustLevel::Sampled
        );
        assert_eq!(
            TrustLevel::Sound.weakest(TrustLevel::Axiomatic),
            TrustLevel::Axiomatic
        );
        assert_eq!(TrustLevel::weakest_of([]), TrustLevel::Sound);
        assert_eq!(
            TrustLevel::weakest_of([TrustLevel::Sound, TrustLevel::Axiomatic]),
            TrustLevel::Axiomatic
        );
    }

    #[test]
    fn only_sound_is_sound() {
        assert!(TrustLevel::Sound.is_sound());
        assert!(!TrustLevel::Axiomatic.is_sound());
        assert!(!TrustLevel::Sampled.is_sound());
        assert!(TrustLevel::Sound.rejection_reason().is_none());
        assert!(TrustLevel::Sampled.rejection_reason().is_some());
    }
}

//! Rigorous interval arithmetic over exact rationals.
//!
//! `Real` in seki means ℝ, and the evaluator computes in `f64`.  Wherever
//! those disagree the kernel refuses to call an evaluated verdict a proof
//! and reports it as `Approximate` (`docs/spec/06-soundness.md` §6.0.13).
//! That is honest but blunt: a claim like
//!
//! ```text
//! |integSimpson 100 f_sq 0 1 - 1/3| < 0.000001
//! ```
//!
//! *is* true of the reals, and saying only "this was floating point" throws
//! away the fact.  What was missing is a way to compute with a **guaranteed
//! enclosure** rather than with one rounded number.
//!
//! An `Interval` is a pair of exact rationals that provably brackets the
//! real value.  Arithmetic rounds *outward*, so the enclosure can only
//! widen, never lie.  A comparison answers `Some(true)` or `Some(false)`
//! only when the whole interval settles it, and `None` when the enclosure
//! is too wide — which the kernel reads as "no verdict", never as a pass.
//!
//! # Why the denominators are capped
//!
//! Exact rationals are exact, but `a/b + c/d` has denominator up to `b·d`,
//! so a few hundred operations overflow `i128` and poison.  Rounding each
//! result outward to a denominator of at most [`MAX_DEN`] keeps the numbers
//! bounded at the cost of widening the enclosure by about `1e-12` per
//! operation — and widening outward is always sound.
//!
//! The cap also keeps the arithmetic below overflow: both operands have
//! denominator at most `MAX_DEN`, so a product's is at most `MAX_DEN²`, and
//! the rounding step's own multiplication stays under `MAX_DEN³ < i128::MAX`.

use crate::algebra::Rat;

/// The largest denominator an endpoint may carry.  See the module note on
/// why this is capped and why `10¹²` in particular.
pub const MAX_DEN: i128 = 1_000_000_000_000;

/// A guaranteed enclosure of a real number: `lo <= value <= hi`.
///
/// A poisoned endpoint marks an enclosure that overflowed or could not be
/// established; every operation propagates it, and the kernel treats a
/// poisoned result as "no verdict".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub lo: Rat,
    pub hi: Rat,
}

impl std::fmt::Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lo, self.hi)
    }
}

/// Round `r` down to a denominator of at most `d`.
///
/// `floor(r·d)/d`, computed so the intermediate stays inside `i128`:
/// splitting `num` into quotient and remainder against `den` first means the
/// only wide multiplication is `rem·d`, and `rem < den`.
fn round_down(r: Rat, d: i128) -> Rat {
    if r.is_poison() {
        return Rat::POISON;
    }
    if r.den <= d {
        return r;
    }
    let q = r.num.div_euclid(r.den);
    let rem = r.num.rem_euclid(r.den); // 0 <= rem < den
    let Some(scaled) = rem.checked_mul(d) else {
        return Rat::POISON;
    };
    let frac = scaled.div_euclid(r.den);
    let Some(whole) = q.checked_mul(d) else {
        return Rat::POISON;
    };
    let Some(n) = whole.checked_add(frac) else {
        return Rat::POISON;
    };
    Rat::new(n, d)
}

/// Round `r` up to a denominator of at most `d`.
fn round_up(r: Rat, d: i128) -> Rat {
    round_down(r.neg(), d).neg()
}

impl Interval {
    /// The single point `r`.
    pub fn exact(r: Rat) -> Self {
        Interval { lo: r, hi: r }.tightened()
    }

    pub fn from_int(n: i128) -> Self {
        Interval::exact(Rat::from_int(n))
    }

    /// An enclosure with the endpoints as given, rounded outward.  A pair in
    /// the wrong order is a bug in the caller, so it poisons rather than
    /// silently swapping.
    pub fn new(lo: Rat, hi: Rat) -> Self {
        if lo.is_poison() || hi.is_poison() || hi.sub(lo).sign() < 0 {
            return Interval::poison();
        }
        Interval { lo, hi }.tightened()
    }

    pub fn poison() -> Self {
        Interval { lo: Rat::POISON, hi: Rat::POISON }
    }

    pub fn is_poison(self) -> bool {
        self.lo.is_poison() || self.hi.is_poison()
    }

    /// Widen outward until both endpoints fit under [`MAX_DEN`].
    fn tightened(self) -> Self {
        if self.is_poison() {
            return Interval::poison();
        }
        let lo = round_down(self.lo, MAX_DEN);
        let hi = round_up(self.hi, MAX_DEN);
        if lo.is_poison() || hi.is_poison() {
            return Interval::poison();
        }
        Interval { lo, hi }
    }

    /// Is this a single exact rational?
    pub fn is_point(self) -> bool {
        !self.is_poison() && self.hi.sub(self.lo).is_zero()
    }

    pub fn add(self, other: Interval) -> Interval {
        if self.is_poison() || other.is_poison() {
            return Interval::poison();
        }
        Interval::new(self.lo.add(other.lo), self.hi.add(other.hi))
    }

    pub fn sub(self, other: Interval) -> Interval {
        if self.is_poison() || other.is_poison() {
            return Interval::poison();
        }
        // The *low* end of a difference pairs this low with that high.
        Interval::new(self.lo.sub(other.hi), self.hi.sub(other.lo))
    }

    pub fn neg(self) -> Interval {
        if self.is_poison() {
            return Interval::poison();
        }
        Interval::new(self.hi.neg(), self.lo.neg())
    }

    pub fn mul(self, other: Interval) -> Interval {
        if self.is_poison() || other.is_poison() {
            return Interval::poison();
        }
        // Signs make the extremes land on different corners, so take all
        // four rather than reasoning about which.
        let corners = [
            self.lo.mul(other.lo),
            self.lo.mul(other.hi),
            self.hi.mul(other.lo),
            self.hi.mul(other.hi),
        ];
        if corners.iter().any(|c| c.is_poison()) {
            return Interval::poison();
        }
        let mut lo = corners[0];
        let mut hi = corners[0];
        for c in &corners[1..] {
            if c.sub(lo).sign() < 0 {
                lo = *c;
            }
            if c.sub(hi).sign() > 0 {
                hi = *c;
            }
        }
        Interval::new(lo, hi)
    }

    /// Division, undefined when the divisor's enclosure straddles zero — an
    /// enclosure that contains zero says nothing about the quotient.
    pub fn div(self, other: Interval) -> Interval {
        if self.is_poison() || other.is_poison() {
            return Interval::poison();
        }
        if other.lo.sign() <= 0 && other.hi.sign() >= 0 {
            return Interval::poison();
        }
        let corners = [
            self.lo.div(other.lo),
            self.lo.div(other.hi),
            self.hi.div(other.lo),
            self.hi.div(other.hi),
        ];
        let Some(first) = corners[0] else {
            return Interval::poison();
        };
        let mut lo = first;
        let mut hi = first;
        for c in &corners {
            let Some(c) = *c else {
                return Interval::poison();
            };
            if c.is_poison() {
                return Interval::poison();
            }
            if c.sub(lo).sign() < 0 {
                lo = c;
            }
            if c.sub(hi).sign() > 0 {
                hi = c;
            }
        }
        Interval::new(lo, hi)
    }

    /// `self < other`, when the enclosures settle it.
    pub fn lt(self, other: Interval) -> Option<bool> {
        if self.is_poison() || other.is_poison() {
            return None;
        }
        if self.hi.sub(other.lo).sign() < 0 {
            return Some(true);
        }
        if self.lo.sub(other.hi).sign() >= 0 {
            return Some(false);
        }
        None
    }

    pub fn le(self, other: Interval) -> Option<bool> {
        if self.is_poison() || other.is_poison() {
            return None;
        }
        if self.hi.sub(other.lo).sign() <= 0 {
            return Some(true);
        }
        if self.lo.sub(other.hi).sign() > 0 {
            return Some(false);
        }
        None
    }

    /// Equality is only ever decidable *negatively* for a genuine interval:
    /// two enclosures that overlap may or may not be the same number.  Two
    /// points are decided outright.
    pub fn eq(self, other: Interval) -> Option<bool> {
        if self.is_poison() || other.is_poison() {
            return None;
        }
        if self.is_point() && other.is_point() {
            return Some(self.lo.sub(other.lo).is_zero());
        }
        if self.hi.sub(other.lo).sign() < 0 || other.hi.sub(self.lo).sign() < 0 {
            return Some(false);
        }
        None
    }

    /// A verified enclosure of the square root.
    ///
    /// Nothing here trusts the floating-point estimate it starts from: each
    /// endpoint is *checked* by squaring it, and moved outward until the
    /// check passes.  An estimate that is wrong merely costs iterations.
    pub fn sqrt(self) -> Interval {
        if self.is_poison() || self.lo.sign() < 0 {
            return Interval::poison();
        }
        let Some(lo) = sqrt_below(self.lo) else {
            return Interval::poison();
        };
        let Some(hi) = sqrt_above(self.hi) else {
            return Interval::poison();
        };
        Interval::new(lo, hi)
    }

}

// ===========================================================================
// Transcendental enclosures
// ===========================================================================
//
// These are the only place seki's trusted base does numerical analysis, so
// each one is written to make its *bound* the thing a reader checks, not its
// arithmetic.  The series themselves are evaluated with the interval
// operations above — already sound — and what has to be right is the
// remainder, stated from Lagrange's form in each case:
//
//     |R_n(x)| <= max|f⁽ⁿ⁺¹⁾| · |x|ⁿ⁺¹ / (n+1)!
//
// For `sin` and `cos` every derivative is bounded by 1, so the bound is the
// next term's magnitude outright.  For `exp` on the reduced range it is that
// times `exp(1/2) < 2`.  For `ln` the series is `atanh`, whose tail is
// bounded by a geometric factor.
//
// Anything outside the range a bound was established for is **refused**, not
// estimated: a goal that needs it keeps its `Approximate` grade, which is
// the honest answer and the one that cannot be wrong.

/// Terms of a Taylor series before the remainder takes over.  Well past the
/// point where the bounds below are microscopic, and cheap: each term is one
/// multiply and one divide.
const TAYLOR_TERMS: u32 = 40;

/// How large an argument `sin` and `cos` accept.  Beyond this the Lagrange
/// bound stops being small — argument reduction modulo a *bracketed* π would
/// widen with the quotient — so the answer is no answer.
const MAX_TRIG_ARG: i128 = 8;

/// How many halvings `exp` may use to bring its argument into range.  Each
/// one is undone by a squaring, which roughly doubles the relative width, so
/// this also bounds how much precision the reduction costs.
const MAX_EXP_HALVINGS: u32 = 16;

impl Interval {
    /// The largest `|v|` for `v` in this enclosure.
    fn magnitude(self) -> Rat {
        let a = self.lo.neg();
        if a.sub(self.hi).sign() > 0 {
            a
        } else {
            self.hi
        }
    }


    /// `exp` of an enclosure.
    ///
    /// `exp` is increasing, so the enclosure of the image is the image of
    /// the endpoints — no need to reason about what the series does in
    /// between.
    pub fn exp(self) -> Interval {
        if self.is_poison() {
            return Interval::poison();
        }
        let (Some(lo), Some(hi)) = (exp_at(self.lo), exp_at(self.hi)) else {
            return Interval::poison();
        };
        Interval::new(lo.lo, hi.hi)
    }

    /// `ln` of an enclosure, which must lie strictly above zero.
    ///
    /// Increasing, so again the endpoints settle it.
    pub fn ln(self) -> Interval {
        if self.is_poison() || self.lo.sign() <= 0 {
            return Interval::poison();
        }
        let (Some(lo), Some(hi)) = (ln_at(self.lo), ln_at(self.hi)) else {
            return Interval::poison();
        };
        Interval::new(lo.lo, hi.hi)
    }

    /// `sin` of an enclosure.
    ///
    /// Not monotone, so the endpoints say nothing on their own.  The series
    /// is evaluated *on the interval itself* instead, which handles a turning
    /// point inside the range by overestimating rather than by missing it.
    /// Intersecting with `[-1, 1]` costs nothing and is always valid.
    pub fn sin(self) -> Interval {
        self.trig(true)
    }

    pub fn cos(self) -> Interval {
        self.trig(false)
    }

    fn trig(self, is_sin: bool) -> Interval {
        if self.is_poison() {
            return Interval::poison();
        }
        let m = self.magnitude();
        if m.sub(Rat::from_int(MAX_TRIG_ARG)).sign() > 0 {
            return Interval::poison();
        }
        // Σ over the odd (sin) or even (cos) powers, built term by term so
        // no factorial is ever formed: t_{k+1} = t_k · x / (k+1).
        let mut term = if is_sin { self } else { Interval::from_int(1) };
        let mut acc = term;
        let mut k: u32 = if is_sin { 1 } else { 0 };
        let mut sign = -1i32;
        while k + 2 <= TAYLOR_TERMS {
            // Advance two orders: x²/((k+1)(k+2)).
            term = term.mul(self).mul(self);
            term = term.div(Interval::from_int(((k + 1) * (k + 2)) as i128));
            if term.is_poison() {
                return Interval::poison();
            }
            acc = if sign < 0 { acc.sub(term) } else { acc.add(term) };
            sign = -sign;
            k += 2;
        }
        // Lagrange: every derivative of sin and cos is bounded by 1, so the
        // tail is at most the next term's magnitude.
        let Some(bound) = power_over_factorial(m, k + 1) else {
            return Interval::poison();
        };
        let widened = Interval::new(acc.lo.sub(bound), acc.hi.add(bound));
        // `sin` and `cos` never leave [-1, 1]; clipping can only tighten.
        clamp_unit(widened)
    }
}

/// `exp(t)` for one rational, as an enclosure.
fn exp_at(t: Rat) -> Option<Interval> {
    if t.is_poison() {
        return None;
    }
    // Halve until |u| <= 1/2, where the remainder bound below is valid and
    // small; each halving is undone by one squaring at the end.
    let half = Rat::new(1, 2);
    let mut u = t;
    let mut halvings = 0u32;
    while u.magnitude_rat().sub(half).sign() > 0 {
        u = u.div(Rat::from_int(2))?;
        halvings += 1;
        if halvings > MAX_EXP_HALVINGS {
            return None;
        }
    }
    let x = Interval::exact(u);
    let mut term = Interval::from_int(1);
    let mut acc = term;
    for k in 1..=TAYLOR_TERMS {
        term = term.mul(x).div(Interval::from_int(k as i128));
        if term.is_poison() {
            return None;
        }
        acc = acc.add(term);
    }
    // Lagrange on [-1/2, 1/2]: |f⁽ⁿ⁺¹⁾(ξ)| = exp(ξ) <= exp(1/2) < 2.
    let bound = power_over_factorial(u.magnitude_rat(), TAYLOR_TERMS + 1)?
        .mul(Rat::from_int(2));
    let mut out = Interval::new(acc.lo.sub(bound), acc.hi.add(bound));
    // exp is positive; a lower end that rounding pushed below zero is not
    // wrong, but clipping it keeps later divisions well defined.
    if out.lo.sign() < 0 {
        out = Interval::new(Rat::ZERO, out.hi);
    }
    for _ in 0..halvings {
        out = out.mul(out);
        if out.is_poison() {
            return None;
        }
    }
    Some(out)
}

/// `ln(x)` for one positive rational, as an enclosure.
fn ln_at(x: Rat) -> Option<Interval> {
    if x.is_poison() || x.sign() <= 0 {
        return None;
    }
    // x = m · 2^k with m in [1, 2), so ln x = ln m + k·ln 2.  Halving and
    // doubling a rational is exact, so the reduction itself loses nothing.
    let two = Rat::from_int(2);
    let mut m = x;
    let mut k: i128 = 0;
    while m.sub(two).sign() >= 0 {
        m = m.div(two)?;
        k += 1;
        if k > 400 {
            return None;
        }
    }
    while m.sub(Rat::ONE).sign() < 0 {
        m = m.mul(two);
        k -= 1;
        if k < -400 {
            return None;
        }
    }
    // ln m = 2·atanh(z) with z = (m-1)/(m+1), and m in [1,2) gives
    // 0 <= z < 1/3.
    let z = m.sub(Rat::ONE).div(m.add(Rat::ONE))?;
    let zi = Interval::exact(z);
    let z2 = zi.mul(zi);
    let mut power = zi;
    let mut acc = zi;
    let mut n: u32 = 1;
    while n + 2 <= TAYLOR_TERMS {
        power = power.mul(z2);
        acc = acc.add(power.div(Interval::from_int((n + 2) as i128)));
        if acc.is_poison() {
            return None;
        }
        n += 2;
    }
    // Tail of Σ z^(2j+1)/(2j+1) from j past the last term: bounded by
    // z^(n+2)/(n+2) · 1/(1-z²), and z < 1/3 makes 1/(1-z²) < 9/8.
    let tail = pow_upper(z, n + 2)?
        .div(Rat::from_int((n + 2) as i128))?
        .mul(Rat::new(9, 8));
    let ln_m = Interval::new(acc.lo.sub(tail), acc.hi.add(tail))
        .mul(Interval::from_int(2));
    let ln2 = Interval {
        // 0.693147180559945309…, bracketed.
        lo: Rat::new(693_147_180_559, MAX_DEN),
        hi: Rat::new(693_147_180_560, MAX_DEN),
    };
    let out = ln_m.add(ln2.mul(Interval::from_int(k)));
    (!out.is_poison()).then_some(out)
}

/// `|x|` as a rational.
impl Rat {
    fn magnitude_rat(self) -> Rat {
        if self.sign() < 0 {
            self.neg()
        } else {
            self
        }
    }
}

/// An upper bound on `x^n`.
///
/// Computed through the interval operations so the denominators stay
/// capped; their outward rounding is what makes the high end a bound and
/// not an estimate.  Exact arithmetic would be tempting and wrong: `z^42`
/// with `z = 1/3` is fine, but with a denominator from the caller's data it
/// overflows and poisons.
fn pow_upper(x: Rat, n: u32) -> Option<Rat> {
    let xi = Interval::exact(x.magnitude_rat());
    let mut acc = Interval::from_int(1);
    for _ in 0..n {
        acc = acc.mul(xi);
        if acc.is_poison() {
            return None;
        }
    }
    Some(acc.hi)
}

/// An upper bound on `|x|^n / n!`, built term by term so neither part is
/// formed on its own — `41!` alone leaves `i128` many times over, while
/// `x^n/n!` stays tiny.  Rounded outward, so the answer is a bound.
fn power_over_factorial(x: Rat, n: u32) -> Option<Rat> {
    let xi = Interval::exact(x.magnitude_rat());
    let mut acc = Interval::from_int(1);
    for k in 1..=n {
        acc = acc.mul(xi).div(Interval::from_int(k as i128));
        if acc.is_poison() {
            return None;
        }
    }
    Some(acc.hi)
}

/// Intersect with `[-1, 1]`, which `sin` and `cos` never leave.
fn clamp_unit(i: Interval) -> Interval {
    if i.is_poison() {
        return Interval::poison();
    }
    let lo = if i.lo.sign() < 0 && i.lo.add(Rat::ONE).sign() < 0 {
        Rat::from_int(-1)
    } else {
        i.lo
    };
    let hi = if i.hi.sub(Rat::ONE).sign() > 0 {
        Rat::ONE
    } else {
        i.hi
    };
    Interval::new(lo, hi)
}

/// Marks a comparison the enclosures were too wide to settle.
///
/// The evaluator reacts to this one error specifically: an `if` whose
/// condition cannot be decided is evaluated down *both* branches and the
/// results are hulled, which is sound because the real value takes one of
/// them.  Reacting to any error that way would not be — an unbound name
/// must stay a failure, not become a hull.
pub const UNDECIDED: &str = "enclosures do not settle";

/// The smallest enclosure containing both, for an `if` whose condition the
/// enclosures did not settle.
pub fn hull(a: Interval, b: Interval) -> Interval {
    if a.is_poison() || b.is_poison() {
        return Interval::poison();
    }
    let lo = if a.lo.sub(b.lo).sign() <= 0 { a.lo } else { b.lo };
    let hi = if a.hi.sub(b.hi).sign() >= 0 { a.hi } else { b.hi };
    Interval::new(lo, hi)
}

/// The greatest integer not above `r`, when it fits in `i64`.
pub fn floor_of(r: Rat) -> Option<i64> {
    if r.is_poison() {
        return None;
    }
    i64::try_from(r.num.div_euclid(r.den)).ok()
}

/// How many times an endpoint may be nudged outward before giving up.
const NUDGE_LIMIT: u32 = 200;

/// One part in `MAX_DEN` of relative slack, the amount an endpoint moves per
/// nudge.
fn shrink_factor() -> Rat {
    Rat::new(MAX_DEN - 1, MAX_DEN)
}

fn grow_factor() -> Rat {
    Rat::new(MAX_DEN + 1, MAX_DEN)
}

/// The largest rational this finds with `r·r <= x`.
fn sqrt_below(x: Rat) -> Option<Rat> {
    if x.sign() <= 0 {
        return Some(Rat::ZERO);
    }
    let mut r = round_down(estimate_sqrt(x)?, MAX_DEN);
    for _ in 0..NUDGE_LIMIT {
        if r.sign() < 0 {
            return Some(Rat::ZERO);
        }
        let sq = r.mul(r);
        if !sq.is_poison() && sq.sub(x).sign() <= 0 {
            return Some(r);
        }
        r = round_down(r.mul(shrink_factor()), MAX_DEN);
        if r.is_poison() {
            return None;
        }
    }
    None
}

/// The smallest rational this finds with `r·r >= x`.
fn sqrt_above(x: Rat) -> Option<Rat> {
    if x.sign() <= 0 {
        return Some(Rat::ZERO);
    }
    let mut r = round_up(estimate_sqrt(x)?, MAX_DEN);
    for _ in 0..NUDGE_LIMIT {
        let sq = r.mul(r);
        if !sq.is_poison() && sq.sub(x).sign() >= 0 {
            return Some(r);
        }
        r = round_up(r.mul(grow_factor()), MAX_DEN);
        if r.is_poison() {
            return None;
        }
    }
    None
}

/// A starting point for the search.  Only its *speed* matters: both callers
/// verify what they end up with.
fn estimate_sqrt(x: Rat) -> Option<Rat> {
    let v = (x.num as f64) / (x.den as f64);
    if !v.is_finite() || v < 0.0 {
        return None;
    }
    let s = v.sqrt();
    if !s.is_finite() {
        return None;
    }
    let scaled = (s * MAX_DEN as f64).round();
    if !scaled.is_finite() || scaled.abs() > i128::MAX as f64 {
        return None;
    }
    Some(Rat::new(scaled as i128, MAX_DEN))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i128, d: i128) -> Rat {
        Rat::new(n, d)
    }

    fn contains(i: Interval, v: f64) -> bool {
        let lo = i.lo.num as f64 / i.lo.den as f64;
        let hi = i.hi.num as f64 / i.hi.den as f64;
        lo <= v && v <= hi
    }

    #[test]
    fn arithmetic_encloses_the_answer() {
        let a = Interval::exact(r(1, 10));
        let b = Interval::exact(r(2, 10));
        let sum = a.add(b);
        assert!(contains(sum, 0.3));
        assert!(sum.is_point(), "exact rationals need no width: {}", sum);
        assert!(contains(a.mul(b), 0.02));
        assert!(contains(a.sub(b), -0.1));
        assert!(contains(b.div(a), 2.0));
    }

    #[test]
    fn a_divisor_that_straddles_zero_has_no_quotient() {
        let num = Interval::exact(Rat::ONE);
        let den = Interval::new(r(-1, 2), r(1, 2));
        assert!(num.div(den).is_poison());
    }

    #[test]
    fn comparisons_answer_only_when_settled() {
        let a = Interval::new(r(0, 1), r(1, 1));
        let b = Interval::new(r(2, 1), r(3, 1));
        assert_eq!(a.lt(b), Some(true));
        assert_eq!(b.lt(a), Some(false));
        // Overlapping: no verdict either way, which the kernel reads as
        // "not settled", never as a pass.
        let c = Interval::new(r(1, 2), r(3, 2));
        assert_eq!(a.lt(c), None);
        assert_eq!(a.eq(c), None);
        // Disjoint enclosures do settle inequality.
        assert_eq!(a.eq(b), Some(false));
    }

    #[test]
    fn the_square_root_endpoints_are_verified_by_squaring() {
        for n in [2i128, 3, 5, 10, 1000, 999983] {
            let x = Rat::from_int(n);
            let s = Interval::exact(x).sqrt();
            assert!(!s.is_poison(), "sqrt {} poisoned", n);
            assert!(
                s.lo.mul(s.lo).sub(x).sign() <= 0,
                "lower endpoint of sqrt {} is too big",
                n
            );
            assert!(
                s.hi.mul(s.hi).sub(x).sign() >= 0,
                "upper endpoint of sqrt {} is too small",
                n
            );
            assert!(contains(s, (n as f64).sqrt()));
        }
    }

    #[test]
    fn the_square_root_of_a_fraction_is_enclosed() {
        let x = r(1, 4);
        let s = Interval::exact(x).sqrt();
        assert!(contains(s, 0.5));
        assert!(s.lo.mul(s.lo).sub(x).sign() <= 0);
        assert!(s.hi.mul(s.hi).sub(x).sign() >= 0);
    }

    #[test]
    fn rounding_only_ever_widens() {
        // A third has no finite decimal, so rounding must move the ends
        // apart rather than pick one of them.
        let third = Interval::exact(r(1, 3));
        assert!(third.lo.sub(r(1, 3)).sign() <= 0);
        assert!(third.hi.sub(r(1, 3)).sign() >= 0);
    }

    fn approx(i: Interval, v: f64, tol: f64) -> bool {
        let lo = i.lo.num as f64 / i.lo.den as f64;
        let hi = i.hi.num as f64 / i.hi.den as f64;
        lo <= v && v <= hi && (hi - lo) < tol
    }

    #[test]
    fn exp_encloses_known_values() {
        for (x, want) in [(0.0, 1.0), (1.0, std::f64::consts::E), (-1.0, 1.0 / std::f64::consts::E), (2.5, 12.182493960703473)] {
            let r = crate::algebra::decimal_to_rat(x).unwrap();
            let e = Interval::exact(r).exp();
            assert!(!e.is_poison(), "exp {} poisoned", x);
            assert!(approx(e, want, 1e-7), "exp {} = {} (want {})", x, e, want);
        }
    }

    #[test]
    fn ln_encloses_known_values() {
        for (x, want) in [(1.0, 0.0), (2.0, std::f64::consts::LN_2), (0.5, -std::f64::consts::LN_2), (10.0, 2.302585092994046)] {
            let r = crate::algebra::decimal_to_rat(x).unwrap();
            let l = Interval::exact(r).ln();
            assert!(!l.is_poison(), "ln {} poisoned", x);
            assert!(approx(l, want, 1e-9), "ln {} = {} (want {})", x, l, want);
        }
    }

    #[test]
    fn sin_and_cos_enclose_known_values() {
        let pi = std::f64::consts::PI;
        for (x, s, c) in [
            (0.0, 0.0, 1.0),
            (0.5, 0.479425538604203, 0.8775825618903728),
            (1.5707963267948966, 1.0, 0.0),
            (3.141592653589793, 0.0, -1.0),
            (-2.0, -0.9092974268256817, -0.4161468365471424),
        ] {
            let _ = pi;
            let r = crate::algebra::decimal_to_rat(x).unwrap();
            let si = Interval::exact(r).sin();
            let ci = Interval::exact(r).cos();
            assert!(approx(si, s, 1e-9), "sin {} = {} (want {})", x, si, s);
            assert!(approx(ci, c, 1e-9), "cos {} = {} (want {})", x, ci, c);
        }
    }

    #[test]
    fn the_enclosures_satisfy_the_identities_that_define_them() {
        // Cross-checks that do not depend on any reference value: if a
        // bound were wrong, these would come apart.
        let one = Interval::from_int(1);
        for x in [0.3f64, 1.0, -1.25, 2.0] {
            let r = crate::algebra::decimal_to_rat(x).unwrap();
            let i = Interval::exact(r);
            // sin² + cos² = 1
            let s = i.sin();
            let c = i.cos();
            let sum = s.mul(s).add(c.mul(c));
            assert!(
                sum.lo.sub(one.hi).sign() <= 0 && sum.hi.sub(one.lo).sign() >= 0,
                "sin²+cos² at {} came out {}",
                x,
                sum
            );
            // ln(exp x) = x
            let back = i.exp().ln();
            assert!(
                back.lo.sub(r).sign() <= 0 && back.hi.sub(r).sign() >= 0,
                "ln(exp {}) came out {}",
                x,
                back
            );
        }
        // exp(a+b) = exp a · exp b
        let a = Interval::exact(Rat::new(3, 4));
        let b = Interval::exact(Rat::new(5, 4));
        let lhs = a.add(b).exp();
        let rhs = a.exp().mul(b.exp());
        assert!(
            lhs.lo.sub(rhs.hi).sign() <= 0 && lhs.hi.sub(rhs.lo).sign() >= 0,
            "exp(a+b) = {} but exp a · exp b = {}",
            lhs,
            rhs
        );
    }

    #[test]
    fn an_argument_outside_the_bounded_range_is_refused() {
        // Beyond where the Lagrange bound stays small, the answer is no
        // answer rather than an estimate.
        assert!(Interval::exact(Rat::from_int(20)).sin().is_poison());
        assert!(Interval::exact(Rat::from_int(-20)).cos().is_poison());
        // `ln` of something that may be zero or negative has no value.
        assert!(Interval::exact(Rat::ZERO).ln().is_poison());
        assert!(Interval::new(r(-1, 1), r(1, 1)).ln().is_poison());
    }

    #[test]
    fn a_turning_point_inside_the_range_is_not_missed() {
        // `sin` peaks at π/2; an enclosure spanning it must reach 1, which
        // taking the endpoints alone would miss (sin 1.4 and sin 1.8 are
        // both below 1).
        let band = Interval::new(r(14, 10), r(18, 10));
        let s = band.sin();
        assert!(!s.is_poison());
        assert!(
            s.hi.sub(Rat::new(9999, 10000)).sign() >= 0,
            "the peak was missed: {}",
            s
        );
    }

    #[test]
    fn a_long_computation_stays_inside_i128() {
        // Repeated division is what overflows exact rationals; the cap is
        // what keeps it bounded.
        let mut acc = Interval::from_int(1);
        let third = Interval::exact(r(1, 3));
        for _ in 0..500 {
            acc = acc.add(third).mul(Interval::exact(r(7, 11)));
        }
        assert!(!acc.is_poison(), "500 operations poisoned: {}", acc);
        assert!(acc.lo.den <= MAX_DEN && acc.hi.den <= MAX_DEN);
    }
}

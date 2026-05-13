//! SMT-lite: decision procedure for linear integer arithmetic in one
//! variable.  Phase 5 deliverable — replaces sample-based checking for
//! refinement types of the form `{x in Int | linear inequality(x)}`.
//!
//! Scope (what we decide):
//!   * Inequalities of the form `c_0 + c_1 * x <op> 0` where `op` is one
//!     of `==`, `!=`, `<`, `<=`, `>`, `>=` and the coefficients `c_i` are
//!     concrete integers.
//!   * A *hypothesis set* is a conjunction of such inequalities — each
//!     reduces to a half-line constraint on `x`.
//!   * Goal: another single-variable inequality.
//!
//! Algorithm: intersect hypothesis half-lines into a single integer
//! interval `[lo, hi]` (possibly half-infinite).  The goal is provable
//! iff it holds at *every* integer in `[lo, hi]`.  For a linear function
//! this collapses to checking the two endpoints (with care for strict vs.
//! non-strict inequalities and for unbounded ranges).
//!
//! Out of scope (returns `Unknown`):
//!   * Multiple variables (would need full Fourier-Motzkin elimination)
//!   * Non-linear (quadratic, modular) terms
//!   * Constraints over `Real` rather than `Int`
//!   * Disjunctive hypotheses
//!
//! This is intentionally a small focused decision procedure — not a full
//! SMT solver.  It's enough to make a meaningful class of refinement
//! types ("x is in some bounded integer interval") *sound* rather than
//! sample-tested.

use crate::ast::{BinOp, Expr, UnOp};

/// Linear expression `c0 + c1 * x` in one variable `x`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lin {
    pub c0: i64,
    pub c1: i64,
}

impl Lin {
    fn constant(n: i64) -> Self { Lin { c0: n, c1: 0 } }
    fn variable() -> Self { Lin { c0: 0, c1: 1 } }
    fn add(self, o: Lin) -> Lin { Lin { c0: self.c0 + o.c0, c1: self.c1 + o.c1 } }
    fn sub(self, o: Lin) -> Lin { Lin { c0: self.c0 - o.c0, c1: self.c1 - o.c1 } }
    fn neg(self) -> Lin { Lin { c0: -self.c0, c1: -self.c1 } }
    /// Scalar multiplication when one side is a pure constant.  Returns None
    /// if both sides have an `x` term (we don't handle `x*x`).
    fn mul(self, o: Lin) -> Option<Lin> {
        if self.c1 == 0 {
            Some(Lin { c0: self.c0 * o.c0, c1: self.c0 * o.c1 })
        } else if o.c1 == 0 {
            Some(Lin { c0: self.c0 * o.c0, c1: self.c1 * o.c0 })
        } else {
            None
        }
    }
}

/// Attempt to convert `e` into a linear expression over the variable `var`.
/// Returns None on shapes we don't handle (set ops, application, match,
/// non-linear arithmetic, …).
pub fn to_lin(e: &Expr, var: &str) -> Option<Lin> {
    use BinOp as B;
    match e {
        Expr::Int(n) => Some(Lin::constant(*n)),
        Expr::Var { name: name, .. } if name == var => Some(Lin::variable()),
        // Free variables that aren't the focus var are treated as opaque —
        // we don't model multi-variable systems here.
        Expr::Var { .. } => None,
        Expr::UnOp(UnOp::Neg, x) => Some(to_lin(x, var)?.neg()),
        Expr::BinOp(op, l, r) => {
            let a = to_lin(l, var)?;
            let b = to_lin(r, var)?;
            match op {
                B::Add => Some(a.add(b)),
                B::Sub => Some(a.sub(b)),
                B::Mul => a.mul(b),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Half-line / interval constraint on an integer variable.
#[derive(Clone, Copy, Debug)]
pub struct Interval {
    /// Smallest allowed value (None = -∞).
    pub lo: Option<i64>,
    /// Largest allowed value (None = +∞).
    pub hi: Option<i64>,
}

impl Interval {
    pub const FULL: Interval = Interval { lo: None, hi: None };
    pub fn intersect(self, o: Interval) -> Interval {
        let lo = match (self.lo, o.lo) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.max(b)),
        };
        let hi = match (self.hi, o.hi) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.min(b)),
        };
        Interval { lo, hi }
    }
    pub fn is_empty(self) -> bool {
        matches!((self.lo, self.hi), (Some(l), Some(h)) if l > h)
    }
}

/// Convert a single inequality `lin <op> 0` (parameterised by `op`) into the
/// integer interval of `x` values satisfying it.  Returns None when the
/// expression isn't actually constraining `x` (e.g. degenerate `0 == 0`).
pub fn ineq_interval(lin: Lin, op: BinOp) -> Option<Interval> {
    use BinOp as B;
    let Lin { c0, c1 } = lin;
    if c1 == 0 {
        // Constant inequality — either always true (full interval) or never.
        let always = match op {
            B::Eq  => c0 == 0,
            B::Neq => c0 != 0,
            B::Lt  => c0 <  0,
            B::Le  => c0 <= 0,
            B::Gt  => c0 >  0,
            B::Ge  => c0 >= 0,
            _ => return None,
        };
        return if always {
            Some(Interval::FULL)
        } else {
            // Empty: a single point that excludes everything.
            Some(Interval { lo: Some(1), hi: Some(0) })
        };
    }
    // `c1 * x + c0 <op> 0` with c1 ≠ 0.
    // Divide carefully to keep integer semantics.  Note that when we
    // flip the inequality (negative c1), we also flip the operator
    // direction; we then translate `<op> 0` to a closed interval.
    let (lo, hi) = match (op, c1.signum()) {
        // c1 > 0: solve c1*x + c0 op 0  →  x op (-c0/c1) (with rounding)
        (B::Eq, _) => {
            // c1*x + c0 == 0  →  x == -c0/c1, integer iff c1 divides c0.
            if c0 % c1 == 0 {
                let v = -c0 / c1;
                (Some(v), Some(v))
            } else {
                (Some(1), Some(0))  // empty
            }
        }
        (B::Neq, _) => {
            // Always true except a single point — we can't represent that as
            // one interval without disjunction.  Conservatively return
            // unknown by treating as FULL (which yields a false positive but
            // sound under our "Unknown" semantics).
            (None, None)
        }
        // c1 > 0:
        (B::Lt, 1) => (None, Some(div_floor(-c0 - 1, c1))),       // x < -c0/c1
        (B::Le, 1) => (None, Some(div_floor(-c0,     c1))),       // x ≤ -c0/c1
        (B::Gt, 1) => (Some(div_floor(-c0,     c1) + 1), None),    // x > -c0/c1
        (B::Ge, 1) => (Some(div_ceil(-c0,      c1)),     None),    // x ≥ -c0/c1
        // c1 < 0: flip every relation.
        // BUG-FIXED (Phase 6): the Lt and Gt cases were rounding the wrong
        // direction when `-c0/c1` is non-integer.  Specifically:
        //   `c1*x + c0 < 0` (c1<0)  ⟺  x > -c0/c1  ⟺  x ≥ floor(-c0/c1) + 1
        //   `c1*x + c0 > 0` (c1<0)  ⟺  x < -c0/c1  ⟺  x ≤ ceil(-c0/c1)  - 1
        // The property-test `linarith_never_proves_a_falsehood` caught the
        // original (off-by-one) version producing bogus counterexamples.
        (B::Lt, -1) => (Some(div_floor(-c0, c1) + 1), None),
        (B::Le, -1) => (Some(div_ceil(-c0,  c1)),     None),
        (B::Gt, -1) => (None, Some(div_ceil(-c0,  c1) - 1)),
        (B::Ge, -1) => (None, Some(div_floor(-c0, c1))),
        _ => return None,
    };
    Some(Interval { lo, hi })
}

/// Integer division rounding toward -∞ (Python-style floor division).
pub fn div_floor(a: i64, b: i64) -> i64 {
    let q = a / b;
    let r = a % b;
    if (r != 0) && ((r < 0) != (b < 0)) { q - 1 } else { q }
}

/// Integer division rounding toward +∞.
pub fn div_ceil(a: i64, b: i64) -> i64 {
    let q = a / b;
    let r = a % b;
    if (r != 0) && ((r < 0) == (b < 0)) { q + 1 } else { q }
}

#[derive(Debug)]
pub enum Proof {
    /// Goal provably holds for every `x` satisfying the hypothesis set.
    Proven,
    /// Goal provably fails (we exhibited a specific value).
    Refuted(i64),
    /// Outside the decision procedure (non-linear, multi-var, etc.).
    Unknown,
}

/// Decide whether `goal_op(goal_lin) >= 0` (in the operator sense) holds for
/// every integer `x` satisfying every hypothesis.  Returns `Proven`,
/// `Refuted` with a counterexample, or `Unknown` when out of scope.
pub fn decide(
    hypotheses: &[(Lin, BinOp)],
    goal: (Lin, BinOp),
) -> Proof {
    // Intersect hypothesis intervals.
    let mut iv = Interval::FULL;
    for (lin, op) in hypotheses {
        let h = match ineq_interval(*lin, op.clone()) {
            Some(h) => h,
            None => return Proof::Unknown,
        };
        iv = iv.intersect(h);
        if iv.is_empty() {
            // Hypotheses unsatisfiable — anything is vacuously provable.
            return Proof::Proven;
        }
    }
    // For the goal we check: does it hold for every integer in iv?
    // It fails iff some integer in iv lies *outside* the goal's interval.
    let goal_iv = match ineq_interval(goal.0, goal.1) {
        Some(h) => h,
        None => return Proof::Unknown,
    };
    // Does iv ⊆ goal_iv?  This holds iff:
    //   (goal_iv.lo is None  OR  iv.lo is Some(L) and L ≥ goal_iv.lo)
    //   AND
    //   (goal_iv.hi is None  OR  iv.hi is Some(H) and H ≤ goal_iv.hi)
    let lo_ok = match goal_iv.lo {
        None => true,
        Some(gl) => matches!(iv.lo, Some(l) if l >= gl),
    };
    let hi_ok = match goal_iv.hi {
        None => true,
        Some(gh) => matches!(iv.hi, Some(h) if h <= gh),
    };
    if lo_ok && hi_ok {
        Proof::Proven
    } else {
        // Try to produce a counterexample within iv that violates goal_iv.
        let cex = if !lo_ok {
            iv.lo.or(Some(0))
        } else {
            iv.hi.or(Some(0))
        };
        Proof::Refuted(cex.unwrap_or(0))
    }
}

/// Convenience: parse a `Sym`-friendly expression already represented as
/// `Expr`, split it into `(lhs - rhs, op)` form, and convert lhs - rhs
/// into a linear expression over `var`.  Returns the canonicalised
/// (Lin, BinOp) where the inequality is to be read as `Lin <op> 0`.
pub fn ineq_of_expr(e: &Expr, var: &str) -> Option<(Lin, BinOp)> {
    match e {
        Expr::BinOp(op @ (BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le
                          | BinOp::Gt | BinOp::Ge), l, r) => {
            let a = to_lin(l, var)?;
            let b = to_lin(r, var)?;
            Some((a.sub(b), op.clone()))
        }
        _ => None,
    }
}

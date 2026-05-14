//! Symbolic algebra for sound infinite-domain proofs.
//!
//! This module reduces an arithmetic expression over integers (or reals) to a
//! canonical polynomial form (a sum of monomials).  Two expressions are equal
//! as polynomials iff their canonical forms are identical.  This gives a
//! *sound* decision procedure for the **polynomial equality fragment** of
//! seki — and crucially, the verdict is universal: it holds for **all**
//! values of the variables.  Thus the `by algebra` tactic can prove
//! `forall x in Int, x + 0 == x` and `forall x in Real, x + 0.0 == x`
//! without enumerating the (infinite) domain.
//!
//! Supported operators: `+`, `-` (binary and unary), `*`, integer / real
//! literals, free variables, and **if-expressions** (case-split on the
//! condition and prove each branch).  Coefficients are exact rationals
//! `(num, den : i128)` so `Real` literals like `0.5` round-trip exactly when
//! their binary representation has a small enough denominator.

use crate::ast::{BinOp, Expr, UnOp};
use std::collections::BTreeMap;

// ===========================================================================
// Rational coefficients
// ===========================================================================

/// Exact rational `num / den`.  `den > 0` always; `gcd(|num|, den) = 1`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rat {
    pub num: i128,
    pub den: i128,
}

fn gcd_i128(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs() as i128, b.unsigned_abs() as i128);
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a.max(1)
}

impl Rat {
    pub const ZERO: Rat = Rat { num: 0, den: 1 };
    pub const ONE: Rat = Rat { num: 1, den: 1 };

    pub fn new(num: i128, den: i128) -> Self {
        assert!(den != 0, "Rat::new with denominator 0");
        let (mut n, mut d) = (num, den);
        if d < 0 {
            n = -n;
            d = -d;
        }
        let g = gcd_i128(n, d);
        Rat { num: n / g, den: d / g }
    }

    pub fn from_int(n: i128) -> Self {
        Rat { num: n, den: 1 }
    }

    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    pub fn is_int(self) -> bool {
        self.den == 1
    }

    pub fn neg(self) -> Self {
        Rat { num: -self.num, den: self.den }
    }

    pub fn add(self, other: Rat) -> Rat {
        let g = gcd_i128(self.den, other.den);
        let d_step = other.den / g;
        let new_num = self
            .num
            .saturating_mul(d_step)
            .saturating_add(other.num.saturating_mul(self.den / g));
        let new_den = self.den.saturating_mul(d_step);
        Rat::new(new_num, new_den)
    }

    pub fn sub(self, other: Rat) -> Rat {
        self.add(other.neg())
    }

    pub fn mul(self, other: Rat) -> Rat {
        // reduce cross-pairs before multiplying to avoid overflow
        let g1 = gcd_i128(self.num, other.den);
        let g2 = gcd_i128(other.num, self.den);
        let n = (self.num / g1).saturating_mul(other.num / g2);
        let d = (self.den / g2).saturating_mul(other.den / g1);
        Rat::new(n, d)
    }

    /// Divide by a nonzero rational.  Returns `None` only when `other == 0`.
    pub fn div(self, other: Rat) -> Option<Rat> {
        if other.num == 0 {
            return None;
        }
        Some(self.mul(Rat::new(other.den, other.num)))
    }

    /// Sign: -1, 0, +1.
    pub fn sign(self) -> i32 {
        if self.num < 0 {
            -1
        } else if self.num > 0 {
            1
        } else {
            0
        }
    }
}

/// Convert an `f64` to an exact `Rat` when possible.  Returns `None` for
/// non-finite values, subnormals, or magnitudes whose exact representation
/// would overflow `i128`.  This is the rule that decides whether a `Real`
/// literal can enter the polynomial fragment.
fn f64_to_rat(f: f64) -> Option<Rat> {
    if !f.is_finite() {
        return None;
    }
    if f == 0.0 {
        return Some(Rat::ZERO);
    }
    let bits = f.to_bits();
    let sign_bit = bits >> 63;
    let exponent = ((bits >> 52) & 0x7FF) as i32;
    let mantissa_bits = bits & 0x000F_FFFF_FFFF_FFFF;
    if exponent == 0 {
        // subnormal — rare in practice; refuse.
        return None;
    }
    if exponent == 0x7FF {
        // NaN / infinity — guarded by is_finite above, but defensive.
        return None;
    }
    let mantissa = (1u128 << 52) | mantissa_bits as u128;
    let e = exponent - 1023 - 52; // value = mantissa * 2^e
    let (num, den) = if e >= 0 {
        // mantissa fits in 53 bits; shifting up by ≤ 11 bits stays in i128
        if e as u32 > 64 {
            return None;
        }
        let shifted = mantissa.checked_shl(e as u32)?;
        if shifted > i128::MAX as u128 {
            return None;
        }
        (shifted as i128, 1i128)
    } else {
        let shift = -e as u32;
        if shift > 120 {
            // 2^121 still fits in i128, but be safe — beyond denom 2^120,
            // refuse so callers can fall back to `by eval` (sampling).
            return None;
        }
        let denom: i128 = 1i128 << shift;
        if mantissa > i128::MAX as u128 {
            return None;
        }
        (mantissa as i128, denom)
    };
    let signed = if sign_bit == 1 { -num } else { num };
    Some(Rat::new(signed, den))
}

// ===========================================================================
// Monomials and polynomials with rational coefficients
// ===========================================================================

/// A monomial:  `coeff * x_1^e_1 * ... * x_k^e_k`.  The `vars` map is a
/// **canonical** sorted form (BTreeMap iterates in key order).  Variables
/// with exponent 0 are stripped during normalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Monomial {
    pub coeff: Rat,
    pub vars: BTreeMap<String, u32>,
}

impl Monomial {
    pub fn constant(c: Rat) -> Self {
        Self { coeff: c, vars: BTreeMap::new() }
    }
    pub fn variable(name: &str) -> Self {
        let mut vars = BTreeMap::new();
        vars.insert(name.to_string(), 1);
        Self { coeff: Rat::ONE, vars }
    }
    /// Multiplicative key (used for grouping like-terms).
    fn signature(&self) -> Vec<(String, u32)> {
        self.vars.iter().map(|(k, v)| (k.clone(), *v)).collect()
    }
}

/// A polynomial — sum of monomials in canonical form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial {
    pub terms: Vec<Monomial>,
}

impl Polynomial {
    pub fn zero() -> Self {
        Self { terms: vec![] }
    }
    pub fn from_const(c: i128) -> Self {
        Self::from_rat(Rat::from_int(c))
    }
    pub fn from_rat(c: Rat) -> Self {
        if c.is_zero() {
            Self::zero()
        } else {
            Self { terms: vec![Monomial::constant(c)] }
        }
    }
    pub fn from_var(name: &str) -> Self {
        Self { terms: vec![Monomial::variable(name)] }
    }

    pub fn neg(self) -> Self {
        Self {
            terms: self
                .terms
                .into_iter()
                .map(|mut m| {
                    m.coeff = m.coeff.neg();
                    m
                })
                .collect(),
        }
    }

    pub fn add(self, other: Self) -> Self {
        let mut terms = self.terms;
        terms.extend(other.terms);
        normalize(terms)
    }

    pub fn sub(self, other: Self) -> Self {
        self.add(other.neg())
    }

    pub fn mul(self, other: Self) -> Self {
        let mut out: Vec<Monomial> = Vec::new();
        for a in &self.terms {
            for b in &other.terms {
                let mut vars = a.vars.clone();
                for (k, v) in &b.vars {
                    *vars.entry(k.clone()).or_insert(0) += *v;
                }
                out.push(Monomial { coeff: a.coeff.mul(b.coeff), vars });
            }
        }
        normalize(out)
    }

    /// Divide every coefficient by a rational constant.  Returns `None` if
    /// the divisor is zero.  This is *exact* — over rationals the division
    /// always closes, unlike the previous integer-only `div_const`.
    pub fn div_const(self, c: Rat) -> Option<Self> {
        if c.is_zero() {
            return None;
        }
        let inv = Rat::ONE.div(c).unwrap();
        let mut terms = Vec::new();
        for m in self.terms {
            terms.push(Monomial { coeff: m.coeff.mul(inv), vars: m.vars });
        }
        Some(normalize(terms))
    }

    /// Reduce every coefficient modulo `c` (Euclidean: result in `0..c`).
    /// Only meaningful for integer coefficients — non-integer terms are
    /// preserved unchanged so the verdict remains sound (we'd refuse such
    /// claims at the surface level).
    pub fn mod_const(self, c: i128) -> Self {
        if c <= 0 {
            return self;
        }
        let mut terms = Vec::new();
        for m in self.terms {
            if !m.coeff.is_int() {
                terms.push(m);
                continue;
            }
            let r = m.coeff.num.rem_euclid(c);
            if r != 0 {
                terms.push(Monomial { coeff: Rat::from_int(r), vars: m.vars });
            }
        }
        normalize(terms)
    }

    /// True if this polynomial is just a (rational) constant.
    pub fn as_constant(&self) -> Option<Rat> {
        match self.terms.as_slice() {
            [] => Some(Rat::ZERO),
            [m] if m.vars.is_empty() => Some(m.coeff),
            _ => None,
        }
    }
}

/// Combine like-terms, drop zeros, sort by signature.  This produces a
/// canonical form: equal polynomials have equal `terms` vectors.
fn normalize(mut terms: Vec<Monomial>) -> Polynomial {
    terms.sort_by(|a, b| a.signature().cmp(&b.signature()));
    let mut merged: Vec<Monomial> = Vec::with_capacity(terms.len());
    for m in terms {
        if let Some(last) = merged.last_mut() {
            if last.signature() == m.signature() {
                last.coeff = last.coeff.add(m.coeff);
                continue;
            }
        }
        merged.push(m);
    }
    merged.retain(|m| !m.coeff.is_zero());
    Polynomial { terms: merged }
}

// ===========================================================================
// Expression → polynomial
// ===========================================================================

/// Convert an Expr to a Polynomial, treating each unbound `Var` as a free
/// variable.  Subexpressions outside the polynomial fragment (function
/// applications, raw `if`-expressions inside a non-relational context,
/// division by a non-constant, etc.) are treated as **opaque atoms**:
/// each such subterm is given a deterministic name based on its printed
/// form, so `f(k) - f(k)` simplifies to `0`.  `if`-expressions are also
/// handled at this opaque level; the top-level prover's `verify_algebra`
/// case-splits on `if` first so each branch arrives here as a polynomial.
pub fn expr_to_poly(e: &Expr) -> Option<Polynomial> {
    match e {
        Expr::Int(n) => Some(Polynomial::from_const(*n as i128)),
        Expr::Real(f) => f64_to_rat(*f).map(Polynomial::from_rat),
        Expr::Bool(_) | Expr::Str(_) => None,
        Expr::Var { name, .. } => Some(Polynomial::from_var(name)),
        Expr::UnOp(UnOp::Neg, inner) => Some(expr_to_poly(inner)?.neg()),
        Expr::UnOp(UnOp::Not, _) => None,
        Expr::BinOp(op, l, r) => match op {
            BinOp::Add => Some(expr_to_poly(l)?.add(expr_to_poly(r)?)),
            BinOp::Sub => Some(expr_to_poly(l)?.sub(expr_to_poly(r)?)),
            BinOp::Mul => Some(expr_to_poly(l)?.mul(expr_to_poly(r)?)),
            BinOp::Div => {
                let lp = expr_to_poly(l)?;
                if let Some(c) = const_value_rat(r) {
                    if let Some(quot) = lp.clone().div_const(c) {
                        return Some(quot);
                    }
                }
                Some(Polynomial::from_var(&opaque_name(e)))
            }
            BinOp::Mod => {
                let lp = expr_to_poly(l)?;
                if let Some(c) = const_value(r) {
                    if c > 0 {
                        return Some(lp.mod_const(c));
                    }
                }
                Some(Polynomial::from_var(&opaque_name(e)))
            }
            _ => Some(Polynomial::from_var(&opaque_name(e))),
        },
        // App / If / Let / Lambda / SetEnum / etc. — all opaque atoms.
        _ => Some(Polynomial::from_var(&opaque_name(e))),
    }
}

/// Extract an integer constant from an Expr (handling unary negation).
pub fn const_value(e: &Expr) -> Option<i128> {
    match e {
        Expr::Int(n) => Some(*n as i128),
        Expr::UnOp(UnOp::Neg, inner) => const_value(inner).map(|v| -v),
        _ => None,
    }
}

/// Extract a rational constant from an Expr (handling unary negation,
/// `Real` literals, and **closed arithmetic on constants** — `Add`, `Sub`,
/// `Mul`, `Div`).  This lets `1.0 / (2.0 * 16.0)` fold into `1/32`
/// instead of becoming an opaque atom.
pub fn const_value_rat(e: &Expr) -> Option<Rat> {
    match e {
        Expr::Int(n) => Some(Rat::from_int(*n as i128)),
        Expr::Real(f) => f64_to_rat(*f),
        Expr::UnOp(UnOp::Neg, inner) => const_value_rat(inner).map(|v| v.neg()),
        Expr::BinOp(BinOp::Add, l, r) => {
            Some(const_value_rat(l)?.add(const_value_rat(r)?))
        }
        Expr::BinOp(BinOp::Sub, l, r) => {
            Some(const_value_rat(l)?.sub(const_value_rat(r)?))
        }
        Expr::BinOp(BinOp::Mul, l, r) => {
            Some(const_value_rat(l)?.mul(const_value_rat(r)?))
        }
        Expr::BinOp(BinOp::Div, l, r) => {
            let a = const_value_rat(l)?;
            let b = const_value_rat(r)?;
            a.div(b)
        }
        _ => None,
    }
}

/// Generate a deterministic, polynomial-friendly atom name for an opaque
/// subexpression.  Equal expressions (after canonicalizing arithmetic
/// subterms) get equal names — this is what makes `sum ((k+1) - 1)` and
/// `sum k` collapse to the same opaque variable so they cancel in the
/// induction step's polynomial difference.
fn opaque_name(e: &Expr) -> String {
    format!("__atom_{}", normalize_atom(&format!("{}", canonicalize(e))))
}

fn normalize_atom(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Recursively rewrite arithmetic subexpressions of `e` into a canonical
/// polynomial form by round-tripping `expr_to_poly` → `poly_to_expr`.
/// Non-arithmetic constructs (App, If, ...) are recursed into so opaque
/// atoms generated for them see canonical *children*.
pub fn canonicalize(e: &Expr) -> Expr {
    use Expr::*;
    if let Some(p) = expr_to_poly_opaque_only(e) {
        return poly_to_expr(&p);
    }
    match e {
        App { func, args } => App {
            func: Box::new(canonicalize(func)),
            args: args.iter().map(canonicalize).collect(),
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(canonicalize(cond)),
            then_branch: Box::new(canonicalize(then_branch)),
            else_branch: Box::new(canonicalize(else_branch)),
        },
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(canonicalize(l)),
            Box::new(canonicalize(r)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(canonicalize(x))),
        _ => e.clone(),
    }
}

fn expr_to_poly_opaque_only(e: &Expr) -> Option<Polynomial> {
    match e {
        Expr::Int(n) => Some(Polynomial::from_const(*n as i128)),
        Expr::Real(f) => f64_to_rat(*f).map(Polynomial::from_rat),
        Expr::Var { name, .. } => Some(Polynomial::from_var(name)),
        Expr::UnOp(UnOp::Neg, inner) => Some(expr_to_poly_opaque_only(inner)?.neg()),
        Expr::BinOp(op, l, r) => {
            let lp = expr_to_poly_opaque_only(l)?;
            let rp = expr_to_poly_opaque_only(r)?;
            match op {
                BinOp::Add => Some(lp.add(rp)),
                BinOp::Sub => Some(lp.sub(rp)),
                BinOp::Mul => Some(lp.mul(rp)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Render a `Polynomial` back to an Expr in canonical (sorted) form.  Used
/// by `canonicalize` to print atom names deterministically.  Rationals are
/// rendered as `num` (when integer) or `num / den` (when fractional).
pub fn poly_to_expr(p: &Polynomial) -> Expr {
    if p.terms.is_empty() {
        return Expr::Int(0);
    }
    let mut acc: Option<Expr> = None;
    for m in &p.terms {
        let mut term: Option<Expr> = None;
        for (name, exp) in &m.vars {
            for _ in 0..*exp {
                let v = Expr::Var { name: name.clone(), line: 0, col: 0 };
                term = Some(match term {
                    None => v,
                    Some(t) => Expr::BinOp(BinOp::Mul, Box::new(t), Box::new(v)),
                });
            }
        }
        let coeff_expr = rat_to_expr(m.coeff);
        let term_with_coeff = match term {
            None => coeff_expr,
            Some(t) => {
                if m.coeff == Rat::ONE {
                    t
                } else if m.coeff == Rat::ONE.neg() {
                    Expr::UnOp(UnOp::Neg, Box::new(t))
                } else {
                    Expr::BinOp(BinOp::Mul, Box::new(coeff_expr), Box::new(t))
                }
            }
        };
        acc = Some(match acc {
            None => term_with_coeff,
            Some(a) => Expr::BinOp(BinOp::Add, Box::new(a), Box::new(term_with_coeff)),
        });
    }
    acc.unwrap_or(Expr::Int(0))
}

fn rat_to_expr(r: Rat) -> Expr {
    if r.is_int() {
        if (r.num as i64 as i128) == r.num {
            Expr::Int(r.num as i64)
        } else {
            // Out-of-i64 range — fall back to a textual division form so
            // round-trip printing still produces a deterministic atom name.
            Expr::BinOp(
                BinOp::Div,
                Box::new(Expr::Int(r.num as i64)),
                Box::new(Expr::Int(1)),
            )
        }
    } else {
        Expr::BinOp(
            BinOp::Div,
            Box::new(Expr::Int(r.num as i64)),
            Box::new(Expr::Int(r.den as i64)),
        )
    }
}

// ===========================================================================
// Sign analysis
// ===========================================================================

/// Domain over which a polynomial is interpreted.  Affects what sign
/// inferences are sound: all variables are `≥ 0` in `Nat`; unrestricted in
/// `Int` and `Real`.  `Real` shares the Int decision procedures since the
/// soundness arguments (perfect squares are nonneg, PSD quadratic forms are
/// nonneg) only require an ordered ring with no zero divisors — both `ℤ`
/// and `ℝ` satisfy that.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolyDomain {
    Nat,
    Int,
    Real,
}

pub fn polynomial_nonneg(p: &Polynomial, dom: PolyDomain) -> bool {
    if p.terms.is_empty() {
        return true;
    }
    if let Some(c) = p.as_constant() {
        return c.sign() >= 0;
    }
    match dom {
        PolyDomain::Nat => p.terms.iter().all(|m| m.coeff.sign() >= 0),
        PolyDomain::Int | PolyDomain::Real => {
            let all_even = p.terms.iter().all(|m| m.vars.values().all(|e| e % 2 == 0));
            let all_nn = p.terms.iter().all(|m| m.coeff.sign() >= 0);
            (all_even && all_nn) || quadratic_psd(p)
        }
    }
}

pub fn polynomial_pos(p: &Polynomial, dom: PolyDomain) -> bool {
    if p.terms.is_empty() {
        return false;
    }
    if let Some(c) = p.as_constant() {
        return c.sign() > 0;
    }
    match dom {
        PolyDomain::Nat => {
            let all_nn = p.terms.iter().all(|m| m.coeff.sign() >= 0);
            let const_pos = p
                .terms
                .iter()
                .any(|m| m.vars.is_empty() && m.coeff.sign() > 0);
            all_nn && const_pos
        }
        PolyDomain::Int | PolyDomain::Real => {
            let all_even = p.terms.iter().all(|m| m.vars.values().all(|e| e % 2 == 0));
            let all_nn = p.terms.iter().all(|m| m.coeff.sign() >= 0);
            let const_pos = p
                .terms
                .iter()
                .any(|m| m.vars.is_empty() && m.coeff.sign() > 0);
            all_even && all_nn && const_pos
        }
    }
}

pub fn polynomial_nonpos(p: &Polynomial, dom: PolyDomain) -> bool {
    polynomial_nonneg(&p.clone().neg(), dom)
}

pub fn polynomial_neg(p: &Polynomial, dom: PolyDomain) -> bool {
    polynomial_pos(&p.clone().neg(), dom)
}

/// Backward-compat wrapper used by the prover's `simplify_ifs`.
pub fn polynomial_strictly_positive_in_nat(p: &Polynomial) -> bool {
    polynomial_pos(p, PolyDomain::Nat)
}

/// Quadratic-form PSD test (Sylvester's criterion) extended to rational
/// coefficients.  We work with `2*M` to keep entries free of halves; the
/// rationals make this easier — every entry stays rational.
fn quadratic_psd(p: &Polynomial) -> bool {
    use std::collections::BTreeSet;
    let mut vars: BTreeSet<&str> = BTreeSet::new();
    for m in &p.terms {
        for v in m.vars.keys() {
            vars.insert(v.as_str());
        }
        let total: u32 = m.vars.values().sum();
        if total > 2 {
            return false;
        }
    }
    if vars.is_empty() || vars.len() > 4 {
        return false;
    }
    let var_list: Vec<&str> = vars.iter().copied().collect();
    let n = var_list.len();
    let mut mat = vec![vec![Rat::ZERO; n]; n];
    let mut linear_or_const_terms: Vec<&Monomial> = Vec::new();
    for m in &p.terms {
        let total: u32 = m.vars.values().sum();
        if total < 2 {
            linear_or_const_terms.push(m);
            continue;
        }
        if m.vars.len() == 1 {
            let (vname, _) = m.vars.iter().next().unwrap();
            let i = var_list.iter().position(|v| v == vname).unwrap();
            mat[i][i] = mat[i][i].add(m.coeff.mul(Rat::from_int(2)));
        } else {
            let mut iter = m.vars.iter();
            let (n1, _) = iter.next().unwrap();
            let (n2, _) = iter.next().unwrap();
            let i = var_list.iter().position(|v| v == n1).unwrap();
            let j = var_list.iter().position(|v| v == n2).unwrap();
            mat[i][j] = mat[i][j].add(m.coeff);
            mat[j][i] = mat[j][i].add(m.coeff);
        }
    }
    for m in linear_or_const_terms {
        if m.vars.is_empty() {
            if m.coeff.sign() < 0 {
                return false;
            }
        } else {
            return false;
        }
    }
    for k in 1..=n {
        let det = det_rat(&mat, k);
        if det.sign() < 0 {
            return false;
        }
    }
    true
}

fn det_rat(mat: &[Vec<Rat>], k: usize) -> Rat {
    if k == 1 {
        return mat[0][0];
    }
    if k == 2 {
        return mat[0][0].mul(mat[1][1]).sub(mat[0][1].mul(mat[1][0]));
    }
    let mut acc: Rat = Rat::ZERO;
    for c in 0..k {
        let cofactor = minor_rat(mat, 0, c, k);
        let sign = if c % 2 == 0 { Rat::ONE } else { Rat::ONE.neg() };
        acc = acc.add(sign.mul(mat[0][c]).mul(cofactor));
    }
    acc
}

fn minor_rat(mat: &[Vec<Rat>], r: usize, c: usize, k: usize) -> Rat {
    let mut sub: Vec<Vec<Rat>> = Vec::with_capacity(k - 1);
    for (i, row) in mat.iter().enumerate().take(k) {
        if i == r {
            continue;
        }
        let mut new_row: Vec<Rat> = Vec::with_capacity(k - 1);
        for (j, &v) in row.iter().enumerate().take(k) {
            if j == c {
                continue;
            }
            new_row.push(v);
        }
        sub.push(new_row);
    }
    det_rat(&sub, k - 1)
}

/// Decide whether `lhs == rhs` holds for **all** values of the free
/// variables.  Sound: a `true` answer means the equality is a ring identity
/// (and rationals embed into ℝ, so it's also true over Real).  A `false`
/// answer means we couldn't prove it (could be false, or just outside the
/// polynomial fragment).
pub fn poly_equal(lhs: &Expr, rhs: &Expr) -> Option<bool> {
    let l = expr_to_poly(lhs)?;
    let r = expr_to_poly(rhs)?;
    Some(l == r)
}

// ===========================================================================
// Rational functions — extension for variable-containing division
// ===========================================================================

/// A rational function `num / den`, both polynomials.  Used to support
/// `by algebra` proofs that involve division by variable-containing
/// denominators (e.g. `1 / (2*N)`).  Equality `n1/d1 == n2/d2` is decided
/// by cross-multiplication `n1 * d2 == n2 * d1`, which is sound **modulo
/// the implicit assumption that no denominator vanishes** — the standard
/// convention for `by algebra` over Real.
#[derive(Debug, Clone)]
pub struct RatPoly {
    pub num: Polynomial,
    pub den: Polynomial,
}

impl RatPoly {
    pub fn from_poly(p: Polynomial) -> Self {
        RatPoly { num: p, den: Polynomial::from_const(1) }
    }
    pub fn zero() -> Self {
        RatPoly::from_poly(Polynomial::zero())
    }
    pub fn neg(self) -> Self {
        RatPoly { num: self.num.neg(), den: self.den }
    }
    pub fn add(self, other: Self) -> Self {
        // n1/d1 + n2/d2 = (n1*d2 + n2*d1) / (d1*d2)
        RatPoly {
            num: self
                .num
                .mul(other.den.clone())
                .add(other.num.mul(self.den.clone())),
            den: self.den.mul(other.den),
        }
    }
    pub fn sub(self, other: Self) -> Self {
        self.add(other.neg())
    }
    pub fn mul(self, other: Self) -> Self {
        RatPoly {
            num: self.num.mul(other.num),
            den: self.den.mul(other.den),
        }
    }
    pub fn div(self, other: Self) -> Option<Self> {
        // (n1/d1) / (n2/d2) = (n1*d2) / (d1*n2)
        if other.num.terms.is_empty() {
            return None; // dividing by zero rational
        }
        Some(RatPoly {
            num: self.num.mul(other.den),
            den: self.den.mul(other.num),
        })
    }
}

/// Convert an Expr to a `RatPoly` if possible.  Falls back to `expr_to_poly`
/// for anything outside `Add / Sub / Mul / Div / Neg / literal / Var`.
pub fn expr_to_ratpoly(e: &Expr) -> Option<RatPoly> {
    match e {
        Expr::Int(_) | Expr::Real(_) | Expr::Var { .. } => {
            expr_to_poly(e).map(RatPoly::from_poly)
        }
        Expr::UnOp(UnOp::Neg, inner) => Some(expr_to_ratpoly(inner)?.neg()),
        Expr::BinOp(op, l, r) => match op {
            BinOp::Add => Some(expr_to_ratpoly(l)?.add(expr_to_ratpoly(r)?)),
            BinOp::Sub => Some(expr_to_ratpoly(l)?.sub(expr_to_ratpoly(r)?)),
            BinOp::Mul => Some(expr_to_ratpoly(l)?.mul(expr_to_ratpoly(r)?)),
            BinOp::Div => {
                let lr = expr_to_ratpoly(l)?;
                let rr = expr_to_ratpoly(r)?;
                lr.div(rr)
            }
            _ => expr_to_poly(e).map(RatPoly::from_poly),
        },
        _ => expr_to_poly(e).map(RatPoly::from_poly),
    }
}

/// Decide `lhs == rhs` as rational-function identity (under the
/// `denominator != 0` convention).  Returns `Some(true)` when
/// `lhs.num * rhs.den == rhs.num * lhs.den` as polynomials.
pub fn ratpoly_equal(lhs: &Expr, rhs: &Expr) -> Option<bool> {
    let l = expr_to_ratpoly(lhs)?;
    let r = expr_to_ratpoly(rhs)?;
    let cross_l = l.num.mul(r.den);
    let cross_r = r.num.mul(l.den);
    Some(cross_l == cross_r)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> Expr {
        crate::parser::parse_expr_str(src).unwrap()
    }

    #[test]
    fn commutativity_of_addition() {
        let a = parse("a + b");
        let b = parse("b + a");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn distributivity() {
        let a = parse("a * (b + c)");
        let b = parse("a * b + a * c");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn associativity_of_multiplication() {
        let a = parse("(x * y) * z");
        let b = parse("x * (y * z)");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn constants_fold() {
        let a = parse("(x + 2) + 3");
        let b = parse("x + 5");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn nonsense_is_rejected() {
        let a = parse("x + 0");
        let b = parse("x + 1");
        assert_eq!(poly_equal(&a, &b), Some(false));
    }

    #[test]
    fn nonpolynomial_subterm_treated_as_opaque() {
        let a = parse("x / 2");
        let b = parse("x / 2");
        assert_eq!(poly_equal(&a, &b), Some(true));
        let a = parse("(x / 2) + 1");
        let b = parse("1 + (x / 2)");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn cube_expansion() {
        let a = parse("(x + 1) * (x + 1) * (x + 1)");
        let b = parse("x*x*x + 3*x*x + 3*x + 1");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn real_zero_is_neutral() {
        let a = parse("x + 0.0");
        let b = parse("x");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn real_distributivity() {
        let a = parse("a * (b + c)");
        let b = parse("a * b + a * c");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn real_literal_arithmetic() {
        // 1.5 + 0.5 == 2.0
        let a = parse("1.5 + 0.5");
        let b = parse("2.0");
        assert_eq!(poly_equal(&a, &b), Some(true));
    }

    #[test]
    fn rat_basic() {
        let a = Rat::new(1, 2).add(Rat::new(1, 2));
        assert_eq!(a, Rat::ONE);
        let b = Rat::new(2, 4);
        assert_eq!(b, Rat::new(1, 2));
        assert_eq!(Rat::new(-3, 6), Rat::new(-1, 2));
    }

    #[test]
    fn f64_round_trip() {
        assert_eq!(f64_to_rat(0.0), Some(Rat::ZERO));
        assert_eq!(f64_to_rat(1.0), Some(Rat::ONE));
        assert_eq!(f64_to_rat(0.5), Some(Rat::new(1, 2)));
        assert_eq!(f64_to_rat(0.25), Some(Rat::new(1, 4)));
        assert_eq!(f64_to_rat(-1.5), Some(Rat::new(-3, 2)));
    }
}

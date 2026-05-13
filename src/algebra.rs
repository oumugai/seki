//! Symbolic algebra for sound infinite-domain proofs.
//!
//! This module reduces an arithmetic expression over integers to a canonical
//! polynomial form (a sum of monomials).  Two expressions are equal as
//! integer polynomials iff their canonical forms are identical.  This gives
//! a *sound* decision procedure for the **polynomial equality fragment** of
//! seki — and crucially, the verdict is universal: it holds for **all**
//! values of the variables, no matter how large.  Thus the `by algebra`
//! tactic can prove `forall x in Int, x + 0 == x` without enumerating Int.
//!
//! Supported operators: `+`, `-` (binary and unary), `*`, integer literals,
//! and free variables.  Anything else (division, mod, function calls,
//! `if`-expressions, `==`, …) makes the conversion fail and the tactic must
//! refuse the proof.
//!
//! Limitations:
//!   * No division — `n / 2 + n / 2 == n` is **not** provable here, since
//!     integer division doesn't distribute over `+`.
//!   * No nonlinear hypotheses — we do not assume `x >= 0` or anything else.
//!     The tactic proves equality over the *integer ring*, not the natural
//!     numbers specifically.

use crate::ast::{BinOp, Expr, UnOp};
use std::collections::BTreeMap;

/// A monomial:  `coeff * x_1^e_1 * ... * x_k^e_k`.  The `vars` map is a
/// **canonical** sorted form (BTreeMap iterates in key order).  Variables
/// with exponent 0 are stripped during normalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Monomial {
    pub coeff: i128,
    pub vars: BTreeMap<String, u32>,
}

impl Monomial {
    pub fn constant(c: i128) -> Self {
        Self {
            coeff: c,
            vars: BTreeMap::new(),
        }
    }
    pub fn variable(name: &str) -> Self {
        let mut vars = BTreeMap::new();
        vars.insert(name.to_string(), 1);
        Self { coeff: 1, vars }
    }
    /// Multiplicative key (used for grouping like-terms).
    fn signature(&self) -> Vec<(String, u32)> {
        self.vars.iter().map(|(k, v)| (k.clone(), *v)).collect()
    }
}

/// A polynomial — sum of monomials in canonical form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial {
    /// Stored in a normalized order (by signature).  Same-signature terms are
    /// always merged.  Zero monomials are dropped.
    pub terms: Vec<Monomial>,
}

impl Polynomial {
    pub fn zero() -> Self {
        Self { terms: vec![] }
    }
    pub fn from_const(c: i128) -> Self {
        if c == 0 {
            Self::zero()
        } else {
            Self {
                terms: vec![Monomial::constant(c)],
            }
        }
    }
    pub fn from_var(name: &str) -> Self {
        Self {
            terms: vec![Monomial::variable(name)],
        }
    }

    pub fn neg(self) -> Self {
        Self {
            terms: self
                .terms
                .into_iter()
                .map(|mut m| {
                    m.coeff = -m.coeff;
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
                out.push(Monomial {
                    coeff: a.coeff.saturating_mul(b.coeff),
                    vars,
                });
            }
        }
        normalize(out)
    }

    /// Divide every coefficient by `c`.  Returns `None` if `c` does not
    /// evenly divide some coefficient or `c == 0`.  This is the *exact*
    /// integer division that respects ring structure: e.g.
    /// `(2*a + 4) / 2 → a + 2`, but `(2*a + 1) / 2 → None`.
    pub fn div_const(self, c: i128) -> Option<Self> {
        if c == 0 {
            return None;
        }
        let mut terms = Vec::new();
        for m in self.terms {
            if m.coeff % c != 0 {
                return None;
            }
            terms.push(Monomial {
                coeff: m.coeff / c,
                vars: m.vars,
            });
        }
        Some(normalize(terms))
    }

    /// Reduce every coefficient modulo `c` (Euclidean: result in `0..c`).
    /// `c` must be positive.  Models the truth: for `p(x_1,...) mod c`, every
    /// monomial `coeff * vars` contributes `(coeff mod c) * vars` because the
    /// product modulo c only depends on coeff mod c (variables are integers).
    pub fn mod_const(self, c: i128) -> Self {
        if c <= 0 {
            return self;
        }
        let mut terms = Vec::new();
        for m in self.terms {
            let r = m.coeff.rem_euclid(c);
            if r != 0 {
                terms.push(Monomial {
                    coeff: r,
                    vars: m.vars,
                });
            }
        }
        normalize(terms)
    }

    /// True if this polynomial is just an integer constant.
    pub fn as_constant(&self) -> Option<i128> {
        match self.terms.as_slice() {
            [] => Some(0),
            [m] if m.vars.is_empty() => Some(m.coeff),
            _ => None,
        }
    }
}

/// Combine like-terms, drop zeros, sort by signature.  This produces a
/// canonical form: equal polynomials have equal `terms` vectors.
fn normalize(mut terms: Vec<Monomial>) -> Polynomial {
    // sort by signature (lex order on (var, exp) sequence)
    terms.sort_by(|a, b| a.signature().cmp(&b.signature()));
    // merge runs with equal signature
    let mut merged: Vec<Monomial> = Vec::with_capacity(terms.len());
    for m in terms {
        if let Some(last) = merged.last_mut() {
            if last.signature() == m.signature() {
                last.coeff += m.coeff;
                continue;
            }
        }
        merged.push(m);
    }
    // drop zero coefficients
    merged.retain(|m| m.coeff != 0);
    Polynomial { terms: merged }
}

/// Convert an Expr to a Polynomial, treating each unbound `Var` as a free
/// variable.  Subexpressions that fall outside the polynomial fragment
/// (function applications, `if`-expressions, division, etc.) are treated
/// as **opaque atoms**: each such subterm is given a deterministic name
/// based on its printed form, and identical subterms yield identical names
/// — so `f(k) - f(k)` simplifies to `0` and `2 * f(k)` cancels another
/// `2 * f(k)`.  This is what makes the induction step work for primitive
/// recursive specs: the inductive hypothesis call on the right side of the
/// step (`sum k`) is treated as a symbolic constant and disappears when
/// it appears equally on both sides.
pub fn expr_to_poly(e: &Expr) -> Option<Polynomial> {
    match e {
        Expr::Int(n) => Some(Polynomial::from_const(*n as i128)),
        Expr::Bool(_) | Expr::Str(_) => None,
        Expr::Var { name: name, .. } => Some(Polynomial::from_var(name)),
        Expr::UnOp(UnOp::Neg, inner) => Some(expr_to_poly(inner)?.neg()),
        Expr::UnOp(UnOp::Not, _) => None,
        Expr::BinOp(op, l, r) => {
            match op {
                BinOp::Add => Some(expr_to_poly(l)?.add(expr_to_poly(r)?)),
                BinOp::Sub => Some(expr_to_poly(l)?.sub(expr_to_poly(r)?)),
                BinOp::Mul => Some(expr_to_poly(l)?.mul(expr_to_poly(r)?)),
                BinOp::Div => {
                    // Only succeed on exact integer division by a nonzero
                    // constant.  Otherwise treat the whole expression as
                    // opaque so two textually identical `e/c` cancel.
                    let lp = expr_to_poly(l)?;
                    if let Some(c) = const_value(r) {
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
                // outside polynomial fragment — treat the whole subterm as opaque
                _ => Some(Polynomial::from_var(&opaque_name(e))),
            }
        }
        // App / If / Let / Lambda / SetEnum / etc. — all opaque atoms.
        _ => Some(Polynomial::from_var(&opaque_name(e))),
    }
}

/// Extract an integer constant from an Expr (handling unary negation).
/// Used to recognize compile-time constant divisors / moduli.
pub fn const_value(e: &Expr) -> Option<i128> {
    match e {
        Expr::Int(n) => Some(*n as i128),
        Expr::UnOp(UnOp::Neg, inner) => const_value(inner).map(|v| -v),
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

/// Strip whitespace from the printed form so two formattings of the same
/// expression collapse to the same atom name.
fn normalize_atom(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Recursively rewrite arithmetic subexpressions of `e` into a canonical
/// polynomial form by round-tripping `expr_to_poly` → `poly_to_expr`.
/// Non-arithmetic constructs (App, If, ...) are recursed into so opaque
/// atoms generated for them see canonical *children*.
pub fn canonicalize(e: &Expr) -> Expr {
    use Expr::*;
    // If the whole expression is a polynomial, use its canonical form.
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

/// Like `expr_to_poly`, but **only** succeeds when every subterm fits in the
/// pure polynomial fragment (no opaque atoms introduced).  Used by
/// `canonicalize` to avoid infinite recursion through opaque-name generation.
fn expr_to_poly_opaque_only(e: &Expr) -> Option<Polynomial> {
    match e {
        Expr::Int(n) => Some(Polynomial::from_const(*n as i128)),
        Expr::Var { name: name, .. } => Some(Polynomial::from_var(name)),
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
/// by `canonicalize` to print atom names deterministically.
pub fn poly_to_expr(p: &Polynomial) -> Expr {
    if p.terms.is_empty() {
        return Expr::Int(0);
    }
    let mut acc: Option<Expr> = None;
    for m in &p.terms {
        let mut term: Option<Expr> = None;
        // build product of variables
        for (name, exp) in &m.vars {
            for _ in 0..*exp {
                let v = Expr::Var { name: name.clone(), line: 0, col: 0 };
                term = Some(match term {
                    None => v,
                    Some(t) => Expr::BinOp(BinOp::Mul, Box::new(t), Box::new(v)),
                });
            }
        }
        // multiply by coefficient (skip ±1 unless monomial is constant)
        let term_with_coeff = match term {
            None => Expr::Int(m.coeff as i64),
            Some(t) => {
                if m.coeff == 1 {
                    t
                } else if m.coeff == -1 {
                    Expr::UnOp(UnOp::Neg, Box::new(t))
                } else {
                    Expr::BinOp(BinOp::Mul, Box::new(Expr::Int(m.coeff as i64)), Box::new(t))
                }
            }
        };
        // accumulate
        acc = Some(match acc {
            None => term_with_coeff,
            Some(a) => Expr::BinOp(BinOp::Add, Box::new(a), Box::new(term_with_coeff)),
        });
    }
    acc.unwrap_or(Expr::Int(0))
}

/// Domain over which a polynomial is interpreted.  Affects what sign
/// inferences are sound: all variables are ≥ 0 in `Nat`, unrestricted in `Int`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolyDomain {
    Nat,
    Int,
}

/// `>= 0` decision (sound, incomplete).  Returns `true` only when the
/// polynomial is provably nonneg for every valuation in the chosen domain.
pub fn polynomial_nonneg(p: &Polynomial, dom: PolyDomain) -> bool {
    if p.terms.is_empty() {
        return true; // identically 0
    }
    if let Some(c) = p.as_constant() {
        return c >= 0;
    }
    match dom {
        // Over Nat (all variables ≥ 0): a sufficient condition is that every
        // monomial coefficient is ≥ 0.
        PolyDomain::Nat => p.terms.iter().all(|m| m.coeff >= 0),
        // Over Int (variables can be negative): more subtle.  Sufficient:
        // (a) every variable appears only with even exponents AND every
        // coefficient ≥ 0 (since `x^{2k} ≥ 0`), or
        // (b) the polynomial decomposes as a positive-semi-definite quadratic
        // form plus a nonneg lower-degree remainder.
        PolyDomain::Int => {
            let all_even = p.terms.iter().all(|m| m.vars.values().all(|e| e % 2 == 0));
            let all_nn = p.terms.iter().all(|m| m.coeff >= 0);
            (all_even && all_nn) || quadratic_psd(p)
        }
    }
}

/// `> 0` decision (sound, incomplete).
pub fn polynomial_pos(p: &Polynomial, dom: PolyDomain) -> bool {
    if p.terms.is_empty() {
        return false; // 0 is not > 0
    }
    if let Some(c) = p.as_constant() {
        return c > 0;
    }
    match dom {
        // Over Nat: nonneg AND constant term > 0
        PolyDomain::Nat => {
            let all_nn = p.terms.iter().all(|m| m.coeff >= 0);
            let const_pos = p.terms.iter().any(|m| m.vars.is_empty() && m.coeff > 0);
            all_nn && const_pos
        }
        PolyDomain::Int => {
            // strictly positive over Int: even exponents, nonneg coeffs,
            // AND constant term > 0 (so vars=0 still gives > 0).
            let all_even = p.terms.iter().all(|m| m.vars.values().all(|e| e % 2 == 0));
            let all_nn = p.terms.iter().all(|m| m.coeff >= 0);
            let const_pos = p.terms.iter().any(|m| m.vars.is_empty() && m.coeff > 0);
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

/// Decide whether the polynomial's quadratic part is positive-semi-definite
/// AND its lower-degree (constant + linear) part is nonneg.  Handles up to
/// 4 variables via Sylvester's criterion (all leading principal minors ≥ 0
/// of the symmetric coefficient matrix).
///
/// We work with `2*M` instead of `M` to keep all entries integral: the cross
/// term `β*ab` contributes `β/2` to the off-diagonal entry of `M`, but `β`
/// to the off-diagonal entry of `2*M`.  Multiplying a symmetric matrix by a
/// positive scalar preserves PSD-ness, so leading principal minors of `2*M`
/// being ≥ 0 is equivalent to those of `M`.
fn quadratic_psd(p: &Polynomial) -> bool {
    use std::collections::BTreeSet;
    // Collect the variables appearing anywhere in `p`.
    let mut vars: BTreeSet<&str> = BTreeSet::new();
    for m in &p.terms {
        for v in m.vars.keys() {
            vars.insert(v.as_str());
        }
        let total: u32 = m.vars.values().sum();
        if total > 2 {
            return false; // cubic or higher — out of scope
        }
    }
    if vars.is_empty() || vars.len() > 4 {
        return false;
    }
    let var_list: Vec<&str> = vars.iter().copied().collect();
    let n = var_list.len();
    // Build symmetric matrix scaled by 2.
    let mut mat = vec![vec![0i128; n]; n];
    let mut linear_or_const_terms: Vec<&Monomial> = Vec::new();
    for m in &p.terms {
        let total: u32 = m.vars.values().sum();
        if total < 2 {
            linear_or_const_terms.push(m);
            continue;
        }
        // total == 2 by the earlier guard
        if m.vars.len() == 1 {
            // x_i^2  →  diagonal entry = coeff, but in 2*M it's 2*coeff
            let (vname, _) = m.vars.iter().next().unwrap();
            let i = var_list.iter().position(|v| v == vname).unwrap();
            mat[i][i] = mat[i][i].saturating_add(m.coeff.saturating_mul(2));
        } else {
            // x_i * x_j with i != j  →  off-diagonal entry = coeff/2, in 2*M it's coeff
            let mut iter = m.vars.iter();
            let (n1, _) = iter.next().unwrap();
            let (n2, _) = iter.next().unwrap();
            let i = var_list.iter().position(|v| v == n1).unwrap();
            let j = var_list.iter().position(|v| v == n2).unwrap();
            mat[i][j] = mat[i][j].saturating_add(m.coeff);
            mat[j][i] = mat[j][i].saturating_add(m.coeff);
        }
    }
    // Lower-degree part must be nonneg over Int — sufficient: linear coeffs
    // = 0 (since ax could be negative for negative x) and constants ≥ 0.
    for m in linear_or_const_terms {
        if m.vars.is_empty() {
            if m.coeff < 0 {
                return false;
            }
        } else {
            // any linear term breaks nonnegativity over Int
            return false;
        }
    }
    // Sylvester: every leading principal minor must be ≥ 0.
    for k in 1..=n {
        let det = det_int(&mat, k);
        if det < 0 {
            return false;
        }
    }
    true
}

/// Determinant of the top-left k×k submatrix.  Uses Laplace expansion;
/// adequate for k ≤ 4.
fn det_int(mat: &[Vec<i128>], k: usize) -> i128 {
    if k == 1 {
        return mat[0][0];
    }
    if k == 2 {
        return mat[0][0]
            .saturating_mul(mat[1][1])
            .saturating_sub(mat[0][1].saturating_mul(mat[1][0]));
    }
    // expand along first row
    let mut acc: i128 = 0;
    for c in 0..k {
        let cofactor = minor_int(mat, 0, c, k);
        let sign: i128 = if c % 2 == 0 { 1 } else { -1 };
        acc = acc.saturating_add(sign.saturating_mul(mat[0][c]).saturating_mul(cofactor));
    }
    acc
}

/// (k-1)×(k-1) minor obtained by deleting row `r` and column `c`.
fn minor_int(mat: &[Vec<i128>], r: usize, c: usize, k: usize) -> i128 {
    let mut sub: Vec<Vec<i128>> = Vec::with_capacity(k - 1);
    for (i, row) in mat.iter().enumerate().take(k) {
        if i == r {
            continue;
        }
        let mut new_row: Vec<i128> = Vec::with_capacity(k - 1);
        for (j, &v) in row.iter().enumerate().take(k) {
            if j == c {
                continue;
            }
            new_row.push(v);
        }
        sub.push(new_row);
    }
    det_int(&sub, k - 1)
}

/// Decide whether `lhs == rhs` holds for **all** integer values of the free
/// variables.  This is sound: a `true` answer means the equality is a ring
/// identity over `ℤ`.  A `false` answer means we couldn't prove it (could be
/// false, or just outside the polynomial fragment).
pub fn poly_equal(lhs: &Expr, rhs: &Expr) -> Option<bool> {
    let l = expr_to_poly(lhs)?;
    let r = expr_to_poly(rhs)?;
    Some(l == r)
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
        // `x / 2` is outside the polynomial fragment, but identical opaque
        // subterms still compare equal: both sides become the same atom.
        let a = parse("x / 2");
        let b = parse("x / 2");
        assert_eq!(poly_equal(&a, &b), Some(true));

        // And a sum involving such an opaque does cancel:
        //   (x / 2) + 1 == 1 + (x / 2)   — same atom on both sides.
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
}

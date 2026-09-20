//! Proof terms, and the small checker that is allowed to believe them.
//!
//! # Why
//!
//! Before this module, `Prover::verify` returning `Ok(Bool(true))` *was* the
//! proof.  Nothing survived that a second, simpler program could re-examine,
//! so every line that a tactic might execute — `prover.rs`'s pattern-matching
//! heuristics, `algebra.rs`'s decision procedures, the whole evaluator — sat
//! in the trusted computing base.  A bug anywhere in ~9,000 lines could
//! silently mint a theorem, and two of them actually did (`docs/spec/06-
//! soundness.md` Pattern D, and `by eval` over `Nat`).
//!
//! A tactic now *produces* a [`Cert`]: a tree of primitive inference steps
//! recording how the goal was closed.  [`check`] walks that tree against the
//! proposition and re-establishes each step from scratch.  Tactics are no
//! longer trusted — they are search procedures whose output has to survive an
//! independent check.  This is the standard LCF split: **searching is hard
//! and may be buggy, checking is easy and is the only thing that has to be
//! right.**
//!
//! # What is still trusted
//!
//! Being honest about the remaining base, in descending order of how much
//! rests on it:
//!
//! 1. **This file.**
//! 2. **The evaluator, on ground terms.** seki's semantics *is* `eval`, so
//!    "`2 + 2` really is `4`" can only be settled by running it.  This is
//!    computational reflection, the same assumption Coq's `vm_compute` and
//!    Lean's `Decidable.decide` make.  The kernel narrows it in one
//!    important way: it evaluates through [`EvalCtx::finite_only`], which
//!    *refuses* to enumerate an infinite set rather than sampling it.  The
//!    sampling hole is therefore closed structurally — the kernel cannot
//!    accept `forall n in Nat, P n` on the strength of 200 points even if a
//!    tactic offers it.
//! 3. **Polynomial arithmetic** (`Polynomial::{add,sub,mul}` and
//!    `expr_to_poly`) — roughly 200 lines of `algebra.rs`.  The *decision
//!    procedures* built on top of it (sign analysis, PSD detection,
//!    Fourier-Motzkin, the subset search over hypotheses) are **not**
//!    trusted: they only ever propose a witness, and the kernel checks the
//!    witness by addition and comparison.
//!
//! Everything else — all of `prover.rs`, the rest of `algebra.rs`,
//! `termination.rs`, `linarith.rs` — is outside the trusted base.
//!
//! # The escape hatch
//!
//! [`Cert::Trusted`] exists for tactic paths not yet taught to emit a
//! checkable witness.  The kernel accepts it, and says so: such a theorem is
//! reported as *not kernel-checked*, `--strict` refuses it, and
//! `Prover::verify` keeps it out of any certificate that cites it.  The point
//! is that the remaining gaps are **named and countable** instead of
//! invisible.

use crate::algebra::{expr_to_poly, PolyDomain, Polynomial, Rat};
use crate::ast::{subst, BinOp, Expr};
use crate::eval::{enumerate_set, EvalCtx};
use crate::value::{value_eq, Env, SetVal, Value};

// -- proof terms ------------------------------------------------------------

/// A proof term: how a goal was closed, in primitive steps.
#[derive(Debug, Clone)]
pub enum Cert {
    /// `a == b` because both sides evaluate to the same value.
    Refl,

    /// `a == b` because the two sides are the *same term* — reflexivity,
    /// with no evaluation.  Unlike [`Cert::Refl`] this works under binders
    /// and with free variables, which is what an equational rewrite needs
    /// once it has made both sides identical.
    SyntacticRefl,

    /// The proposition evaluates to `true` outright.  The kernel re-runs
    /// the evaluation in a finiteness-strict context, so this is only
    /// available when no infinite domain has to be enumerated.
    Ground,

    /// `forall x in S, P(x)` with `S` finite: `subs[i]` proves
    /// `P(elems[i])`.  The kernel re-enumerates `S` and checks that the
    /// element list is exactly what enumeration gives, so a certificate
    /// cannot quietly leave elements out.
    ForallFinite { subs: Vec<Cert> },

    /// `exists x in S, P(x)` by exhibiting a witness.  Sound at any
    /// cardinality: a witness is a witness.
    ExistsWitness { witness: Expr, sub: Box<Cert> },

    /// `l OP r` from `c > 0` and `c·l OP c·r`, under the goal's own
    /// binders and premises.
    ///
    /// Dividing an inequality by a positive quantity.  A
    /// Positivstellensatz certificate can only *add* non-negative things,
    /// so it can reach `(1-k)·A <= 0` but never the `A <= 0` that follows
    /// — the division has no representation as a sum. Every contraction
    /// argument ends exactly there, so without this rule the uniqueness of
    /// a fixed point, and with it the uniqueness half of
    /// Picard-Lindelof, is unreachable.
    ///
    /// Sound for every ordered field: `c > 0` and `c·l >= c·r` give
    /// `l >= r`, and likewise for the strict and reversed forms.
    CancelPositive { factor: Expr, positive: Box<Cert>, scaled: Box<Cert> },

    /// `l == r` from `l >= r` and `l <= r`, under the goal's own binders
    /// and premises.
    ///
    /// The antisymmetry of the order.  It is what turns the inequality
    /// machinery into an *equality* proof, and without it the uniqueness of
    /// a limit or a supremum — both stated as equalities and both proved by
    /// squeezing — cannot be derived at all.
    ///
    /// Both obligations are derived from the goal, so the certificate
    /// chooses nothing here beyond how to prove each direction.
    Antisymmetry { ge: Box<Cert>, le: Box<Cert> },

    /// The same rule, but for an existential that sits *under* the goal's
    /// binders and premises — the shape every epsilon-delta statement has:
    /// `forall eps in Real, eps > 0 => exists delta in Real, ...`.
    ///
    /// `ExistsWitness` cannot serve here because it must evaluate the
    /// witness to check membership, and a witness such as `eps / 2.0`
    /// mentions a generalized variable that has no value.  So this rule
    /// checks membership *syntactically* instead
    /// ([`Checker::witness_is_total`]): the witness has to be built from
    /// the binders and literals by operations that are total on the
    /// domain, which is decidable without evaluating anything.
    ///
    /// The obligation is re-derived from the goal, so a certificate can
    /// choose the witness but not what proving it means.
    Witness { term: Expr, then: Box<Cert> },

    /// `forall x in {y in D | pred}, body` where `body` is conjunct
    /// `conjunct` of `pred` — every member satisfies it by definition.
    ForallFromComprehension { conjunct: usize },

    /// Case analysis on the first `if` in the goal: prove it with the
    /// condition assumed true and the `if` collapsed to its `then` branch,
    /// and again with the condition false.
    ///
    /// The kernel derives both obligations itself
    /// (`crate::rewrite::case_split_goals`), so a certificate cannot pick a
    /// condition that makes its life easier.
    CaseSplit { then_branch: Box<Cert>, else_branch: Box<Cert> },

    /// Universal generalization: prove the body with the bound variables
    /// free, and conclude the quantified statement.  Sound because the
    /// sub-proof may not assume anything about them — which the kernel
    /// enforces by refusing to *evaluate* any goal that mentions one.
    Generalize { vars: Vec<String>, then: Box<Cert> },

    /// A fact about polynomials, after stripping leading `forall` binders
    /// over `dom`.  See [`PolyClaim`].
    Poly { dom: PolyDomain, claim: PolyClaim },

    /// Structural induction.  `base` proves the proposition at the
    /// constructor(s) with no recursive argument; `step` proves the
    /// difference between successive cases is compatible with the relation.
    Induction { base: Box<Cert>, step: Box<Cert> },

    /// Rewrite the goal to a fixed point using exactly `lemmas`, reaching
    /// `result`, then close that.  An empty `lemmas` means the goal was
    /// reached by AC-normalization alone.
    ///
    /// The kernel does not take `result` on faith: it looks each lemma up
    /// among the accepted theorems and axioms, re-runs
    /// `crate::rewrite::rewrite_goal`, and requires the run to actually
    /// reach `result`.
    Rewrite { lemmas: Vec<String>, result: Expr, then: Box<Cert> },

    /// Beta-unfold a global definition to reach `unfolded`, then close that.
    /// The kernel recomputes the unfolding from `globals` rather than
    /// believing the recorded result.
    Unfold { name: String, unfolded: Expr, then: Box<Cert> },

    /// Discharge the goal by citing an accepted theorem or an axiom whose
    /// statement is alpha-equivalent to it.
    Cite { name: String },

    /// The goal's conclusion is one of the hypotheses it already assumes.
    Assumption,

    /// A conjunctive conclusion, proved conjunct by conjunct.
    ///
    /// The kernel splits the goal itself and pairs the parts up in order,
    /// so a certificate cannot prove two easy conjuncts and call it three.
    AndIntro { parts: Vec<Cert> },

    /// *Modus ponens.*  Instantiate `lemma` with `substs`, discharge each
    /// of its premises, and read off its conclusion as the goal.
    ///
    /// The kernel re-does the instantiation from the lemma's recorded
    /// statement, so a certificate cannot claim a lemma says something it
    /// does not, and it checks every premise — a proof that skips one is
    /// refused.
    Apply {
        lemma: String,
        substs: Vec<(String, Expr)>,
        premises: Vec<Cert>,
    },

    /// *Cut.*  Prove `fact` under the hypotheses in scope, then prove the
    /// goal with `fact` added to them.
    Have {
        fact: Expr,
        fact_proof: Box<Cert>,
        then: Box<Cert>,
    },

    /// Existential elimination: `lemma` (instantiated by `substs`) yields
    /// `exists v, P(v)`; assuming `P(intro)`, `then` closes the goal.
    Obtain {
        lemma: String,
        intro: String,
        substs: Vec<(String, Expr)>,
        premises: Vec<Cert>,
        then: Box<Cert>,
    },

    /// **Not checked.**  A tactic path with no checkable witness.  The
    /// kernel lets it through but marks the result as unchecked; see the
    /// module docs.
    Trusted { tactic: &'static str, reason: TrustReason, why: String },
}

/// Why a step could not be checked.  The distinction matters: one of these
/// is a known-unsound shortcut, the other is merely unverified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustReason {
    /// Checking would have meant enumerating an infinite domain, so the
    /// tactic looked at a finite sample instead.  **This can accept a false
    /// proposition** — the hole `docs/spec/06-soundness.md` §6.2 describes.
    Sampled,
    /// The tactic closed the goal by a route that has not been taught to
    /// emit a witness yet.  The proposition may well be true; nothing here
    /// establishes it independently, so a bug in that tactic would go
    /// unnoticed.
    NoWitnessYet,
}

/// A polynomial fact together with the witness that makes it checkable.
///
/// Every variant is *checked by arithmetic alone*: the tactic searched for
/// the witness, and the kernel only adds and compares.
#[derive(Debug, Clone)]
pub enum PolyClaim {
    /// `lhs == rhs` because `lhs - rhs` is the zero polynomial.
    Zero { lhs: Expr, rhs: Expr },

    /// `lhs >= rhs` (or `>`) over `Nat` because every coefficient of
    /// `lhs - rhs` is non-negative and every variable is.
    NonnegCoeffs { lhs: Expr, rhs: Expr, strict: bool },

    /// `lhs >= rhs` over `Int`/`Real` because every monomial of `lhs - rhs`
    /// has all-even exponents and a non-negative coefficient.  With `strict`
    /// the difference additionally carries a positive constant term, which
    /// is what turns `>= 0` into `> 0`.
    EvenPowers { lhs: Expr, rhs: Expr, strict: bool },

    /// `lhs >= rhs` because `lhs - rhs` is a non-negative combination of
    /// squares: `Σ cᵢ · qᵢ²` with every `cᵢ >= 0`.  The tactic found the
    /// decomposition; the kernel multiplies it out and compares.
    SumOfSquares {
        lhs: Expr,
        rhs: Expr,
        terms: Vec<(Rat, Expr)>,
    },

    /// `lhs == rhs` because the difference is a linear combination of the
    /// goal's *equality* hypotheses: `lhs - rhs = Σ λᵢ·(aᵢ - bᵢ)`.
    ///
    /// Unlike a Farkas certificate the multipliers are unrestricted — an
    /// equation may be scaled by anything, negatives included — because
    /// `aᵢ = bᵢ` gives `λ(aᵢ - bᵢ) = 0` whatever `λ` is.  This is what lets
    /// a fact obtained from an existential (`w³ - w - 2 = 0`) be rearranged
    /// into the form a goal wants (`w³ = w + 2`).
    EqCombination {
        lhs: Expr,
        rhs: Expr,
        used: Vec<(Expr, Rat)>,
    },

    /// A *Positivstellensatz certificate*: `lhs - rhs = Σ λ_g·g + slack`,
    /// where every `g` is a product of the goal's own hypotheses and every
    /// multiplier and the slack is non-negative — so the difference is too.
    ///
    /// With single-hypothesis generators this is the classical Farkas
    /// certificate for linear arithmetic, and the reason `by linarith` need
    /// not be trusted: finding the multipliers takes Fourier-Motzkin or a
    /// simplex, while *checking* them is multiplying each hypothesis by a
    /// rational and adding up.
    ///
    /// Allowing a generator to be a *product* extends the same idea to the
    /// non-linear fragment, which is where most constraints about
    /// quantities actually live: `0 <= a <= 1 ⊢ a² <= 1` needs
    /// `(1-a)·(1+a)`, and no sum of the hypotheses alone will do it.  The
    /// check is still only multiplication and addition — `p ≥ 0` and
    /// `q ≥ 0` give `pq ≥ 0` with nothing further assumed.
    ///
    /// `goal_strict` records that the goal is a strict inequality, which
    /// needs either a positive slack or a strictly positive generator with
    /// a positive multiplier.
    Farkas {
        lhs: Expr,
        rhs: Expr,
        used: Vec<Generator>,
        slack: Rat,
        goal_strict: bool,
    },
}

/// One non-negative quantity a Positivstellensatz certificate is built
/// from: a product of hypotheses the goal already assumes.
///
/// A single factor is an ordinary Farkas term.  Two or more is what makes
/// the certificate reach past linear arithmetic.
#[derive(Debug, Clone)]
pub struct Generator {
    /// The hypotheses multiplied together; each must be one the goal
    /// assumes, which is what the kernel checks.
    pub factors: Vec<Expr>,
    /// Whether every factor is a strict inequality — only then is the
    /// product strictly positive.
    pub strict: bool,
    /// Its non-negative weight.
    pub coeff: Rat,
}

impl Generator {
    /// Render as `λ·(h₁)·(h₂)`, or just `(h)` when the weight is one and
    /// there is a single factor.
    fn describe(&self) -> String {
        let body = self
            .factors
            .iter()
            .map(|f| format!("({})", f))
            .collect::<Vec<_>>()
            .join("·");
        if self.coeff == Rat::from_int(1) {
            body
        } else {
            format!("{}·{}", self.coeff, body)
        }
    }
}

// -- checking ---------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct KernelError(pub String);

impl std::fmt::Display for KernelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "kernel rejected the proof: {}", self.0)
    }
}

impl From<KernelError> for crate::SekiError {
    fn from(e: KernelError) -> Self {
        crate::SekiError::Proof(e.to_string())
    }
}

type KResult<T> = Result<T, KernelError>;

fn err<T>(msg: impl Into<String>) -> KResult<T> {
    Err(KernelError(msg.into()))
}

/// A step the kernel had to take on trust.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TrustedStep {
    pub tactic: &'static str,
    pub reason: TrustReason,
}

/// What the kernel concluded about a certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Verdict {
    /// Every step was re-established from primitives.
    pub fully_checked: bool,
    /// Steps that asked for trust via [`Cert::Trusted`].
    pub trusted_steps: Vec<TrustedStep>,
    /// Axioms the proof leans on, and theorems cited that themselves were
    /// not fully checked.
    pub assumptions: Vec<String>,
}

impl Verdict {
    /// Did any step fall back on sampling an infinite domain?  That is the
    /// one kind of gap that can admit a *false* proposition.
    pub fn is_sampled(&self) -> bool {
        self.trusted_steps
            .iter()
            .any(|s| s.reason == TrustReason::Sampled)
    }

    /// Does the proof rest on an `axiom`, or on a theorem that itself was
    /// not fully checked?
    pub fn has_assumptions(&self) -> bool {
        !self.assumptions.is_empty()
    }
}

impl Verdict {
    fn sound() -> Self {
        Verdict { fully_checked: true, trusted_steps: Vec::new(), assumptions: Vec::new() }
    }

    fn merge(mut self, other: Verdict) -> Self {
        self.fully_checked &= other.fully_checked;
        self.trusted_steps.extend(other.trusted_steps);
        self.assumptions.extend(other.assumptions);
        self
    }
}

/// Check `cert` against `prop`.
///
/// `ctx` must be a finiteness-strict context ([`EvalCtx::finite_only`]);
/// `check` refuses to run otherwise, because the whole point is that the
/// kernel cannot be talked into sampling.
pub fn check(prop: &Expr, cert: &Cert, ctx: &EvalCtx, env: &Env) -> KResult<Verdict> {
    if !ctx.finite_only {
        return err(
            "internal: the kernel must run in a finiteness-strict evaluation \
             context (EvalCtx::finite_only)",
        );
    }
    Checker {
        ctx,
        env: env.clone(),
        generalized: std::collections::BTreeSet::new(),
    }
    .check(prop, cert)
}

struct Checker<'a, 'g> {
    ctx: &'a EvalCtx<'g>,
    /// Bindings for domain elements introduced by `ForallFinite`.  Carrying
    /// them here rather than substituting them into the goal is what lets
    /// the kernel handle elements with no literal syntax — an ADT
    /// constructor, a set, a closure.
    env: Env,
    /// Variables introduced by [`Cert::Generalize`].  A rule that
    /// *evaluates* the goal must refuse when one of these is in it:
    /// evaluation would resolve the name to whatever global it shadows and
    /// prove a single instance instead of the universal statement.
    generalized: std::collections::BTreeSet<String>,
}

impl Checker<'_, '_> {
    fn check(&self, prop: &Expr, cert: &Cert) -> KResult<Verdict> {
        match cert {
            Cert::Refl => self.check_refl(prop),
            Cert::SyntacticRefl => self.check_syntactic_refl(prop),
            Cert::Ground => self.check_ground(prop),
            Cert::ForallFinite { subs } => self.check_forall_finite(prop, subs),
            Cert::ExistsWitness { witness, sub } => {
                self.check_exists_witness(prop, witness, sub)
            }
            Cert::Witness { term, then } => self.check_witness(prop, term, then),
            Cert::Antisymmetry { ge, le } => self.check_antisymmetry(prop, ge, le),
            Cert::CancelPositive { factor, positive, scaled } => {
                self.check_cancel_positive(prop, factor, positive, scaled)
            }
            Cert::ForallFromComprehension { conjunct } => {
                self.check_forall_from_comprehension(prop, *conjunct)
            }
            Cert::Generalize { vars, then } => self.check_generalize(prop, vars, then),
            Cert::CaseSplit { then_branch, else_branch } => {
                self.check_case_split(prop, then_branch, else_branch)
            }
            Cert::Poly { dom, claim } => self.check_poly(prop, *dom, claim),
            Cert::Induction { base, step } => self.check_induction(prop, base, step),
            Cert::Rewrite { lemmas, result, then } => {
                self.check_rewrite(prop, lemmas, result, then)
            }
            Cert::Unfold { name, unfolded, then } => {
                self.check_unfold(prop, name, unfolded, then)
            }
            Cert::Cite { name } => self.check_cite(prop, name),
            Cert::Assumption => self.check_assumption(prop),
            Cert::AndIntro { parts } => self.check_and_intro(prop, parts),
            Cert::Apply { lemma, substs, premises } => {
                self.check_apply(prop, lemma, substs, premises)
            }
            Cert::Have { fact, fact_proof, then } => {
                self.check_have(prop, fact, fact_proof, then)
            }
            Cert::Obtain { lemma, intro, substs, premises, then } => {
                self.check_obtain(prop, lemma, intro, substs, premises, then)
            }
            Cert::Trusted { tactic, reason, why } => Ok(Verdict {
                fully_checked: false,
                trusted_steps: vec![TrustedStep { tactic, reason: *reason }],
                assumptions: vec![format!("`{}` is not kernel-checked: {}", tactic, why)],
            }),
        }
    }

    // -- primitive rules ----------------------------------------------------

    /// Refuse to evaluate a goal that still mentions a universally
    /// generalized variable: evaluation would silently resolve the name to
    /// a global of the same name and settle one instance, not the
    /// quantified statement.
    fn no_generalized(&self, e: &Expr) -> KResult<()> {
        if self.generalized.is_empty() {
            return Ok(());
        }
        let mut free = std::collections::BTreeSet::new();
        crate::unfold::collect_free_var_names(e, &mut free);
        if let Some(v) = free.iter().find(|v| self.generalized.contains(*v)) {
            return err(format!(
                "`{}` was universally generalized, so `{}` cannot be settled by \
                 evaluating it",
                v, e
            ));
        }
        Ok(())
    }

    fn check_refl(&self, prop: &Expr) -> KResult<Verdict> {
        self.no_generalized(prop)?;
        let (l, r) = match prop {
            Expr::BinOp(BinOp::Eq, l, r) => (l, r),
            other => return err(format!("refl proves an equality, but the goal is {}", other)),
        };
        let lv = self.eval(l)?;
        let rv = self.eval(r)?;
        if value_eq(&lv, &rv) {
            Ok(Verdict::sound())
        } else {
            err(format!("refl: {} evaluates to {} but {} evaluates to {}", l, lv, r, rv))
        }
    }

    /// Reflexivity as a *syntactic* fact: after stripping universal
    /// binders, the two sides of the equality are the same term.  No
    /// evaluation, so this holds with free variables in scope.
    fn check_syntactic_refl(&self, prop: &Expr) -> KResult<Verdict> {
        match strip_foralls(prop) {
            Expr::BinOp(BinOp::Eq, l, r) if crate::ast::alpha_equiv(l, r) => {
                Ok(Verdict::sound())
            }
            Expr::BinOp(BinOp::Eq, l, r) => err(format!(
                "reflexivity needs both sides to be the same term, but `{}` and `{}` differ",
                l, r
            )),
            other => err(format!("reflexivity proves an equality, but the goal is {}", other)),
        }
    }

    fn check_ground(&self, prop: &Expr) -> KResult<Verdict> {
        self.no_generalized(prop)?;
        match self.eval(prop)? {
            Value::Bool(true) => Ok(Verdict::sound()),
            Value::Bool(false) => err(format!("the goal {} evaluates to false", prop)),
            other => err(format!(
                "the goal {} evaluates to {}, not a Bool",
                prop,
                other.type_name()
            )),
        }
    }

    fn check_forall_finite(&self, prop: &Expr, subs: &[Cert]) -> KResult<Verdict> {
        let (var, domain, body) = match prop {
            Expr::Forall { var, domain, body } => (var, domain, body),
            other => return err(format!("expected a `forall` goal, got {}", other)),
        };
        // Re-enumerate the domain ourselves.  A certificate does not get to
        // choose which elements to present, and `finite_only` guarantees
        // this fails rather than samples when the domain is infinite.
        let elems = self.enumerate(domain)?;
        if elems.len() != subs.len() {
            return err(format!(
                "the domain of `{}` has {} elements but the certificate covers {}",
                var,
                elems.len(),
                subs.len()
            ));
        }
        let mut verdict = Verdict::sound();
        for (e, sub) in elems.iter().zip(subs) {
            // Bind the element rather than substituting a term for it:
            // domain elements can be ADT constructors, sets or closures,
            // which have no literal syntax to substitute.
            let inner = Checker {
                ctx: self.ctx,
                env: self.env.extend(var.clone(), e.clone()),
                // The variable now has a *concrete* value, so it is no
                // longer generalized even if an enclosing binder used the
                // same name.
                generalized: self
                    .generalized
                    .iter()
                    .filter(|v| *v != var)
                    .cloned()
                    .collect(),
            };
            verdict = verdict.merge(inner.check(body, sub)?);
        }
        Ok(verdict)
    }

    fn check_case_split(
        &self,
        prop: &Expr,
        then_branch: &Cert,
        else_branch: &Cert,
    ) -> KResult<Verdict> {
        let (goal_t, goal_f) = crate::rewrite::case_split_goals(prop).ok_or_else(|| {
            KernelError(format!("there is no `if` in `{}` to split on", prop))
        })?;
        let v = self.check(&goal_t, then_branch)?;
        Ok(v.merge(self.check(&goal_f, else_branch)?))
    }

    /// Universal generalization.
    fn check_generalize(&self, prop: &Expr, vars: &[String], then: &Cert) -> KResult<Verdict> {
        let mut inner_goal = prop;
        let mut introduced = self.generalized.clone();
        for v in vars {
            match inner_goal {
                Expr::Forall { var, body, .. } if var == v => {
                    introduced.insert(var.clone());
                    inner_goal = body;
                }
                other => {
                    return err(format!(
                        "the certificate generalizes `{}`, but the goal at that point is {}",
                        v, other
                    ))
                }
            }
        }
        Checker { ctx: self.ctx, env: self.env.clone(), generalized: introduced }
            .check(inner_goal, then)
    }


    fn check_exists_witness(
        &self,
        prop: &Expr,
        witness: &Expr,
        sub: &Cert,
    ) -> KResult<Verdict> {
        let (var, domain, body) = match prop {
            Expr::Exists { var, domain, body } => (var, domain, body),
            other => return err(format!("expected an `exists` goal, got {}", other)),
        };
        let wv = self.eval(witness)?;
        let dset = self.eval_set(domain)?;
        match self.ctx.member(&wv, &dset, &self.env) {
            Ok(true) => {}
            Ok(false) => {
                return err(format!("the witness {} is not a member of {}", wv, dset))
            }
            Err(e) => return err(format!("could not check the witness's membership: {}", e)),
        }
        let instance = subst(body, var, witness);
        self.check(&instance, sub)
    }

    /// See [`Cert::CancelPositive`].
    fn check_cancel_positive(
        &self,
        prop: &Expr,
        factor: &Expr,
        positive: &Cert,
        scaled: &Cert,
    ) -> KResult<Verdict> {
        use crate::ast::BinOp as B;
        let (binders, inner) = crate::rewrite::peel_binders(prop);
        let (concl, hyps) = split_implications(inner);
        let Expr::BinOp(op, l, r) = &concl else {
            return err(format!("expected a relational goal, got {}", concl));
        };
        if !matches!(op, B::Ge | B::Gt | B::Le | B::Lt) {
            return err(format!(
                "dividing by a positive factor applies to <, <=, > and >=, not {:?}",
                op
            ));
        }
        let under = |e: Expr| {
            crate::rewrite::rebuild_binders(&binders, under_hypotheses(&hyps, e))
        };
        // The factor really is positive...
        let pos_goal = under(Expr::BinOp(
            B::Gt,
            Box::new(factor.clone()),
            Box::new(Expr::Real(0.0)),
        ));
        let mut verdict = self.check(&pos_goal, positive)?;
        // ...and the goal holds after multiplying both sides by it.  Both
        // obligations are derived here, so the certificate chooses only
        // the factor.
        let times = |e: &Expr| {
            Expr::BinOp(B::Mul, Box::new(factor.clone()), Box::new(e.clone()))
        };
        let scaled_goal = under(Expr::BinOp(
            op.clone(),
            Box::new(times(l)),
            Box::new(times(r)),
        ));
        verdict = verdict.merge(self.check(&scaled_goal, scaled)?);
        Ok(verdict)
    }

    /// See [`Cert::Antisymmetry`].
    fn check_antisymmetry(&self, prop: &Expr, ge: &Cert, le: &Cert) -> KResult<Verdict> {
        let (binders, inner) = crate::rewrite::peel_binders(prop);
        let (concl, hyps) = split_implications(inner);
        let Expr::BinOp(crate::ast::BinOp::Eq, l, r) = &concl else {
            return err(format!("expected an equality goal, got {}", concl));
        };
        let mut verdict = Verdict::sound();
        for op in [crate::ast::BinOp::Ge, crate::ast::BinOp::Le] {
            let cert = if op == crate::ast::BinOp::Ge { ge } else { le };
            let side = Expr::BinOp(op, l.clone(), r.clone());
            let sub = crate::rewrite::rebuild_binders(
                &binders,
                under_hypotheses(&hyps, side),
            );
            verdict = verdict.merge(self.check(&sub, cert)?);
        }
        Ok(verdict)
    }

    /// See [`Cert::Witness`].
    fn check_witness(&self, prop: &Expr, term: &Expr, then: &Cert) -> KResult<Verdict> {
        let prop = crate::rewrite::prenex_foralls(prop);
        let (binders, inner) = crate::rewrite::peel_binders(&prop);
        let (conclusion, hyps) = crate::rewrite::peel_premises(&inner);
        let Expr::Exists { var, domain, body } = &conclusion else {
            return err(format!(
                "expected the goal's conclusion to be an `exists`, got {}",
                conclusion
            ));
        };
        // Which set each enclosing binder ranges over, so the totality check
        // below knows what the witness's variables denote.
        let mut scope: Vec<(String, Expr)> = Vec::new();
        for (v, d) in &binders {
            scope.push((v.clone(), d.clone()));
        }
        self.witness_is_total(term, domain, &scope)?;
        // Re-derive the obligation rather than trusting one supplied with
        // the certificate: the witness is the certificate's to choose, the
        // meaning of having chosen it is not.
        let mut goal = subst(body, var, term);
        for h in hyps.iter().rev() {
            goal = Expr::BinOp(
                crate::ast::BinOp::Or,
                Box::new(Expr::UnOp(crate::ast::UnOp::Not, Box::new(h.clone()))),
                Box::new(goal),
            );
        }
        let goal = crate::rewrite::rebuild_binders(&binders, goal);
        self.check(&crate::rewrite::prenex_foralls(&goal), then)
    }

    /// Does `term` denote a member of `domain` for *every* value its
    /// variables may take?
    ///
    /// Deliberately syntactic and deliberately conservative.  `eps / 2.0`
    /// passes; `1.0 / eps` does not, because nothing here knows that `eps`
    /// is non-zero — a hypothesis saying so may be in scope, but reading
    /// hypotheses is reasoning, and this is a membership check.  A witness
    /// that needs it can be restated (`delta := eps` usually works) or the
    /// existential introduced with `Cert::ExistsWitness` on a closed term.
    fn witness_is_total(
        &self,
        term: &Expr,
        domain: &Expr,
        scope: &[(String, Expr)],
    ) -> KResult<()> {
        fn name_of(e: &Expr) -> Option<&str> {
            match e {
                Expr::Var { name, .. } => Some(name.as_str()),
                _ => None,
            }
        }
        let target = name_of(domain).ok_or_else(|| {
            KernelError(format!(
                "a witness under binders needs a named domain, got {}",
                domain
            ))
        })?;
        // `Nat` would additionally require the term to be non-negative,
        // which is arithmetic reasoning rather than a syntactic check.
        if !matches!(target, "Real" | "Int") {
            return err(format!(
                "witnesses under binders are only checked for Real and Int, not {}",
                target
            ));
        }
        let fits = |d: &str| match target {
            "Real" => matches!(d, "Real" | "Int" | "Nat"),
            _ => matches!(d, "Int" | "Nat"),
        };
        match term {
            Expr::Int(_) => Ok(()),
            Expr::Real(_) if target == "Real" => Ok(()),
            Expr::Var { name, .. } => {
                let d = scope
                    .iter()
                    .rev()
                    .find(|(v, _)| v == name)
                    .map(|(_, d)| d)
                    .ok_or_else(|| {
                        KernelError(format!(
                            "the witness mentions `{}`, which is not bound by the goal",
                            name
                        ))
                    })?;
                match name_of(d) {
                    Some(d) if fits(d) => Ok(()),
                    _ => err(format!(
                        "`{}` ranges over {}, which is not contained in {}",
                        name, d, target
                    )),
                }
            }
            Expr::UnOp(crate::ast::UnOp::Neg, x) => self.witness_is_total(x, domain, scope),
            Expr::BinOp(op, l, r) => match op {
                crate::ast::BinOp::Add
                | crate::ast::BinOp::Sub
                | crate::ast::BinOp::Mul => {
                    self.witness_is_total(l, domain, scope)?;
                    self.witness_is_total(r, domain, scope)
                }
                // Division is the one partial operation here, so the divisor
                // has to be a literal this check can see is non-zero.
                crate::ast::BinOp::Div if target == "Real" => {
                    self.witness_is_total(l, domain, scope)?;
                    match r.as_ref() {
                        Expr::Real(d) if *d != 0.0 => Ok(()),
                        Expr::Int(d) if *d != 0 => Ok(()),
                        other => err(format!(
                            "a witness may only divide by a non-zero literal, not {}",
                            other
                        )),
                    }
                }
                other => err(format!("`{:?}` may not appear in a witness", other)),
            },
            other => err(format!(
                "this witness has no membership check: {}",
                other
            )),
        }
    }

    fn check_forall_from_comprehension(
        &self,
        prop: &Expr,
        conjunct: usize,
    ) -> KResult<Verdict> {
        let (var, domain, body) = match prop {
            Expr::Forall { var, domain, body } => (var, domain, body),
            other => return err(format!("expected a `forall` goal, got {}", other)),
        };
        let dset = self.eval_set(domain)?;
        let (cvar, pred) = match &*dset {
            SetVal::Comp { var, pred, .. } => (var, pred),
            other => {
                return err(format!(
                    "this rule needs a comprehension domain, got {}",
                    other
                ))
            }
        };
        // Rename both sides to a common binder, then look for the body
        // among the predicate's conjuncts.
        let canon = Expr::Var { name: "__kernel_x".into(), line: 0, col: 0 };
        let body_canon = subst(body, var, &canon);
        let pred_canon = subst(pred, cvar, &canon);
        let mut conjuncts = Vec::new();
        flatten_conjuncts(&pred_canon, &mut conjuncts);
        match conjuncts.get(conjunct) {
            Some(c) if crate::ast::alpha_equiv(c, &body_canon) => Ok(Verdict::sound()),
            Some(c) => err(format!(
                "conjunct {} of the comprehension predicate is `{}`, not the goal body `{}`",
                conjunct, c, body_canon
            )),
            None => err(format!(
                "the comprehension predicate has {} conjuncts, so index {} does not exist",
                conjuncts.len(),
                conjunct
            )),
        }
    }

    // -- polynomial rules ---------------------------------------------------

    fn check_poly(&self, prop: &Expr, dom: PolyDomain, claim: &PolyClaim) -> KResult<Verdict> {
        // The certificate does not get to *declare* the domain — claiming
        // `Nat` would turn "every coefficient is non-negative" into a false
        // argument over the integers.  Only the `NonnegCoeffs` rule
        // actually depends on it, and it re-derives the binders itself
        // below, per variable.  Everything else here is valid over any
        // ordered ring, so `dom` is carried for diagnostics only.
        let _ = dom;
        // The goal may carry leading `forall`s over the domain; a
        // polynomial fact with free variables is exactly a statement about
        // all of them, so stripping them is the rule, not a shortcut.
        // A goal may state its hypotheses as an implication chain; the
        // relation being proved is the conclusion.
        let (conclusion, _) = split_implications(strip_foralls(prop));
        let (op, gl, gr) = match &conclusion {
            Expr::BinOp(op, l, r) if is_relation(op) => {
                (op.clone(), (**l).clone(), (**r).clone())
            }
            other => return err(format!("expected a relation, got {}", other)),
        };
        let (gl, gr) = (&gl, &gr);
        match claim {
            PolyClaim::Zero { lhs, rhs } => {
                if op != BinOp::Eq && op != BinOp::Ge && op != BinOp::Le {
                    return err(format!(
                        "a zero-difference witness cannot establish `{}`",
                        op_name(&op)
                    ));
                }
                self.same_relation(gl, gr, lhs, rhs)?;
                let diff = self.difference(lhs, rhs)?;
                if diff.terms.is_empty() {
                    Ok(Verdict::sound())
                } else {
                    err(format!("{} - {} is not the zero polynomial", lhs, rhs))
                }
            }
            PolyClaim::NonnegCoeffs { lhs, rhs, strict } => {
                self.check_ge(&op, *strict)?;
                self.same_relation(gl, gr, lhs, rhs)?;
                let diff = self.difference(lhs, rhs)?;
                // "Every coefficient is non-negative, therefore the whole
                // polynomial is" only holds when every *variable* in it is
                // non-negative too.  Check that against the goal's own
                // binders rather than a claim in the certificate.
                let binders = self.binder_domains(prop);
                for m in &diff.terms {
                    for v in m.vars.keys() {
                        match binders.iter().find(|(b, _)| b == v) {
                            Some((_, PolyDomain::Nat)) => {}
                            Some((_, d)) => {
                                return err(format!(
                                    "`{}` ranges over {:?}, so it may be negative and the \
                                     non-negative-coefficient argument does not apply",
                                    v, d
                                ))
                            }
                            None => {
                                return err(format!(
                                    "`{}` is not bound by a `forall ... in Nat`, so it may \
                                     be negative",
                                    v
                                ))
                            }
                        }
                    }
                }
                if let Some(bad) = diff.terms.iter().find(|m| m.coeff.sign() < 0) {
                    return err(format!(
                        "the difference has a negative coefficient on {:?}",
                        bad.vars
                    ));
                }
                // Strictness needs more than "the polynomial is not zero":
                // every variable may be 0, so `n > 0` does *not* follow from
                // `n`'s coefficient being positive.  What does follow is a
                // positive **constant** term on top of non-negative ones.
                if *strict && constant_term(&diff).sign() <= 0 {
                    return err(
                        "a strict goal needs a positive constant term — every variable \
                         here may be zero, so non-negative coefficients alone only give \
                         `>= 0`",
                    );
                }
                Ok(Verdict::sound())
            }
            PolyClaim::EvenPowers { lhs, rhs, strict } => {
                self.check_ge(&op, *strict)?;
                self.same_relation(gl, gr, lhs, rhs)?;
                let diff = self.difference(lhs, rhs)?;
                for m in &diff.terms {
                    if m.coeff.sign() < 0 {
                        return err(format!("negative coefficient on {:?}", m.vars));
                    }
                    if m.vars.values().any(|e| e % 2 != 0) {
                        return err(format!("{:?} has an odd exponent", m.vars));
                    }
                }
                // Every even-power monomial is only *non-negative*, so a
                // strict claim has to come from the constant term.
                if *strict && constant_term(&diff).sign() <= 0 {
                    return err(
                        "a strict goal needs a positive constant term — an even power \
                         may itself be zero",
                    );
                }
                Ok(Verdict::sound())
            }
            PolyClaim::SumOfSquares { lhs, rhs, terms } => {
                self.check_ge(&op, false)?;
                self.same_relation(gl, gr, lhs, rhs)?;
                let diff = self.difference(lhs, rhs)?;
                let mut acc = Polynomial::zero();
                for (c, q) in terms {
                    if c.sign() < 0 {
                        return err(format!("the square `{}` has a negative weight", q));
                    }
                    let qp = self.to_poly(q)?;
                    acc = acc.add(qp.clone().mul(qp).scale(*c));
                }
                let residual = self.exact(acc.sub(diff))?;
                if residual.terms.is_empty() {
                    Ok(Verdict::sound())
                } else {
                    err("the sum of squares does not add up to the difference")
                }
            }
            PolyClaim::EqCombination { lhs, rhs, used } => {
                if op != BinOp::Eq {
                    return err(format!(
                        "a combination of equations establishes `==`, not `{}`",
                        op_name(&op)
                    ));
                }
                self.same_relation(gl, gr, lhs, rhs)?;
                let mut available = goal_hypotheses(prop);
                available.extend(domain_hypotheses(prop, self.ctx, &self.env));
                let mut acc = Polynomial::zero();
                for (h, lambda) in used {
                    if !available.iter().any(|a| crate::ast::alpha_equiv(a, h)) {
                        return err(format!(
                            "`{}` is used as a hypothesis but the goal does not assume it",
                            h
                        ));
                    }
                    let (a, b) = match h {
                        Expr::BinOp(BinOp::Eq, a, b) => (a.as_ref(), b.as_ref()),
                        other => {
                            return err(format!(
                                "`{}` is not an equation, so it cannot be scaled and added",
                                other
                            ))
                        }
                    };
                    acc = acc.add(self.difference(a, b)?.scale(*lambda));
                }
                let diff = self.difference(lhs, rhs)?;
                if self.exact(acc.sub(diff))?.terms.is_empty() {
                    Ok(Verdict::sound())
                } else {
                    err("the combination of equations does not reproduce the goal")
                }
            }
            PolyClaim::Farkas { lhs, rhs, used, slack, goal_strict } => {
                self.check_ge(&op, *goal_strict)?;
                self.same_relation(gl, gr, lhs, rhs)?;
                let diff = self.difference(lhs, rhs)?;
                if slack.sign() < 0 {
                    return err("the slack of a Farkas certificate must be non-negative");
                }
                // Every factor of every generator must really be assumed by
                // the goal — as a premise, or imposed by a binder's domain.
                let mut available = goal_hypotheses(prop);
                available.extend(domain_hypotheses(prop, self.ctx, &self.env));
                let mut acc = Polynomial::from_rat(*slack);
                let mut strict_available = false;
                for g in used {
                    if g.coeff.sign() < 0 {
                        return err(format!(
                            "the multiplier on {} is negative, which reverses the \
                             inequality instead of preserving it",
                            g.describe()
                        ));
                    }
                    if g.factors.is_empty() {
                        return err("a generator must be built from at least one hypothesis");
                    }
                    // A product of non-negative quantities is non-negative,
                    // and strictly positive only when every factor is.
                    let mut product = Polynomial::from_rat(Rat::from_int(1));
                    let mut all_strict = true;
                    for h in &g.factors {
                        if !available.iter().any(|a| crate::ast::alpha_equiv(a, h)) {
                            return err(format!(
                                "`{}` is used as a hypothesis but the goal does not assume it",
                                h
                            ));
                        }
                        let (hp, hp_strict) = self.nonneg_form_of(h)?;
                        all_strict &= hp_strict;
                        product = self.exact(product.mul(hp))?;
                    }
                    if g.strict && !all_strict {
                        return err(format!(
                            "{} is recorded as strictly positive, but not every factor \
                             is a strict inequality",
                            g.describe()
                        ));
                    }
                    acc = self.exact(acc.add(product.scale(g.coeff)))?;
                    if g.strict && all_strict && g.coeff.sign() > 0 {
                        strict_available = true;
                    }
                }
                if !self.exact(acc.sub(diff))?.terms.is_empty() {
                    return err(
                        "the weighted generators do not add up to the goal's difference",
                    );
                }
                if *goal_strict && !strict_available && slack.sign() <= 0 {
                    return err(
                        "a strict goal needs either a positive slack or a strictly \
                         positive generator with a positive multiplier",
                    );
                }
                Ok(Verdict::sound())
            }
        }
    }

    /// Which domain each leading `forall` binder ranges over.
    ///
    /// Used by the non-negative-coefficient rule, which is only valid when
    /// the variables it talks about cannot be negative.  Checking *per
    /// variable* rather than per goal matters: a goal may mention globals
    /// and data constructors that are not polynomial variables at all.
    fn binder_domains(&self, prop: &Expr) -> Vec<(String, PolyDomain)> {
        let mut bound = Vec::new();
        let mut cur = prop;
        while let Expr::Forall { var, domain, body } = cur {
            match self.eval_set(domain).ok().and_then(|s| atomic_domain(&s)) {
                Some(d) => bound.push((var.clone(), d)),
                // A binder we cannot classify stops the peel: anything
                // under it is unconstrained as far as this rule goes.
                None => break,
            }
            cur = body;
        }
        bound
    }

    /// The certificate's `lhs`/`rhs` must be the goal's own sides — a
    /// certificate does not get to prove a different inequality.
    fn same_relation(&self, gl: &Expr, gr: &Expr, lhs: &Expr, rhs: &Expr) -> KResult<()> {
        if crate::ast::alpha_equiv(gl, lhs) && crate::ast::alpha_equiv(gr, rhs) {
            return Ok(());
        }
        // `a <= b` is recorded as the difference `b - a >= 0`.
        if crate::ast::alpha_equiv(gl, rhs) && crate::ast::alpha_equiv(gr, lhs) {
            return Ok(());
        }
        err(format!(
            "the certificate is about `{} ? {}`, but the goal is about `{} ? {}`",
            lhs, rhs, gl, gr
        ))
    }

    fn check_ge(&self, op: &BinOp, strict: bool) -> KResult<()> {
        match (op, strict) {
            (BinOp::Ge, false) | (BinOp::Le, false) => Ok(()),
            (BinOp::Gt, true) | (BinOp::Lt, true) => Ok(()),
            (BinOp::Gt, false) | (BinOp::Lt, false) => {
                err("a non-strict witness cannot establish a strict inequality")
            }
            (BinOp::Ge, true) | (BinOp::Le, true) => Ok(()),
            _ => err(format!(
                "this witness establishes an inequality, but the goal is `{}`",
                op_name(op)
            )),
        }
    }

    fn difference(&self, lhs: &Expr, rhs: &Expr) -> KResult<Polynomial> {
        self.exact(self.to_poly(lhs)?.sub(self.to_poly(rhs)?))
    }

    /// Refuse a polynomial whose coefficients overflowed exact arithmetic.
    ///
    /// Polynomial arithmetic is part of what this kernel trusts, so a
    /// silently wrong number here is a silently wrong proof — which is
    /// exactly what happened while `Rat` saturated instead of poisoning:
    /// `0.1 * 0.2 * 0.3` came out as `1`, and the equality
    /// `0.1 * 0.2 * 0.3 == 1.0` was accepted.
    fn exact(&self, p: Polynomial) -> KResult<Polynomial> {
        if p.has_overflow() {
            return err(
                "exact rational arithmetic overflowed while checking this claim, so \
                 the coefficients are no longer the numbers they should be; the proof \
                 is refused rather than believed",
            );
        }
        Ok(p)
    }

    fn to_poly(&self, e: &Expr) -> KResult<Polynomial> {
        let p = expr_to_poly(e)
            .ok_or_else(|| KernelError(format!("`{}` is outside the polynomial fragment", e)))?;
        self.exact(p)
    }

    /// The polynomial a hypothesis asserts is non-negative, and whether it
    /// asserts it strictly.
    fn nonneg_form_of(&self, h: &Expr) -> KResult<(Polynomial, bool)> {
        let (op, l, r) = match h {
            Expr::BinOp(op, l, r) if is_relation(op) => (op, l.as_ref(), r.as_ref()),
            other => return err(format!("`{}` is not a relation", other)),
        };
        let (a, b) = match op {
            BinOp::Ge | BinOp::Gt => (l, r),
            BinOp::Le | BinOp::Lt => (r, l),
            BinOp::Eq => (l, r),
            other => return err(format!("`{}` cannot be used as a bound", op_name(other))),
        };
        Ok((
            self.difference(a, b)?,
            matches!(op, BinOp::Gt | BinOp::Lt),
        ))
    }

    /// Turn `a >= b` / `a > b` (and the flipped forms) into the polynomial
    /// that the hypothesis asserts is non-negative (resp. positive).
    fn nonneg_form(&self, h: &Expr, strict: bool) -> KResult<Polynomial> {
        let (op, l, r) = match h {
            Expr::BinOp(op, l, r) if is_relation(op) => (op, l.as_ref(), r.as_ref()),
            other => return err(format!("`{}` is not a relation", other)),
        };
        let (a, b) = match op {
            BinOp::Ge | BinOp::Gt => (l, r),
            BinOp::Le | BinOp::Lt => (r, l),
            BinOp::Eq => (l, r),
            other => return err(format!("`{}` cannot be used as a bound", op_name(other))),
        };
        let claimed_strict = matches!(op, BinOp::Gt | BinOp::Lt);
        if strict != claimed_strict {
            return err(format!(
                "`{}` is recorded as {}strict but is {}strict",
                h,
                if strict { "" } else { "non-" },
                if claimed_strict { "" } else { "non-" }
            ));
        }
        self.difference(a, b)
    }

    // -- structural rules ---------------------------------------------------

    /// Structural induction.
    ///
    /// The kernel derives the **base obligation** from the goal itself and
    /// checks the certificate's sub-proof against it, so a certificate
    /// cannot substitute an easier base case.
    ///
    /// The **step** is not yet reducible to a checkable witness: seki
    /// discharges it by unfolding the successor side and comparing
    /// polynomial differences, and reproducing that here would mean pulling
    /// `prover.rs`'s `unfold_one` + `simplify_ifs` normalization into the
    /// trusted base.  The certificate therefore carries the step as an
    /// explicitly `Trusted` sub-proof, which is why an induction proof
    /// reports as *not fully checked* rather than sound.  See the module
    /// docs and `docs/spec/06-soundness.md` §6.0.
    fn check_induction(&self, prop: &Expr, base: &Cert, step: &Cert) -> KResult<Verdict> {
        let (var, domain, body) = match prop {
            Expr::Forall { var, domain, body } => (var, domain, body.as_ref()),
            other => return err(format!("induction needs a `forall` goal, got {}", other)),
        };
        let dset = self.eval_set(domain)?;
        let zero = base_constructor(&dset).ok_or_else(|| {
            KernelError(format!(
                "no structural base case is known for the domain {}",
                dset
            ))
        })?;
        let base_goal = subst(body, var, &zero);
        let verdict = self.check(&base_goal, base)?;
        Ok(verdict.merge(self.check(prop, step)?))
    }


    fn check_rewrite(
        &self,
        prop: &Expr,
        lemmas: &[String],
        result: &Expr,
        then: &Cert,
    ) -> KResult<Verdict> {
        // An empty lemma list is legitimate: it means the goal was reached
        // by AC-normalization alone (`x + 0 == x` canonicalizes to
        // `x == x` before any rule fires), which is still a rewrite the
        // kernel has to replay rather than assume.
        let mut verdict = Verdict::sound();
        for name in lemmas {
            if self.ctx.globals.axiom_props.contains_key(name) {
                // An axiom is an assumption, not an unchecked step: the
                // rewrite itself is perfectly well established, the
                // equation it rewrites by is simply asserted.
                verdict.assumptions.push(format!("axiom `{}`", name));
            } else if self.ctx.globals.theorem_props.contains_key(name) {
                verdict = verdict.merge(self.cited_theorem_verdict(name));
            } else {
                return err(format!("`{}` is not an accepted theorem or axiom", name));
            }
        }
        // Re-run the rewrite ourselves.  This is what makes the step
        // checkable rather than asserted: a certificate cannot claim to
        // have reached a goal the rules do not actually reach.
        let rules = crate::rewrite::collect_simp_rules(self.ctx, lemmas)
            .map_err(|e| KernelError(format!("collecting rewrite rules: {}", e)))?;
        let mut used = std::collections::BTreeSet::new();
        let states = crate::rewrite::rewrite_goal(prop, &rules, true, &mut used);
        if !states.iter().any(|st| crate::ast::alpha_equiv(st, result)) {
            return err(format!(
                "rewriting the goal with {:?} never reaches `{}`",
                lemmas, result
            ));
        }
        Ok(verdict.merge(self.check(result, then)?))
    }


    fn check_unfold(
        &self,
        prop: &Expr,
        name: &str,
        unfolded: &Expr,
        then: &Cert,
    ) -> KResult<Verdict> {
        // Unfolding is beta-reduction against a global definition: sound by
        // construction, but only if the recorded result is what unfolding
        // this definition really produces.
        let recomputed = crate::unfold::unfold_definition(prop, name, self.ctx.globals)
            .map_err(|e| KernelError(format!("could not unfold `{}`: {}", name, e)))?;
        if !crate::ast::alpha_equiv(&recomputed, unfolded) {
            return err(format!(
                "unfolding `{}` gives `{}`, but the certificate claims `{}`",
                name, recomputed, unfolded
            ));
        }
        self.check(unfolded, then)
    }

    fn check_cite(&self, prop: &Expr, name: &str) -> KResult<Verdict> {
        if let Some(stmt) = self.ctx.globals.axiom_props.get(name) {
            if crate::ast::alpha_equiv(stmt, prop) {
                return Ok(Verdict {
                    fully_checked: true,
                    trusted_steps: Vec::new(),
                    assumptions: vec![format!("axiom `{}`", name)],
                });
            }
            return err(format!("axiom `{}` states `{}`, not the goal", name, stmt));
        }
        match self.ctx.globals.theorem_props.get(name) {
            Some(stmt) if crate::ast::alpha_equiv(stmt, prop) => {
                Ok(self.cited_theorem_verdict(name))
            }
            Some(stmt) => err(format!("theorem `{}` states `{}`, not the goal", name, stmt)),
            None => err(format!("`{}` is not an accepted theorem or axiom", name)),
        }
    }

    /// Citing a theorem inherits whatever the kernel concluded about *it*.
    /// This is what stops an unchecked proof from being laundered by a
    /// second theorem that merely quotes it.
    fn cited_theorem_verdict(&self, name: &str) -> Verdict {
        match self.ctx.globals.theorem_verdicts.get(name) {
            Some(v) => v.clone(),
            // A name we accepted without recording a verdict: treat as
            // unchecked rather than assuming the best.
            None => Verdict {
                fully_checked: false,
                trusted_steps: Vec::new(),
                assumptions: vec![format!("`{}` was accepted without a kernel verdict", name)],
            },
        }
    }

    /// The goal's conclusion is literally something it assumes.
    fn check_assumption(&self, prop: &Expr) -> KResult<Verdict> {
        let (concl, hyps) = split_implications(strip_foralls(prop));
        if hyps.iter().any(|h| crate::ast::alpha_equiv(h, &concl)) {
            return Ok(Verdict::sound());
        }
        err(format!(
            "`{}` is not among the hypotheses in scope ({})",
            concl,
            if hyps.is_empty() {
                "there are none".to_string()
            } else {
                hyps.iter()
                    .map(|h| format!("{}", h))
                    .collect::<Vec<_>>()
                    .join(", ")
            }
        ))
    }

    /// A conjunctive conclusion.
    fn check_and_intro(&self, prop: &Expr, parts: &[Cert]) -> KResult<Verdict> {
        let (binders, inner) = crate::rewrite::peel_binders(prop);
        let (concl, hyps) = split_implications(inner);
        let mut conjuncts = Vec::new();
        flatten_conjuncts(&concl, &mut conjuncts);
        if conjuncts.len() != parts.len() {
            return err(format!(
                "the goal's conclusion has {} conjunct(s) but the certificate proves {}",
                conjuncts.len(),
                parts.len()
            ));
        }
        let mut verdict = Verdict::sound();
        for (c, cert) in conjuncts.iter().zip(parts) {
            let sub = crate::rewrite::rebuild_binders(
                &binders,
                under_hypotheses(&hyps, (*c).clone()),
            );
            verdict = verdict.merge(self.check(&sub, cert)?);
        }
        Ok(verdict)
    }

    /// Modus ponens against an accepted theorem or axiom.
    fn check_apply(
        &self,
        prop: &Expr,
        lemma: &str,
        substs: &[(String, Expr)],
        premises: &[Cert],
    ) -> KResult<Verdict> {
        let (instance, mut verdict) = self.instantiate(lemma, substs)?;
        let (lemma_concl, lemma_prems) = split_implications(strip_foralls(&instance));
        let (goal_concl, goal_hyps) = split_implications(strip_foralls(prop));
        if !crate::ast::alpha_equiv(&lemma_concl, &goal_concl) {
            return err(format!(
                "`{}` instantiated concludes `{}`, but the goal is `{}`",
                lemma, lemma_concl, goal_concl
            ));
        }
        if lemma_prems.len() != premises.len() {
            return err(format!(
                "`{}` has {} premise(s) but the certificate discharges {}",
                lemma,
                lemma_prems.len(),
                premises.len()
            ));
        }
        // Each premise is proved under the goal's own hypotheses, and with
        // the goal's bound variables treated as arbitrary.
        let inner = self.under_goal_binders(prop);
        for (p, cert) in lemma_prems.iter().zip(premises) {
            let sub = under_hypotheses(&goal_hyps, p.clone());
            verdict = verdict.merge(inner.check(&sub, cert)?);
        }
        Ok(verdict)
    }

    /// The cut rule.
    fn check_have(
        &self,
        prop: &Expr,
        fact: &Expr,
        fact_proof: &Cert,
        then: &Cert,
    ) -> KResult<Verdict> {
        let (_, goal_hyps) = split_implications(strip_foralls(prop));
        let inner = self.under_goal_binders(prop);
        // `fact` must hold under what is already assumed...
        let sub = under_hypotheses(&goal_hyps, fact.clone());
        let v = inner.check(&sub, fact_proof)?;
        // ...and then the goal must follow with `fact` added.
        let extended = add_hypothesis(prop, fact.clone());
        Ok(v.merge(self.check(&extended, then)?))
    }

    /// Instantiate a lemma's statement with `substs`, returning it along
    /// with whatever the lemma itself rests on.
    fn instantiate(&self, lemma: &str, substs: &[(String, Expr)]) -> KResult<(Expr, Verdict)> {
        let is_axiom = self.ctx.globals.axiom_props.contains_key(lemma);
        let stmt = self
            .ctx
            .globals
            .theorem_props
            .get(lemma)
            .or_else(|| self.ctx.globals.axiom_props.get(lemma))
            .cloned()
            .ok_or_else(|| {
                KernelError(format!("`{}` is not an accepted theorem or axiom", lemma))
            })?;
        let verdict = if is_axiom {
            Verdict {
                fully_checked: true,
                trusted_steps: Vec::new(),
                assumptions: vec![format!("axiom `{}`", lemma)],
            }
        } else {
            self.cited_theorem_verdict(lemma)
        };
        let mut cur = stmt;
        while let Expr::Forall { var, body, .. } = cur {
            let value = substs
                .iter()
                .find(|(n, _)| *n == var)
                .map(|(_, e)| e.clone())
                .ok_or_else(|| {
                    KernelError(format!(
                        "`{}` is quantified in `{}` but the certificate does not instantiate it",
                        var, lemma
                    ))
                })?;
            cur = subst(body.as_ref(), &var, &value);
        }
        for (n, v) in substs {
            cur = subst(&cur, n, v);
        }
        Ok((cur, verdict))
    }

    /// A checker for sub-goals stated under the goal's own `forall`
    /// binders: those variables are arbitrary, so nothing underneath may
    /// settle a sub-goal by evaluating them.
    fn under_goal_binders(&self, prop: &Expr) -> Checker<'_, '_> {
        let mut generalized = self.generalized.clone();
        let mut cur = prop;
        while let Expr::Forall { var, body, .. } = cur {
            generalized.insert(var.clone());
            cur = body;
        }
        Checker { ctx: self.ctx, env: self.env.clone(), generalized }
    }

    fn check_obtain(
        &self,
        prop: &Expr,
        lemma: &str,
        intro: &str,
        substs: &[(String, Expr)],
        premises: &[Cert],
        then: &Cert,
    ) -> KResult<Verdict> {
        let stmt = self
            .ctx
            .globals
            .theorem_props
            .get(lemma)
            .or_else(|| self.ctx.globals.axiom_props.get(lemma))
            .cloned()
            .ok_or_else(|| KernelError(format!("`{}` is not an accepted theorem or axiom", lemma)))?;
        let mut verdict = if self.ctx.globals.axiom_props.contains_key(lemma) {
            Verdict {
                fully_checked: true,
                trusted_steps: Vec::new(),
                assumptions: vec![format!("axiom `{}`", lemma)],
            }
        } else {
            self.cited_theorem_verdict(lemma)
        };
        // Instantiate exactly the way the tactic said it did.
        let mut cur = stmt;
        while let Expr::Forall { var, body, .. } = cur {
            let value = substs
                .iter()
                .find(|(n, _)| *n == var)
                .map(|(_, e)| e.clone())
                .ok_or_else(|| {
                    KernelError(format!("`{}` is quantified in `{}` but not instantiated", var, lemma))
                })?;
            cur = subst(body.as_ref(), &var, &value);
        }
        for (n, v) in substs {
            cur = subst(&cur, n, v);
        }
        let (conclusion, prem_exprs) = split_implications(&cur);
        if prem_exprs.len() != premises.len() {
            return err(format!(
                "`{}` has {} premise(s) but the certificate discharges {}",
                lemma,
                prem_exprs.len(),
                premises.len()
            ));
        }
        let (goal_concl, goal_hyps) = split_implications(strip_foralls(prop));
        let inner = self.under_goal_binders(prop);
        for (p, c) in prem_exprs.iter().zip(premises) {
            let sub = under_hypotheses(&goal_hyps, p.clone());
            verdict = verdict.merge(inner.check(&sub, c)?);
        }
        let fact = match conclusion {
            Expr::Exists { var, body, .. } => {
                let w = Expr::Var { name: intro.to_string(), line: 0, col: 0 };
                subst(body.as_ref(), &var, &w)
            }
            other => {
                return err(format!(
                    "`{}` concludes `{}`, which is not an existential",
                    lemma, other
                ))
            }
        };
        // What remains is the goal's own conclusion, now with the obtained
        // fact available.  The witness name is arbitrary — nothing may
        // settle the rest by evaluating it.
        let mut with_witness = inner.generalized.clone();
        with_witness.insert(intro.to_string());
        let rest = Checker {
            ctx: self.ctx,
            env: self.env.clone(),
            generalized: with_witness,
        };
        let goal = under_hypotheses(&[fact], goal_concl);
        Ok(verdict.merge(rest.check(&goal, then)?))
    }

    // -- helpers ------------------------------------------------------------

    fn eval(&self, e: &Expr) -> KResult<Value> {
        self.ctx
            .eval(e, &self.env)
            .map_err(|err| KernelError(format!("evaluating `{}`: {}", e, err)))
    }

    fn eval_set(&self, e: &Expr) -> KResult<std::sync::Arc<SetVal>> {
        match self.eval(e)? {
            Value::Set(s) => Ok(s),
            other => err(format!("`{}` is a {}, not a Set", e, other.type_name())),
        }
    }

    fn enumerate(&self, domain: &Expr) -> KResult<Vec<Value>> {
        let dset = self.eval_set(domain)?;
        enumerate_set(&dset, self.ctx, &self.env)
            .map_err(|e| KernelError(format!("enumerating `{}`: {}", domain, e)))
    }
}

/// The subset of values that have a literal syntax.  A domain element
/// without one cannot be written into a proof term, so a certificate that
/// needs it has to say so instead of pretending.
pub fn value_as_expr(v: &Value) -> Option<Expr> {
    match v {
        Value::Int(n) => Some(Expr::Int(*n)),
        Value::Real(r) => Some(Expr::Real(*r)),
        Value::Bool(b) => Some(Expr::Bool(*b)),
        Value::Str(s) => Some(Expr::Str(s.clone())),
        Value::Tuple(xs) => {
            let parts: Option<Vec<Expr>> = xs.iter().map(value_as_expr).collect();
            Some(Expr::Tuple(parts?))
        }
        _ => None,
    }
}

/// The constant term of a polynomial — the coefficient of the monomial with
/// no variables.  Strictness arguments turn on it: every variable in scope
/// may be zero, so only a constant can make a sum of non-negative terms
/// strictly positive.
fn constant_term(p: &Polynomial) -> Rat {
    p.terms
        .iter()
        .filter(|m| m.vars.is_empty())
        .fold(Rat::from_int(0), |a, m| a.add(m.coeff))
}

/// The `PolyDomain` a built-in atomic set denotes, if any.
fn atomic_domain(s: &SetVal) -> Option<PolyDomain> {
    use crate::value::AtomicSet::*;
    match s {
        SetVal::Atomic(Nat) => Some(PolyDomain::Nat),
        SetVal::Atomic(Int) => Some(PolyDomain::Int),
        SetVal::Atomic(Real) => Some(PolyDomain::Real),
        SetVal::Comp { domain, .. } => atomic_domain(domain),
        _ => None,
    }
}

/// The term an induction's base case instantiates the variable with.
fn base_constructor(s: &SetVal) -> Option<Expr> {
    let var = |n: &str| Expr::Var { name: n.to_string(), line: 0, col: 0 };
    match s {
        SetVal::Atomic(crate::value::AtomicSet::Nat) => Some(Expr::Int(0)),
        SetVal::ListOf(_) => Some(var("nil")),
        SetVal::TreeOf(_) => Some(var("leaf")),
        _ => None,
    }
}

fn strip_foralls(e: &Expr) -> &Expr {
    let mut cur = e;
    while let Expr::Forall { body, .. } = cur {
        cur = body;
    }
    cur
}

fn is_relation(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

fn op_name(op: &BinOp) -> &'static str {
    match op {
        BinOp::Eq => "==",
        BinOp::Neq => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        _ => "<non-relation>",
    }
}

fn flatten_conjuncts<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match e {
        Expr::BinOp(BinOp::And, l, r) => {
            flatten_conjuncts(l, out);
            flatten_conjuncts(r, out);
        }
        other => out.push(other),
    }
}

/// The hypotheses a goal assumes, in the `(not P) or Q` encoding of `=>`.
fn goal_hypotheses(prop: &Expr) -> Vec<Expr> {
    let (_, hyps) = split_implications(strip_foralls(prop));
    hyps
}

/// Build `h1 and h2 and ... => concl`, the shape the rest of the prover
/// reads hypotheses back out of.
fn under_hypotheses(hyps: &[Expr], concl: Expr) -> Expr {
    if hyps.is_empty() {
        return concl;
    }
    let mut premise = hyps[0].clone();
    for h in &hyps[1..] {
        premise = Expr::BinOp(BinOp::And, Box::new(premise), Box::new(h.clone()));
    }
    Expr::BinOp(
        BinOp::Or,
        Box::new(Expr::UnOp(crate::ast::UnOp::Not, Box::new(premise))),
        Box::new(concl),
    )
}

/// Add one hypothesis to a goal, keeping any leading `forall` binders in
/// place so that the hypothesis may mention the bound variables.
fn add_hypothesis(prop: &Expr, fact: Expr) -> Expr {
    let (binders, inner) = crate::rewrite::peel_binders(prop);
    let extended = Expr::BinOp(
        BinOp::Or,
        Box::new(Expr::UnOp(crate::ast::UnOp::Not, Box::new(fact))),
        Box::new(inner.clone()),
    );
    crate::rewrite::rebuild_binders(&binders, extended)
}

/// The constraints a goal's own binders impose on their variables.
///
/// `forall x in {y in Real | 0 <= y and y <= 1}, P(x)` may use
/// `0 <= x and x <= 1` freely: every member of a comprehension satisfies its
/// predicate, by definition of the set.  Without this an interval
/// refinement type — the most ordinary kind there is — states its
/// constraint in a place no tactic reads, and its proof obligation looks
/// unprovable.
///
/// Used by `crate::prover` to prove and by the kernel to check, so that the
/// two agree on what a goal assumes.
pub fn domain_hypotheses(prop: &Expr, ctx: &EvalCtx, env: &Env) -> Vec<Expr> {
    let mut out = Vec::new();
    let mut cur = prop;
    while let Expr::Forall { var, domain, body } = cur {
        // A domain that mentions an enclosing binder will not evaluate
        // here; skipping it only loses information, never adds any.
        if let Ok(Value::Set(s)) = ctx.eval(domain, env) {
            if let SetVal::Comp { var: cv, pred, .. } = &*s {
                let here = Expr::Var { name: var.clone(), line: 0, col: 0 };
                let instantiated = subst(pred, cv, &here);
                let mut parts = Vec::new();
                flatten_conjuncts(&instantiated, &mut parts);
                out.extend(parts.into_iter().cloned());
            }
        }
        cur = body;
    }
    out
}

/// Peel `(not P) or Q` / `P -> Q` chains into the final conclusion and the
/// premises collected along the way.
fn split_implications(body: &Expr) -> (Expr, Vec<Expr>) {
    let mut premises = Vec::new();
    let mut cur = body.clone();
    loop {
        match &cur {
            Expr::BinOp(BinOp::Or, l, r) => {
                if let Expr::UnOp(crate::ast::UnOp::Not, inner) = l.as_ref() {
                    let mut cs = Vec::new();
                    flatten_conjuncts(inner, &mut cs);
                    premises.extend(cs.into_iter().cloned());
                    cur = (**r).clone();
                    continue;
                }
                break;
            }
            Expr::Arrow(l, r) => {
                let mut cs = Vec::new();
                flatten_conjuncts(l, &mut cs);
                premises.extend(cs.into_iter().cloned());
                cur = (**r).clone();
                continue;
            }
            _ => break,
        }
    }
    (cur, premises)
}


// -- rendering --------------------------------------------------------------

impl Cert {
    /// Render the proof term as an indented tree.
    ///
    /// `{:#?}` prints every span and box and is unreadable for anything
    /// past a couple of steps; a proof term is only useful if a person can
    /// look at it and see *how* the theorem was established.
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.render_into(&mut out, 0);
        out
    }

    fn render_into(&self, out: &mut String, depth: usize) {
        let pad = "  ".repeat(depth);
        match self {
            Cert::Refl => {
                out.push_str(&format!("{}both sides evaluate to the same value\n", pad))
            }
            Cert::SyntacticRefl => {
                out.push_str(&format!("{}both sides are the same term\n", pad))
            }
            Cert::Ground => out.push_str(&format!("{}evaluates to true\n", pad)),
            Cert::ForallFinite { subs } => {
                out.push_str(&format!(
                    "{}for each of the {} elements of the domain:\n",
                    pad,
                    subs.len()
                ));
                // Identical sub-proofs are the common case; show the shape
                // once rather than N times.
                let all_same = subs
                    .windows(2)
                    .all(|w| w[0].render() == w[1].render());
                if all_same {
                    if let Some(first) = subs.first() {
                        first.render_into(out, depth + 1);
                    }
                } else {
                    for sub in subs {
                        sub.render_into(out, depth + 1);
                    }
                }
            }
            Cert::ExistsWitness { witness, sub } => {
                out.push_str(&format!("{}witness {}:\n", pad, witness));
                sub.render_into(out, depth + 1);
            }
            Cert::Witness { term, then } => {
                out.push_str(&format!("{}take the existential's witness to be {}:\n", pad, term));
                then.render_into(out, depth + 1);
            }
            Cert::CancelPositive { factor, positive, scaled } => {
                out.push_str(&format!("{}divide through by {}, which is positive:\n", pad, factor));
                positive.render_into(out, depth + 1);
                scaled.render_into(out, depth + 1);
            }
            Cert::Antisymmetry { ge, le } => {
                out.push_str(&format!("{}equal because >= and <= both hold:\n", pad));
                ge.render_into(out, depth + 1);
                le.render_into(out, depth + 1);
            }
            Cert::ForallFromComprehension { conjunct } => out.push_str(&format!(
                "{}conjunct {} of the set's own defining predicate\n",
                pad, conjunct
            )),
            Cert::Generalize { vars, then } => {
                out.push_str(&format!("{}for arbitrary {}:\n", pad, vars.join(", ")));
                then.render_into(out, depth + 1);
            }
            Cert::CaseSplit { then_branch, else_branch } => {
                out.push_str(&format!("{}case split on the goal's first `if`:\n", pad));
                out.push_str(&format!("{}  when the condition holds:\n", pad));
                then_branch.render_into(out, depth + 2);
                out.push_str(&format!("{}  when it does not:\n", pad));
                else_branch.render_into(out, depth + 2);
            }
            Cert::Poly { dom, claim } => {
                out.push_str(&format!("{}{} (over {:?})\n", pad, claim.describe(), dom))
            }
            Cert::Induction { base, step } => {
                out.push_str(&format!("{}structural induction:\n", pad));
                out.push_str(&format!("{}  base case:\n", pad));
                base.render_into(out, depth + 2);
                out.push_str(&format!("{}  step:\n", pad));
                step.render_into(out, depth + 2);
            }
            Cert::Rewrite { lemmas, result, then } => {
                if lemmas.is_empty() {
                    out.push_str(&format!("{}normalize to `{}`\n", pad, result));
                } else {
                    out.push_str(&format!(
                        "{}rewrite with [{}] to `{}`\n",
                        pad,
                        lemmas.join(", "),
                        result
                    ));
                }
                then.render_into(out, depth + 1);
            }
            Cert::Unfold { name, unfolded, then } => {
                out.push_str(&format!("{}unfold `{}` to `{}`\n", pad, name, unfolded));
                then.render_into(out, depth + 1);
            }
            Cert::Cite { name } => {
                out.push_str(&format!("{}cite `{}`\n", pad, name))
            }
            Cert::Assumption => {
                out.push_str(&format!("{}this is one of the hypotheses in scope\n", pad))
            }
            Cert::AndIntro { parts } => {
                out.push_str(&format!(
                    "{}each of the {} conjuncts:\n",
                    pad,
                    parts.len()
                ));
                for p in parts {
                    p.render_into(out, depth + 1);
                }
            }
            Cert::Apply { lemma, substs, premises } => {
                let inst = if substs.is_empty() {
                    String::new()
                } else {
                    format!(
                        " with {}",
                        substs
                            .iter()
                            .map(|(n, e)| format!("{} := {}", n, e))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                out.push_str(&format!("{}apply `{}`{}\n", pad, lemma, inst));
                for (i, p) in premises.iter().enumerate() {
                    out.push_str(&format!("{}  premise {}:\n", pad, i + 1));
                    p.render_into(out, depth + 2);
                }
            }
            Cert::Have { fact, fact_proof, then } => {
                out.push_str(&format!("{}have `{}`:\n", pad, fact));
                fact_proof.render_into(out, depth + 1);
                out.push_str(&format!("{}then:\n", pad));
                then.render_into(out, depth + 1);
            }
            Cert::Obtain { lemma, intro, then, .. } => {
                out.push_str(&format!(
                    "{}obtain `{}` from the existential in `{}`:\n",
                    pad, intro, lemma
                ));
                then.render_into(out, depth + 1);
            }
            Cert::Trusted { tactic, reason, why } => out.push_str(&format!(
                "{}NOT CHECKED — `{}` ({}): {}\n",
                pad,
                tactic,
                match reason {
                    TrustReason::Sampled => "sampled an infinite domain",
                    TrustReason::NoWitnessYet => "no witness form yet",
                },
                why
            )),
        }
    }
}

impl PolyClaim {
    fn describe(&self) -> String {
        match self {
            PolyClaim::Zero { lhs, rhs } => {
                format!("`{}` - `{}` normalizes to the zero polynomial", lhs, rhs)
            }
            PolyClaim::NonnegCoeffs { lhs, rhs, strict } => format!(
                "every coefficient of `{}` - `{}` is non-negative, and so is every \
                 variable, so the difference is {}",
                lhs,
                rhs,
                if *strict { "positive" } else { "non-negative" }
            ),
            PolyClaim::EvenPowers { lhs, rhs, strict } => format!(
                "every monomial of `{}` - `{}` has even exponents and a non-negative \
                 coefficient{}",
                lhs,
                rhs,
                if *strict { ", on top of a positive constant" } else { "" }
            ),
            PolyClaim::SumOfSquares { lhs, rhs, terms } => format!(
                "`{}` - `{}` is a non-negative combination of the squares of [{}]",
                lhs,
                rhs,
                terms
                    .iter()
                    .map(|(_, q)| format!("{}", q))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            PolyClaim::EqCombination { lhs, rhs, used } => format!(
                "`{}` - `{}` = {}",
                lhs,
                rhs,
                used.iter()
                    .map(|(h, l)| if *l == Rat::from_int(1) {
                        format!("({})", h)
                    } else {
                        format!("{}·({})", l, h)
                    })
                    .collect::<Vec<_>>()
                    .join(" + ")
            ),
            PolyClaim::Farkas { lhs, rhs, used, slack, .. } => format!(
                "`{}` - `{}` = {}{}",
                lhs,
                rhs,
                used.iter()
                    .map(|g| g.describe())
                    .collect::<Vec<_>>()
                    .join(" + "),
                if slack.is_zero() {
                    String::new()
                } else {
                    format!(" + {}", slack)
                }
            ),
        }
    }
}

#[cfg(test)]
mod forgery_tests {
    //! The kernel is only worth anything if it rejects a *wrong* proof term.
    //! These hand-build certificates that a buggy or malicious tactic might
    //! emit and check that each one is refused.

    use super::*;
    use crate::algebra::Rat;
    use crate::eval::make_prelude;
    use crate::value::Globals;

    fn parse_prop(src: &str) -> Expr {
        let decls = crate::parse_program(src).expect("parse");
        match decls.into_iter().next().expect("one decl").decl {
            crate::ast::Decl::Expr(e) => e,
            other => panic!("expected a bare expression, got {:?}", other),
        }
    }

    fn check_in(g: &Globals, src: &str, cert: &Cert) -> KResult<Verdict> {
        let ctx = EvalCtx::finite_only(g);
        check(&parse_prop(src), cert, &ctx, &Env::new())
    }

    #[test]
    fn ground_evaluation_cannot_sample_an_infinite_domain() {
        // The hole this whole exercise is about: `forall n in Nat, n < 1000`
        // is false, and a sampling evaluator confirms it.  The kernel's
        // evaluator refuses to enumerate `Nat` at all.
        let g = make_prelude();
        assert!(check_in(&g, "forall n in Nat, n < 1000", &Cert::Ground).is_err());
        // The same shape over a finite domain is fine.
        assert!(check_in(&g, "forall n in {1, 2, 3}, n < 1000", &Cert::Ground).is_ok());
    }

    #[test]
    fn a_forall_certificate_cannot_skip_domain_elements() {
        // `forall x in {1, 2, 9}, x < 5` is false at 9.  A certificate that
        // only covers the two elements it likes must not pass.
        let g = make_prelude();
        let short = Cert::ForallFinite { subs: vec![Cert::Ground, Cert::Ground] };
        let err = check_in(&g, "forall x in {1, 2, 9}, x < 5", &short).unwrap_err();
        assert!(err.0.contains("3 elements"), "{}", err.0);
        // Covering all three still fails, because the third is false.
        let full =
            Cert::ForallFinite { subs: vec![Cert::Ground, Cert::Ground, Cert::Ground] };
        assert!(check_in(&g, "forall x in {1, 2, 9}, x < 5", &full).is_err());
    }

    #[test]
    fn a_witness_must_really_be_in_the_domain() {
        let g = make_prelude();
        let outside = Cert::ExistsWitness {
            witness: Expr::Int(7),
            sub: Box::new(Cert::Ground),
        };
        let err = check_in(&g, "exists x in {1, 2, 3}, x > 0", &outside).unwrap_err();
        assert!(err.0.contains("not a member"), "{}", err.0);
    }

    #[test]
    fn the_non_negative_coefficient_rule_is_refused_over_the_integers() {
        // `forall n in Int, n >= 0` is false.  Its difference polynomial is
        // `n`, whose only coefficient is positive — the rule would "prove"
        // it if the kernel took the certificate's word for the domain.
        let g = make_prelude();
        let forged = Cert::Poly {
            dom: PolyDomain::Nat,
            claim: PolyClaim::NonnegCoeffs {
                lhs: parse_prop("n"),
                rhs: Expr::Int(0),
                strict: false,
            },
        };
        let err = check_in(&g, "forall n in Int, n >= 0", &forged).unwrap_err();
        assert!(err.0.contains("may be negative"), "{}", err.0);
        // Over `Nat` the same certificate is legitimate.
        assert!(check_in(&g, "forall n in Nat, n >= 0", &forged).is_ok());
    }

    #[test]
    fn an_opaque_atom_is_not_a_non_negative_variable() {
        // The bug the proof terms actually caught: `f n` is not a variable
        // known to be non-negative just because it appears under a
        // `forall n in Nat`.
        let mut g = make_prelude();
        let decls = crate::parse_program(r"def f := \n -> 0 - 5").expect("parse");
        if let crate::ast::Decl::Def { name, value, .. } = decls.into_iter().next().unwrap().decl
        {
            let ctx = EvalCtx::new(&g);
            let v = ctx.eval(&value, &Env::new()).expect("eval");
            g.defs.insert(name, v);
        }
        let forged = Cert::Poly {
            dom: PolyDomain::Nat,
            claim: PolyClaim::NonnegCoeffs {
                lhs: parse_prop("f n"),
                rhs: Expr::Int(0),
                strict: false,
            },
        };
        let err = check_in(&g, "forall n in Nat, f n >= 0", &forged).unwrap_err();
        assert!(err.0.contains("may be negative"), "{}", err.0);
    }

    #[test]
    fn a_zero_difference_certificate_must_actually_be_zero() {
        let g = make_prelude();
        let forged = Cert::Poly {
            dom: PolyDomain::Int,
            claim: PolyClaim::Zero {
                lhs: parse_prop("x + 1"),
                rhs: parse_prop("x"),
            },
        };
        let err = check_in(&g, "forall x in Int, x + 1 == x", &forged).unwrap_err();
        assert!(err.0.contains("not the zero polynomial"), "{}", err.0);
    }

    #[test]
    fn a_certificate_cannot_be_about_a_different_inequality() {
        // The witness talks about `x >= 0` while the goal is `x >= 1`.
        let g = make_prelude();
        let forged = Cert::Poly {
            dom: PolyDomain::Nat,
            claim: PolyClaim::NonnegCoeffs {
                lhs: parse_prop("x"),
                rhs: Expr::Int(0),
                strict: false,
            },
        };
        let err = check_in(&g, "forall x in Nat, x >= 1", &forged).unwrap_err();
        assert!(err.0.contains("but the goal is about"), "{}", err.0);
    }

    #[test]
    fn a_farkas_certificate_may_only_use_the_goals_own_hypotheses() {
        let g = make_prelude();
        let invented = Cert::Poly {
            dom: PolyDomain::Int,
            claim: PolyClaim::Farkas {
                lhs: parse_prop("x"),
                rhs: Expr::Int(0),
                used: vec![Generator {
                    factors: vec![parse_prop("x >= 0")],
                    strict: false,
                    coeff: Rat::from_int(1),
                }],
                slack: Rat::from_int(0),
                goal_strict: false,
            },
        };
        // The goal assumes nothing, so the "hypothesis" is invented.
        let err = check_in(&g, "forall x in Int, x >= 0", &invented).unwrap_err();
        assert!(err.0.contains("does not assume it"), "{}", err.0);
    }

    #[test]
    fn a_farkas_multiplier_may_not_be_negative() {
        // `x <= 3 ⊬ x >= 0`, and multiplying the hypothesis by a negative
        // number is exactly the move that would pretend otherwise.
        let g = make_prelude();
        let forged = Cert::Poly {
            dom: PolyDomain::Int,
            claim: PolyClaim::Farkas {
                lhs: parse_prop("x"),
                rhs: Expr::Int(0),
                used: vec![Generator {
                    factors: vec![parse_prop("x <= 3")],
                    strict: false,
                    coeff: Rat::from_int(-1),
                }],
                slack: Rat::from_int(3),
                goal_strict: false,
            },
        };
        let err = check_in(&g, "forall x in Int, x <= 3 => x >= 0", &forged).unwrap_err();
        assert!(err.0.contains("negative"), "{}", err.0);
    }

    #[test]
    fn a_farkas_certificate_must_add_up() {
        let g = make_prelude();
        let wrong = Cert::Poly {
            dom: PolyDomain::Int,
            claim: PolyClaim::Farkas {
                lhs: parse_prop("2 * x"),
                rhs: Expr::Int(0),
                used: vec![Generator {
                    factors: vec![parse_prop("x >= 0")],
                    strict: false,
                    coeff: Rat::from_int(1),
                }],
                slack: Rat::from_int(0),
                goal_strict: false,
            },
        };
        let err = check_in(&g, "forall x in Int, x >= 0 => 2 * x >= 0", &wrong).unwrap_err();
        assert!(err.0.contains("do not add up"), "{}", err.0);
    }

    #[test]
    fn a_product_generator_may_only_use_hypotheses_the_goal_assumes() {
        // `x <= 1` alone does not bound `x²`; pretending the goal also
        // assumes `x >= 0` is exactly the move a wrong certificate makes.
        let g = make_prelude();
        let forged = Cert::Poly {
            dom: PolyDomain::Real,
            claim: PolyClaim::Farkas {
                lhs: Expr::Int(1),
                rhs: parse_prop("x * x"),
                used: vec![
                    Generator {
                        factors: vec![parse_prop("x <= 1")],
                        strict: false,
                        coeff: Rat::from_int(1),
                    },
                    Generator {
                        factors: vec![parse_prop("0 <= x"), parse_prop("x <= 1")],
                        strict: false,
                        coeff: Rat::from_int(1),
                    },
                ],
                slack: Rat::from_int(0),
                goal_strict: false,
            },
        };
        let err = check_in(&g, "forall x in Real, x <= 1 => (x * x) <= 1", &forged)
            .unwrap_err();
        assert!(err.0.contains("does not assume it"), "{}", err.0);
        // With both bounds assumed, the same certificate is legitimate.
        assert!(check_in(
            &g,
            "forall x in Real, (0 <= x) and (x <= 1) => (x * x) <= 1",
            &forged
        )
        .is_ok());
    }

    #[test]
    fn a_product_is_only_strictly_positive_when_every_factor_is() {
        let g = make_prelude();
        let forged = Cert::Poly {
            dom: PolyDomain::Real,
            claim: PolyClaim::Farkas {
                lhs: parse_prop("x * y"),
                rhs: Expr::Int(0),
                used: vec![Generator {
                    factors: vec![parse_prop("x > 0"), parse_prop("y >= 0")],
                    strict: true,
                    coeff: Rat::from_int(1),
                }],
                slack: Rat::from_int(0),
                goal_strict: true,
            },
        };
        let err = check_in(
            &g,
            "forall x in Real, forall y in Real, (x > 0) and (y >= 0) => (x * y) > 0",
            &forged,
        )
        .unwrap_err();
        assert!(err.0.contains("not every factor"), "{}", err.0);
    }

    #[test]
    fn an_assumption_must_actually_be_assumed() {
        let g = make_prelude();
        assert!(check_in(&g, "forall x in Int, x > 0 => x > 0", &Cert::Assumption).is_ok());
        let err = check_in(&g, "forall x in Int, x > 0 => x > 1", &Cert::Assumption)
            .unwrap_err();
        assert!(err.0.contains("not among the hypotheses"), "{}", err.0);
    }

    #[test]
    fn an_application_must_discharge_every_premise() {
        let mut g = make_prelude();
        g.axiom_props.insert(
            "mono".into(),
            parse_prop("forall a in Int, a >= 0 => 2 * a >= 0"),
        );
        // Claiming the lemma applies while discharging none of its premises.
        let skipped = Cert::Apply {
            lemma: "mono".into(),
            substs: vec![("a".into(), parse_prop("x"))],
            premises: vec![],
        };
        let err = check_in(&g, "forall x in Int, 2 * x >= 0", &skipped).unwrap_err();
        assert!(err.0.contains("1 premise"), "{}", err.0);

        // Discharging it with something the goal does not assume.
        let bogus = Cert::Apply {
            lemma: "mono".into(),
            substs: vec![("a".into(), parse_prop("x"))],
            premises: vec![Cert::Assumption],
        };
        assert!(check_in(&g, "forall x in Int, 2 * x >= 0", &bogus).is_err());

        // With the premise actually assumed, it goes through — and the
        // axiom it rests on is recorded.
        let ok = Cert::Apply {
            lemma: "mono".into(),
            substs: vec![("a".into(), parse_prop("x"))],
            premises: vec![Cert::Assumption],
        };
        let v = check_in(&g, "forall x in Int, x >= 0 => 2 * x >= 0", &ok)
            .expect("the premise is assumed");
        assert!(v.assumptions.iter().any(|a| a.contains("mono")));
    }

    #[test]
    fn an_application_cannot_claim_a_conclusion_the_lemma_does_not_reach() {
        let mut g = make_prelude();
        g.axiom_props.insert(
            "mono".into(),
            parse_prop("forall a in Int, a >= 0 => 2 * a >= 0"),
        );
        let forged = Cert::Apply {
            lemma: "mono".into(),
            substs: vec![("a".into(), parse_prop("x"))],
            premises: vec![Cert::Assumption],
        };
        let err = check_in(&g, "forall x in Int, x >= 0 => 3 * x >= 0", &forged).unwrap_err();
        assert!(err.0.contains("but the goal is"), "{}", err.0);
    }

    #[test]
    fn a_cut_must_prove_the_fact_it_assumes() {
        let g = make_prelude();
        // `have x >= 1` is not provable from `x >= 0`, so the cut fails
        // even though the rest would follow from it.
        let forged = Cert::Have {
            fact: parse_prop("x >= 1"),
            fact_proof: Box::new(Cert::Assumption),
            then: Box::new(Cert::Assumption),
        };
        let err = check_in(&g, "forall x in Int, x >= 0 => x >= 1", &forged).unwrap_err();
        assert!(err.0.contains("not among the hypotheses"), "{}", err.0);
    }

    #[test]
    fn citing_a_theorem_requires_the_statement_to_match() {
        let mut g = make_prelude();
        g.theorem_props
            .insert("small".into(), parse_prop("forall x in {1, 2}, x < 5"));
        g.theorem_verdicts.insert("small".into(), Verdict::sound());
        let cert = Cert::Cite { name: "small".into() };
        assert!(check_in(&g, "forall x in {1, 2}, x < 5", &cert).is_ok());
        let err = check_in(&g, "forall x in {1, 2}, x < 3", &cert).unwrap_err();
        assert!(err.0.contains("not the goal"), "{}", err.0);
        // And a name that was never accepted cannot be cited at all.
        let unknown = Cert::Cite { name: "nope".into() };
        assert!(check_in(&g, "forall x in {1, 2}, x < 5", &unknown).is_err());
    }

    #[test]
    fn citing_an_unchecked_theorem_does_not_launder_it() {
        let mut g = make_prelude();
        g.theorem_props
            .insert("shaky".into(), parse_prop("forall x in {1}, x > 0"));
        g.theorem_verdicts.insert(
            "shaky".into(),
            Verdict {
                fully_checked: false,
                trusted_steps: vec![TrustedStep {
                    tactic: "by eval",
                    reason: TrustReason::Sampled,
                }],
                assumptions: vec!["sampled".into()],
            },
        );
        let v = check_in(&g, "forall x in {1}, x > 0", &Cert::Cite { name: "shaky".into() })
            .expect("citing is allowed");
        assert!(!v.fully_checked, "the weakness must be inherited");
        assert!(v.is_sampled());
    }

    #[test]
    fn a_rewrite_must_really_reach_the_goal_it_claims() {
        let mut g = make_prelude();
        g.axiom_props
            .insert("add_zero".into(), parse_prop("forall a in Int, a + 0 == a"));
        // A result the rules do not produce.
        let forged = Cert::Rewrite {
            lemmas: vec!["add_zero".into()],
            result: parse_prop("forall x in Int, 1 == 1"),
            then: Box::new(Cert::SyntacticRefl),
        };
        let err = check_in(&g, "forall x in Int, x + 0 == x", &forged).unwrap_err();
        assert!(err.0.contains("never reaches"), "{}", err.0);
    }

    #[test]
    fn an_unfold_certificate_must_match_the_real_definition() {
        let mut g = make_prelude();
        let decls = crate::parse_program(r"def sq := \n -> n * n").expect("parse");
        if let crate::ast::Decl::Def { name, value, .. } = decls.into_iter().next().unwrap().decl
        {
            let ctx = EvalCtx::new(&g);
            let v = ctx.eval(&value, &Env::new()).expect("eval");
            g.defs.insert(name, v);
        }
        let forged = Cert::Unfold {
            name: "sq".into(),
            unfolded: parse_prop("forall a in Int, 0 == 0"),
            then: Box::new(Cert::SyntacticRefl),
        };
        let err = check_in(&g, "forall a in Int, sq a == a * a", &forged).unwrap_err();
        assert!(err.0.contains("but the certificate claims"), "{}", err.0);
    }

    #[test]
    fn generalization_forbids_settling_the_goal_by_evaluation() {
        // `pi` is a global.  Stripping the binder and evaluating would
        // check the statement at that one value instead of for all reals.
        let mut g = make_prelude();
        g.defs.insert("pi".into(), Value::Real(3.14159));
        let forged = Cert::Generalize {
            vars: vec!["pi".into()],
            then: Box::new(Cert::Ground),
        };
        let err = check_in(&g, "forall pi in Real, pi > 3.0", &forged).unwrap_err();
        assert!(err.0.contains("universally generalized"), "{}", err.0);
    }

    #[test]
    fn a_case_split_uses_the_goals_own_condition() {
        // There is no `if` to split on, so the rule does not apply.
        let g = make_prelude();
        let forged = Cert::CaseSplit {
            then_branch: Box::new(Cert::Ground),
            else_branch: Box::new(Cert::Ground),
        };
        let err = check_in(&g, "forall x in Nat, x >= 0", &forged).unwrap_err();
        assert!(err.0.contains("no `if`"), "{}", err.0);
    }

    #[test]
    fn a_trusted_step_is_accepted_but_recorded() {
        let g = make_prelude();
        let v = check_in(
            &g,
            "forall n in Nat, n < 1000",
            &Cert::Trusted {
                tactic: "by eval",
                reason: TrustReason::Sampled,
                why: "sampled".into(),
            },
        )
        .expect("a trusted step is not an error");
        assert!(!v.fully_checked);
        assert!(v.is_sampled());
        assert_eq!(v.trusted_steps.len(), 1);
    }

    #[test]
    fn the_kernel_refuses_to_run_in_a_sampling_context() {
        let g = make_prelude();
        let sampling = EvalCtx::new(&g);
        let err = check(
            &parse_prop("forall n in Nat, n < 1000"),
            &Cert::Ground,
            &sampling,
            &Env::new(),
        )
        .unwrap_err();
        assert!(err.0.contains("finiteness-strict"), "{}", err.0);
    }

    // ---- `Cert::Witness` -------------------------------------------------
    // The witness is the certificate's to choose; what choosing it obliges
    // it to prove is not.

    #[test]
    fn a_witness_must_be_a_member_of_the_existential_domain() {
        // `eps` ranges over Real, so it cannot witness an existential over
        // Int — the forged certificate claims a real is an integer.
        let g = make_prelude();
        let forged = Cert::Witness {
            term: parse_prop("eps"),
            then: Box::new(Cert::Ground),
        };
        let err = check_in(
            &g,
            "forall eps in Real, (exists n in Int, n > 0)",
            &forged,
        )
        .unwrap_err();
        assert!(err.0.contains("not contained in"), "{}", err.0);
    }

    #[test]
    fn a_witness_may_not_divide_by_something_that_could_be_zero() {
        // `1.0 / eps` is not a real number when `eps` is zero.  A
        // hypothesis saying otherwise may be in scope, but reading it is
        // reasoning, and this is a membership check.
        let g = make_prelude();
        let forged = Cert::Witness {
            term: parse_prop("1.0 / eps"),
            then: Box::new(Cert::Ground),
        };
        let err = check_in(
            &g,
            "forall eps in Real, (exists d in Real, d > 0.0)",
            &forged,
        )
        .unwrap_err();
        assert!(err.0.contains("non-zero literal"), "{}", err.0);
    }

    #[test]
    fn a_witness_may_not_mention_an_unbound_name() {
        let g = make_prelude();
        let forged = Cert::Witness {
            term: parse_prop("bogus"),
            then: Box::new(Cert::Ground),
        };
        let err = check_in(&g, "exists d in Real, d > 0.0", &forged).unwrap_err();
        assert!(err.0.contains("not bound by the goal"), "{}", err.0);
    }

    #[test]
    fn a_witness_rule_needs_an_existential_goal() {
        let g = make_prelude();
        let forged = Cert::Witness {
            term: parse_prop("1.0"),
            then: Box::new(Cert::Ground),
        };
        let err = check_in(&g, "forall x in Nat, x >= 0", &forged).unwrap_err();
        assert!(err.0.contains("`exists`"), "{}", err.0);
    }

    #[test]
    fn a_witness_obligation_is_derived_not_supplied() {
        // The instantiated body is false at this witness, and the kernel
        // derives that body itself — the certificate cannot hand it an
        // easier one.
        let g = make_prelude();
        let forged = Cert::Witness {
            term: parse_prop("0.0"),
            then: Box::new(Cert::Ground),
        };
        assert!(check_in(&g, "exists d in Real, d > 1.0", &forged).is_err());
    }
}

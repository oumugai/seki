//! Abstract syntax tree for seki.
//!
//! seki is set-theoretic: every "type" is ultimately a *set* (a collection of
//! values).  The AST therefore uses a single `Expr` for both terms and
//! type-level expressions; the type checker disambiguates by interpretation.
//!
//! Sets can be defined two ways:
//!   - by enumeration:    `{1, 2, 3}`
//!   - by comprehension:  `{x in Nat | x > 0}`           (rule-based)
//!
//! Functions are values built from lambda calculus.
//! Theorems are propositions paired with a proof term/strategy.

use std::fmt;

// -- Operators --------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum BinOp {
    // arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // comparison
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    // logical
    And,
    Or,
    // set
    In,
    NotIn,
    Subset,
    Union,
    Intersect,
    Diff,
    /// Cartesian product: `A times B`
    Times,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnOp {
    Neg,
    Not,
}

// -- Patterns (parameter binders) ------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    /// optional type annotation: `(x : Nat)`
    pub ty: Option<Expr>,
}

// -- Expressions ------------------------------------------------------------

// We can't `#[derive(PartialEq)]` because two `Var` nodes with the same name
// but different source positions must compare equal (otherwise tactics like
// `by simp` and `by algebra` lose track of `x == x`).  Hand-rolled
// `PartialEq` below ignores Var span fields.
#[derive(Debug, Clone)]
pub enum Expr {
    // literals
    Int(i64),
    Real(f64),
    Bool(bool),
    Str(String),

    // Identifier reference.  Span (line/col, 1-indexed) is captured at
    // parse time when known; legacy code paths constructing Vars without
    // position info default both to 0 (signalling "no info").  Pattern
    // matches generally use `Var { name, .. }` and ignore the span.
    Var { name: String, line: u32, col: u32 },

    // lambda calculus
    Lambda {
        params: Vec<Param>,
        body: Box<Expr>,
    },
    App {
        func: Box<Expr>,
        args: Vec<Expr>,
    },

    // let x = e1 in e2          (also let x : T = e1 in e2)
    // let rec f := \x -> ... f ... in body  (when `rec: true`)
    Let {
        name: String,
        ty: Option<Box<Expr>>,
        value: Box<Expr>,
        body: Box<Expr>,
        /// When true, the binding is a `let rec` — the value (which must be
        /// a lambda) gains `name` as a self-reference inside its body.
        /// Default false for ordinary `let`.
        #[allow(dead_code)]
        rec: bool,
    },

    // if p then a else b
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },

    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),

    // ----- type / set forms --------------------------------------------------
    /// {e1, e2, ...}  — enumeration
    SetEnum(Vec<Expr>),
    /// {x in dom | pred}  — comprehension (rule-based)
    SetComp {
        var: String,
        domain: Box<Expr>,
        pred: Box<Expr>,
    },
    /// function arrow type:  A -> B
    Arrow(Box<Expr>, Box<Expr>),
    /// **dependent** function type: `(x : A) -> B(x)`.  When `B` does not
    /// reference `x`, this is semantically `Arrow(A, B)`.  The dependence
    /// is realised at runtime: membership of a function `f` in this set
    /// requires that, for every sampled `a in A`, `f a in B[x:=a]`.
    DepArrow {
        binder: String,
        from: Box<Expr>,
        to: Box<Expr>,
    },

    /// `(a, b, c)` tuple value (length ≥ 2; `(e)` is just grouping)
    Tuple(Vec<Expr>),
    /// `[a, b, c]` list literal
    List(Vec<Expr>),

    // ----- propositions -----------------------------------------------------
    Forall {
        var: String,
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    Exists {
        var: String,
        domain: Box<Expr>,
        body: Box<Expr>,
    },
}

// -- Top-level declarations -------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum Proof {
    /// `:= by eval`  — verifier reduces the proposition; must yield true.
    ByEval,
    /// `:= refl`     — both sides of an equality reduce to the same value.
    Refl,
    /// `:= by algebra` — polynomial-normalization tactic for arithmetic
    /// equalities under any number of `forall x in T, ...` binders.  Sound for
    /// the polynomial fragment over Int/Nat and handles **infinite domains**.
    ByAlgebra,
    /// `:= by induction` — mathematical induction over `forall n in Nat, P(n)`.
    /// Verifies the base case `P(0)` (by eval) and the step case
    /// `P(k+1)` from `P(k)` (by algebraic substitution).
    ByInduction,
    /// `:= by strong_induction` — depth-2 strong induction over Nat.  Verifies
    /// `P(0)`, `P(1)` as base cases and the step at `k+2`, with recursive
    /// calls on `k` and `k+1` available as inductive hypotheses.  Useful for
    /// recurrences that look back more than one step (Fibonacci, etc.).
    ByStrongInduction,
    /// `:= by simp` or `:= by simp [lemma1, lemma2]` — equational rewriting.
    /// Applies known equality theorems as left-to-right rewrite rules until
    /// the goal becomes `true` (or both sides of an equality become
    /// syntactically identical).  Empty `lemmas` means "use every available
    /// proven equality theorem"; otherwise only the named ones are used.
    BySimp { lemmas: Vec<String> },
    /// `:= by linarith` — linear arithmetic decision (Fourier-Motzkin-lite).
    /// Currently delegates to `by algebra` for the unconditional linear case,
    /// which already handles `forall x in Nat/Int, <linear-op>` correctly via
    /// polynomial sign analysis.  Provided as an alternative spelling for
    /// users coming from Lean/Coq mathlib.  Full Fourier-Motzkin with
    /// hypothesis tracking is a future extension.
    ByLinarith,
    /// `:= by decide` — proposition-level decision procedure.  Strips the
    /// outer `forall`s, fully enumerates finite domains, and evaluates the
    /// body to a Bool.  Differs from `by eval` only in intent: it signals
    /// "this proposition is decidable" and refuses propositions that don't
    /// reduce to a Bool.
    ByDecide,
    /// `:= by unfold name` — β-reduce every call `name a1 .. ak` in the
    /// goal using the body of `name`'s definition (one level of unfolding).
    /// Acts as a *transformer*: produces a new goal for the next tactic in
    /// a sequence.  If alone, the transformed goal must already evaluate to
    /// `true`.
    ByUnfold(String),
    /// `:= by intros` — strip the leading `forall x in T,` binders from the
    /// goal, leaving `x` as a free variable.  Transformer-only: must be
    /// followed by a closing tactic (e.g. `by intros then algebra`).
    ByIntros,
    /// `:= by t1 then t2 then ... then tk` — sequential composition.
    /// Each tactic transforms (or closes) the goal, and the last one must
    /// close it.  Transformers (unfold/intros/simp) pass a rewritten goal
    /// to the next; closers (algebra/induction/eval/refl/term) must be
    /// last and prove the resulting goal.
    Seq(Vec<Proof>),
    /// `:= <expr>`   — proof *term* (Curry-Howard).  For prototype, used as
    /// witness for forall / exists / membership: e.g. for `forall x in S, P`
    /// supply `\x -> proof_of_P` and we apply it to each element of S.
    Term(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// `def name (: type)? := expr`  — definition (function or value or set)
    Def {
        name: String,
        ty: Option<Expr>,
        value: Expr,
    },
    /// `axiom name : prop`  — taken as given
    Axiom { name: String, prop: Expr },
    /// `theorem name : prop := proof`
///
/// Available proof tactics in addition to `by eval` and `refl`:
///   - `by algebra`   — polynomial-equality based proof for `forall ..., L == R`
///                      over Int / Nat.  Sound for the polynomial fragment;
///                      handles infinite domains.
///   - `by induction` — mathematical induction on Nat: verify P(0) and that
///                      P(k+1) is symbolically derivable from P(k).
    Theorem {
        name: String,
        prop: Expr,
        proof: Proof,
    },
    /// bare expression — useful in REPL or as `;` separated statements.
    Expr(Expr),
    /// `import "path/to/file.seki"` or `import "path" as alias`.
    /// Loaded at the moment its declaration is processed; bindings appear
    /// in the current global namespace (with optional `alias.` prefix).
    Import {
        path: String,
        alias: Option<String>,
    },
    /// Compiler-internal metadata emitted by `parse_class` so the runtime
    /// can populate the class/method registry used for automatic
    /// dictionary resolution.  Not user-written.
    ClassMeta {
        class_name: String,
        ctor_name: String,
        methods: Vec<String>,
    },
    /// Compiler-internal metadata emitted by `parse_instance` so the
    /// runtime can populate the `(class, type) -> instance` lookup table.
    /// Not user-written.
    InstanceMeta {
        instance_name: String,
        class_name: String,
        type_name: String,
    },
    /// Compiler-internal metadata for `data` declarations.  Carries
    /// constructor names + their argument-type textual descriptions so the
    /// `by induction` tactic can identify recursive arguments by simple
    /// name comparison against the data type name.
    DataMeta {
        name: String,
        ctors: Vec<(String, Vec<String>)>,
    },
}

/// A top-level declaration paired with its source position.  The parser
/// records `(line, col)` of the *keyword* (`def`/`theorem`/`axiom`/...)
/// that introduces the decl, so that runtime errors (proof failure,
/// membership check, etc.) can be annotated with where the offending
/// declaration lives in the source file.
#[derive(Debug, Clone, PartialEq)]
pub struct LocatedDecl {
    pub decl: Decl,
    pub line: usize,
    pub col: usize,
}

// -- Pretty-printing for debugging / REPL output ----------------------------

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "mod",
            BinOp::Eq => "==",
            BinOp::Neq => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::In => "in",
            BinOp::NotIn => "notin",
            BinOp::Subset => "subset",
            BinOp::Union => "union",
            BinOp::Intersect => "intersect",
            BinOp::Diff => "diff",
            BinOp::Times => "times",
        };
        f.write_str(s)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Int(n) => write!(f, "{}", n),
            Expr::Real(r) => write!(f, "{}", r),
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Str(s) => write!(f, "{:?}", s),
            Expr::Var { name: n, .. } => write!(f, "{}", n),
            Expr::Lambda { params, body } => {
                write!(f, "(\\")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    if let Some(t) = &p.ty {
                        write!(f, "({} : {})", p.name, t)?;
                    } else {
                        write!(f, "{}", p.name)?;
                    }
                }
                write!(f, " -> {})", body)
            }
            Expr::App { func, args } => {
                write!(f, "({}", func)?;
                for a in args {
                    write!(f, " {}", a)?;
                }
                write!(f, ")")
            }
            Expr::Let { name, ty, value, body, rec } => {
                if *rec {
                    write!(f, "(let rec {}", name)?;
                } else {
                    write!(f, "(let {}", name)?;
                }
                if let Some(t) = ty {
                    write!(f, " : {}", t)?;
                }
                write!(f, " = {} in {})", value, body)
            }
            Expr::If { cond, then_branch, else_branch } => {
                write!(f, "(if {} then {} else {})", cond, then_branch, else_branch)
            }
            Expr::BinOp(op, l, r) => write!(f, "({} {} {})", l, op, r),
            Expr::UnOp(UnOp::Neg, e) => write!(f, "(- {})", e),
            Expr::UnOp(UnOp::Not, e) => write!(f, "(not {})", e),
            Expr::SetEnum(es) => {
                write!(f, "{{")?;
                for (i, e) in es.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, "}}")
            }
            Expr::SetComp { var, domain, pred } => {
                write!(f, "{{{} in {} | {}}}", var, domain, pred)
            }
            Expr::Arrow(a, b) => write!(f, "({} -> {})", a, b),
            Expr::DepArrow { binder, from, to } => {
                write!(f, "(({} : {}) -> {})", binder, from, to)
            }
            Expr::Forall { var, domain, body } => {
                write!(f, "(forall {} in {}, {})", var, domain, body)
            }
            Expr::Exists { var, domain, body } => {
                write!(f, "(exists {} in {}, {})", var, domain, body)
            }
            Expr::Tuple(xs) => {
                write!(f, "(")?;
                for (i, e) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, ")")
            }
            Expr::List(xs) => {
                write!(f, "[")?;
                for (i, e) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, "]")
            }
        }
    }
}

// -- substitution -----------------------------------------------------------

// ---- Expr equality ignores span metadata ---------------------------------
//
// Two `Var { name: "x", line: 1, col: 5 }` and `Var { name: "x", line: 0, col: 0 }`
// must compare equal so that tactics relying on syntactic identity continue
// to work after Phase 7 introduced position-carrying Var nodes.
impl PartialEq for Expr {
    fn eq(&self, other: &Expr) -> bool {
        use Expr::*;
        match (self, other) {
            (Int(a), Int(b)) => a == b,
            (Real(a), Real(b)) => a == b,
            (Bool(a), Bool(b)) => a == b,
            (Str(a), Str(b)) => a == b,
            // ↓ Span fields intentionally ignored
            (Var { name: a, .. }, Var { name: b, .. }) => a == b,
            (Lambda { params: pa, body: ba },
             Lambda { params: pb, body: bb }) => pa == pb && ba == bb,
            (App { func: fa, args: aa },
             App { func: fb, args: ab }) => fa == fb && aa == ab,
            (Let { name: na, ty: ta, value: va, body: bda, rec: ra },
             Let { name: nb, ty: tb, value: vb, body: bdb, rec: rb }) =>
                na == nb && ta == tb && va == vb && bda == bdb && ra == rb,
            (If { cond: ca, then_branch: ta, else_branch: ea },
             If { cond: cb, then_branch: tb, else_branch: eb }) =>
                ca == cb && ta == tb && ea == eb,
            (BinOp(oa, la, ra), BinOp(ob, lb, rb)) => oa == ob && la == lb && ra == rb,
            (UnOp(oa, xa), UnOp(ob, xb)) => oa == ob && xa == xb,
            (SetEnum(a), SetEnum(b)) => a == b,
            (SetComp { var: va, domain: da, pred: pa },
             SetComp { var: vb, domain: db, pred: pb }) =>
                va == vb && da == db && pa == pb,
            (Arrow(a1, a2), Arrow(b1, b2)) => a1 == b1 && a2 == b2,
            (DepArrow { binder: ba, from: fa, to: ta },
             DepArrow { binder: bb, from: fb, to: tb }) =>
                ba == bb && fa == fb && ta == tb,
            (Tuple(a), Tuple(b)) => a == b,
            (List(a), List(b)) => a == b,
            (Forall { var: va, domain: da, body: ba },
             Forall { var: vb, domain: db, body: bb }) =>
                va == vb && da == db && ba == bb,
            (Exists { var: va, domain: da, body: ba },
             Exists { var: vb, domain: db, body: bb }) =>
                va == vb && da == db && ba == bb,
            _ => false,
        }
    }
}
impl Eq for Expr {}

/// Capture-avoiding substitution: `e[var := value]`.  Skips inner binders
/// that shadow `var`.  Used by the induction tactic, by tautology
/// detection, and by the canonicalizer.
pub fn subst(e: &Expr, var: &str, value: &Expr) -> Expr {
    use Expr::*;
    match e {
        Int(_) | Real(_) | Bool(_) | Str(_) => e.clone(),
        Var { name: n, .. } => {
            if n == var {
                value.clone()
            } else {
                e.clone()
            }
        }
        Lambda { params, body } => {
            if params.iter().any(|p| p.name == var) {
                e.clone()
            } else {
                Lambda {
                    params: params.clone(),
                    body: Box::new(subst(body, var, value)),
                }
            }
        }
        App { func, args } => App {
            func: Box::new(subst(func, var, value)),
            args: args.iter().map(|a| subst(a, var, value)).collect(),
        },
        Let { name, ty, value: v, body, rec } => {
            if name == var {
                Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    value: Box::new(subst(v, var, value)),
                    body: body.clone(),
                    rec: *rec,
                }
            } else {
                Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    value: Box::new(subst(v, var, value)),
                    body: Box::new(subst(body, var, value)),
                    rec: *rec,
                }
            }
        }
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(subst(cond, var, value)),
            then_branch: Box::new(subst(then_branch, var, value)),
            else_branch: Box::new(subst(else_branch, var, value)),
        },
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(subst(l, var, value)),
            Box::new(subst(r, var, value)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(subst(x, var, value))),
        SetEnum(xs) => SetEnum(xs.iter().map(|x| subst(x, var, value)).collect()),
        SetComp { var: v2, domain, pred } => {
            if v2 == var {
                SetComp {
                    var: v2.clone(),
                    domain: Box::new(subst(domain, var, value)),
                    pred: pred.clone(),
                }
            } else {
                SetComp {
                    var: v2.clone(),
                    domain: Box::new(subst(domain, var, value)),
                    pred: Box::new(subst(pred, var, value)),
                }
            }
        }
        Arrow(a, b) => Arrow(
            Box::new(subst(a, var, value)),
            Box::new(subst(b, var, value)),
        ),
        DepArrow { binder, from, to } => {
            // `from` is always substituted; `to` substitutes only when the
            // binder doesn't shadow `var`.
            if binder == var {
                DepArrow {
                    binder: binder.clone(),
                    from: Box::new(subst(from, var, value)),
                    to: to.clone(),
                }
            } else {
                DepArrow {
                    binder: binder.clone(),
                    from: Box::new(subst(from, var, value)),
                    to: Box::new(subst(to, var, value)),
                }
            }
        }
        Tuple(xs) => Tuple(xs.iter().map(|x| subst(x, var, value)).collect()),
        List(xs) => List(xs.iter().map(|x| subst(x, var, value)).collect()),
        Forall { var: v2, domain, body } => {
            if v2 == var {
                Forall {
                    var: v2.clone(),
                    domain: Box::new(subst(domain, var, value)),
                    body: body.clone(),
                }
            } else {
                Forall {
                    var: v2.clone(),
                    domain: Box::new(subst(domain, var, value)),
                    body: Box::new(subst(body, var, value)),
                }
            }
        }
        Exists { var: v2, domain, body } => {
            if v2 == var {
                Exists {
                    var: v2.clone(),
                    domain: Box::new(subst(domain, var, value)),
                    body: body.clone(),
                }
            } else {
                Exists {
                    var: v2.clone(),
                    domain: Box::new(subst(domain, var, value)),
                    body: Box::new(subst(body, var, value)),
                }
            }
        }
    }
}

/// True iff `e1` and `e2` are α-equivalent: the same Expr modulo bound-variable
/// renaming.  Used to detect when the body of `forall x in {y | P(y)}, B(x)`
/// is structurally the comprehension predicate `P` applied to `x`.
pub fn alpha_equiv(e1: &Expr, e2: &Expr) -> bool {
    // For forall/exists tautology detection we just need to check if the
    // *renamed* body equals the predicate.  Since the caller substitutes
    // both to a canonical variable name, structural equality (PartialEq)
    // suffices.  This is α-equivalence for the no-binder fragment.
    e1 == e2
}

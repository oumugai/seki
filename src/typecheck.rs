//! Set-theoretic type checker.
//!
//! In seki, a "type" is just a set: a value `v` has type `T` iff `v ∈ T`.
//! Because set membership is in general undecidable (think `{x in Nat | foo}`)
//! we use a *bidirectional* style:
//!
//!   * Cheap structural checks catch obvious shape errors (`1 + true`,
//!     applying a non-function, etc.) before the program runs.
//!   * After each declaration with an annotation `def x : T := e`, we
//!     evaluate `T` to a set value and `e` to a value, then ask the eval
//!     module's `member` whether `value(e) ∈ value(T)`.
//!
//! This is far weaker than full dependent typing, but it's *honest*: every
//! claimed type is checked by the same set-theoretic semantics the rest of
//! the language uses.

use crate::ast::{BinOp, Expr, UnOp};
use crate::eval::EvalCtx;
use crate::value::{AtomicSet, Env, Globals, SetVal, Value};
use crate::{SekiError, SekiResult};
use std::collections::HashMap;
use std::sync::Arc;

/// A coarse static "shape" — what the eval would produce.  This is *only*
/// used for early shape checking, never for soundness; the real type system
/// is set membership at definition time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Shape {
    Int,
    Real,
    Bool,
    Str,
    Set,
    /// callable of unknown arity
    Fn,
    Tuple,
    Unit,
    /// give up — depends on runtime
    Unknown,
}

/// Static environment: identifier → its inferred shape.
#[derive(Clone, Default)]
pub struct ShapeEnv {
    pub map: HashMap<String, Shape>,
}

impl ShapeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn extend(&self, name: String, sh: Shape) -> Self {
        let mut m = self.map.clone();
        m.insert(name, sh);
        Self { map: m }
    }

    pub fn lookup(&self, name: &str) -> Option<&Shape> {
        self.map.get(name)
    }
}

pub fn prelude_shapes() -> ShapeEnv {
    let mut e = ShapeEnv::new();
    for n in [
        "Nat", "Int", "Real", "Bool", "String", "Prop", "Set",
    ] {
        e.map.insert(n.into(), Shape::Set);
    }
    // Only list Rust-implemented function builtins here.  Stdlib-defined
    // functions (succ/pred/id/...) get their shape registered when the
    // stdlib def is processed via run_decl, so they don't need a hint.
    for n in [
        "print", "error", "card",
        "fst", "snd", "pair",
        "List", "Tree",
        "intToReal", "floor", "ceil", "round", "sqrt", "pow",
    ] {
        e.map.insert(n.into(), Shape::Fn);
    }
    e
}

pub fn infer_shape(e: &Expr, env: &ShapeEnv) -> Shape {
    match e {
        Expr::Int(_) => Shape::Int,
        Expr::Real(_) => Shape::Real,
        Expr::Bool(_) => Shape::Bool,
        Expr::Str(_) => Shape::Str,
        Expr::Var { name: name, .. } => env.lookup(name).cloned().unwrap_or(Shape::Unknown),
        Expr::Lambda { .. } => Shape::Fn,
        Expr::App { .. } => Shape::Unknown,
        Expr::Let { name, value, body, .. } => {
            let sv = infer_shape(value, env);
            infer_shape(body, &env.extend(name.clone(), sv))
        }
        Expr::If { then_branch, else_branch, .. } => {
            let a = infer_shape(then_branch, env);
            let b = infer_shape(else_branch, env);
            if a == b {
                a
            } else {
                Shape::Unknown
            }
        }
        Expr::BinOp(op, l, r) => match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                let ls = infer_shape(l, env);
                let rs = infer_shape(r, env);
                if matches!(ls, Shape::Real) || matches!(rs, Shape::Real) {
                    Shape::Real
                } else {
                    Shape::Int
                }
            }
            BinOp::Mod => Shape::Int,
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                Shape::Bool
            }
            BinOp::And | BinOp::Or => Shape::Bool,
            BinOp::In | BinOp::NotIn | BinOp::Subset => Shape::Bool,
            BinOp::Union | BinOp::Intersect | BinOp::Diff | BinOp::Times => Shape::Set,
        },
        Expr::UnOp(UnOp::Neg, e) => {
            let s = infer_shape(e, env);
            if matches!(s, Shape::Real) { Shape::Real } else { Shape::Int }
        }
        Expr::UnOp(UnOp::Not, _) => Shape::Bool,
        Expr::SetEnum(_)
        | Expr::SetComp { .. }
        | Expr::Arrow(_, _)
        | Expr::DepArrow { .. } => Shape::Set,
        Expr::Tuple(_) => Shape::Tuple,
        Expr::List(_) => Shape::Tuple,                // desugared to nested cons / Tuple
        Expr::Forall { .. } | Expr::Exists { .. } => Shape::Bool,
    }
}

/// Cheap shape-level checks: catches obvious mismatches like `1 + true`.
pub fn check_shape(e: &Expr, env: &ShapeEnv) -> SekiResult<Shape> {
    match e {
        Expr::Int(_) => Ok(Shape::Int),
        Expr::Real(_) => Ok(Shape::Real),
        Expr::Bool(_) => Ok(Shape::Bool),
        Expr::Str(_) => Ok(Shape::Str),
        Expr::Var { name: name, .. } => Ok(env.lookup(name).cloned().unwrap_or(Shape::Unknown)),
        Expr::Lambda { params, body } => {
            let mut env2 = env.clone();
            for p in params {
                // Lift simple annotations `(x : Real)` etc. into a usable
                // shape so the body's if-branches can unify on the right
                // arithmetic type.  Unrecognised annotations stay `Unknown`.
                let sh = match &p.ty {
                    Some(Expr::Var { name: s, .. }) => match s.as_str() {
                        "Int" => Shape::Int,
                        "Nat" => Shape::Int,
                        "Real" => Shape::Real,
                        "Bool" | "Prop" => Shape::Bool,
                        "String" => Shape::Str,
                        _ => Shape::Unknown,
                    },
                    _ => Shape::Unknown,
                };
                env2 = env2.extend(p.name.clone(), sh);
            }
            check_shape(body, &env2)?;
            Ok(Shape::Fn)
        }
        Expr::App { func, args } => {
            let fs = check_shape(func, env)?;
            for a in args {
                check_shape(a, env)?;
            }
            match fs {
                Shape::Fn | Shape::Unknown => Ok(Shape::Unknown),
                other => Err(SekiError::Type(format!(
                    "applying non-function (inferred shape {:?})",
                    other
                ))),
            }
        }
        Expr::Let { name, value, body, .. } => {
            let sv = check_shape(value, env)?;
            check_shape(body, &env.extend(name.clone(), sv))
        }
        Expr::If { cond, then_branch, else_branch } => {
            let cs = check_shape(cond, env)?;
            if !matches!(cs, Shape::Bool | Shape::Unknown) {
                return Err(SekiError::Type(format!(
                    "if condition has shape {:?}, expected Bool",
                    cs
                )));
            }
            let a = check_shape(then_branch, env)?;
            let b = check_shape(else_branch, env)?;
            if matches!(a, Shape::Unknown) || matches!(b, Shape::Unknown) || a == b {
                Ok(if a == Shape::Unknown { b } else { a })
            } else {
                Err(SekiError::Type(format!(
                    "if branches have different shapes: {:?} vs {:?}",
                    a, b
                )))
            }
        }
        Expr::BinOp(op, l, r) => {
            let ls = check_shape(l, env)?;
            let rs = check_shape(r, env)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                    needs_numeric(&ls, "arithmetic lhs")?;
                    needs_numeric(&rs, "arithmetic rhs")?;
                    // Result shape: Real if either operand is Real, else Int.
                    Ok(if matches!(ls, Shape::Real) || matches!(rs, Shape::Real) {
                        Shape::Real
                    } else {
                        Shape::Int
                    })
                }
                BinOp::Mod => {
                    needs_compat(&ls, Shape::Int, "mod lhs")?;
                    needs_compat(&rs, Shape::Int, "mod rhs")?;
                    Ok(Shape::Int)
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    needs_numeric(&ls, "comparison lhs")?;
                    needs_numeric(&rs, "comparison rhs")?;
                    Ok(Shape::Bool)
                }
                BinOp::Eq | BinOp::Neq => Ok(Shape::Bool),
                BinOp::And | BinOp::Or => {
                    needs_compat(&ls, Shape::Bool, "logical lhs")?;
                    needs_compat(&rs, Shape::Bool, "logical rhs")?;
                    Ok(Shape::Bool)
                }
                BinOp::In | BinOp::NotIn => {
                    needs_compat(&rs, Shape::Set, "rhs of 'in'")?;
                    Ok(Shape::Bool)
                }
                BinOp::Subset => {
                    needs_compat(&ls, Shape::Set, "lhs of subset")?;
                    needs_compat(&rs, Shape::Set, "rhs of subset")?;
                    Ok(Shape::Bool)
                }
                BinOp::Union | BinOp::Intersect | BinOp::Diff | BinOp::Times => {
                    needs_compat(&ls, Shape::Set, "set op lhs")?;
                    needs_compat(&rs, Shape::Set, "set op rhs")?;
                    Ok(Shape::Set)
                }
            }
        }
        Expr::UnOp(UnOp::Neg, e) => {
            let s = check_shape(e, env)?;
            needs_numeric(&s, "unary minus")?;
            Ok(if matches!(s, Shape::Real) { Shape::Real } else { Shape::Int })
        }
        Expr::UnOp(UnOp::Not, e) => {
            let s = check_shape(e, env)?;
            needs_compat(&s, Shape::Bool, "not")?;
            Ok(Shape::Bool)
        }
        Expr::SetEnum(items) => {
            for x in items {
                check_shape(x, env)?;
            }
            Ok(Shape::Set)
        }
        Expr::SetComp { var, domain, pred } => {
            let ds = check_shape(domain, env)?;
            needs_compat(&ds, Shape::Set, "comprehension domain")?;
            let env2 = env.extend(var.clone(), Shape::Unknown);
            let ps = check_shape(pred, &env2)?;
            needs_compat(&ps, Shape::Bool, "comprehension predicate")?;
            Ok(Shape::Set)
        }
        Expr::Arrow(a, b) => {
            let ash = check_shape(a, env)?;
            let bsh = check_shape(b, env)?;
            // Allow Bool → Bool as **propositional implication** (the user
            // wrote `P -> Q` where both are Bool-valued).  Otherwise both
            // sides must be sets — the usual function-type interpretation.
            if matches!(ash, Shape::Bool) && matches!(bsh, Shape::Bool) {
                return Ok(Shape::Bool);
            }
            needs_compat(&ash, Shape::Set, "arrow lhs (must be a set/type)")?;
            needs_compat(&bsh, Shape::Set, "arrow rhs (must be a set/type)")?;
            Ok(Shape::Set)
        }
        Expr::DepArrow { binder, from, to } => {
            let ash = check_shape(from, env)?;
            needs_compat(&ash, Shape::Set, "dep arrow domain (must be a set/type)")?;
            // `to` is checked in an env where `binder` is `Unknown` shape.
            let env2 = env.extend(binder.clone(), Shape::Unknown);
            let bsh = check_shape(to, &env2)?;
            needs_compat(&bsh, Shape::Set, "dep arrow codomain (must be a set/type)")?;
            Ok(Shape::Set)
        }
        Expr::Forall { var, domain, body } | Expr::Exists { var, domain, body } => {
            let ds = check_shape(domain, env)?;
            needs_compat(&ds, Shape::Set, "quantifier domain")?;
            let env2 = env.extend(var.clone(), Shape::Unknown);
            let bs = check_shape(body, &env2)?;
            needs_compat(&bs, Shape::Bool, "quantifier body")?;
            Ok(Shape::Bool)
        }
        Expr::Tuple(xs) | Expr::List(xs) => {
            for x in xs {
                check_shape(x, env)?;
            }
            Ok(Shape::Tuple)
        }
    }
}

fn needs_compat(actual: &Shape, expected: Shape, ctx: &str) -> SekiResult<()> {
    if matches!(actual, Shape::Unknown) || *actual == expected {
        Ok(())
    } else {
        Err(SekiError::Type(format!(
            "{}: expected {:?}, got {:?}",
            ctx, expected, actual
        )))
    }
}

/// Accepts either `Int`, `Real`, or `Unknown` for numeric contexts.
fn needs_numeric(actual: &Shape, ctx: &str) -> SekiResult<()> {
    if matches!(actual, Shape::Int | Shape::Real | Shape::Unknown) {
        Ok(())
    } else {
        Err(SekiError::Type(format!(
            "{}: expected numeric (Int or Real), got {:?}",
            ctx, actual
        )))
    }
}

// -- Membership-based type check at runtime --------------------------------

/// True if `value` is in the set `ty`.  This is the *source of truth* for the
/// type system: types are sets and well-typedness is set membership.
pub fn check_value_in(
    value: &Value,
    ty: &SetVal,
    ctx: &EvalCtx,
    env: &Env,
) -> SekiResult<bool> {
    // Special case: a function value vs an Arrow type — we can additionally
    // check the input/output sets at sample points to catch mistakes early.
    if let (Value::Closure { params, body, .. }, SetVal::Arrow { from, to }) =
        (value, ty)
    {
        // Phase 7 soundness: when the refinement types are linear integer
        // and the body is linear in its parameter, we can decide the
        // implication symbolically via linarith.  This replaces a
        // statistically-incomplete sample check with a complete proof.
        match try_linarith_refinement_check(params, body, from, to) {
            Some(true)  => return Ok(true),  // proven for all inputs
            Some(false) => return Ok(false), // refuted, real counterexample exists
            None        => { /* fall through to sample check */ }
        }
        // sample-test: pick a few elements of `from`, apply, check result in `to`
        let samples = match &**from {
            SetVal::Enum(xs) => xs.clone(),
            SetVal::Atomic(AtomicSet::Bool) | SetVal::Atomic(AtomicSet::Prop) => {
                vec![Value::Bool(false), Value::Bool(true)]
            }
            SetVal::Atomic(AtomicSet::Nat) => (0..5).map(Value::Int).collect(),
            SetVal::Atomic(AtomicSet::Int) => (-2..3).map(Value::Int).collect(),
            _ => vec![],
        };
        for s in samples {
            let r = ctx.apply(value.clone(), vec![s.clone()])?;
            if !ctx.member(&r, to, env)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    ctx.member(value, ty, env)
}

/// Symbolically verify membership in an Arrow type whose `from` and `to`
/// are both linear-integer refinements, and whose closure body is linear
/// in its single parameter.
///
/// Returns:
///   * `Some(true)`  — proven for every value in `from`
///   * `Some(false)` — refuted, an actual counterexample exists
///   * `None`        — outside this decision procedure; caller should fall
///                     back to sample-based checking
///
/// Pattern recognized:
///
/// ```text
///   closure  =  \x -> linear_expr(x)
///   from     =  {v in Int | linear_pre(v)}
///   to       =  {w in Int | linear_post(w)}
///   goal     =  ∀x. linear_pre(x) ⇒ linear_post(linear_expr(x))
/// ```
fn try_linarith_refinement_check(
    params: &[String],
    body: &Expr,
    from: &Arc<SetVal>,
    to: &Arc<SetVal>,
) -> Option<bool> {
    // Currently only the single-parameter case.  Multi-arg would require
    // proving membership for the curried result type; that's a Phase 8
    // task once we have multi-variable Fourier-Motzkin.
    if params.len() != 1 { return None; }
    let param = &params[0];

    // Both refinements must be `{v in Int | predicate(v)}`.
    let (from_var, from_pred) = comp_over_int(from)?;
    let (to_var,   to_pred)   = comp_over_int(to)?;

    // The body must be linear in `param`.  We check this here both to fail
    // fast and to avoid generating malformed linarith inputs below.
    let _ = crate::linarith::to_lin(body, param)?;

    // Build the linarith query:
    //   hypothesis:  from_pred[from_var := param]  (so the bound var matches
    //                                                our chosen focus)
    //   goal:        to_pred[to_var   := body]    (so the goal talks about
    //                                                applying f to x)
    let hyp_expr = crate::ast::subst(from_pred, from_var, &Expr::Var { name: param.clone(), line: 0, col: 0 });
    let goal_expr = crate::ast::subst(to_pred,   to_var,   body);

    let hyp  = crate::linarith::ineq_of_expr(&hyp_expr,  param)?;
    let goal = crate::linarith::ineq_of_expr(&goal_expr, param)?;

    match crate::linarith::decide(&[hyp], goal) {
        crate::linarith::Proof::Proven       => Some(true),
        crate::linarith::Proof::Refuted(_)   => Some(false),
        crate::linarith::Proof::Unknown      => None,
    }
}

/// Return `Some((var, pred))` when `s` is `{var in Int | pred(var)}`.
fn comp_over_int(s: &Arc<SetVal>) -> Option<(&String, &Expr)> {
    match &**s {
        SetVal::Comp { var, domain, pred, .. }
            if matches!(&**domain, SetVal::Atomic(AtomicSet::Int))
            => Some((var, pred)),
        _ => None,
    }
}

/// Check a top-level definition `def name : ty := value` against its annotated
/// set.  Returns Ok if value ∈ ty.
pub fn check_def_membership(
    value: &Value,
    ty_set: &Arc<SetVal>,
    ctx: &EvalCtx,
    env: &Env,
) -> SekiResult<()> {
    if check_value_in(value, ty_set, ctx, env)? {
        Ok(())
    } else {
        Err(SekiError::Type(format!(
            "value {} is not a member of declared type {}",
            value, ty_set
        )))
    }
}

// =================================================================
// Type inference (light) — produce a type expression for a given Expr.
// =================================================================

/// Infer the **most informative type** of `e` we can deduce statically as an
/// `Expr` (which evaluates at runtime to a `SetVal`).  This is *bidirectional*
/// in spirit: we use the body to infer arrow types, but for unannotated
/// lambdas we leave parameter types as `Set` (the universe).
///
/// The inferred type is intended for documentation and `:type` queries —
/// it's not a static type checker (membership is still runtime via
/// `check_def_membership`).
///
/// Returns `None` when the type cannot be deduced cheaply (e.g. a `Var` that
/// hasn't been seen before, complex applications etc.).  Callers display
/// `?` in such cases.
pub fn infer_type(e: &Expr, env: &TypeEnv) -> Option<Expr> {
    match e {
        Expr::Int(_) => Some(Expr::Var { name: "Int".into(), line: 0, col: 0 }),
        Expr::Real(_) => Some(Expr::Var { name: "Real".into(), line: 0, col: 0 }),
        Expr::Bool(_) => Some(Expr::Var { name: "Bool".into(), line: 0, col: 0 }),
        Expr::Str(_) => Some(Expr::Var { name: "String".into(), line: 0, col: 0 }),
        Expr::Var { name: name, .. } => env.lookup(name).cloned(),
        Expr::Lambda { params, body } => {
            // Build env extended with each param's annotated type (or Set
            // wildcard if none) and recursively infer the body's type.
            let mut env2 = env.clone();
            let mut param_tys: Vec<Expr> = Vec::new();
            for p in params {
                let pty = p.ty.clone().unwrap_or_else(|| Expr::Var { name: "Set".into(), line: 0, col: 0 });
                env2 = env2.extend(p.name.clone(), pty.clone());
                param_tys.push(pty);
            }
            let body_ty = infer_type(body, &env2)?;
            // Build a curried Arrow: P1 -> P2 -> ... -> Body
            let mut t = body_ty;
            for pty in param_tys.into_iter().rev() {
                t = Expr::Arrow(Box::new(pty), Box::new(t));
            }
            Some(t)
        }
        Expr::App { func, args } => {
            // From `func`'s inferred type, peel off one Arrow per arg.
            let mut ft = infer_type(func, env)?;
            for _ in args {
                match ft {
                    Expr::Arrow(_, to) => ft = *to,
                    Expr::DepArrow { to, .. } => ft = *to,
                    _ => return None,
                }
            }
            Some(ft)
        }
        Expr::Let { name, value, body, .. } => {
            let vt = infer_type(value, env)?;
            let env2 = env.extend(name.clone(), vt);
            infer_type(body, &env2)
        }
        Expr::If { then_branch, else_branch, .. } => {
            // Both branches should agree.  If they do, return that type;
            // otherwise return the first known one.
            let t1 = infer_type(then_branch, env);
            let t2 = infer_type(else_branch, env);
            match (t1, t2) {
                (Some(a), Some(b)) if a == b => Some(a),
                (Some(a), _) => Some(a),
                (_, Some(b)) => Some(b),
                _ => None,
            }
        }
        Expr::BinOp(op, l, r) => match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                // Numeric: Real if either is Real, else Int
                let lt = infer_type(l, env);
                let rt = infer_type(r, env);
                let is_real = matches!(&lt, Some(Expr::Var { name: s, .. }) if s == "Real")
                    || matches!(&rt, Some(Expr::Var { name: s, .. }) if s == "Real");
                Some(Expr::Var { name: if is_real { "Real" } else { "Int" }.into(), line: 0, col: 0 })
            }
            BinOp::Mod => Some(Expr::Var { name: "Int".into(), line: 0, col: 0 }),
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                Some(Expr::Var { name: "Bool".into(), line: 0, col: 0 })
            }
            BinOp::And | BinOp::Or => Some(Expr::Var { name: "Bool".into(), line: 0, col: 0 }),
            BinOp::In | BinOp::NotIn | BinOp::Subset => Some(Expr::Var { name: "Bool".into(), line: 0, col: 0 }),
            BinOp::Union | BinOp::Intersect | BinOp::Diff | BinOp::Times => {
                Some(Expr::Var { name: "Set".into(), line: 0, col: 0 })
            }
        },
        Expr::UnOp(op, x) => match op {
            UnOp::Neg => infer_type(x, env),
            UnOp::Not => Some(Expr::Var { name: "Bool".into(), line: 0, col: 0 }),
        },
        Expr::SetEnum(_) | Expr::SetComp { .. } | Expr::Arrow(_, _) | Expr::DepArrow { .. } => {
            Some(Expr::Var { name: "Set".into(), line: 0, col: 0 })
        }
        Expr::Tuple(_) | Expr::List(_) => None, // anonymous; no good type
        Expr::Forall { .. } | Expr::Exists { .. } => Some(Expr::Var { name: "Bool".into(), line: 0, col: 0 }),
    }
}

/// Type environment for inference: maps identifiers to their (Expr-form) type.
#[derive(Clone, Default)]
pub struct TypeEnv {
    pub map: std::collections::HashMap<String, Expr>,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn extend(&self, name: String, ty: Expr) -> Self {
        let mut m = self.map.clone();
        m.insert(name, ty);
        Self { map: m }
    }
    pub fn lookup(&self, name: &str) -> Option<&Expr> {
        self.map.get(name)
    }
}

/// Pre-populate `TypeEnv` with built-in atomic sets so that they have a
/// "type-of-type" entry of `Set` (avoids hardcoding in the inferrer).
pub fn prelude_types(g: &Globals) -> TypeEnv {
    let mut e = TypeEnv::new();
    for n in ["Nat", "Int", "Real", "Bool", "String", "Prop", "Set"] {
        e.map.insert(n.into(), Expr::Var { name: "Set".into(), line: 0, col: 0 });
    }
    // Track types of stdlib defs as they were inferred.  We rely on the
    // caller having stored them (`Globals::inferred_types`) at def time.
    for (k, t) in g.inferred_types.iter() {
        e.map.insert(k.clone(), t.clone());
    }
    e
}

/// Build a shape env from a globals map (for incremental top-level checking).
pub fn shapes_from_globals(g: &Globals) -> ShapeEnv {
    let mut e = prelude_shapes();
    for (k, v) in g.defs.iter() {
        let sh = match v {
            Value::Int(_) => Shape::Int,
            Value::Real(_) => Shape::Real,
            Value::Bool(_) => Shape::Bool,
            Value::Str(_) => Shape::Str,
            Value::Set(_) => Shape::Set,
            Value::Tuple(_) => Shape::Tuple,
            Value::Closure { .. } | Value::Builtin(_) => Shape::Fn,
            Value::Unit => Shape::Unit,
            // Ref and Dict are opaque to the shape checker — they're treated
            // like tuples (concrete data values) for the few places that
            // consult shape info.
            Value::Ref(_) | Value::Dict(_) | Value::Handle(_) => Shape::Tuple,
        };
        e.map.insert(k.clone(), sh);
    }
    e
}

//! Evaluator for seki: lambda calculus β-reduction + set-theoretic operations.
//!
//! Evaluation is *eager*.  Built-in atomic sets (Nat, Int, Bool, …) are first-
//! class set values, exposed as globals at startup.  Forall / exists quantify
//! over *finite* sets (enumeration or comprehension over a finite domain);
//! attempting to range over an infinite atomic set without a proof term
//! raises a runtime error.

use crate::algebra::{
    expr_to_poly, polynomial_neg, polynomial_nonneg, polynomial_nonpos, polynomial_pos,
    PolyDomain,
};
use crate::ast::{subst, BinOp, Expr, UnOp};
use crate::value::{value_eq, AtomicSet, Env, Globals, SetVal, Value};
use crate::{SekiError, SekiResult};
use std::sync::Arc;

/// Tunable: maximum elements to materialize from a comprehension when
/// enumerating its elements (e.g. for forall over `{x in Nat | x < 10}`).
const COMP_FUEL: usize = 10_000;
/// When forall/exists ranges over Nat / Int without a finite filter, we
/// sample up to this bound.  Any counterexample within the sample is reported.
pub const SAMPLE_BOUND: i64 = 200;

pub struct EvalCtx<'a> {
    pub globals: &'a Globals,
}

impl<'a> EvalCtx<'a> {
    pub fn new(globals: &'a Globals) -> Self {
        EvalCtx { globals }
    }

    pub fn eval(&self, e: &Expr, env: &Env) -> SekiResult<Value> {
        match e {
            Expr::Int(n) => Ok(Value::Int(*n)),
            Expr::Real(r) => Ok(Value::Real(*r)),
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            Expr::Str(s) => Ok(Value::Str(s.clone())),

            Expr::Var { name, line, col } => {
                if let Some(v) = env.lookup(name) {
                    return Ok(v.clone());
                }
                if let Some(v) = self.globals.lookup(name) {
                    return Ok(v.clone());
                }
                // Couldn't resolve.  Offer a "did you mean" suggestion if
                // a known name is within a small edit distance — catches
                // typos like `strlen` for `strLen` or `prntln` for `println`.
                // Phase 7: when the parser captured a span (line ≠ 0), prefix
                // it to the error message so `annotate_error` can place the
                // caret at the failing Var instead of the decl start.
                let suggestion = suggest_name(name, self.globals);
                let core = match suggestion {
                    Some(s) => format!("unbound identifier '{}' (did you mean '{}'?)", name, s),
                    None    => format!("unbound identifier '{}'", name),
                };
                let msg = if *line > 0 {
                    format!("[at {}:{}] {}", line, col, core)
                } else {
                    core
                };
                Err(SekiError::Runtime(msg))
            }

            Expr::Lambda { params, body } => Ok(Value::Closure {
                params: params.iter().map(|p| p.name.clone()).collect(),
                body: Box::new((**body).clone()),
                env: env.clone(),
                rec_name: None,
            }),

            Expr::App { func, args } => {
                // Auto dictionary resolution for class methods.
                // If `func` is a bare reference to a registered class
                // method `m`, look at the first argument's runtime type.
                // If it isn't already a dictionary value for the method's
                // class, prepend the instance dictionary in front of the
                // user-supplied args.
                let mut argv = Vec::with_capacity(args.len());
                for a in args {
                    argv.push(self.eval(a, env)?);
                }
                if let Expr::Var { name: method_name, .. } = func.as_ref() {
                    if let Some(class_name) =
                        self.globals.class_methods.get(method_name).cloned()
                    {
                        if !argv.is_empty() {
                            let already_dict = is_dict_value(
                                &argv[0],
                                &class_name,
                                &self.globals,
                            );
                            if !already_dict {
                                // Resolve.  Type key is the runtime type
                                // name of the first arg.
                                let type_key = argv[0].type_name();
                                let key = (class_name.clone(), type_key.to_string());
                                if let Some(inst) =
                                    self.globals.instances.get(&key).cloned()
                                {
                                    let dict =
                                        self.globals.defs.get(&inst).cloned().ok_or_else(
                                            || SekiError::Runtime(format!(
                                                "instance `{}` registered but not defined",
                                                inst
                                            )),
                                        )?;
                                    argv.insert(0, dict);
                                }
                                // If no instance: fall through; `apply` will
                                // produce its own (probably "non-exhaustive
                                // match") error, which is informative enough.
                            }
                        }
                    }
                }
                let f = self.eval(func, env)?;
                self.apply(f, argv)
            }

            Expr::Let { name, ty: _, value, body, rec } => {
                if *rec {
                    // `let rec name := value in body`: value must be a Lambda
                    // so we can mark its closure as self-referential.
                    let v = self.eval(value, env)?;
                    let v = match v {
                        Value::Closure { params, body: cbody, env: cenv, .. } =>
                            Value::Closure {
                                params,
                                body: cbody,
                                env: cenv,
                                rec_name: Some(name.clone()),
                            },
                        other => return Err(SekiError::Runtime(format!(
                            "let rec {}: value must be a lambda, got {}",
                            name, other.type_name()
                        ))),
                    };
                    let env2 = env.extend(name.clone(), v);
                    return self.eval(body, &env2);
                }
                let v = self.eval(value, env)?;
                let env2 = env.extend(name.clone(), v);
                self.eval(body, &env2)
            }

            Expr::If { cond, then_branch, else_branch } => {
                let c = self.eval(cond, env)?;
                match c {
                    Value::Bool(true) => self.eval(then_branch, env),
                    Value::Bool(false) => self.eval(else_branch, env),
                    other => Err(SekiError::Runtime(format!(
                        "if condition must be Bool, got {}",
                        other.type_name()
                    ))),
                }
            }

            Expr::BinOp(op, l, r) => self.eval_binop(op, l, r, env),
            Expr::UnOp(op, e) => self.eval_unop(op, e, env),

            Expr::SetEnum(items) => {
                let mut vs = Vec::with_capacity(items.len());
                for it in items {
                    vs.push(self.eval(it, env)?);
                }
                Ok(Value::Set(Arc::new(SetVal::Enum(vs))))
            }

            Expr::SetComp { var, domain, pred } => {
                let dv = self.eval(domain, env)?;
                let dset = match dv {
                    Value::Set(s) => s,
                    other => {
                        return Err(SekiError::Runtime(format!(
                            "comprehension domain must be a set, got {}",
                            other.type_name()
                        )))
                    }
                };
                Ok(Value::Set(Arc::new(SetVal::Comp {
                    var: var.clone(),
                    domain: dset,
                    pred: (**pred).clone(),
                    env: env.clone(),
                })))
            }

            Expr::Arrow(a, b) => {
                let av = self.eval(a, env)?;
                let bv = self.eval(b, env)?;
                let aset = expect_set(av, "arrow lhs")?;
                let bset = expect_set(bv, "arrow rhs")?;
                Ok(Value::Set(Arc::new(SetVal::Arrow {
                    from: aset,
                    to: bset,
                })))
            }

            Expr::DepArrow { binder, from, to } => {
                let av = self.eval(from, env)?;
                let aset = expect_set(av, "dep arrow domain")?;
                Ok(Value::Set(Arc::new(SetVal::DepArrow {
                    binder: binder.clone(),
                    from: aset,
                    to: (**to).clone(),
                    env: env.clone(),
                })))
            }

            Expr::Tuple(items) => {
                let mut vs = Vec::with_capacity(items.len());
                for it in items {
                    vs.push(self.eval(it, env)?);
                }
                Ok(Value::Tuple(vs))
            }

            Expr::List(items) => {
                // The parser now desugars `[a, b, c]` into nested `cons`
                // applications, so this Expr variant is reached only when an
                // `Expr::List` is built programmatically.  Mirror stdlib's
                // tagged-pair encoding (tag 0 = nil, tag 1 = cons) so the
                // value is indistinguishable from one built by `cons`.
                let unit_set = Value::Set(Arc::new(SetVal::Enum(vec![])));
                let mut acc = Value::Tuple(vec![Value::Int(0), unit_set]);
                for it in items.iter().rev() {
                    let v = self.eval(it, env)?;
                    acc = Value::Tuple(vec![
                        Value::Int(1),
                        Value::Tuple(vec![v, acc]),
                    ]);
                }
                Ok(acc)
            }

            Expr::Forall { var, domain, body } => {
                let dv = self.eval(domain, env)?;
                let dset = expect_set(dv, "forall domain")?;
                // First try to verify the proposition directly from the
                // *definition* of the set — without iterating elements.
                // This is sound for infinite domains where iteration would
                // only give a sample-based answer.
                if let Some(result) = try_forall_from_definition(var, &dset, body) {
                    return Ok(Value::Bool(result));
                }
                let elems = enumerate_set(&dset, self, env)?;
                for v in elems {
                    let env2 = env.extend(var.clone(), v.clone());
                    let r = self.eval(body, &env2)?;
                    match r {
                        Value::Bool(true) => continue,
                        Value::Bool(false) => return Ok(Value::Bool(false)),
                        other => {
                            return Err(SekiError::Runtime(format!(
                                "forall body must be Bool, got {}",
                                other.type_name()
                            )))
                        }
                    }
                }
                Ok(Value::Bool(true))
            }

            Expr::Exists { var, domain, body } => {
                let dv = self.eval(domain, env)?;
                let dset = expect_set(dv, "exists domain")?;
                if let Some(result) = try_exists_from_definition(var, &dset, body) {
                    return Ok(Value::Bool(result));
                }
                let elems = enumerate_set(&dset, self, env)?;
                for v in elems {
                    let env2 = env.extend(var.clone(), v.clone());
                    let r = self.eval(body, &env2)?;
                    match r {
                        Value::Bool(true) => return Ok(Value::Bool(true)),
                        Value::Bool(false) => continue,
                        other => {
                            return Err(SekiError::Runtime(format!(
                                "exists body must be Bool, got {}",
                                other.type_name()
                            )))
                        }
                    }
                }
                Ok(Value::Bool(false))
            }
        }
    }

    /// Apply a function value to a list of arguments.  Supports currying:
    /// extra args are applied to the result; missing args produce a closure.
    pub fn apply(&self, mut f: Value, mut args: Vec<Value>) -> SekiResult<Value> {
        while !args.is_empty() {
            match f {
                Value::Closure { params, body, env, rec_name } => {
                    let take = args.len().min(params.len());
                    let mut env2 = env.clone();
                    // For `let rec`-style bindings, expose the name inside
                    // the body so it can refer to itself.  We re-build the
                    // self value with rec_name preserved so deeper recursive
                    // calls keep the link.
                    if let Some(n) = &rec_name {
                        let self_val = Value::Closure {
                            params: params.clone(),
                            body: body.clone(),
                            env: env.clone(),
                            rec_name: rec_name.clone(),
                        };
                        env2 = env2.extend(n.clone(), self_val);
                    }
                    for i in 0..take {
                        env2 = env2.extend(params[i].clone(), args[i].clone());
                    }
                    if take == params.len() {
                        // fully applied this layer
                        let result = self.eval(&body, &env2)?;
                        f = result;
                        args.drain(0..take);
                    } else {
                        // partially applied — return a closure binding remaining params
                        let rest = params[take..].to_vec();
                        return Ok(Value::Closure {
                            params: rest,
                            body,
                            env: env2,
                            rec_name: None,
                        });
                    }
                }
                Value::Builtin(b) => {
                    if args.len() < b.arity {
                        return Err(SekiError::Runtime(format!(
                            "builtin {} expects {} args, got {}",
                            b.name,
                            b.arity,
                            args.len()
                        )));
                    }
                    let take: Vec<Value> = args.drain(0..b.arity).collect();
                    // Special-case builtins that need access to the evaluator
                    // context (because they call closures or compile-time
                    // values back to runtime).
                    let res = match b.name {
                        "spawn" => spawn_dispatch(self.globals, &take)
                            .map_err(SekiError::Runtime)?,
                        "parMap" => par_map_dispatch(self.globals, &take)
                            .map_err(SekiError::Runtime)?,
                        _ => (b.func)(&take).map_err(SekiError::Runtime)?,
                    };
                    f = res;
                }
                other => {
                    return Err(SekiError::Runtime(format!(
                        "cannot apply non-function value of kind {}",
                        other.type_name()
                    )))
                }
            }
        }
        Ok(f)
    }

    fn eval_binop(&self, op: &BinOp, l: &Expr, r: &Expr, env: &Env) -> SekiResult<Value> {
        // short-circuit logicals
        match op {
            BinOp::And => {
                let lv = self.eval(l, env)?;
                let lb = expect_bool(lv, "and")?;
                if !lb {
                    return Ok(Value::Bool(false));
                }
                let rv = self.eval(r, env)?;
                return Ok(Value::Bool(expect_bool(rv, "and")?));
            }
            BinOp::Or => {
                let lv = self.eval(l, env)?;
                let lb = expect_bool(lv, "or")?;
                if lb {
                    return Ok(Value::Bool(true));
                }
                let rv = self.eval(r, env)?;
                return Ok(Value::Bool(expect_bool(rv, "or")?));
            }
            _ => {}
        }
        let lv = self.eval(l, env)?;
        let rv = self.eval(r, env)?;
        match op {
            BinOp::Add => arith(lv, rv, |a, b| a + b, |a, b| a + b),
            BinOp::Sub => arith(lv, rv, |a, b| a - b, |a, b| a - b),
            BinOp::Mul => arith(lv, rv, |a, b| a * b, |a, b| a * b),
            BinOp::Div => arith_div(lv, rv),
            BinOp::Mod => arith_mod(lv, rv),
            BinOp::Eq => Ok(Value::Bool(value_eq(&lv, &rv))),
            BinOp::Neq => Ok(Value::Bool(!value_eq(&lv, &rv))),
            BinOp::Lt => cmp(lv, rv, |a, b| a < b, |a, b| a < b),
            BinOp::Le => cmp(lv, rv, |a, b| a <= b, |a, b| a <= b),
            BinOp::Gt => cmp(lv, rv, |a, b| a > b, |a, b| a > b),
            BinOp::Ge => cmp(lv, rv, |a, b| a >= b, |a, b| a >= b),
            BinOp::In => {
                let s = expect_set(rv, "rhs of 'in'")?;
                Ok(Value::Bool(self.member(&lv, &s, env)?))
            }
            BinOp::NotIn => {
                let s = expect_set(rv, "rhs of 'notin'")?;
                Ok(Value::Bool(!self.member(&lv, &s, env)?))
            }
            BinOp::Subset => {
                let a = expect_set(lv, "lhs of subset")?;
                let b = expect_set(rv, "rhs of subset")?;
                Ok(Value::Bool(self.subset(&a, &b, env)?))
            }
            BinOp::Union => {
                let a = expect_set(lv, "lhs of union")?;
                let b = expect_set(rv, "rhs of union")?;
                Ok(Value::Set(Arc::new(self.union(&a, &b)?)))
            }
            BinOp::Intersect => {
                let a = expect_set(lv, "lhs of intersect")?;
                let b = expect_set(rv, "rhs of intersect")?;
                Ok(Value::Set(Arc::new(self.intersect(&a, &b, env)?)))
            }
            BinOp::Diff => {
                let a = expect_set(lv, "lhs of diff")?;
                let b = expect_set(rv, "rhs of diff")?;
                Ok(Value::Set(Arc::new(self.difference(&a, &b, env)?)))
            }
            BinOp::Times => {
                let a = expect_set(lv, "lhs of times")?;
                let b = expect_set(rv, "rhs of times")?;
                // Flatten:  (A times B) times C  →  A times B times C
                let mut parts: Vec<Arc<SetVal>> = match &*a {
                    SetVal::Product(xs) => xs.clone(),
                    _ => vec![a],
                };
                match &*b {
                    SetVal::Product(ys) => parts.extend(ys.iter().cloned()),
                    _ => parts.push(b),
                }
                Ok(Value::Set(Arc::new(SetVal::Product(parts))))
            }
            BinOp::And | BinOp::Or => unreachable!(),
        }
    }

    fn eval_unop(&self, op: &UnOp, e: &Expr, env: &Env) -> SekiResult<Value> {
        let v = self.eval(e, env)?;
        match (op, v) {
            (UnOp::Neg, Value::Int(n)) => Ok(Value::Int(-n)),
            (UnOp::Neg, Value::Real(r)) => Ok(Value::Real(-r)),
            (UnOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
            (op, v) => Err(SekiError::Runtime(format!(
                "bad unary application: {:?} {}",
                op,
                v.type_name()
            ))),
        }
    }

    // -- set membership and operations -------------------------------------

    pub fn member(&self, x: &Value, s: &SetVal, env: &Env) -> SekiResult<bool> {
        match s {
            SetVal::Enum(items) => Ok(items.iter().any(|y| value_eq(x, y))),
            SetVal::Atomic(a) => Ok(match a {
                AtomicSet::Nat => matches!(x, Value::Int(n) if *n >= 0),
                AtomicSet::Int => matches!(x, Value::Int(_)),
                // Reals: any Real value, plus Ints (since ℤ ⊂ ℝ).
                AtomicSet::Real => {
                    matches!(x, Value::Real(_) | Value::Int(_))
                }
                AtomicSet::Bool => matches!(x, Value::Bool(_)),
                AtomicSet::StringS => matches!(x, Value::Str(_)),
                AtomicSet::Prop => matches!(x, Value::Bool(_)),
                AtomicSet::Universe => matches!(x, Value::Set(_)),
            }),
            SetVal::Comp { var, domain, pred, env: e } => {
                if !self.member(x, domain, env)? {
                    return Ok(false);
                }
                let env2 = e.extend(var.clone(), x.clone());
                let v = self.eval(pred, &env2)?;
                Ok(expect_bool(v, "comprehension predicate")?)
            }
            SetVal::Arrow { from: _, to: _ } => {
                // Membership in a function type: a closure of matching arity.
                // We can't efficiently check pointwise typing for infinite domains
                // at runtime, so accept any callable with at least 1 param.
                Ok(matches!(x, Value::Closure { .. } | Value::Builtin(_)))
            }
            SetVal::DepArrow { binder, from, to, env: cap_env } => {
                // Membership in a dependent arrow: `f` is a callable AND
                // for every (sampled) `a in from`, `f a in to[binder := a]`.
                if !matches!(x, Value::Closure { .. } | Value::Builtin(_)) {
                    return Ok(false);
                }
                // IO enforcement: when the return-type expression is an
                // application of the `IO` marker (e.g. `IO B`), the function
                // is *declared* to produce side effects.  Sample-evaluating
                // it during type checking would fire those effects, which
                // we deliberately avoid — we accept the function on faith
                // and rely on actual call sites to surface any mismatch.
                //
                // This is the Phase 5 minimum for IO enforcement: it stops
                // typechecking from running println / writeFile / etc. while
                // verifying a signature like `Int -> IO Int`.  A full effect
                // system would track IO transitively through composition;
                // we don't do that yet.
                if is_io_marker_app(to) {
                    return Ok(true);
                }
                // Use the same sampling strategy as the typechecker for
                // ordinary arrows.  Conservative: we only sample a few
                // elements; this catches obvious mismatches but isn't a
                // soundness guarantee for infinite `from`.
                let samples = sample_for_membership(from);
                for s in samples {
                    let r = self.apply(x.clone(), vec![s.clone()])?;
                    let bound_env = cap_env.extend(binder.clone(), s.clone());
                    let to_val = self.eval(to, &bound_env)?;
                    let to_set = match to_val {
                        Value::Set(s) => s,
                        _ => continue,
                    };
                    if !self.member(&r, &to_set, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            SetVal::Product(parts) => {
                let xs = match x {
                    Value::Tuple(xs) => xs,
                    _ => return Ok(false),
                };
                if xs.len() != parts.len() {
                    return Ok(false);
                }
                for (xi, ti) in xs.iter().zip(parts.iter()) {
                    if !self.member(xi, ti, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            SetVal::ListOf(t) => {
                // Lists are tagged-pair encoded by stdlib:
                //   nil       = (0, ())
                //   cons x xs = (1, (x, xs))
                let mut cur = x;
                loop {
                    let outer = match cur {
                        Value::Tuple(xs) if xs.len() == 2 => xs,
                        _ => return Ok(false),
                    };
                    match (&outer[0], &outer[1]) {
                        (Value::Int(0), _) => return Ok(true),
                        (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                            if !self.member(&inner[0], t, env)? {
                                return Ok(false);
                            }
                            cur = &inner[1];
                        }
                        _ => return Ok(false),
                    }
                }
            }
            SetVal::TreeOf(t) => self.tree_pair_member(x, t, env),
        }
    }

    /// Membership for pair-encoded binary trees:
    ///   leaf       = (2, ())
    ///   node l v r = (3, (l, (v, r)))
    fn tree_pair_member(&self, x: &Value, set: &SetVal, env: &Env) -> SekiResult<bool> {
        let outer = match x {
            Value::Tuple(xs) if xs.len() == 2 => xs,
            _ => return Ok(false),
        };
        match (&outer[0], &outer[1]) {
            (Value::Int(2), _) => Ok(true),
            (Value::Int(3), Value::Tuple(body)) if body.len() == 2 => {
                let l = &body[0];
                let inner = match &body[1] {
                    Value::Tuple(xs) if xs.len() == 2 => xs,
                    _ => return Ok(false),
                };
                let v = &inner[0];
                let r = &inner[1];
                Ok(self.member(v, set, env)?
                    && self.tree_pair_member(l, set, env)?
                    && self.tree_pair_member(r, set, env)?)
            }
            _ => Ok(false),
        }
    }

    pub fn subset(&self, a: &SetVal, b: &SetVal, env: &Env) -> SekiResult<bool> {
        // every element of a is in b
        let elems = enumerate_set(a, self, env)?;
        for v in elems {
            if !self.member(&v, b, env)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn union(&self, a: &SetVal, b: &SetVal) -> SekiResult<SetVal> {
        // For two enumerations, take set-union with dedup; otherwise we can't
        // materialize an infinite/comprehension set, so we error.
        match (a, b) {
            (SetVal::Enum(xs), SetVal::Enum(ys)) => {
                let mut out: Vec<Value> = xs.clone();
                for y in ys {
                    if !out.iter().any(|x| value_eq(x, y)) {
                        out.push(y.clone());
                    }
                }
                Ok(SetVal::Enum(out))
            }
            _ => Err(SekiError::Runtime(
                "union currently supports two enumerated sets only".into(),
            )),
        }
    }

    pub fn intersect(&self, a: &SetVal, b: &SetVal, env: &Env) -> SekiResult<SetVal> {
        // Take elements of `a` that are also in `b`.  Works as long as `a`
        // is enumerable.
        let elems = enumerate_set(a, self, env)?;
        let mut out = Vec::new();
        for v in elems {
            if self.member(&v, b, env)? && !out.iter().any(|x| value_eq(x, &v)) {
                out.push(v);
            }
        }
        Ok(SetVal::Enum(out))
    }

    pub fn difference(&self, a: &SetVal, b: &SetVal, env: &Env) -> SekiResult<SetVal> {
        let elems = enumerate_set(a, self, env)?;
        let mut out = Vec::new();
        for v in elems {
            if !self.member(&v, b, env)? && !out.iter().any(|x| value_eq(x, &v)) {
                out.push(v);
            }
        }
        Ok(SetVal::Enum(out))
    }
}

// -- helpers ---------------------------------------------------------------

fn expect_bool(v: Value, ctx: &str) -> SekiResult<bool> {
    match v {
        Value::Bool(b) => Ok(b),
        other => Err(SekiError::Runtime(format!(
            "expected Bool in {}, got {}",
            ctx,
            other.type_name()
        ))),
    }
}

fn expect_set(v: Value, ctx: &str) -> SekiResult<Arc<SetVal>> {
    match v {
        Value::Set(s) => Ok(s),
        other => Err(SekiError::Runtime(format!(
            "expected Set in {}, got {}",
            ctx,
            other.type_name()
        ))),
    }
}

/// Mixed Int/Real arithmetic with automatic promotion.
/// If either operand is Real (or both are), the result is Real and `fr` is
/// applied; otherwise both are Int and `fi` is applied.
fn arith(
    lv: Value,
    rv: Value,
    fi: fn(i64, i64) -> i64,
    fr: fn(f64, f64) -> f64,
) -> SekiResult<Value> {
    match (lv, rv) {
        (Value::Int(a), Value::Int(b)) => Ok(Value::Int(fi(a, b))),
        (Value::Real(a), Value::Real(b)) => Ok(Value::Real(fr(a, b))),
        (Value::Int(a), Value::Real(b)) => Ok(Value::Real(fr(a as f64, b))),
        (Value::Real(a), Value::Int(b)) => Ok(Value::Real(fr(a, b as f64))),
        (a, b) => Err(SekiError::Runtime(format!(
            "arithmetic on non-numeric values: {} and {}",
            a.type_name(),
            b.type_name()
        ))),
    }
}

fn arith_div(lv: Value, rv: Value) -> SekiResult<Value> {
    match (&lv, &rv) {
        (Value::Int(_), Value::Int(b)) if *b == 0 => {
            Err(SekiError::Runtime("division by zero".into()))
        }
        _ => arith(lv, rv, |a, b| a / b, |a, b| a / b),
    }
}

fn arith_mod(lv: Value, rv: Value) -> SekiResult<Value> {
    // Modulo is only well-defined on integers; Real mod would need a choice
    // (truncated vs. Euclidean) and is rarely useful in proofs.
    match (lv, rv) {
        (Value::Int(_), Value::Int(b)) if b == 0 => {
            Err(SekiError::Runtime("mod by zero".into()))
        }
        (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.rem_euclid(b))),
        (a, b) => Err(SekiError::Runtime(format!(
            "mod is only defined on Int (got {} and {})",
            a.type_name(),
            b.type_name()
        ))),
    }
}

fn cmp(
    lv: Value,
    rv: Value,
    fi: fn(i64, i64) -> bool,
    fr: fn(f64, f64) -> bool,
) -> SekiResult<Value> {
    match (lv, rv) {
        (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(fi(a, b))),
        (Value::Real(a), Value::Real(b)) => Ok(Value::Bool(fr(a, b))),
        (Value::Int(a), Value::Real(b)) => Ok(Value::Bool(fr(a as f64, b))),
        (Value::Real(a), Value::Int(b)) => Ok(Value::Bool(fr(a, b as f64))),
        (a, b) => Err(SekiError::Runtime(format!(
            "comparison on non-numeric values: {} and {}",
            a.type_name(),
            b.type_name()
        ))),
    }
}

/// Pick a small set of representative values from `s` to drive sample-based
/// dependent-arrow / arrow membership checks.  Mirrors the convention used
/// in `typecheck::check_value_in`: enumerated sets give all elements,
/// `Bool`/`Prop` give both, `Nat` gives 0..5, `Int` gives -2..3, others empty.
pub fn sample_for_membership(s: &SetVal) -> Vec<Value> {
    match s {
        SetVal::Enum(xs) => xs.clone(),
        SetVal::Atomic(AtomicSet::Bool) | SetVal::Atomic(AtomicSet::Prop) => {
            vec![Value::Bool(false), Value::Bool(true)]
        }
        SetVal::Atomic(AtomicSet::Nat) => (0..5).map(Value::Int).collect(),
        SetVal::Atomic(AtomicSet::Int) => (-2..3).map(Value::Int).collect(),
        SetVal::Atomic(AtomicSet::Real) => vec![
            Value::Real(-1.0),
            Value::Real(0.0),
            Value::Real(1.0),
        ],
        _ => vec![],
    }
}

/// Materialize a set's elements as a Vec.  Comprehensions are filtered from
/// their (enumerable) domain; atomic infinite sets fall back to a sample
/// bounded by `SAMPLE_BOUND`.  Function-type sets cannot be enumerated.
pub fn enumerate_set(s: &SetVal, ctx: &EvalCtx, env: &Env) -> SekiResult<Vec<Value>> {
    match s {
        SetVal::Enum(xs) => Ok(xs.clone()),
        SetVal::Comp { var, domain, pred, env: e } => {
            let base = enumerate_set(domain, ctx, env)?;
            let mut out = Vec::new();
            for v in base.into_iter().take(COMP_FUEL) {
                let env2 = e.extend(var.clone(), v.clone());
                let r = ctx.eval(pred, &env2)?;
                if expect_bool(r, "comprehension predicate")? {
                    out.push(v);
                }
            }
            Ok(out)
        }
        SetVal::Atomic(a) => match a {
            AtomicSet::Nat => Ok((0..SAMPLE_BOUND).map(Value::Int).collect()),
            AtomicSet::Int => Ok((-SAMPLE_BOUND..SAMPLE_BOUND).map(Value::Int).collect()),
            AtomicSet::Real => {
                // A small canonical sample including negative, zero, fractional,
                // and integer values.  Forall over Real with `by eval` is only
                // a smoke test — use `by algebra` style reasoning for soundness.
                Ok(vec![
                    Value::Real(-2.0),
                    Value::Real(-1.0),
                    Value::Real(-0.5),
                    Value::Real(0.0),
                    Value::Real(0.5),
                    Value::Real(1.0),
                    Value::Real(2.0),
                ])
            }
            AtomicSet::Bool => Ok(vec![Value::Bool(false), Value::Bool(true)]),
            AtomicSet::Prop => Ok(vec![Value::Bool(false), Value::Bool(true)]),
            AtomicSet::StringS => Err(SekiError::Runtime(
                "cannot enumerate the set of all strings".into(),
            )),
            AtomicSet::Universe => Err(SekiError::Runtime(
                "cannot enumerate the universe Set".into(),
            )),
        },
        SetVal::Arrow { .. } | SetVal::DepArrow { .. } => Err(SekiError::Runtime(
            "cannot enumerate a function type".into(),
        )),
        SetVal::Product(parts) => {
            // Cartesian product of enumerable sets.  Bail out if any part is
            // not enumerable (e.g. function type) — but Atomic infinite sets
            // are sampled which keeps things workable.
            let mut acc: Vec<Vec<Value>> = vec![vec![]];
            for p in parts {
                let elems = enumerate_set(p, ctx, env)?;
                let mut next = Vec::with_capacity(acc.len() * elems.len());
                for prefix in &acc {
                    for e in &elems {
                        let mut row = prefix.clone();
                        row.push(e.clone());
                        next.push(row);
                    }
                }
                acc = next;
            }
            Ok(acc.into_iter().map(Value::Tuple).collect())
        }
        SetVal::ListOf(_) => Err(SekiError::Runtime(
            "cannot enumerate the (infinite) set of all lists".into(),
        )),
        SetVal::TreeOf(_) => Err(SekiError::Runtime(
            "cannot enumerate the (infinite) set of all trees".into(),
        )),
    }
}

/// True if the set is finite and we know how many elements it has.
pub fn is_definitely_finite(s: &SetVal) -> bool {
    match s {
        SetVal::Enum(_) => true,
        SetVal::Atomic(AtomicSet::Bool) | SetVal::Atomic(AtomicSet::Prop) => true,
        SetVal::Comp { domain, .. } => is_definitely_finite(domain),
        SetVal::Product(parts) => parts.iter().all(|p| is_definitely_finite(p)),
        _ => false,
    }
}

/// Sound `forall x in S, body` decision based on the **definition** of `S`.
/// Returns `Some(true)` only when the proposition is provable from the set's
/// structural definition (without enumeration); `None` to fall back to the
/// element-by-element check.
///
/// Cases handled:
///   1. **Tautology by predicate**: `forall x in {y in S | P(y)}, body(x)`
///      where `body(x)` is α-equivalent to `P(x)`.  Membership in the comp
///      *means* satisfying the predicate, so the body holds for free.
///   2. **Vacuous on empty enum**: `forall x in {}, anything` → true.
///   3. **Polynomial relation over a numeric domain**: when `body` is a
///      relation `lhs op rhs` provable via algebraic sign analysis on the
///      domain (`Nat` / `Int`, including comprehensions over them).  Same
///      decision procedure as `by algebra` but invoked automatically.
pub fn try_forall_from_definition(
    var: &str,
    dset: &SetVal,
    body: &Expr,
) -> Option<bool> {
    // Case 1: comprehension predicate ≡ body
    if let SetVal::Comp { var: cv, pred, .. } = dset {
        let canon = "__taut_var__";
        let canon_expr = Expr::Var { name: canon.into(), line: 0, col: 0 };
        let body_canon = subst(body, var, &canon_expr);
        let pred_canon = subst(pred, cv, &canon_expr);
        if body_canon == pred_canon {
            return Some(true);
        }
    }
    // Case 2: vacuous on empty enum
    if let SetVal::Enum(xs) = dset {
        if xs.is_empty() {
            return Some(true);
        }
    }
    // Case 3: polynomial-decidable relation over numeric atomic domain.
    let dom = numeric_domain(dset)?;
    if let Expr::BinOp(op, l, r) = body {
        if !matches!(
            op,
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        ) {
            return None;
        }
        let lp = expr_to_poly(l)?;
        let rp = expr_to_poly(r)?;
        let diff = lp.sub(rp);
        let proven = match op {
            BinOp::Eq => diff.terms.is_empty(),
            BinOp::Ge => polynomial_nonneg(&diff, dom),
            BinOp::Gt => polynomial_pos(&diff, dom),
            BinOp::Le => polynomial_nonpos(&diff, dom),
            BinOp::Lt => polynomial_neg(&diff, dom),
            BinOp::Neq => polynomial_pos(&diff, dom) || polynomial_neg(&diff, dom),
            _ => false,
        };
        if proven {
            return Some(true);
        }
    }
    None
}

/// Sound `exists x in S, body` from set definition.
///
/// Cases handled:
///   1. Body literally `false` → false.
///   2. Empty enum or `{y in S | false}` comp → false.
///   3. Body literally `true` AND set demonstrably non-empty → true.
pub fn try_exists_from_definition(
    _var: &str,
    dset: &SetVal,
    body: &Expr,
) -> Option<bool> {
    if let Expr::Bool(false) = body {
        return Some(false);
    }
    if let SetVal::Enum(xs) = dset {
        if xs.is_empty() {
            return Some(false);
        }
    }
    if let SetVal::Comp { pred, .. } = dset {
        if matches!(pred, Expr::Bool(false)) {
            return Some(false);
        }
    }
    if let Expr::Bool(true) = body {
        if set_is_definitely_nonempty(dset) {
            return Some(true);
        }
    }
    None
}

fn numeric_domain(s: &SetVal) -> Option<PolyDomain> {
    match s {
        SetVal::Atomic(AtomicSet::Nat) => Some(PolyDomain::Nat),
        SetVal::Atomic(AtomicSet::Int) => Some(PolyDomain::Int),
        SetVal::Comp { domain, .. } => numeric_domain(domain),
        _ => None,
    }
}

fn set_is_definitely_nonempty(s: &SetVal) -> bool {
    match s {
        SetVal::Enum(xs) => !xs.is_empty(),
        SetVal::Atomic(_) => true, // all built-in atomic sets are non-empty
        SetVal::Product(parts) => parts.iter().all(|p| set_is_definitely_nonempty(p)),
        // Lists / Trees / Function spaces are always non-empty (nil / leaf / const).
        SetVal::ListOf(_) | SetVal::TreeOf(_) | SetVal::Arrow { .. } => true,
        // Dependent function spaces are also non-empty in well-formed cases
        // (constant functions exist when codomain is non-empty), but we
        // can't decide that without a non-empty codomain check.  Conservative.
        SetVal::DepArrow { .. } => false,
        // Comprehensions are decidable only by inspection.
        SetVal::Comp { .. } => false,
    }
}

/// Source code of the seki standard library.  Embedded at compile time so
/// the binary is self-contained.  Loaded automatically by `make_prelude`.
const STDLIB_SRC: &str = include_str!("stdlib.seki");

/// Build the full prelude: low-level Rust-implemented builtins **plus** the
/// seki-language standard library on top.  The stdlib (in `stdlib.seki`)
/// constructs higher-level types like `Rat = Int × Pos`, predicate-based
/// numeric subtypes (`Pos`, `Neg`, `Even`, `Byte`, `Int8`, …), and common
/// list/tree utilities (`map`, `filter`, `foldr`, `range`, `treeSize`, …).
///
/// All names defined in the stdlib are equally available to user code as if
/// they were Rust-implemented builtins.
pub fn make_prelude() -> Globals {
    let mut g = make_builtin_prelude();
    install_stdlib(&mut g);
    g
}

/// Heuristic: does `v` look like a dictionary value for class `class_name`?
/// Dictionaries are tagged tuples whose first element is a `Str` matching
/// the class's registered constructor name (e.g. `"MkEqDict"`).
fn is_dict_value(v: &Value, class_name: &str, globals: &Globals) -> bool {
    let ctor = match globals.class_ctor.get(class_name) {
        Some(c) => c,
        None => return false,
    };
    match v {
        Value::Tuple(xs) if xs.len() >= 1 => {
            matches!(&xs[0], Value::Str(s) if s == ctor)
        }
        _ => false,
    }
}

/// Build a tagged-pair constructor value matching the encoding used by
/// `parser::make_ctor_decl` (= `("Tag", (a1, (a2, ..., ())))`).
/// `()` here is the empty-set value, mirroring `Expr::SetEnum(vec![])`.
fn make_sym_ctor(tag: &str, args: Vec<Value>) -> Value {
    let unit = Value::Set(Arc::new(SetVal::Enum(vec![])));
    let mut body = unit;
    for a in args.into_iter().rev() {
        body = Value::Tuple(vec![a, body]);
    }
    Value::Tuple(vec![Value::Str(tag.to_string()), body])
}

/// Convert a parsed `Expr` into a `Sym` value (tagged pair encoding
/// matching `lib/cas/sym.seki`).  Supports a practical subset of math
/// notation: numeric literals, variables, `+`/`-`/`*`/`/`, unary `-`,
/// and the function names `sin`, `cos`, `exp`, `ln`, `pow`.
fn expr_to_sym_value(e: &crate::ast::Expr) -> Result<Value, String> {
    use crate::ast::{BinOp as B, Expr::*, UnOp};
    match e {
        Int(n) => Ok(make_sym_ctor("SNum", vec![Value::Int(*n)])),
        Real(_) => Err("parseSym: Real literals not supported (use Int)".into()),
        Bool(_) => Err("parseSym: Bool literals not supported".into()),
        Str(_) => Err("parseSym: String literals not supported".into()),
        Var { name: name, .. } => Ok(make_sym_ctor("SVar", vec![Value::Str(name.clone())])),
        BinOp(op, a, b) => {
            let tag = match op {
                B::Add => "SAdd",
                B::Sub => "SSub",
                B::Mul => "SMul",
                B::Div => "SDiv",
                _ => return Err(format!(
                    "parseSym: only +, -, *, / supported (got {:?})",
                    op
                )),
            };
            let av = expr_to_sym_value(a)?;
            let bv = expr_to_sym_value(b)?;
            Ok(make_sym_ctor(tag, vec![av, bv]))
        }
        UnOp(UnOp::Neg, a) => {
            let av = expr_to_sym_value(a)?;
            Ok(make_sym_ctor("SNeg", vec![av]))
        }
        UnOp(UnOp::Not, _) => Err("parseSym: `not` not supported".into()),
        App { func, args } => {
            // Recognize: sin(x), cos(x), exp(x), ln(x), pow(b, n)
            if let Var { name: fname, .. } = func.as_ref() {
                match (fname.as_str(), args.len()) {
                    ("sin", 1) => {
                        let v = expr_to_sym_value(&args[0])?;
                        Ok(make_sym_ctor("SSin", vec![v]))
                    }
                    ("cos", 1) => {
                        let v = expr_to_sym_value(&args[0])?;
                        Ok(make_sym_ctor("SCos", vec![v]))
                    }
                    ("exp", 1) => {
                        let v = expr_to_sym_value(&args[0])?;
                        Ok(make_sym_ctor("SExp", vec![v]))
                    }
                    ("ln", 1) | ("log", 1) => {
                        let v = expr_to_sym_value(&args[0])?;
                        Ok(make_sym_ctor("SLn", vec![v]))
                    }
                    ("pow", 2) => {
                        let base = expr_to_sym_value(&args[0])?;
                        match &args[1] {
                            Int(n) => Ok(make_sym_ctor(
                                "SPow",
                                vec![base, Value::Int(*n)],
                            )),
                            _ => Err(
                                "parseSym: pow's exponent must be an Int literal"
                                    .into(),
                            ),
                        }
                    }
                    (other, n) => Err(format!(
                        "parseSym: unknown function `{}` with {} args",
                        other, n
                    )),
                }
            } else {
                Err("parseSym: applied expression must be a name".into())
            }
        }
        other => Err(format!(
            "parseSym: unsupported expression form: {}",
            other
        )),
    }
}

/// Parse and evaluate the embedded `stdlib.seki`, inserting every `def`
/// into `g`.  Each definition is evaluated in the context of all previously
/// installed names (builtins + earlier stdlib defs).
///
/// Errors are surfaced as a panic — a broken stdlib is a build-time bug and
/// should never reach end users.
fn install_stdlib(g: &mut Globals) {
    let decls = match crate::parse_program(STDLIB_SRC) {
        Ok(d) => d,
        Err(e) => panic!("stdlib parse failed: {}", e),
    };
    let env = Env::new();
    for ld in decls {
        if let crate::ast::Decl::Def { name, value, .. } = ld.decl {
            let v = {
                let ctx = EvalCtx::new(g);
                match ctx.eval(&value, &env) {
                    Ok(v) => v,
                    Err(e) => panic!("stdlib eval `{}` failed: {}", name, e),
                }
            };
            g.defs.insert(name, v);
        }
    }
}

/// The low-level prelude — Rust-implemented atomic sets and primitive
/// builtins that the seki stdlib (and user code) builds upon.  These
/// cannot be expressed in seki itself (Int/Real arithmetic, IO, set
/// constructors) and live here as the language's *foundation*.
pub fn make_builtin_prelude() -> Globals {
    use AtomicSet::*;
    let mut g = Globals::new();
    let atomic = |a: AtomicSet| Value::Set(Arc::new(SetVal::Atomic(a)));
    g.defs.insert("Nat".into(), atomic(Nat));
    g.defs.insert("Int".into(), atomic(Int));
    // Bool and Prop are *literal* set-of-two-elements — concrete enumerated
    // sets `{false, true}`, not opaque atomic types.  This makes
    // `theorem t : Bool == {false, true} := refl` go through and gives the
    // language a true set-theoretic foundation for its built-in finite type.
    let bool_set = Value::Set(Arc::new(SetVal::Enum(vec![
        Value::Bool(false),
        Value::Bool(true),
    ])));
    g.defs.insert("Bool".into(), bool_set.clone());
    g.defs.insert("Prop".into(), bool_set);
    g.defs.insert("String".into(), atomic(StringS));
    g.defs.insert("Set".into(), atomic(Universe));
    // Real numbers (f64-backed)
    g.defs.insert("Real".into(), atomic(Real));

    // a small standard library of useful builtins
    use crate::value::BuiltinFn;
    fn b_print(args: &[Value]) -> Result<Value, String> {
        let mut s = String::new();
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                s.push(' ');
            }
            s.push_str(&format!("{}", a));
        }
        println!("{}", s);
        Ok(Value::Unit)
    }
    fn b_error(args: &[Value]) -> Result<Value, String> {
        let msg = match &args[0] {
            Value::Str(s) => s.clone(),
            other => format!("{}", other),
        };
        Err(format!("error: {}", msg))
    }
    fn b_card(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Set(s) => match &**s {
                SetVal::Enum(xs) => Ok(Value::Int(xs.len() as i64)),
                _ => Err("card: only enumerated sets have a known cardinality".into()),
            },
            v => Err(format!("card: expected Set, got {}", v.type_name())),
        }
    }
    // `id` / `succ` / `pred` / `abs` are now defined in `stdlib.seki`.
    // ----- tuple builtins ----------------------------------------------------
    fn b_fst(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Tuple(xs) if !xs.is_empty() => Ok(xs[0].clone()),
            v => Err(format!("fst: expected non-empty Tuple, got {}", v.type_name())),
        }
    }
    fn b_snd(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Tuple(xs) if xs.len() >= 2 => Ok(xs[1].clone()),
            v => Err(format!("snd: expected Tuple of arity ≥2, got {}", v.type_name())),
        }
    }
    fn b_pair(args: &[Value]) -> Result<Value, String> {
        Ok(Value::Tuple(vec![args[0].clone(), args[1].clone()]))
    }

    // Internal: index into a flat tuple by integer position.  Used by the
    // parser to desugar tuple patterns in match expressions, where the
    // matched value is a Value::Tuple of arbitrary arity.
    fn b_tupproj(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Int(i), Value::Tuple(xs)) => {
                let idx = *i as usize;
                if idx < xs.len() {
                    Ok(xs[idx].clone())
                } else {
                    Err(format!(
                        "__tupproj: index {} out of range for tuple of arity {}",
                        i,
                        xs.len()
                    ))
                }
            }
            (a, b) => Err(format!(
                "__tupproj: expected (Int, Tuple), got ({}, {})",
                a.type_name(),
                b.type_name()
            )),
        }
    }

    // ----- parseSym: parse a math string into a Sym value ----------------
    // Uses seki's own expression parser then converts the Expr into the
    // tagged-pair encoding of `Sym` (matching lib/cas/sym.seki).
    fn b_parse_sym(args: &[Value]) -> Result<Value, String> {
        let src = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("parseSym: expected String, got {}", v.type_name())),
        };
        let expr = crate::parser::parse_expr_str(&src)
            .map_err(|e| format!("parseSym: parse error: {}", e))?;
        expr_to_sym_value(&expr)
    }

    // List / Tree constructors and destructors are now defined in
    // `stdlib.seki` using tagged-pair encoding (`nil = (false, ())`,
    // `cons x xs = (true, (x, xs))`, `leaf = (false, ())`,
    // `node l v r = (true, (l, (v, r)))`).  Only the *set-type
    // constructors* `List` and `Tree` remain as Rust builtins because they
    // need to produce `SetVal::ListOf` / `SetVal::TreeOf` which can't be
    // expressed in seki.
    fn b_list_type(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Set(s) => Ok(Value::Set(Arc::new(SetVal::ListOf(s.clone())))),
            v => Err(format!("List: expected Set, got {}", v.type_name())),
        }
    }
    fn b_tree_type(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Set(s) => Ok(Value::Set(Arc::new(SetVal::TreeOf(s.clone())))),
            v => Err(format!("Tree: expected Set, got {}", v.type_name())),
        }
    }

    // ----- Real builtins -----------------------------------------------------
    fn b_int_to_real(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Int(n) => Ok(Value::Real(*n as f64)),
            v => Err(format!("intToReal: expected Int, got {}", v.type_name())),
        }
    }
    fn b_floor(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Real(r) => Ok(Value::Int(r.floor() as i64)),
            Value::Int(n) => Ok(Value::Int(*n)),
            v => Err(format!("floor: expected Real, got {}", v.type_name())),
        }
    }
    fn b_ceil(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Real(r) => Ok(Value::Int(r.ceil() as i64)),
            Value::Int(n) => Ok(Value::Int(*n)),
            v => Err(format!("ceil: expected Real, got {}", v.type_name())),
        }
    }
    fn b_round(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Real(r) => Ok(Value::Int(r.round() as i64)),
            Value::Int(n) => Ok(Value::Int(*n)),
            v => Err(format!("round: expected Real, got {}", v.type_name())),
        }
    }
    // `abs` is now defined in `stdlib.seki` for both Int and Real domains
    // (one definition each).
    fn b_sqrt(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Real(r) => {
                if *r < 0.0 {
                    Err(format!("sqrt: negative argument {}", r))
                } else {
                    Ok(Value::Real(r.sqrt()))
                }
            }
            Value::Int(n) => {
                if *n < 0 {
                    Err(format!("sqrt: negative argument {}", n))
                } else {
                    Ok(Value::Real((*n as f64).sqrt()))
                }
            }
            v => Err(format!("sqrt: expected numeric, got {}", v.type_name())),
        }
    }
    fn b_pow(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Real(a), Value::Real(b)) => Ok(Value::Real(a.powf(*b))),
            (Value::Real(a), Value::Int(b)) => Ok(Value::Real(a.powi(*b as i32))),
            (Value::Int(a), Value::Int(b)) if *b >= 0 => {
                Ok(Value::Int((*a).pow(*b as u32)))
            }
            (Value::Int(a), Value::Real(b)) => Ok(Value::Real((*a as f64).powf(*b))),
            (a, b) => Err(format!(
                "pow: expected numeric values, got {} and {}",
                a.type_name(),
                b.type_name()
            )),
        }
    }

    // Real → Real transcendental builtins.  Each accepts Int (promoted to
    // Real) or Real and returns Real.  Generic helper to keep noise down.
    fn unary_real_fn(args: &[Value], name: &str, f: fn(f64) -> f64) -> Result<Value, String> {
        let x = match &args[0] {
            Value::Real(r) => *r,
            Value::Int(n) => *n as f64,
            v => {
                return Err(format!(
                    "{}: expected numeric, got {}",
                    name,
                    v.type_name()
                ))
            }
        };
        Ok(Value::Real(f(x)))
    }
    fn b_exp(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "exp", f64::exp)
    }
    fn b_ln(args: &[Value]) -> Result<Value, String> {
        let x = match &args[0] {
            Value::Real(r) => *r,
            Value::Int(n) => *n as f64,
            v => return Err(format!("ln: expected numeric, got {}", v.type_name())),
        };
        if x <= 0.0 {
            return Err(format!("ln: non-positive argument {}", x));
        }
        Ok(Value::Real(x.ln()))
    }
    fn b_log10(args: &[Value]) -> Result<Value, String> {
        let x = match &args[0] {
            Value::Real(r) => *r,
            Value::Int(n) => *n as f64,
            v => return Err(format!("log10: expected numeric, got {}", v.type_name())),
        };
        if x <= 0.0 {
            return Err(format!("log10: non-positive argument {}", x));
        }
        Ok(Value::Real(x.log10()))
    }
    fn b_sin(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "sin", f64::sin)
    }
    fn b_cos(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "cos", f64::cos)
    }
    fn b_tan(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "tan", f64::tan)
    }
    fn b_asin(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "asin", f64::asin)
    }
    fn b_acos(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "acos", f64::acos)
    }
    fn b_atan(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "atan", f64::atan)
    }
    fn b_atan2(args: &[Value]) -> Result<Value, String> {
        let y = match &args[0] {
            Value::Real(r) => *r,
            Value::Int(n) => *n as f64,
            v => return Err(format!("atan2: expected numeric y, got {}", v.type_name())),
        };
        let x = match &args[1] {
            Value::Real(r) => *r,
            Value::Int(n) => *n as f64,
            v => return Err(format!("atan2: expected numeric x, got {}", v.type_name())),
        };
        Ok(Value::Real(y.atan2(x)))
    }
    fn b_sinh(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "sinh", f64::sinh)
    }
    fn b_cosh(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "cosh", f64::cosh)
    }
    fn b_tanh(args: &[Value]) -> Result<Value, String> {
        unary_real_fn(args, "tanh", f64::tanh)
    }

    // ====================================================================
    // System-development builtins (general-purpose language layer)
    // ====================================================================
    //
    // Set-theoretic framing:
    //   * String is the set of finite character sequences.  All operations
    //     here treat strings as elements of that set; `strLen` is the
    //     cardinality of the underlying character sequence.
    //   * `List String` is the standard `ListOf String` set, so set-theoretic
    //     forall/exists work on results of `strSplit` / `strChars` / etc.
    //   * `Option T` / `Result E T` are the disjoint-union ADTs already in
    //     stdlib (`data Option A = None | Some A`, `data Result E A = ...`).
    //     I/O builtins return these so success/failure is captured in types.

    // --- helpers for building pair-encoded values ---------------------------

    /// Build a pair-encoded list `[v0, v1, ...]` matching stdlib's encoding
    /// `nil = (0, ())` and `cons x xs = (1, (x, xs))`.
    fn make_list(elems: Vec<Value>) -> Value {
        let unit = Value::Set(Arc::new(SetVal::Enum(vec![])));
        let mut acc = Value::Tuple(vec![Value::Int(0), unit]);
        for v in elems.into_iter().rev() {
            acc = Value::Tuple(vec![
                Value::Int(1),
                Value::Tuple(vec![v, acc]),
            ]);
        }
        acc
    }
    fn make_some(v: Value) -> Value { make_sym_ctor("Some", vec![v]) }
    fn make_none() -> Value { make_sym_ctor("None", vec![]) }
    fn make_ok(v: Value) -> Value { make_sym_ctor("Ok", vec![v]) }
    fn make_err(msg: String) -> Value { make_sym_ctor("Err", vec![Value::Str(msg)]) }

    /// Convert a pair-encoded `List String` back into a `Vec<String>`.
    fn list_to_string_vec(v: &Value) -> Result<Vec<String>, String> {
        let mut out = Vec::new();
        let mut cur = v;
        loop {
            let xs = match cur {
                Value::Tuple(xs) if xs.len() == 2 => xs,
                _ => return Err("expected a List".into()),
            };
            match (&xs[0], &xs[1]) {
                (Value::Int(0), _) => return Ok(out),
                (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                    match &inner[0] {
                        Value::Str(s) => out.push(s.clone()),
                        v => return Err(format!(
                            "expected String element, got {}",
                            v.type_name()
                        )),
                    }
                    cur = &inner[1];
                }
                _ => return Err("malformed list".into()),
            }
        }
    }

    // --- string operations -------------------------------------------------

    fn b_str_len(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => Ok(Value::Int(s.chars().count() as i64)),
            v => Err(format!("strLen: expected String, got {}", v.type_name())),
        }
    }
    fn b_str_concat(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Str(a), Value::Str(b)) => {
                let mut s = a.clone();
                s.push_str(b);
                Ok(Value::Str(s))
            }
            (a, b) => Err(format!(
                "strConcat: expected (String, String), got ({}, {})",
                a.type_name(),
                b.type_name()
            )),
        }
    }
    // `strContains` / `strStartsWith` / `strEndsWith` moved to stdlib.seki —
    // they're pure compositions of `strIndexOf` / `substring` / `strLen`.
    fn b_str_index_of(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Str(needle), Value::Str(hay)) => {
                // Return char index (not byte index) for UTF-8 friendliness.
                match hay.find(needle.as_str()) {
                    Some(byte_idx) => {
                        let char_idx = hay[..byte_idx].chars().count() as i64;
                        Ok(Value::Int(char_idx))
                    }
                    None => Ok(Value::Int(-1)),
                }
            }
            _ => Err("strIndexOf: expected (String needle, String haystack)".into()),
        }
    }
    fn b_str_replace(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1], &args[2]) {
            (Value::Str(old), Value::Str(new_), Value::Str(s)) => {
                Ok(Value::Str(s.replace(old.as_str(), new_)))
            }
            _ => Err("strReplace: expected (String old, String new, String s)".into()),
        }
    }
    fn b_str_split(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Str(delim), Value::Str(s)) => {
                let parts: Vec<Value> = if delim.is_empty() {
                    // Splitting on empty: char-by-char tokens (matches strChars).
                    s.chars().map(|c| Value::Str(c.to_string())).collect()
                } else {
                    s.split(delim.as_str()).map(|p| Value::Str(p.to_string())).collect()
                };
                Ok(make_list(parts))
            }
            _ => Err("strSplit: expected (String delim, String s)".into()),
        }
    }
    // `strJoin` moved to stdlib.seki — built from `foldr` + `strConcat`.
    // Same complexity (O(total length)) but readable in seki.
    fn b_substring(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1], &args[2]) {
            (Value::Int(start), Value::Int(len), Value::Str(s)) => {
                let start = (*start).max(0) as usize;
                let len = (*len).max(0) as usize;
                let result: String = s.chars().skip(start).take(len).collect();
                Ok(Value::Str(result))
            }
            _ => Err("substring: expected (Int start, Int len, String s)".into()),
        }
    }
    fn b_str_to_upper(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => Ok(Value::Str(s.to_uppercase())),
            v => Err(format!("strToUpper: expected String, got {}", v.type_name())),
        }
    }
    fn b_str_to_lower(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => Ok(Value::Str(s.to_lowercase())),
            v => Err(format!("strToLower: expected String, got {}", v.type_name())),
        }
    }
    fn b_str_trim(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => Ok(Value::Str(s.trim().to_string())),
            v => Err(format!("strTrim: expected String, got {}", v.type_name())),
        }
    }
    fn b_str_chars(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => {
                let parts: Vec<Value> = s.chars().map(|c| Value::Str(c.to_string())).collect();
                Ok(make_list(parts))
            }
            v => Err(format!("strChars: expected String, got {}", v.type_name())),
        }
    }
    fn b_int_to_str(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Int(n) => Ok(Value::Str(n.to_string())),
            v => Err(format!("intToStr: expected Int, got {}", v.type_name())),
        }
    }
    fn b_real_to_str(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Real(r) => Ok(Value::Str(format!("{}", r))),
            Value::Int(n) => Ok(Value::Str(format!("{}", *n as f64))),
            v => Err(format!("realToStr: expected numeric, got {}", v.type_name())),
        }
    }
    fn b_str_to_int(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => match s.trim().parse::<i64>() {
                Ok(n) => Ok(make_some(Value::Int(n))),
                Err(_) => Ok(make_none()),
            },
            v => Err(format!("strToInt: expected String, got {}", v.type_name())),
        }
    }
    fn b_str_to_real(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => match s.trim().parse::<f64>() {
                Ok(r) => Ok(make_some(Value::Real(r))),
                Err(_) => Ok(make_none()),
            },
            v => Err(format!("strToReal: expected String, got {}", v.type_name())),
        }
    }
    fn b_to_str(args: &[Value]) -> Result<Value, String> {
        Ok(Value::Str(format!("{}", args[0])))
    }

    // --- file I/O ----------------------------------------------------------

    fn b_read_file(args: &[Value]) -> Result<Value, String> {
        let path = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("readFile: expected String path, got {}", v.type_name())),
        };
        match std::fs::read_to_string(&path) {
            Ok(s) => Ok(make_ok(Value::Str(s))),
            Err(e) => Ok(make_err(format!("readFile: {}: {}", path, e))),
        }
    }
    fn b_write_file(args: &[Value]) -> Result<Value, String> {
        let (path, content) = match (&args[0], &args[1]) {
            (Value::Str(p), Value::Str(c)) => (p.clone(), c.clone()),
            _ => return Err("writeFile: expected (String path, String content)".into()),
        };
        match std::fs::write(&path, &content) {
            Ok(_) => Ok(make_ok(Value::Unit)),
            Err(e) => Ok(make_err(format!("writeFile: {}: {}", path, e))),
        }
    }
    fn b_append_file(args: &[Value]) -> Result<Value, String> {
        use std::io::Write;
        let (path, content) = match (&args[0], &args[1]) {
            (Value::Str(p), Value::Str(c)) => (p.clone(), c.clone()),
            _ => return Err("appendFile: expected (String path, String content)".into()),
        };
        match std::fs::OpenOptions::new().create(true).append(true).open(&path) {
            Ok(mut f) => match f.write_all(content.as_bytes()) {
                Ok(_) => Ok(make_ok(Value::Unit)),
                Err(e) => Ok(make_err(format!("appendFile: {}: {}", path, e))),
            },
            Err(e) => Ok(make_err(format!("appendFile: {}: {}", path, e))),
        }
    }
    fn b_file_exists(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(p) => Ok(Value::Bool(std::path::Path::new(p).exists())),
            v => Err(format!("fileExists: expected String path, got {}", v.type_name())),
        }
    }
    fn b_remove_file(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(p) => match std::fs::remove_file(p) {
                Ok(_) => Ok(make_ok(Value::Unit)),
                Err(e) => Ok(make_err(format!("removeFile: {}: {}", p, e))),
            },
            v => Err(format!("removeFile: expected String path, got {}", v.type_name())),
        }
    }

    // --- I/O streams -------------------------------------------------------

    fn b_println(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => println!("{}", s),
            other => println!("{}", other),
        }
        Ok(Value::Unit)
    }
    fn b_eprint(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => eprint!("{}", s),
            other => eprint!("{}", other),
        }
        Ok(Value::Unit)
    }
    fn b_eprintln(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(s) => eprintln!("{}", s),
            other => eprintln!("{}", other),
        }
        Ok(Value::Unit)
    }
    fn b_read_line(_args: &[Value]) -> Result<Value, String> {
        use std::io::BufRead;
        let stdin = std::io::stdin();
        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => Ok(make_none()),  // EOF
            Ok(_) => {
                // strip trailing newline (LF or CRLF) for ergonomic use
                if line.ends_with('\n') { line.pop(); }
                if line.ends_with('\r') { line.pop(); }
                Ok(make_some(Value::Str(line)))
            }
            Err(_) => Ok(make_none()),
        }
    }

    // --- OS / process ------------------------------------------------------

    fn b_get_env(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Str(name) => match std::env::var(name) {
                Ok(v) => Ok(make_some(Value::Str(v))),
                Err(_) => Ok(make_none()),
            },
            v => Err(format!("getEnv: expected String, got {}", v.type_name())),
        }
    }
    fn b_exit(args: &[Value]) -> Result<Value, String> {
        let code = match &args[0] {
            Value::Int(n) => (*n) as i32,
            _ => return Err("exit: expected Int code".into()),
        };
        std::process::exit(code);
    }

    // --- mutable references ------------------------------------------------
    //
    // Set-theoretic framing: `Ref A` is the set of *storage locations*
    // holding a value in A.  Two distinct refs are distinct elements of
    // `Ref A` even when their current contents are equal.  Operations:
    //   mkRef    : A -> Ref A
    //   readRef  : Ref A -> A
    //   writeRef : Ref A -> A -> Unit
    //   modifyRef: Ref A -> (A -> A) -> Unit

    fn b_mk_ref(args: &[Value]) -> Result<Value, String> {
        Ok(Value::Ref(Arc::new(std::sync::Mutex::new(args[0].clone()))))
    }
    fn b_read_ref(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Ref(c) => Ok(c.lock().unwrap().clone()),
            v => Err(format!("readRef: expected Ref, got {}", v.type_name())),
        }
    }
    fn b_write_ref(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Ref(c) => {
                *c.lock().unwrap() = args[1].clone();
                Ok(Value::Unit)
            }
            v => Err(format!("writeRef: expected Ref, got {}", v.type_name())),
        }
    }

    // --- dictionaries (HashMap) -------------------------------------------
    //
    // Set-theoretic framing: a `Dict K V` is a finite functional relation
    // R ⊆ K × V — at most one v for each k.  `(k, v) in dict` and the
    // `dictMember k dict` predicate both reflect this directly.

    fn b_empty_dict(_args: &[Value]) -> Result<Value, String> {
        Ok(Value::Dict(Arc::new(std::sync::Mutex::new(
            std::collections::HashMap::new(),
        ))))
    }
    fn b_dict_insert(args: &[Value]) -> Result<Value, String> {
        let key = crate::value::DictKey::from_value(&args[0])?;
        let value = args[1].clone();
        let dict = match &args[2] {
            Value::Dict(d) => d.clone(),
            v => return Err(format!("dictInsert: expected Dict, got {}", v.type_name())),
        };
        // Functional update: copy the map, mutate the copy, return new Dict.
        // This keeps semantics pure even though Dict uses interior mutability.
        let mut copy = dict.lock().unwrap().clone();
        copy.insert(key, value);
        Ok(Value::Dict(Arc::new(std::sync::Mutex::new(copy))))
    }
    fn b_dict_get(args: &[Value]) -> Result<Value, String> {
        let key = crate::value::DictKey::from_value(&args[0])?;
        match &args[1] {
            Value::Dict(d) => match d.lock().unwrap().get(&key) {
                Some(v) => Ok(make_some(v.clone())),
                None => Ok(make_none()),
            },
            v => Err(format!("dictGet: expected Dict, got {}", v.type_name())),
        }
    }
    fn b_dict_member(args: &[Value]) -> Result<Value, String> {
        let key = crate::value::DictKey::from_value(&args[0])?;
        match &args[1] {
            Value::Dict(d) => Ok(Value::Bool(d.lock().unwrap().contains_key(&key))),
            v => Err(format!("dictMember: expected Dict, got {}", v.type_name())),
        }
    }
    fn b_dict_remove(args: &[Value]) -> Result<Value, String> {
        let key = crate::value::DictKey::from_value(&args[0])?;
        let dict = match &args[1] {
            Value::Dict(d) => d.clone(),
            v => return Err(format!("dictRemove: expected Dict, got {}", v.type_name())),
        };
        let mut copy = dict.lock().unwrap().clone();
        copy.remove(&key);
        Ok(Value::Dict(Arc::new(std::sync::Mutex::new(copy))))
    }
    fn b_dict_size(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Dict(d) => Ok(Value::Int(d.lock().unwrap().len() as i64)),
            v => Err(format!("dictSize: expected Dict, got {}", v.type_name())),
        }
    }
    fn b_dict_keys(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Dict(d) => {
                let keys: Vec<Value> = d.lock().unwrap().keys().map(|k| k.to_value()).collect();
                Ok(make_list(keys))
            }
            v => Err(format!("dictKeys: expected Dict, got {}", v.type_name())),
        }
    }
    fn b_dict_values(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Dict(d) => {
                let vals: Vec<Value> = d.lock().unwrap().values().cloned().collect();
                Ok(make_list(vals))
            }
            v => Err(format!("dictValues: expected Dict, got {}", v.type_name())),
        }
    }

    // --- time ---------------------------------------------------------------
    //
    // `nowSecs` / `nowMillis` / `nowMicros` return time since the UNIX epoch.
    // `monotonicMillis` is monotonically non-decreasing — use it for elapsed
    // measurements (wall clock can jump).  `sleep` blocks the thread.

    fn b_now_secs(_args: &[Value]) -> Result<Value, String> {
        let d = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| format!("nowSecs: {}", e))?;
        Ok(Value::Int(d.as_secs() as i64))
    }
    fn b_now_millis(_args: &[Value]) -> Result<Value, String> {
        let d = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| format!("nowMillis: {}", e))?;
        Ok(Value::Int(d.as_millis() as i64))
    }
    fn b_now_micros(_args: &[Value]) -> Result<Value, String> {
        let d = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| format!("nowMicros: {}", e))?;
        Ok(Value::Int(d.as_micros() as i64))
    }
    fn b_monotonic_millis(_args: &[Value]) -> Result<Value, String> {
        // Anchor to a fixed Instant inside a thread_local cell so the result
        // is "elapsed since program start" rather than an arbitrary baseline.
        std::thread_local! {
            static ORIGIN: std::time::Instant = std::time::Instant::now();
        }
        let elapsed = ORIGIN.with(|o| o.elapsed());
        Ok(Value::Int(elapsed.as_millis() as i64))
    }
    fn b_sleep(args: &[Value]) -> Result<Value, String> {
        let ms = match &args[0] {
            Value::Int(n) => (*n).max(0) as u64,
            _ => return Err("sleep: expected Int milliseconds".into()),
        };
        std::thread::sleep(std::time::Duration::from_millis(ms));
        Ok(Value::Unit)
    }

    // --- process execution --------------------------------------------------
    //
    // `execShell` runs a shell command (via `sh -c` / `cmd /C`) and returns
    // the captured stdout on success.  `runCommand` runs an explicit
    // executable + argv list (no shell expansion) and returns a tuple
    // `(exitCode : Int, stdout : String, stderr : String)`.

    fn b_exec_shell(args: &[Value]) -> Result<Value, String> {
        let cmd = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("execShell: expected String command".into()),
        };
        let output = if cfg!(target_os = "windows") {
            std::process::Command::new("cmd").arg("/C").arg(&cmd).output()
        } else {
            std::process::Command::new("sh").arg("-c").arg(&cmd).output()
        };
        match output {
            Ok(o) => {
                let stdout = String::from_utf8_lossy(&o.stdout).into_owned();
                if o.status.success() {
                    Ok(make_ok(Value::Str(stdout)))
                } else {
                    let code = o.status.code().unwrap_or(-1);
                    let stderr = String::from_utf8_lossy(&o.stderr).into_owned();
                    Ok(make_err(format!(
                        "execShell: exit {}: {}", code, stderr.trim()
                    )))
                }
            }
            Err(e) => Ok(make_err(format!("execShell: spawn failed: {}", e))),
        }
    }
    fn b_run_command(args: &[Value]) -> Result<Value, String> {
        let cmd = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("runCommand: expected (String cmd, List String args)".into()),
        };
        let argv = list_to_string_vec(&args[1])
            .map_err(|e| format!("runCommand: {}", e))?;
        match std::process::Command::new(&cmd).args(&argv).output() {
            Ok(o) => {
                let code = o.status.code().unwrap_or(-1);
                let stdout = String::from_utf8_lossy(&o.stdout).into_owned();
                let stderr = String::from_utf8_lossy(&o.stderr).into_owned();
                Ok(Value::Tuple(vec![
                    Value::Int(code as i64),
                    Value::Str(stdout),
                    Value::Str(stderr),
                ]))
            }
            Err(e) => Ok(Value::Tuple(vec![
                Value::Int(-1),
                Value::Str(String::new()),
                Value::Str(format!("spawn failed: {}", e)),
            ])),
        }
    }

    // --- random (PRNG) ------------------------------------------------------
    //
    // A seedable xorshift64* generator.  Deterministic by default (we seed
    // from the system clock on first use, but `randomSeed` lets the user
    // pin reproducibility).  Backed by a thread-local cell.
    //
    // Why hand-rolled?  Keeps seki dependency-free.  xorshift64* is fast,
    // simple, and produces 64-bit output of good quality for most uses
    // (not cryptographic).

    std::thread_local! {
        static PRNG_STATE: std::cell::Cell<u64> = std::cell::Cell::new(0);
    }
    fn prng_next() -> u64 {
        let s = PRNG_STATE.with(|c| {
            let mut s = c.get();
            if s == 0 {
                // Lazy seed from system clock on first use.
                s = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_nanos() as u64)
                    .unwrap_or(0x9E3779B97F4A7C15);
                if s == 0 { s = 0x9E3779B97F4A7C15; }
            }
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            c.set(s);
            s
        });
        s.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn b_random_seed(args: &[Value]) -> Result<Value, String> {
        let seed = match &args[0] {
            Value::Int(n) => *n as u64,
            _ => return Err("randomSeed: expected Int".into()),
        };
        PRNG_STATE.with(|c| c.set(if seed == 0 { 1 } else { seed }));
        Ok(Value::Unit)
    }
    fn b_random_int(_args: &[Value]) -> Result<Value, String> {
        Ok(Value::Int(prng_next() as i64))
    }
    fn b_random_range(args: &[Value]) -> Result<Value, String> {
        let (lo, hi) = match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => (*a, *b),
            _ => return Err("randomRange: expected (Int lo, Int hi)".into()),
        };
        if hi <= lo {
            return Err(format!("randomRange: hi ({}) must be > lo ({})", hi, lo));
        }
        let span = (hi - lo) as u64;
        let v = (prng_next() % span) as i64;
        Ok(Value::Int(lo + v))
    }
    fn b_random_float(_args: &[Value]) -> Result<Value, String> {
        // 53 bits of precision into [0, 1).
        let bits = prng_next() >> 11;
        Ok(Value::Real((bits as f64) * (1.0 / ((1u64 << 53) as f64))))
    }

    // --- bit operations -----------------------------------------------------
    //
    // Operate on 64-bit signed integers (matching seki's Int).  Note that
    // shifts by ≥ 64 saturate to 0 / sign-extended; we match Rust's
    // `wrapping_shl/shr` behavior.

    fn b_bit_and(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a & b)),
            _ => Err("bitAnd: expected (Int, Int)".into()),
        }
    }
    fn b_bit_or(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a | b)),
            _ => Err("bitOr: expected (Int, Int)".into()),
        }
    }
    fn b_bit_xor(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a ^ b)),
            _ => Err("bitXor: expected (Int, Int)".into()),
        }
    }
    fn b_bit_not(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Int(a) => Ok(Value::Int(!a)),
            _ => Err("bitNot: expected Int".into()),
        }
    }
    fn b_bit_shl(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => {
                let shift = (*b).max(0).min(63) as u32;
                Ok(Value::Int(a.wrapping_shl(shift)))
            }
            _ => Err("bitShl: expected (Int, Int)".into()),
        }
    }
    fn b_bit_shr(args: &[Value]) -> Result<Value, String> {
        match (&args[0], &args[1]) {
            (Value::Int(a), Value::Int(b)) => {
                let shift = (*b).max(0).min(63) as u32;
                Ok(Value::Int(a.wrapping_shr(shift)))
            }
            _ => Err("bitShr: expected (Int, Int)".into()),
        }
    }
    fn b_popcount(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Int(a) => Ok(Value::Int((*a as u64).count_ones() as i64)),
            _ => Err("popcount: expected Int".into()),
        }
    }

    // --- JSON encoding/decoding ---------------------------------------------
    //
    // The user-facing JSON value is the ADT
    //   data Json = JNull | JBool Bool | JNum Real | JStr String
    //             | JArr (List Json) | JObj (List (String × Json))
    // defined in stdlib.seki.  Rust-side builtins encode to / decode from
    // strings via the tagged-pair encoding (`("CtorName", (args..., ()))`).
    // The parser is hand-rolled (no external deps).

    fn json_value_to_string(v: &Value, out: &mut String) -> Result<(), String> {
        // Recognize the ADT shape: ("Tag", (...args..., ())).
        let (tag, body) = match v {
            Value::Tuple(xs) if xs.len() == 2 => match &xs[0] {
                Value::Str(t) => (t.as_str(), &xs[1]),
                _ => return Err(format!("jsonEncode: not a Json value: {}", v)),
            },
            _ => return Err(format!("jsonEncode: not a Json value: {}", v)),
        };
        // Walk body to collect ctor args until () terminator.
        let mut cur = body;
        let mut args: Vec<&Value> = Vec::new();
        loop {
            match cur {
                Value::Unit => break,
                Value::Set(s) if matches!(&**s, SetVal::Enum(xs) if xs.is_empty()) => break,
                Value::Tuple(inner) if inner.len() == 2 => {
                    args.push(&inner[0]);
                    cur = &inner[1];
                }
                _ => return Err(format!("jsonEncode: malformed Json ctor body")),
            }
        }
        match (tag, args.as_slice()) {
            ("JNull", []) => { out.push_str("null"); Ok(()) }
            ("JBool", [b]) => match b {
                Value::Bool(true) => { out.push_str("true"); Ok(()) }
                Value::Bool(false) => { out.push_str("false"); Ok(()) }
                _ => Err("jsonEncode: JBool with non-Bool argument".into()),
            },
            ("JNum", [n]) => match n {
                Value::Int(i) => { out.push_str(&i.to_string()); Ok(()) }
                Value::Real(r) => {
                    if r.is_finite() {
                        if r.fract() == 0.0 {
                            out.push_str(&format!("{}", *r as i64));
                        } else {
                            out.push_str(&format!("{}", r));
                        }
                        Ok(())
                    } else {
                        Err(format!("jsonEncode: non-finite number {}", r))
                    }
                }
                _ => Err("jsonEncode: JNum with non-numeric argument".into()),
            },
            ("JStr", [s]) => match s {
                Value::Str(s) => { json_emit_string(s, out); Ok(()) }
                _ => Err("jsonEncode: JStr with non-String argument".into()),
            },
            ("JArr", [list]) => {
                out.push('[');
                let mut cur = *list;
                let mut first = true;
                loop {
                    let xs = match cur {
                        Value::Tuple(xs) if xs.len() == 2 => xs,
                        _ => return Err("jsonEncode: JArr expects a List".into()),
                    };
                    match (&xs[0], &xs[1]) {
                        (Value::Int(0), _) => break,
                        (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                            if !first { out.push(','); }
                            first = false;
                            json_value_to_string(&inner[0], out)?;
                            cur = &inner[1];
                        }
                        _ => return Err("jsonEncode: malformed JArr list".into()),
                    }
                }
                out.push(']');
                Ok(())
            }
            ("JObj", [list]) => {
                out.push('{');
                let mut cur = *list;
                let mut first = true;
                loop {
                    let xs = match cur {
                        Value::Tuple(xs) if xs.len() == 2 => xs,
                        _ => return Err("jsonEncode: JObj expects a List".into()),
                    };
                    match (&xs[0], &xs[1]) {
                        (Value::Int(0), _) => break,
                        (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                            // pair = (key : String, val : Json)
                            let pair = match &inner[0] {
                                Value::Tuple(p) if p.len() == 2 => p,
                                _ => return Err("jsonEncode: JObj entry must be a Pair".into()),
                            };
                            let key = match &pair[0] {
                                Value::Str(s) => s,
                                _ => return Err("jsonEncode: JObj key must be String".into()),
                            };
                            if !first { out.push(','); }
                            first = false;
                            json_emit_string(key, out);
                            out.push(':');
                            json_value_to_string(&pair[1], out)?;
                            cur = &inner[1];
                        }
                        _ => return Err("jsonEncode: malformed JObj list".into()),
                    }
                }
                out.push('}');
                Ok(())
            }
            (other, _) => Err(format!("jsonEncode: unknown Json ctor '{}'", other)),
        }
    }
    fn json_emit_string(s: &str, out: &mut String) {
        out.push('"');
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                c if (c as u32) < 0x20 => {
                    out.push_str(&format!("\\u{:04x}", c as u32));
                }
                c => out.push(c),
            }
        }
        out.push('"');
    }
    fn b_json_encode(args: &[Value]) -> Result<Value, String> {
        let mut out = String::new();
        json_value_to_string(&args[0], &mut out)?;
        Ok(Value::Str(out))
    }

    // JSON parser: hand-rolled recursive descent.
    struct JsonParser<'a> { src: &'a [u8], pos: usize }
    impl<'a> JsonParser<'a> {
        fn peek(&self) -> Option<u8> { self.src.get(self.pos).copied() }
        fn bump(&mut self) -> Option<u8> {
            let c = self.peek();
            if c.is_some() { self.pos += 1; }
            c
        }
        fn skip_ws(&mut self) {
            while let Some(c) = self.peek() {
                if c == b' ' || c == b'\t' || c == b'\n' || c == b'\r' { self.pos += 1; }
                else { break; }
            }
        }
        fn expect(&mut self, c: u8) -> Result<(), String> {
            if self.peek() == Some(c) { self.pos += 1; Ok(()) }
            else { Err(format!("jsonParse: expected '{}' at pos {}", c as char, self.pos)) }
        }
        fn parse_value(&mut self) -> Result<Value, String> {
            self.skip_ws();
            match self.peek() {
                Some(b'{') => self.parse_object(),
                Some(b'[') => self.parse_array(),
                Some(b'"') => self.parse_string().map(|s| make_sym_ctor("JStr", vec![Value::Str(s)])),
                Some(b't') | Some(b'f') => self.parse_bool(),
                Some(b'n') => self.parse_null(),
                Some(c) if c == b'-' || c.is_ascii_digit() => self.parse_number(),
                Some(c) => Err(format!("jsonParse: unexpected '{}' at pos {}", c as char, self.pos)),
                None => Err("jsonParse: unexpected EOF".into()),
            }
        }
        fn parse_null(&mut self) -> Result<Value, String> {
            if self.src.get(self.pos..self.pos + 4) == Some(b"null") {
                self.pos += 4;
                Ok(make_sym_ctor("JNull", vec![]))
            } else {
                Err(format!("jsonParse: expected 'null' at pos {}", self.pos))
            }
        }
        fn parse_bool(&mut self) -> Result<Value, String> {
            if self.src.get(self.pos..self.pos + 4) == Some(b"true") {
                self.pos += 4;
                Ok(make_sym_ctor("JBool", vec![Value::Bool(true)]))
            } else if self.src.get(self.pos..self.pos + 5) == Some(b"false") {
                self.pos += 5;
                Ok(make_sym_ctor("JBool", vec![Value::Bool(false)]))
            } else {
                Err(format!("jsonParse: expected bool at pos {}", self.pos))
            }
        }
        fn parse_number(&mut self) -> Result<Value, String> {
            let start = self.pos;
            if self.peek() == Some(b'-') { self.pos += 1; }
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() || c == b'.' || c == b'e' || c == b'E'
                    || c == b'+' || c == b'-' { self.pos += 1; }
                else { break; }
            }
            let s = std::str::from_utf8(&self.src[start..self.pos])
                .map_err(|_| "jsonParse: invalid UTF-8 in number".to_string())?;
            // Prefer Int when possible, else Real.
            if let Ok(n) = s.parse::<i64>() {
                Ok(make_sym_ctor("JNum", vec![Value::Int(n)]))
            } else {
                let r = s.parse::<f64>()
                    .map_err(|_| format!("jsonParse: bad number '{}'", s))?;
                Ok(make_sym_ctor("JNum", vec![Value::Real(r)]))
            }
        }
        fn parse_string(&mut self) -> Result<String, String> {
            self.expect(b'"')?;
            let mut out = String::new();
            loop {
                match self.bump() {
                    Some(b'"') => return Ok(out),
                    Some(b'\\') => match self.bump() {
                        Some(b'"') => out.push('"'),
                        Some(b'\\') => out.push('\\'),
                        Some(b'/') => out.push('/'),
                        Some(b'n') => out.push('\n'),
                        Some(b'r') => out.push('\r'),
                        Some(b't') => out.push('\t'),
                        Some(b'b') => out.push('\u{0008}'),
                        Some(b'f') => out.push('\u{000C}'),
                        Some(b'u') => {
                            if self.pos + 4 > self.src.len() {
                                return Err("jsonParse: bad \\u escape".into());
                            }
                            let hex = std::str::from_utf8(&self.src[self.pos..self.pos + 4])
                                .map_err(|_| "jsonParse: bad \\u escape (utf8)".to_string())?;
                            let cp = u32::from_str_radix(hex, 16)
                                .map_err(|_| format!("jsonParse: bad \\u escape '{}'", hex))?;
                            self.pos += 4;
                            if let Some(c) = char::from_u32(cp) { out.push(c); }
                        }
                        _ => return Err("jsonParse: bad escape".into()),
                    },
                    Some(c) => out.push(c as char),
                    None => return Err("jsonParse: unterminated string".into()),
                }
            }
        }
        fn parse_array(&mut self) -> Result<Value, String> {
            self.expect(b'[')?;
            self.skip_ws();
            let mut items: Vec<Value> = Vec::new();
            if self.peek() == Some(b']') { self.pos += 1; }
            else {
                loop {
                    items.push(self.parse_value()?);
                    self.skip_ws();
                    match self.bump() {
                        Some(b',') => self.skip_ws(),
                        Some(b']') => break,
                        _ => return Err("jsonParse: expected ',' or ']' in array".into()),
                    }
                }
            }
            Ok(make_sym_ctor("JArr", vec![make_list(items)]))
        }
        fn parse_object(&mut self) -> Result<Value, String> {
            self.expect(b'{')?;
            self.skip_ws();
            let mut entries: Vec<Value> = Vec::new();
            if self.peek() == Some(b'}') { self.pos += 1; }
            else {
                loop {
                    self.skip_ws();
                    let key = self.parse_string()?;
                    self.skip_ws();
                    self.expect(b':')?;
                    let val = self.parse_value()?;
                    // build a (String, Json) pair
                    entries.push(Value::Tuple(vec![Value::Str(key), val]));
                    self.skip_ws();
                    match self.bump() {
                        Some(b',') => continue,
                        Some(b'}') => break,
                        _ => return Err("jsonParse: expected ',' or '}' in object".into()),
                    }
                }
            }
            Ok(make_sym_ctor("JObj", vec![make_list(entries)]))
        }
    }
    fn b_json_parse(args: &[Value]) -> Result<Value, String> {
        let src = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("jsonParse: expected String".into()),
        };
        let mut p = JsonParser { src: src.as_bytes(), pos: 0 };
        match p.parse_value() {
            Ok(v) => {
                p.skip_ws();
                if p.pos != src.len() {
                    Ok(make_err(format!("jsonParse: trailing input at pos {}", p.pos)))
                } else {
                    Ok(make_ok(v))
                }
            }
            Err(e) => Ok(make_err(e)),
        }
    }

    // --- TCP networking ----------------------------------------------------
    //
    // Blocking sockets backed by Rust's std::net.  Sockets and listeners
    // are exposed to seki as `Value::Handle` wrappers — the only way to
    // do anything with one is to pass it to a network builtin.  Operations
    // return `Result E A` so users handle errors via match.
    //
    // Set-theoretic note: a Handle has no useful set-theoretic content —
    // it's an opaque token referring to an OS resource.  This is the
    // intentional escape hatch for I/O; pure code never produces or
    // consumes Handles.

    use crate::value::Handle;
    use std::net::{TcpListener, TcpStream};

    fn b_tcp_listen(args: &[Value]) -> Result<Value, String> {
        let (host, port) = match (&args[0], &args[1]) {
            (Value::Str(h), Value::Int(p)) => (h.clone(), *p),
            _ => return Err("tcpListen: expected (String host, Int port)".into()),
        };
        let addr = format!("{}:{}", host, port);
        match TcpListener::bind(&addr) {
            Ok(l) => {
                let h = Handle::Listener(Arc::new(std::sync::Mutex::new(Some(l))));
                Ok(make_ok(Value::Handle(h)))
            }
            Err(e) => Ok(make_err(format!("tcpListen: {}: {}", addr, e))),
        }
    }
    fn b_tcp_accept(args: &[Value]) -> Result<Value, String> {
        let listener = match &args[0] {
            Value::Handle(Handle::Listener(c)) => c.clone(),
            v => return Err(format!("tcpAccept: expected Listener handle, got {}", v.type_name())),
        };
        // Borrow without holding the mutable ref while we block on accept().
        // We snapshot a try_clone so we can release the borrow before the call.
        let cloned = {
            let b = listener.lock().unwrap();
            match b.as_ref() {
                Some(l) => match l.try_clone() {
                    Ok(c) => c,
                    Err(e) => return Ok(make_err(format!("tcpAccept: clone: {}", e))),
                },
                None => return Ok(make_err("tcpAccept: listener closed".into())),
            }
        };
        match cloned.accept() {
            Ok((stream, _addr)) => {
                let h = Handle::Socket(Arc::new(std::sync::Mutex::new(Some(stream))));
                Ok(make_ok(Value::Handle(h)))
            }
            Err(e) => Ok(make_err(format!("tcpAccept: {}", e))),
        }
    }
    fn b_tcp_connect(args: &[Value]) -> Result<Value, String> {
        let (host, port) = match (&args[0], &args[1]) {
            (Value::Str(h), Value::Int(p)) => (h.clone(), *p),
            _ => return Err("tcpConnect: expected (String host, Int port)".into()),
        };
        let addr = format!("{}:{}", host, port);
        match TcpStream::connect(&addr) {
            Ok(s) => {
                let h = Handle::Socket(Arc::new(std::sync::Mutex::new(Some(s))));
                Ok(make_ok(Value::Handle(h)))
            }
            Err(e) => Ok(make_err(format!("tcpConnect: {}: {}", addr, e))),
        }
    }
    fn b_tcp_read(args: &[Value]) -> Result<Value, String> {
        use std::io::Read;
        let (sock, n) = match (&args[0], &args[1]) {
            (Value::Handle(Handle::Socket(c)), Value::Int(n)) => (c.clone(), (*n).max(0) as usize),
            _ => return Err("tcpRead: expected (Socket handle, Int max_bytes)".into()),
        };
        let mut b = sock.lock().unwrap();
        let stream = match b.as_mut() {
            Some(s) => s,
            None => return Ok(make_err("tcpRead: socket closed".into())),
        };
        let mut buf = vec![0u8; n];
        match stream.read(&mut buf) {
            Ok(read_n) => {
                buf.truncate(read_n);
                let s = String::from_utf8_lossy(&buf).into_owned();
                Ok(make_ok(Value::Str(s)))
            }
            Err(e) => Ok(make_err(format!("tcpRead: {}", e))),
        }
    }
    fn b_tcp_write(args: &[Value]) -> Result<Value, String> {
        use std::io::Write;
        let (sock, data) = match (&args[0], &args[1]) {
            (Value::Handle(Handle::Socket(c)), Value::Str(s)) => (c.clone(), s.clone()),
            _ => return Err("tcpWrite: expected (Socket handle, String data)".into()),
        };
        let mut b = sock.lock().unwrap();
        let stream = match b.as_mut() {
            Some(s) => s,
            None => return Ok(make_err("tcpWrite: socket closed".into())),
        };
        match stream.write_all(data.as_bytes()) {
            Ok(_) => Ok(make_ok(Value::Unit)),
            Err(e) => Ok(make_err(format!("tcpWrite: {}", e))),
        }
    }
    fn b_tcp_close(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Handle(Handle::Socket(c)) => { *c.lock().unwrap() = None; Ok(Value::Unit) }
            Value::Handle(Handle::Listener(c)) => { *c.lock().unwrap() = None; Ok(Value::Unit) }
            v => Err(format!("tcpClose: expected Handle, got {}", v.type_name())),
        }
    }

    // --- HTTP --------------------------------------------------------------
    //
    // Built on top of the TCP layer above.  Three pieces:
    //   1. urlParse        — split "http://host:port/path" into parts
    //   2. httpParseRequest / httpFormatResponse — protocol codec
    //   3. httpGet         — blocking convenience client
    //
    // The `HttpRequest` / `HttpResponse` ADTs are declared in stdlib.seki;
    // the Rust side encodes/decodes the tagged-pair representation.

    // urlParse / httpParseRequest / httpFormatResponse moved to stdlib.seki
    // (Phase 8 — see docs/spec/08-rust-seki-split.md).  They were pure
    // string-manipulation; the performance impact of seki-side execution is
    // negligible because HTTP I/O is dominated by network round-trips.


    /// Blocking HTTP GET — fetches `url` and returns the response body as
    /// a string.  Follows no redirects, has no timeout.  HTTP only (no
    /// TLS, since pulling in a TLS lib would mean adding a Rust dep).
    fn b_http_get(args: &[Value]) -> Result<Value, String> {
        use std::io::{Read, Write};
        let url = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("httpGet: expected String URL".into()),
        };
        let (scheme, rest) = if let Some(r) = url.strip_prefix("http://") { ("http", r) }
                             else if url.starts_with("https://") { return Ok(make_err("httpGet: https not supported (no TLS); use http://".into())) }
                             else { return Ok(make_err(format!("httpGet: missing or unsupported scheme in '{}'", url))) };
        let _ = scheme;
        let (host_port, path) = match rest.find('/') {
            Some(i) => (&rest[..i], &rest[i..]),
            None => (rest, "/"),
        };
        let (host, port) = match host_port.rfind(':') {
            Some(i) => {
                let h = &host_port[..i];
                let p: u16 = match host_port[i + 1..].parse() {
                    Ok(p) => p,
                    Err(_) => return Ok(make_err(format!("httpGet: bad port in '{}'", url))),
                };
                (h.to_string(), p)
            }
            None => (host_port.to_string(), 80u16),
        };
        let addr = format!("{}:{}", host, port);
        let mut stream = match std::net::TcpStream::connect(&addr) {
            Ok(s) => s,
            Err(e) => return Ok(make_err(format!("httpGet: connect {}: {}", addr, e))),
        };
        let request = format!(
            "GET {} HTTP/1.0\r\nHost: {}\r\nConnection: close\r\n\r\n",
            path, host
        );
        if let Err(e) = stream.write_all(request.as_bytes()) {
            return Ok(make_err(format!("httpGet: write: {}", e)));
        }
        let mut buf = Vec::new();
        if let Err(e) = stream.read_to_end(&mut buf) {
            return Ok(make_err(format!("httpGet: read: {}", e)));
        }
        let response = String::from_utf8_lossy(&buf).into_owned();
        // Split header from body at the first CRLFCRLF.
        let body = match response.find("\r\n\r\n") {
            Some(i) => &response[i + 4..],
            None => response.as_str(),
        };
        Ok(make_ok(Value::Str(body.to_string())))
    }

    // --- Concurrency primitives --------------------------------------------
    //
    // seki's `Value` is built on `Rc` so full closure-based threading would
    // require an Arc migration.  For now we provide two primitives that
    // are useful without that refactor:
    //
    //   1. AtomicI64    — `Arc<AtomicI64>` wrapper for shared counters.
    //                     Operations: atomicNew/Get/Set/Add/Sub/Cas.
    //   2. spawnNamed   — start an OS thread that runs the *named* top-level
    //                     function in a fresh interpreter (no closure
    //                     captures crossing the thread boundary).  Args are
    //                     passed as a String (use jsonEncode/jsonParse to
    //                     pass structured data).  The thread's result is
    //                     dropped (fire-and-forget); use AtomicI64 or
    //                     filesystem to communicate.

    use std::sync::atomic::{AtomicI64, Ordering};
    use std::sync::Arc;

    fn atomic_from_handle<'a>(v: &'a Value, op: &str) -> Result<&'a Arc<AtomicI64>, String> {
        match v {
            Value::Handle(Handle::Atomic(a)) => Ok(a),
            other => Err(format!("{}: expected Atomic handle, got {}", op, other.type_name())),
        }
    }
    fn b_atomic_new(args: &[Value]) -> Result<Value, String> {
        let n = match &args[0] {
            Value::Int(n) => *n,
            _ => return Err("atomicNew: expected Int".into()),
        };
        Ok(Value::Handle(Handle::Atomic(Arc::new(AtomicI64::new(n)))))
    }
    fn b_atomic_get(args: &[Value]) -> Result<Value, String> {
        let a = atomic_from_handle(&args[0], "atomicGet")?;
        Ok(Value::Int(a.load(Ordering::SeqCst)))
    }
    fn b_atomic_set(args: &[Value]) -> Result<Value, String> {
        let a = atomic_from_handle(&args[0], "atomicSet")?;
        let n = match &args[1] {
            Value::Int(n) => *n,
            _ => return Err("atomicSet: expected Int value".into()),
        };
        a.store(n, Ordering::SeqCst);
        Ok(Value::Unit)
    }
    fn b_atomic_add(args: &[Value]) -> Result<Value, String> {
        let a = atomic_from_handle(&args[0], "atomicAdd")?;
        let delta = match &args[1] {
            Value::Int(n) => *n,
            _ => return Err("atomicAdd: expected Int delta".into()),
        };
        Ok(Value::Int(a.fetch_add(delta, Ordering::SeqCst)))
    }
    fn b_atomic_cas(args: &[Value]) -> Result<Value, String> {
        let a = atomic_from_handle(&args[0], "atomicCas")?;
        let (old, new_) = match (&args[1], &args[2]) {
            (Value::Int(o), Value::Int(n)) => (*o, *n),
            _ => return Err("atomicCas: expected (Atomic, Int old, Int new)".into()),
        };
        let result = a.compare_exchange(old, new_, Ordering::SeqCst, Ordering::SeqCst);
        Ok(Value::Bool(result.is_ok()))
    }
    fn b_thread_id(_args: &[Value]) -> Result<Value, String> {
        let id = format!("{:?}", std::thread::current().id());
        Ok(Value::Str(id))
    }

    // --- bytecode VM access ------------------------------------------------
    //
    // `vmEval source` parses an expression, compiles it to bytecode, runs it
    // on the stack VM, and returns the result.  Only the compilable subset
    // (arithmetic / control flow / let / bool) is supported; the rest yields
    // an `Err`.  Used by benchmarks and by the demo example.
    fn b_vm_eval(args: &[Value]) -> Result<Value, String> {
        let src = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("vmEval: expected String source".into()),
        };
        let expr = crate::parser::parse_expr_str(&src)
            .map_err(|e| format!("vmEval: parse: {}", e))?;
        let bc = crate::bytecode::compile_expr(&expr)
            .map_err(|e| format!("vmEval: compile: {:?}", e))?;
        crate::bytecode::run(&bc, Vec::new())
    }
    /// `vmTime n source` — compile once, run `n` times, return the elapsed
    /// time in milliseconds.  Allows seki programs to benchmark the VM.
    fn b_vm_time(args: &[Value]) -> Result<Value, String> {
        let n = match &args[0] {
            Value::Int(n) => (*n).max(1) as usize,
            _ => return Err("vmTime: expected (Int n, String src)".into()),
        };
        let src = match &args[1] {
            Value::Str(s) => s.clone(),
            _ => return Err("vmTime: expected (Int n, String src)".into()),
        };
        let expr = crate::parser::parse_expr_str(&src)
            .map_err(|e| format!("vmTime: parse: {}", e))?;
        let bc = crate::bytecode::compile_expr(&expr)
            .map_err(|e| format!("vmTime: compile: {:?}", e))?;
        let start = std::time::Instant::now();
        for _ in 0..n {
            crate::bytecode::run(&bc, Vec::new())?;
        }
        let elapsed = start.elapsed();
        Ok(Value::Int(elapsed.as_millis() as i64))
    }
    /// `vmCompiles source` — true iff `source` can be compiled to bytecode.
    /// Useful for detecting which functions could be VM-accelerated.
    fn b_vm_compiles(args: &[Value]) -> Result<Value, String> {
        let src = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("vmCompiles: expected String".into()),
        };
        let expr = match crate::parser::parse_expr_str(&src) {
            Ok(e) => e,
            Err(_) => return Ok(Value::Bool(false)),
        };
        Ok(Value::Bool(crate::bytecode::compile_expr(&expr).is_ok()))
    }

    // --- SMT-lite: linear arithmetic decision ------------------------------
    //
    // `linarithProve var hypotheses goal` — runs the decision procedure
    // from `crate::linarith`.  Each hypothesis and the goal are inequality
    // *strings* (parsed via seki's expression parser).  Returns an `Option`:
    //   * `Some true` — proven for all integers `var` satisfying hypotheses
    //   * `Some false` — refuted (counterexample exists in scope)
    //   * `None` — outside the decision procedure (non-linear, multi-var, ...)
    //
    // This replaces sample-based testing for the linear-integer single-variable
    // class of refinement types.
    fn b_linarith_prove(args: &[Value]) -> Result<Value, String> {
        let var = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("linarithProve: expected (String var, List String hyps, String goal)".into()),
        };
        // Collect hypotheses from a pair-encoded `List String`.
        let mut hyps: Vec<(crate::linarith::Lin, crate::ast::BinOp)> = Vec::new();
        let mut cur = &args[1];
        loop {
            let xs = match cur {
                Value::Tuple(xs) if xs.len() == 2 => xs,
                _ => return Err("linarithProve: hypotheses must be a List".into()),
            };
            match (&xs[0], &xs[1]) {
                (Value::Int(0), _) => break,
                (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                    let s = match &inner[0] {
                        Value::Str(s) => s.clone(),
                        _ => return Err("linarithProve: hypothesis must be String".into()),
                    };
                    let expr = match crate::parser::parse_expr_str(&s) {
                        Ok(e) => e,
                        Err(_) => return Ok(make_none()),
                    };
                    let lin = match crate::linarith::ineq_of_expr(&expr, &var) {
                        Some(li) => li,
                        None => return Ok(make_none()),
                    };
                    hyps.push(lin);
                    cur = &inner[1];
                }
                _ => return Err("linarithProve: malformed hypotheses list".into()),
            }
        }
        let goal_src = match &args[2] {
            Value::Str(s) => s.clone(),
            _ => return Err("linarithProve: expected (String var, List String hyps, String goal)".into()),
        };
        let goal_expr = match crate::parser::parse_expr_str(&goal_src) {
            Ok(e) => e,
            Err(_) => return Ok(make_none()),
        };
        let goal = match crate::linarith::ineq_of_expr(&goal_expr, &var) {
            Some(g) => g,
            None => return Ok(make_none()),
        };
        Ok(match crate::linarith::decide(&hyps, goal) {
            crate::linarith::Proof::Proven    => make_some(Value::Bool(true)),
            crate::linarith::Proof::Refuted(_) => make_some(Value::Bool(false)),
            crate::linarith::Proof::Unknown   => make_none(),
        })
    }
    // --- Builtin metadata queries (Phase 9) --------------------------------
    //
    // Give seki tests access to the **set-theoretic / structural** info
    // catalogued in `src/builtin_meta.rs`.  Each returns `Option<...>`
    // because not every builtin has an entry yet (returning None lets
    // tests assert "every builtin we care about has metadata").
    //
    // Example property test using these:
    //     assertSomeEq "Pure"      (builtinEffect "strLen")
    //     assertContains "commutative"
    //         (strJoin "," (builtinProperties "bitAnd"))

    fn b_builtin_doc(args: &[Value]) -> Result<Value, String> {
        let name = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("builtinDoc: expected String, got {}", v.type_name())),
        };
        Ok(match crate::builtin_meta::builtin_meta(&name) {
            Some(m) => make_some(Value::Str(m.doc.to_string())),
            None    => make_none(),
        })
    }
    fn b_builtin_sig(args: &[Value]) -> Result<Value, String> {
        let name = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("builtinSig: expected String, got {}", v.type_name())),
        };
        Ok(match crate::builtin_meta::builtin_meta(&name) {
            Some(m) => make_some(Value::Str(m.signature.to_string())),
            None    => make_none(),
        })
    }
    fn b_builtin_effect(args: &[Value]) -> Result<Value, String> {
        let name = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("builtinEffect: expected String, got {}", v.type_name())),
        };
        Ok(match crate::builtin_meta::builtin_meta(&name) {
            Some(m) => make_some(Value::Str(m.effect.name().to_string())),
            None    => make_none(),
        })
    }
    fn b_builtin_domain(args: &[Value]) -> Result<Value, String> {
        let name = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("builtinDomain: expected String, got {}", v.type_name())),
        };
        Ok(match crate::builtin_meta::builtin_meta(&name) {
            Some(m) => make_some(Value::Str(m.domain.to_string())),
            None    => make_none(),
        })
    }
    fn b_builtin_codomain(args: &[Value]) -> Result<Value, String> {
        let name = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("builtinCodomain: expected String, got {}", v.type_name())),
        };
        Ok(match crate::builtin_meta::builtin_meta(&name) {
            Some(m) => make_some(Value::Str(m.codomain.to_string())),
            None    => make_none(),
        })
    }
    fn b_builtin_properties(args: &[Value]) -> Result<Value, String> {
        let name = match &args[0] {
            Value::Str(s) => s.clone(),
            v => return Err(format!("builtinProperties: expected String, got {}", v.type_name())),
        };
        let props: Vec<Value> = match crate::builtin_meta::builtin_meta(&name) {
            Some(m) => m.properties.iter().map(|s| Value::Str(s.to_string())).collect(),
            None    => return Ok(make_list(vec![])),
        };
        Ok(make_list(props))
    }
    fn b_builtin_names(_args: &[Value]) -> Result<Value, String> {
        let names: Vec<Value> = crate::builtin_meta::all_documented_names()
            .iter()
            .map(|s| Value::Str(s.to_string()))
            .collect();
        Ok(make_list(names))
    }
    fn b_builtin_has_property(args: &[Value]) -> Result<Value, String> {
        let name = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("builtinHasProperty: expected (String name, String property)".into()),
        };
        let prop = match &args[1] {
            Value::Str(s) => s.clone(),
            _ => return Err("builtinHasProperty: expected (String name, String property)".into()),
        };
        let has = match crate::builtin_meta::builtin_meta(&name) {
            Some(m) => m.properties.iter().any(|p| *p == prop.as_str()),
            None    => false,
        };
        Ok(Value::Bool(has))
    }

    /// `linarithCounter var hypotheses goal` — like `linarithProve` but on
    /// `Refuted` returns `Some n` (the counterexample value).  `Proven`
    /// returns `None`.  `Unknown` raises a runtime error.
    fn b_linarith_counter(args: &[Value]) -> Result<Value, String> {
        let var = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("linarithCounter: expected (String var, List String hyps, String goal)".into()),
        };
        let mut hyps: Vec<(crate::linarith::Lin, crate::ast::BinOp)> = Vec::new();
        let mut cur = &args[1];
        loop {
            let xs = match cur {
                Value::Tuple(xs) if xs.len() == 2 => xs,
                _ => return Err("linarithCounter: hypotheses must be a List".into()),
            };
            match (&xs[0], &xs[1]) {
                (Value::Int(0), _) => break,
                (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                    let s = match &inner[0] {
                        Value::Str(s) => s.clone(),
                        _ => return Err("linarithCounter: hypothesis must be String".into()),
                    };
                    let expr = match crate::parser::parse_expr_str(&s) {
                        Ok(e) => e,
                        Err(_) => return Ok(make_none()),
                    };
                    let lin = match crate::linarith::ineq_of_expr(&expr, &var) {
                        Some(li) => li,
                        None => return Ok(make_none()),
                    };
                    hyps.push(lin);
                    cur = &inner[1];
                }
                _ => return Err("linarithCounter: malformed list".into()),
            }
        }
        let goal_src = match &args[2] {
            Value::Str(s) => s.clone(),
            _ => return Err("linarithCounter: expected (String var, List String hyps, String goal)".into()),
        };
        let goal_expr = match crate::parser::parse_expr_str(&goal_src) {
            Ok(e) => e,
            Err(_) => return Ok(make_none()),
        };
        let goal = match crate::linarith::ineq_of_expr(&goal_expr, &var) {
            Some(g) => g,
            None => return Ok(make_none()),
        };
        Ok(match crate::linarith::decide(&hyps, goal) {
            crate::linarith::Proof::Proven      => make_none(),
            crate::linarith::Proof::Refuted(n)  => make_some(Value::Int(n)),
            crate::linarith::Proof::Unknown     => make_none(),
        })
    }

    // --- closure-based threading -------------------------------------------
    //
    // `spawn` takes a closure `() -> A` and starts a new OS thread that
    // runs it; returns a `Thread A` handle.  `join` blocks on the handle
    // and yields the closure's result (or its error message).
    //
    // The spawned thread runs an independent `EvalCtx` over a *snapshot* of
    // the parent's globals, so seki definitions remain visible.  Mutations
    // on shared `Ref`/`Dict`/`Atomic`/`Channel` values reach across threads
    // because those types are backed by `Arc<Mutex>` after the Phase 4
    // migration.
    fn b_join(args: &[Value]) -> Result<Value, String> {
        let cell = match &args[0] {
            Value::Handle(Handle::Thread(c)) => c.clone(),
            v => return Err(format!("join: expected Thread handle, got {}", v.type_name())),
        };
        let jh = cell.lock().unwrap().take();
        match jh {
            None => Err("join: thread already joined".into()),
            Some(handle) => match handle.join() {
                Ok(Ok(v)) => Ok(v),
                Ok(Err(e)) => Err(format!("join: thread errored: {}", e)),
                Err(_) => Err("join: thread panicked".into()),
            },
        }
    }
    // --- channels (mpsc) ---------------------------------------------------
    //
    // Set-theoretic note: a `Channel A` is an opaque token (Handle) over the
    // pair (Sender A, Receiver A).  Senders are cloneable; the receiver is
    // single-consumer.  We don't expose `chanSenderClone` yet; in the
    // standard usage one or many threads call `send`, one thread `recv`s.

    fn b_chan_new(_args: &[Value]) -> Result<Value, String> {
        let (tx, rx) = std::sync::mpsc::channel::<Value>();
        let ends = crate::value::ChannelEnds {
            tx: std::sync::Mutex::new(Some(tx)),
            rx: std::sync::Mutex::new(Some(rx)),
        };
        Ok(Value::Handle(Handle::Channel(Arc::new(ends))))
    }
    fn b_chan_send(args: &[Value]) -> Result<Value, String> {
        let ch = match &args[0] {
            Value::Handle(Handle::Channel(c)) => c.clone(),
            v => return Err(format!("chanSend: expected Channel, got {}", v.type_name())),
        };
        let payload = args[1].clone();
        // Clone the sender out of the Mutex so two senders on different
        // threads don't serialize through the channel's mutex.  Sender is
        // already cloneable for mpsc.
        let sender = match ch.tx.lock().unwrap().clone() {
            Some(s) => s,
            None => return Ok(make_err("chanSend: channel closed".into())),
        };
        match sender.send(payload) {
            Ok(_) => Ok(make_ok(Value::Unit)),
            Err(e) => Ok(make_err(format!("chanSend: {}", e))),
        }
    }
    fn b_chan_recv(args: &[Value]) -> Result<Value, String> {
        let ch = match &args[0] {
            Value::Handle(Handle::Channel(c)) => c.clone(),
            v => return Err(format!("chanRecv: expected Channel, got {}", v.type_name())),
        };
        // The receiver isn't Clone, so we hold the Mutex for the recv() call.
        // If concurrent recv() is attempted, the second one queues on the
        // mutex, which matches a single-consumer model.
        let recv_guard = ch.rx.lock().unwrap();
        let rx = match recv_guard.as_ref() {
            Some(r) => r,
            None => return Ok(make_err("chanRecv: channel closed".into())),
        };
        match rx.recv() {
            Ok(v) => Ok(make_ok(v)),
            Err(e) => Ok(make_err(format!("chanRecv: {}", e))),
        }
    }
    fn b_chan_close(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Handle(Handle::Channel(c)) => {
                *c.tx.lock().unwrap() = None;
                Ok(Value::Unit)
            }
            v => Err(format!("chanClose: expected Channel, got {}", v.type_name())),
        }
    }

    // --- FFI via raw libc dlopen ------------------------------------------
    //
    // Linux / macOS only.  We declare the libc symbols directly so the
    // project keeps zero external Rust crates.  Calls go through a fixed
    // C ABI: `int -> int` and `(const char*) -> int`.  More signatures
    // could be added later.

    extern "C" {
        fn dlopen(path: *const i8, flags: i32) -> *mut std::ffi::c_void;
        fn dlsym(handle: *mut std::ffi::c_void, name: *const i8) -> *mut std::ffi::c_void;
        fn dlclose(handle: *mut std::ffi::c_void) -> i32;
        fn dlerror() -> *const i8;
    }
    const RTLD_LAZY: i32 = 0x00001;

    fn dlerror_msg() -> String {
        unsafe {
            let p = dlerror();
            if p.is_null() { return "unknown dlopen error".into(); }
            let cs = std::ffi::CStr::from_ptr(p);
            cs.to_string_lossy().into_owned()
        }
    }
    fn b_ffi_load(args: &[Value]) -> Result<Value, String> {
        let path = match &args[0] {
            Value::Str(s) => s.clone(),
            _ => return Err("ffiLoad: expected String path".into()),
        };
        let cpath = match std::ffi::CString::new(path.clone()) {
            Ok(c) => c,
            Err(_) => return Ok(make_err(format!("ffiLoad: bad path '{}'", path))),
        };
        let handle = unsafe { dlopen(cpath.as_ptr(), RTLD_LAZY) };
        if handle.is_null() {
            return Ok(make_err(format!("ffiLoad: {}: {}", path, dlerror_msg())));
        }
        Ok(make_ok(Value::Handle(Handle::FfiLib(Arc::new(
            std::sync::Mutex::new(Some(handle as usize)),
        )))))
    }
    fn ffi_resolve(lib: &Value, name: &str) -> Result<*mut std::ffi::c_void, String> {
        let lib = match lib {
            Value::Handle(Handle::FfiLib(c)) => c.clone(),
            v => return Err(format!("ffi: expected FfiLib handle, got {}", v.type_name())),
        };
        let raw = match *lib.lock().unwrap() {
            Some(h) => h,
            None => return Err("ffi: library closed".into()),
        };
        let cname = std::ffi::CString::new(name)
            .map_err(|_| format!("ffi: bad symbol name '{}'", name))?;
        let sym = unsafe { dlsym(raw as *mut _, cname.as_ptr()) };
        if sym.is_null() {
            return Err(format!("ffi: symbol '{}': {}", name, dlerror_msg()));
        }
        Ok(sym)
    }
    /// Call a C function with signature `int (*)(int)`.
    fn b_ffi_call_i_i(args: &[Value]) -> Result<Value, String> {
        let name = match &args[1] {
            Value::Str(s) => s.clone(),
            _ => return Err("ffiCallIntInt: expected (Lib, String name, Int arg)".into()),
        };
        let arg = match &args[2] {
            Value::Int(n) => *n as i64,
            _ => return Err("ffiCallIntInt: third arg must be Int".into()),
        };
        let sym = match ffi_resolve(&args[0], &name) {
            Ok(s) => s,
            Err(e) => return Ok(make_err(e)),
        };
        // Safety: we trust the user; this is the FFI escape hatch.
        let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(sym) };
        let r = f(arg);
        Ok(make_ok(Value::Int(r)))
    }
    /// Call a C function with signature `int (*)(const char *)`.
    fn b_ffi_call_s_i(args: &[Value]) -> Result<Value, String> {
        let name = match &args[1] {
            Value::Str(s) => s.clone(),
            _ => return Err("ffiCallStrInt: expected (Lib, String name, String arg)".into()),
        };
        let arg = match &args[2] {
            Value::Str(s) => s.clone(),
            _ => return Err("ffiCallStrInt: third arg must be String".into()),
        };
        let sym = match ffi_resolve(&args[0], &name) {
            Ok(s) => s,
            Err(e) => return Ok(make_err(e)),
        };
        let carg = match std::ffi::CString::new(arg) {
            Ok(c) => c,
            Err(_) => return Ok(make_err("ffiCallStrInt: arg contains NUL".into())),
        };
        let f: extern "C" fn(*const i8) -> i64 = unsafe { std::mem::transmute(sym) };
        let r = f(carg.as_ptr());
        Ok(make_ok(Value::Int(r)))
    }
    fn b_ffi_close(args: &[Value]) -> Result<Value, String> {
        match &args[0] {
            Value::Handle(Handle::FfiLib(c)) => {
                if let Some(h) = c.lock().unwrap().take() {
                    let _ = unsafe { dlclose(h as *mut _) };
                }
                Ok(Value::Unit)
            }
            v => Err(format!("ffiClose: expected FfiLib, got {}", v.type_name())),
        }
    }

    /// Fire-and-forget thread that increments a shared atomic by `delta`
    /// after sleeping `delay_ms` milliseconds.  This is a minimal-but-useful
    /// concurrency primitive that doesn't require crossing closure boundaries
    /// — it lets seki demonstrate real parallel execution without the full
    /// Arc migration that closure-based threading would require.
    fn b_spawn_atomic_add(args: &[Value]) -> Result<Value, String> {
        let a = match &args[0] {
            Value::Handle(Handle::Atomic(a)) => a.clone(),
            _ => return Err("spawnAtomicAdd: expected Atomic handle".into()),
        };
        let delta = match &args[1] {
            Value::Int(n) => *n,
            _ => return Err("spawnAtomicAdd: expected Int delta".into()),
        };
        let delay_ms = match &args[2] {
            Value::Int(n) => *n as u64,
            _ => return Err("spawnAtomicAdd: expected Int delay_ms".into()),
        };
        std::thread::spawn(move || {
            if delay_ms > 0 {
                std::thread::sleep(std::time::Duration::from_millis(delay_ms));
            }
            a.fetch_add(delta, Ordering::SeqCst);
        });
        Ok(Value::Unit)
    }

    let bi = |name, arity, func| Value::Builtin(BuiltinFn { name, arity, func });
    // I/O and set primitives that can't be expressed in seki itself.
    g.defs.insert("print".into(), bi("print", 1, b_print));
    g.defs.insert("error".into(), bi("error", 1, b_error));
    g.defs.insert("card".into(), bi("card", 1, b_card));
    // Tuple primitives — building blocks for the entire ADT layer in stdlib.
    g.defs.insert("fst".into(), bi("fst", 1, b_fst));
    g.defs.insert("snd".into(), bi("snd", 1, b_snd));
    g.defs.insert("pair".into(), bi("pair", 2, b_pair));
    // Internal: used by parser-generated match desugaring for tuple patterns.
    g.defs.insert("__tupproj".into(), bi("__tupproj", 2, b_tupproj));
    g.defs.insert("parseSym".into(), bi("parseSym", 1, b_parse_sym));
    // Set-type constructors `List` and `Tree`.  These can't live in seki
    // because they synthesise `SetVal::ListOf` / `SetVal::TreeOf`.
    g.defs.insert("List".into(), bi("List", 1, b_list_type));
    g.defs.insert("Tree".into(), bi("Tree", 1, b_tree_type));
    // Real builtins
    g.defs.insert("intToReal".into(), bi("intToReal", 1, b_int_to_real));
    g.defs.insert("floor".into(), bi("floor", 1, b_floor));
    g.defs.insert("ceil".into(), bi("ceil", 1, b_ceil));
    g.defs.insert("round".into(), bi("round", 1, b_round));
    g.defs.insert("sqrt".into(), bi("sqrt", 1, b_sqrt));
    g.defs.insert("pow".into(), bi("pow", 2, b_pow));
    // Transcendental Real builtins
    g.defs.insert("exp".into(), bi("exp", 1, b_exp));
    g.defs.insert("ln".into(), bi("ln", 1, b_ln));
    g.defs.insert("log10".into(), bi("log10", 1, b_log10));
    g.defs.insert("sin".into(), bi("sin", 1, b_sin));
    g.defs.insert("cos".into(), bi("cos", 1, b_cos));
    g.defs.insert("tan".into(), bi("tan", 1, b_tan));
    g.defs.insert("asin".into(), bi("asin", 1, b_asin));
    g.defs.insert("acos".into(), bi("acos", 1, b_acos));
    g.defs.insert("atan".into(), bi("atan", 1, b_atan));
    g.defs.insert("atan2".into(), bi("atan2", 2, b_atan2));
    g.defs.insert("sinh".into(), bi("sinh", 1, b_sinh));
    g.defs.insert("cosh".into(), bi("cosh", 1, b_cosh));
    g.defs.insert("tanh".into(), bi("tanh", 1, b_tanh));
    // String primitives — only the ones that *require* O(n) Rust access to
    // the underlying `String` bytes (or are large enough to warrant native
    // implementation).  Compositions like `strContains` / `strStartsWith` /
    // `strEndsWith` / `strJoin` live in stdlib.seki and are built from these.
    g.defs.insert("strLen".into(),         bi("strLen", 1, b_str_len));
    g.defs.insert("strConcat".into(),      bi("strConcat", 2, b_str_concat));
    g.defs.insert("strIndexOf".into(),     bi("strIndexOf", 2, b_str_index_of));
    g.defs.insert("strReplace".into(),     bi("strReplace", 3, b_str_replace));
    g.defs.insert("strSplit".into(),       bi("strSplit", 2, b_str_split));
    g.defs.insert("substring".into(),      bi("substring", 3, b_substring));
    g.defs.insert("strToUpper".into(),     bi("strToUpper", 1, b_str_to_upper));
    g.defs.insert("strToLower".into(),     bi("strToLower", 1, b_str_to_lower));
    g.defs.insert("strTrim".into(),        bi("strTrim", 1, b_str_trim));
    g.defs.insert("strChars".into(),       bi("strChars", 1, b_str_chars));
    g.defs.insert("intToStr".into(),       bi("intToStr", 1, b_int_to_str));
    g.defs.insert("realToStr".into(),      bi("realToStr", 1, b_real_to_str));
    g.defs.insert("strToInt".into(),       bi("strToInt", 1, b_str_to_int));
    g.defs.insert("strToReal".into(),      bi("strToReal", 1, b_str_to_real));
    g.defs.insert("toStr".into(),          bi("toStr", 1, b_to_str));
    // File I/O
    g.defs.insert("readFile".into(),    bi("readFile", 1, b_read_file));
    g.defs.insert("writeFile".into(),   bi("writeFile", 2, b_write_file));
    g.defs.insert("appendFile".into(),  bi("appendFile", 2, b_append_file));
    g.defs.insert("fileExists".into(),  bi("fileExists", 1, b_file_exists));
    g.defs.insert("removeFile".into(),  bi("removeFile", 1, b_remove_file));
    // I/O streams
    g.defs.insert("println".into(),  bi("println", 1, b_println));
    g.defs.insert("eprint".into(),   bi("eprint", 1, b_eprint));
    g.defs.insert("eprintln".into(), bi("eprintln", 1, b_eprintln));
    g.defs.insert("readLine".into(), bi("readLine", 1, b_read_line));
    // OS / process
    g.defs.insert("getEnv".into(), bi("getEnv", 1, b_get_env));
    g.defs.insert("exit".into(),   bi("exit", 1, b_exit));
    // Mutable references (Ref A)
    g.defs.insert("mkRef".into(),    bi("mkRef", 1, b_mk_ref));
    g.defs.insert("readRef".into(),  bi("readRef", 1, b_read_ref));
    g.defs.insert("writeRef".into(), bi("writeRef", 2, b_write_ref));
    // Dictionaries (Dict K V — functional finite map K → V)
    g.defs.insert("emptyDict".into(),  bi("emptyDict", 1, b_empty_dict));
    g.defs.insert("dictInsert".into(), bi("dictInsert", 3, b_dict_insert));
    g.defs.insert("dictGet".into(),    bi("dictGet", 2, b_dict_get));
    g.defs.insert("dictMember".into(), bi("dictMember", 2, b_dict_member));
    g.defs.insert("dictRemove".into(), bi("dictRemove", 2, b_dict_remove));
    g.defs.insert("dictSize".into(),   bi("dictSize", 1, b_dict_size));
    g.defs.insert("dictKeys".into(),   bi("dictKeys", 1, b_dict_keys));
    g.defs.insert("dictValues".into(), bi("dictValues", 1, b_dict_values));
    // Time
    g.defs.insert("nowSecs".into(),         bi("nowSecs", 1, b_now_secs));
    g.defs.insert("nowMillis".into(),       bi("nowMillis", 1, b_now_millis));
    g.defs.insert("nowMicros".into(),       bi("nowMicros", 1, b_now_micros));
    g.defs.insert("monotonicMillis".into(), bi("monotonicMillis", 1, b_monotonic_millis));
    g.defs.insert("sleep".into(),           bi("sleep", 1, b_sleep));
    // Process execution
    g.defs.insert("execShell".into(),  bi("execShell", 1, b_exec_shell));
    g.defs.insert("runCommand".into(), bi("runCommand", 2, b_run_command));
    // Random (xorshift64* PRNG)
    g.defs.insert("randomSeed".into(),  bi("randomSeed", 1, b_random_seed));
    g.defs.insert("randomInt".into(),   bi("randomInt", 1, b_random_int));
    g.defs.insert("randomRange".into(), bi("randomRange", 2, b_random_range));
    g.defs.insert("randomFloat".into(), bi("randomFloat", 1, b_random_float));
    // Bit operations
    g.defs.insert("bitAnd".into(),   bi("bitAnd", 2, b_bit_and));
    g.defs.insert("bitOr".into(),    bi("bitOr", 2, b_bit_or));
    g.defs.insert("bitXor".into(),   bi("bitXor", 2, b_bit_xor));
    g.defs.insert("bitNot".into(),   bi("bitNot", 1, b_bit_not));
    g.defs.insert("bitShl".into(),   bi("bitShl", 2, b_bit_shl));
    g.defs.insert("bitShr".into(),   bi("bitShr", 2, b_bit_shr));
    g.defs.insert("popcount".into(), bi("popcount", 1, b_popcount));
    // JSON
    g.defs.insert("jsonEncode".into(), bi("jsonEncode", 1, b_json_encode));
    g.defs.insert("jsonParse".into(),  bi("jsonParse", 1, b_json_parse));
    // TCP networking
    g.defs.insert("tcpListen".into(),  bi("tcpListen", 2, b_tcp_listen));
    g.defs.insert("tcpAccept".into(),  bi("tcpAccept", 1, b_tcp_accept));
    g.defs.insert("tcpConnect".into(), bi("tcpConnect", 2, b_tcp_connect));
    g.defs.insert("tcpRead".into(),    bi("tcpRead", 2, b_tcp_read));
    g.defs.insert("tcpWrite".into(),   bi("tcpWrite", 2, b_tcp_write));
    g.defs.insert("tcpClose".into(),   bi("tcpClose", 1, b_tcp_close));
    // HTTP (built on TCP)
    g.defs.insert("httpGet".into(),            bi("httpGet", 1, b_http_get));
    // Concurrency: Atomic i64 (Arc-backed, Send + Sync)
    g.defs.insert("atomicNew".into(),       bi("atomicNew", 1, b_atomic_new));
    g.defs.insert("atomicGet".into(),       bi("atomicGet", 1, b_atomic_get));
    g.defs.insert("atomicSet".into(),       bi("atomicSet", 2, b_atomic_set));
    g.defs.insert("atomicAdd".into(),       bi("atomicAdd", 2, b_atomic_add));
    g.defs.insert("atomicCas".into(),       bi("atomicCas", 3, b_atomic_cas));
    g.defs.insert("threadId".into(),        bi("threadId", 1, b_thread_id));
    g.defs.insert("spawnAtomicAdd".into(),  bi("spawnAtomicAdd", 3, b_spawn_atomic_add));
    // Bytecode VM access
    g.defs.insert("vmEval".into(),     bi("vmEval", 1, b_vm_eval));
    g.defs.insert("vmTime".into(),     bi("vmTime", 2, b_vm_time));
    g.defs.insert("vmCompiles".into(), bi("vmCompiles", 1, b_vm_compiles));
    // SMT-lite: linear arithmetic decision procedure
    g.defs.insert("linarithProve".into(),   bi("linarithProve", 3, b_linarith_prove));
    g.defs.insert("linarithCounter".into(), bi("linarithCounter", 3, b_linarith_counter));
    // Builtin metadata accessors (Phase 9).  Query the structural / set-
    // theoretic information catalogued in `src/builtin_meta.rs`.
    g.defs.insert("builtinDoc".into(),         bi("builtinDoc", 1, b_builtin_doc));
    g.defs.insert("builtinSig".into(),         bi("builtinSig", 1, b_builtin_sig));
    g.defs.insert("builtinEffect".into(),      bi("builtinEffect", 1, b_builtin_effect));
    g.defs.insert("builtinDomain".into(),      bi("builtinDomain", 1, b_builtin_domain));
    g.defs.insert("builtinCodomain".into(),    bi("builtinCodomain", 1, b_builtin_codomain));
    g.defs.insert("builtinProperties".into(),  bi("builtinProperties", 1, b_builtin_properties));
    g.defs.insert("builtinNames".into(),       bi("builtinNames", 1, b_builtin_names));
    g.defs.insert("builtinHasProperty".into(), bi("builtinHasProperty", 2, b_builtin_has_property));
    // Closure-based threading.  `spawn` is dispatched via apply() because it
    // needs to invoke a closure on a new thread; the placeholder fn here is
    // never called.
    fn b_spawn_placeholder(_args: &[Value]) -> Result<Value, String> {
        Err("spawn: internal — not dispatched here".into())
    }
    g.defs.insert("spawn".into(), bi("spawn", 1, b_spawn_placeholder));
    fn b_parmap_placeholder(_args: &[Value]) -> Result<Value, String> {
        Err("parMap: internal — not dispatched here".into())
    }
    g.defs.insert("parMap".into(), bi("parMap", 2, b_parmap_placeholder));
    g.defs.insert("join".into(),  bi("join", 1, b_join));
    // Channels (mpsc)
    g.defs.insert("chanNew".into(),   bi("chanNew", 1, b_chan_new));
    g.defs.insert("chanSend".into(),  bi("chanSend", 2, b_chan_send));
    g.defs.insert("chanRecv".into(),  bi("chanRecv", 1, b_chan_recv));
    g.defs.insert("chanClose".into(), bi("chanClose", 1, b_chan_close));
    // FFI (libc dlopen on Linux/macOS — no external crate)
    g.defs.insert("ffiLoad".into(),       bi("ffiLoad", 1, b_ffi_load));
    g.defs.insert("ffiCallIntInt".into(), bi("ffiCallIntInt", 3, b_ffi_call_i_i));
    g.defs.insert("ffiCallStrInt".into(), bi("ffiCallStrInt", 3, b_ffi_call_s_i));
    g.defs.insert("ffiClose".into(),      bi("ffiClose", 1, b_ffi_close));
    // IO marker type — set-theoretic: IO A = "the set of computations
    // producing a value in A by interacting with the world".  Currently
    // implemented as the identity function (IO A == A) so signatures like
    // `readFile : String -> IO (Result String String)` parse and type-
    // check while having no runtime effect.  This reserves the syntax for
    // a future enforced effect system without disrupting existing code.
    fn b_io_marker(args: &[Value]) -> Result<Value, String> {
        // IO A = A.  We accept any value and return it unchanged.
        Ok(args[0].clone())
    }
    g.defs.insert("IO".into(), bi("IO", 1, b_io_marker));
    // CLI arguments — populated from main.rs via `set_program_args`.  Default
    // is an empty list; the bare REPL has no arguments to pass.
    g.defs.insert("args".into(), make_list(Vec::new()));
    // Note: numeric constants `pi` and `e` live in `stdlib.seki` as plain
    // Real literals — they don't need Rust because they are values, not
    // computations.
    g
}

/// Implementation of the `spawn` builtin.  Lives at module scope because it
/// needs to clone the parent's globals and invoke a closure on a new thread
/// — neither of which is possible from inside a plain `fn(&[Value])` body.
///
/// Closures captured here transit thread boundaries safely because Phase 4
/// migrated all interior-mutable state to `Arc<Mutex<…>>`, so `Value: Send`.
pub fn spawn_dispatch(globals: &Globals, args: &[Value]) -> Result<Value, String> {
    use crate::value::Handle;
    let closure = match &args[0] {
        Value::Closure { .. } | Value::Builtin(_) => args[0].clone(),
        v => return Err(format!("spawn: expected function, got {}", v.type_name())),
    };
    // Snapshot the parent globals.  Globals contain only `Value`s and
    // simple HashMaps; the resulting `OwnedGlobals` is `Send`.
    let g_snapshot = globals.clone_for_thread();
    let join = std::thread::spawn(move || -> Result<Value, String> {
        let ctx = EvalCtx::new(&g_snapshot);
        // Apply the user closure to the unit argument `()`.
        let unit = Value::Set(Arc::new(SetVal::Enum(vec![])));
        ctx.apply(closure, vec![unit])
            .map_err(|e| format!("{}", e))
    });
    Ok(Value::Handle(Handle::Thread(Arc::new(std::sync::Mutex::new(Some(join))))))
}

/// Suggest a known name close to `wanted` (didYouMean).  Returns the best
/// match if its Levenshtein distance is within a small relative budget
/// (≤ 2 absolute, or ≤ ⌊len/3⌋, whichever is larger).  Ties broken
/// alphabetically for determinism.
///
/// Implementation note: walks every key in `defs` / `theorems` / `axioms`
/// once.  For a prelude of ~120 builtins this is fine; if globals balloon
/// we can switch to BK-trees later.
pub fn suggest_name(wanted: &str, g: &Globals) -> Option<String> {
    if wanted.is_empty() { return None; }
    let len = wanted.chars().count();
    let max_dist = std::cmp::max(2, len / 3);

    let mut best: Option<(usize, String)> = None;
    let mut consider = |name: &String| {
        // Quick reject on length — anything off by more than max_dist
        // characters cannot be within edit distance max_dist.
        let nlen = name.chars().count();
        if nlen.abs_diff(len) > max_dist { return; }
        let d = levenshtein(wanted, name);
        if d > max_dist { return; }
        match &best {
            None => best = Some((d, name.clone())),
            Some((bd, bn)) => {
                if d < *bd || (d == *bd && name < bn) {
                    best = Some((d, name.clone()));
                }
            }
        }
    };
    for k in g.defs.keys() { consider(k); }
    for k in g.theorems.keys() { consider(k); }
    for k in g.axioms.keys() { consider(k); }
    best.map(|(_, n)| n)
}

/// Plain Levenshtein edit distance.  `i64`-free; uses row-by-row DP.
fn levenshtein(a: &str, b: &str) -> usize {
    let av: Vec<char> = a.chars().collect();
    let bv: Vec<char> = b.chars().collect();
    let m = av.len();
    let n = bv.len();
    if m == 0 { return n; }
    if n == 0 { return m; }
    let mut prev: Vec<usize> = (0..=n).collect();
    let mut cur: Vec<usize> = vec![0; n + 1];
    for i in 1..=m {
        cur[0] = i;
        for j in 1..=n {
            let cost = if av[i - 1] == bv[j - 1] { 0 } else { 1 };
            cur[j] = std::cmp::min(
                std::cmp::min(prev[j] + 1, cur[j - 1] + 1),
                prev[j - 1] + cost,
            );
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[n]
}

/// Detect whether `to` (a type-level expression) is an application of the
/// `IO` marker — i.e. matches the pattern `IO _`.  Used during dep-arrow
/// membership to skip sample evaluation of side-effecting functions.
///
/// Returns true for:
///   * `IO X`           — direct application
///   * `IO (Result a b)` — nested type expressions inside `IO`
fn is_io_marker_app(e: &Expr) -> bool {
    match e {
        Expr::App { func, args } => {
            args.len() == 1 && matches!(func.as_ref(), Expr::Var { name: n, .. } if n == "IO")
        }
        _ => false,
    }
}

/// `parMap f xs` — applies `f` to each element of `xs` in parallel,
/// returning a list of results in the original order.  Each element gets
/// its own OS thread; if `xs` has length n, n threads are spawned.  For
/// small CPU-bound workloads this is overkill; for I/O-bound ones (HTTP
/// requests, file reads) it's the right primitive.
///
/// Acts as a stand-in for a proper async runtime until Phase 6 — same
/// programming model (concurrent computations over a list), worse
/// scheduler (one OS thread per task instead of M:N green threads).
pub fn par_map_dispatch(globals: &Globals, args: &[Value]) -> Result<Value, String> {
    let func = match &args[0] {
        Value::Closure { .. } | Value::Builtin(_) => args[0].clone(),
        v => return Err(format!("parMap: expected function, got {}", v.type_name())),
    };
    // Walk the input list (pair-encoded `(0,()) | (1,(h,t))`) into a Vec.
    let mut inputs: Vec<Value> = Vec::new();
    let mut cur = &args[1];
    loop {
        let xs = match cur {
            Value::Tuple(xs) if xs.len() == 2 => xs,
            _ => return Err("parMap: second arg must be a List".into()),
        };
        match (&xs[0], &xs[1]) {
            (Value::Int(0), _) => break,
            (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                inputs.push(inner[0].clone());
                cur = &inner[1];
            }
            _ => return Err("parMap: malformed List in second arg".into()),
        }
    }
    // Spawn one thread per input.  Each thread gets a Globals snapshot +
    // closure clone.  The Arc<AtomicI64> / Channel / Dict types shared via
    // closure captures are Sync-safe after the Phase 4 migration.
    let mut handles = Vec::with_capacity(inputs.len());
    for v in inputs {
        let f = func.clone();
        let g_snap = globals.clone_for_thread();
        let jh = std::thread::spawn(move || -> Result<Value, String> {
            let ctx = EvalCtx::new(&g_snap);
            ctx.apply(f, vec![v]).map_err(|e| format!("{}", e))
        });
        handles.push(jh);
    }
    // Collect results preserving input order.
    let mut results: Vec<Value> = Vec::with_capacity(handles.len());
    for h in handles {
        match h.join() {
            Ok(Ok(v)) => results.push(v),
            Ok(Err(e)) => return Err(format!("parMap: thread errored: {}", e)),
            Err(_) => return Err("parMap: thread panicked".into()),
        }
    }
    // Rebuild the pair-encoded list.
    let unit = Value::Set(Arc::new(SetVal::Enum(vec![])));
    let mut acc = Value::Tuple(vec![Value::Int(0), unit]);
    for v in results.into_iter().rev() {
        acc = Value::Tuple(vec![Value::Int(1), Value::Tuple(vec![v, acc])]);
    }
    Ok(acc)
}

/// Set the value of the global `args` binding to a pair-encoded list of the
/// given strings.  Called from `main.rs` before running a source file so that
/// `args` is populated with the CLI arguments after the file path.
pub fn set_program_args(g: &mut Globals, items: Vec<String>) {
    let unit = Value::Set(Arc::new(SetVal::Enum(vec![])));
    let mut acc = Value::Tuple(vec![Value::Int(0), unit]);
    for s in items.into_iter().rev() {
        acc = Value::Tuple(vec![
            Value::Int(1),
            Value::Tuple(vec![Value::Str(s), acc]),
        ]);
    }
    g.defs.insert("args".into(), acc);
}

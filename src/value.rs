//! Runtime values, set representations, and lexical environments.
//!
//! In set-theory we treat *types* and *sets* uniformly: every type is the set
//! of its inhabitants.  Built-in atomic sets (Nat, Int, Bool, String, Prop)
//! are represented symbolically because they are infinite or syntactic; user
//! sets can be enumerated or defined by a predicate (comprehension).

use crate::ast::Expr;
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex};

// Phase 4: all shared / interior-mutable runtime data uses `Arc` and
// `Mutex` instead of `Rc` and `RefCell`.  This makes `Value` (and every
// type that transitively contains it) `Send + Sync`, which is the
// prerequisite for closure-based threading via `std::thread::spawn`.
//
// Locks are taken in narrow scopes so single-threaded contention stays
// near-zero.  An uncontended `Mutex::lock()` on x86 is a few nanoseconds.

// -- Values -----------------------------------------------------------------

#[derive(Clone)]
pub enum Value {
    Unit,
    Int(i64),
    /// IEEE-754 `f64`.  Used for the `Real` built-in set.  Note that `Real`
    /// in seki is a computational (machine-precision) approximation of `ℝ`,
    /// not a constructive Cauchy-sequence representation.
    Real(f64),
    Bool(bool),
    Str(String),
    Set(Arc<SetVal>),
    /// Heterogeneous fixed-arity tuple — `(a, b, c)`.
    /// **Lists and binary trees are encoded as nested tagged tuples** by the
    /// stdlib (`nil = (false, ())`, `cons x xs = (true, (x, xs))`,
    /// `leaf = (false, ())`, `node l v r = (true, (l, (v, r)))`).  The
    /// runtime no longer has dedicated `List`/`Tree` variants — those types
    /// are user-level constructions in `stdlib.seki`.  Display logic
    /// recognizes the canonical shapes and renders them as `[a, b, c]` and
    /// `(node l v r)` for readability.
    Tuple(Vec<Value>),
    Closure {
        params: Vec<String>,
        body: Box<Expr>,
        env: Env,
        /// When `Some(name)`, this closure is a `let rec name := ...` binding.
        /// `apply` extends the local env with `name → self` so the body can
        /// reference its own name for recursion.  None for ordinary lambdas.
        rec_name: Option<String>,
    },
    Builtin(BuiltinFn),
    /// Mutable reference cell.  Set-theoretically: an element of the set
    /// `Ref A`, which is the set of mutable storage locations holding a
    /// value in A.  `Arc<Mutex<_>>` provides shared ownership + interior
    /// mutability so `writeRef` can modify the cell that other bindings
    /// share, while keeping `Value: Clone`.  Equality is reference identity
    /// (two distinct cells are distinct elements of `Ref A`, even if they
    /// currently hold equal values).
    Ref(Arc<Mutex<Value>>),
    /// Efficient dictionary (HashMap).  Set-theoretically: a finite element
    /// of the powerset of `K × V` subject to the functional constraint
    /// (each key appears at most once).  Membership `(k, v) in dict`
    /// holds iff the map contains `k` and maps it to `v`.
    Dict(Arc<Mutex<HashMap<DictKey, Value>>>),
    /// Opaque OS resource handle (TCP socket / listener etc.).  Carries no
    /// set-theoretic semantics — handles are externally-allocated tokens.
    /// Equality is reference identity.
    Handle(Handle),
}

/// Kinds of OS handles carried inside `Value::Handle`.  Each variant wraps a
/// shared, interior-mutable resource so the same handle can be passed around
/// freely after it's been allocated.  Closing returns `()`; subsequent ops
/// on a closed handle return `Err` at the builtin layer.
#[derive(Clone)]
pub enum Handle {
    Socket(Arc<Mutex<Option<std::net::TcpStream>>>),
    Listener(Arc<Mutex<Option<std::net::TcpListener>>>),
    /// Shared atomic 64-bit integer — Arc keeps it Send+Sync so spawned
    /// threads can observe writes done by other threads.
    Atomic(Arc<std::sync::atomic::AtomicI64>),
    /// JoinHandle for a thread spawned by `spawn`.  Inner `Option` lets
    /// `join` *take* the JoinHandle exactly once.  The thread's result
    /// (or error message) flows out via this handle.
    Thread(Arc<Mutex<Option<std::thread::JoinHandle<Result<Value, String>>>>>),
    /// Multi-producer-single-consumer channel — Phase 4 messaging.  The
    /// sender / receiver are both stored so a `Value::Handle` can be used
    /// for either operation; each side checks the relevant Option is
    /// populated.
    Channel(Arc<ChannelEnds>),
    /// Foreign function library (a loaded shared object).  Currently just
    /// stores the `void *` returned by dlopen as a usize; loading and
    /// symbol resolution go through `b_ffi_*` builtins.
    FfiLib(Arc<Mutex<Option<usize>>>),
}

/// Storage for one mpsc channel's ends.  Both ends are `Option<Mutex<_>>`
/// so the channel can be shared, cloned, and operated on from either side.
pub struct ChannelEnds {
    pub tx: Mutex<Option<std::sync::mpsc::Sender<Value>>>,
    pub rx: Mutex<Option<std::sync::mpsc::Receiver<Value>>>,
}

/// Key wrapper for `Value::Dict` — only the hashable, equality-decidable
/// subset of values (Int / Bool / Str / Tuple of these) can serve as keys.
/// Anything else triggers a runtime error at insert/lookup time.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum DictKey {
    Int(i64),
    Bool(bool),
    Str(String),
    Tuple(Vec<DictKey>),
}

impl DictKey {
    pub fn from_value(v: &Value) -> Result<Self, String> {
        match v {
            Value::Int(n) => Ok(DictKey::Int(*n)),
            Value::Bool(b) => Ok(DictKey::Bool(*b)),
            Value::Str(s) => Ok(DictKey::Str(s.clone())),
            Value::Tuple(xs) => {
                let parts: Result<Vec<_>, _> =
                    xs.iter().map(DictKey::from_value).collect();
                Ok(DictKey::Tuple(parts?))
            }
            other => Err(format!(
                "dict: key must be Int/Bool/String/Tuple, got {}",
                other.type_name()
            )),
        }
    }
    pub fn to_value(&self) -> Value {
        match self {
            DictKey::Int(n) => Value::Int(*n),
            DictKey::Bool(b) => Value::Bool(*b),
            DictKey::Str(s) => Value::Str(s.clone()),
            DictKey::Tuple(xs) => Value::Tuple(xs.iter().map(DictKey::to_value).collect()),
        }
    }
}

#[derive(Clone)]
pub struct BuiltinFn {
    pub name: &'static str,
    pub arity: usize,
    pub func: fn(&[Value]) -> Result<Value, String>,
}

impl std::fmt::Debug for BuiltinFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<builtin:{} arity={}>", self.name, self.arity)
    }
}

#[derive(Clone)]
pub enum SetVal {
    /// {a, b, c, ...}
    Enum(Vec<Value>),
    /// {x in domain | predicate}  with closure environment
    Comp {
        var: String,
        domain: Arc<SetVal>,
        pred: Expr,
        env: Env,
    },
    /// Symbolic atomic set: Nat, Int, Bool, String, Prop, Universe
    Atomic(AtomicSet),
    /// Function type: A -> B  (set of functions from A to B)
    Arrow {
        from: Arc<SetVal>,
        to: Arc<SetVal>,
    },
    /// Dependent function type: `(x : A) -> B(x)`.  Membership of a
    /// closure `f` requires that `f a in B[x:=a]` for every (sampled)
    /// `a in A`.  The `to` expression captures the closure environment so
    /// that `B(x)` can reference outer-scope names beyond the binder.
    DepArrow {
        binder: String,
        from: Arc<SetVal>,
        to: Expr,
        env: Env,
    },
    /// Cartesian product:  A times B,  A times B times C, ...
    /// A tuple `(a_1, ..., a_n)` belongs to the product iff each `a_i in T_i`.
    Product(Vec<Arc<SetVal>>),
    /// `List of A` — the set of all finite lists whose elements lie in A.
    /// Membership is decided element-wise.
    ListOf(Arc<SetVal>),
    /// `Tree of A` — the set of all finite binary trees whose node values
    /// lie in A.  Membership recurses into both subtrees.
    TreeOf(Arc<SetVal>),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AtomicSet {
    Nat,
    Int,
    /// `Real` — the set of IEEE-754 `f64` values.  An approximation of `ℝ`.
    Real,
    /// Retained for source-level compatibility but no longer the prelude
    /// representation of Bool (it's now a literal Enum set).
    Bool,
    StringS,
    /// Same situation as `Bool` — kept as a variant but not used in the
    /// default prelude.
    Prop,
    /// the universe of all sets — "Set"
    Universe,
}

impl AtomicSet {
    pub fn name(&self) -> &'static str {
        match self {
            AtomicSet::Nat => "Nat",
            AtomicSet::Int => "Int",
            AtomicSet::Real => "Real",
            AtomicSet::Bool => "Bool",
            AtomicSet::StringS => "String",
            AtomicSet::Prop => "Prop",
            AtomicSet::Universe => "Set",
        }
    }
}

impl Value {
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Unit => "Unit",
            Value::Int(_) => "Int",
            Value::Real(_) => "Real",
            Value::Bool(_) => "Bool",
            Value::Str(_) => "String",
            Value::Set(_) => "Set",
            Value::Tuple(_) => "Tuple",
            Value::Closure { .. } => "Function",
            Value::Builtin(_) => "Builtin",
            Value::Ref(_) => "Ref",
            Value::Dict(_) => "Dict",
            Value::Handle(_) => "Handle",
        }
    }
}

// -- Display ---------------------------------------------------------------

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Int(n) => write!(f, "{}", n),
            Value::Real(r) => {
                // Always show a decimal point so `1.0` doesn't masquerade as Int.
                if r.fract() == 0.0 && r.is_finite() {
                    write!(f, "{:.1}", r)
                } else {
                    write!(f, "{}", r)
                }
            }
            Value::Bool(b) => write!(f, "{}", b),
            Value::Str(s) => write!(f, "{:?}", s),
            Value::Set(s) => write!(f, "{}", s),
            Value::Tuple(_) => {
                // Friendly renders for canonical tagged-pair shapes.
                if let Some(s) = render_as_list(self) {
                    return f.write_str(&s);
                }
                if let Some(s) = render_as_tree(self) {
                    return f.write_str(&s);
                }
                if let Some(s) = render_as_ctor(self) {
                    return f.write_str(&s);
                }
                // Fall back to a plain tuple display.
                if let Value::Tuple(xs) = self {
                    write!(f, "(")?;
                    for (i, v) in xs.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", v)?;
                    }
                    write!(f, ")")
                } else {
                    unreachable!()
                }
            }
            Value::Closure { params, .. } => write!(f, "<fn:{}>", params.join(",")),
            Value::Builtin(b) => write!(f, "<builtin:{}>", b.name),
            Value::Ref(cell) => write!(f, "<ref {}>", cell.lock().unwrap()),
            Value::Dict(cells) => {
                let m = cells.lock().unwrap();
                write!(f, "{{")?;
                let mut first = true;
                for (k, v) in m.iter() {
                    if !first { write!(f, ", ")?; }
                    first = false;
                    write!(f, "{} => {}", k.to_value(), v)?;
                }
                write!(f, "}}")
            }
            Value::Handle(h) => match h {
                Handle::Socket(c) => {
                    if c.lock().unwrap().is_none() { write!(f, "<socket:closed>") }
                    else { write!(f, "<socket>") }
                }
                Handle::Listener(c) => {
                    if c.lock().unwrap().is_none() { write!(f, "<listener:closed>") }
                    else { write!(f, "<listener>") }
                }
                Handle::Atomic(a) => write!(
                    f, "<atomic {}>", a.load(std::sync::atomic::Ordering::SeqCst)
                ),
                Handle::Thread(j) => {
                    let still_running = j.lock().unwrap().as_ref().is_some();
                    if still_running { write!(f, "<thread:running>") }
                    else { write!(f, "<thread:done>") }
                }
                Handle::Channel(_) => write!(f, "<channel>"),
                Handle::FfiLib(c) => {
                    if c.lock().unwrap().is_none() { write!(f, "<ffilib:closed>") }
                    else { write!(f, "<ffilib>") }
                }
            }
        }
    }
}

impl fmt::Display for SetVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SetVal::Enum(vs) => {
                write!(f, "{{")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "}}")
            }
            SetVal::Comp { var, domain, pred, .. } => {
                write!(f, "{{{} in {} | {}}}", var, domain, pred)
            }
            SetVal::Atomic(a) => write!(f, "{}", a.name()),
            SetVal::Arrow { from, to } => write!(f, "({} -> {})", from, to),
            SetVal::DepArrow { binder, from, to, .. } => {
                write!(f, "(({} : {}) -> {})", binder, from, to)
            }
            SetVal::Product(parts) => {
                write!(f, "(")?;
                for (i, p) in parts.iter().enumerate() {
                    if i > 0 {
                        write!(f, " times ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")
            }
            SetVal::ListOf(t) => write!(f, "(List {})", t),
            SetVal::TreeOf(t) => write!(f, "(Tree {})", t),
        }
    }
}

// ---- pair-encoded list / tree pretty-printers ----------------------------

// Tag values used by stdlib's tagged-pair encoding of lists and trees.
const TAG_NIL: i64 = 0;
const TAG_CONS: i64 = 1;
const TAG_LEAF: i64 = 2;
const TAG_NODE: i64 = 3;

/// Try to render `v` as a `[a, b, c]` list when it has the canonical
/// list-tagged-pair shape: `(0, ())` for nil and `(1, (head, tail))` for
/// cons.  Returns `None` for anything that doesn't conform.
pub fn render_as_list(v: &Value) -> Option<String> {
    let mut elems: Vec<String> = Vec::new();
    let mut cur = v;
    loop {
        let xs = match cur {
            Value::Tuple(xs) if xs.len() == 2 => xs,
            _ => return None,
        };
        match (&xs[0], &xs[1]) {
            (Value::Int(t), _) if *t == TAG_NIL => {
                let mut s = String::from("[");
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }
                    s.push_str(e);
                }
                s.push(']');
                return Some(s);
            }
            (Value::Int(t), Value::Tuple(inner)) if *t == TAG_CONS && inner.len() == 2 => {
                elems.push(format!("{}", inner[0]));
                cur = &inner[1];
            }
            _ => return None,
        }
    }
}

/// Try to render `v` as a `data`-defined constructor — values built by the
/// stdlib `data` desugar have shape `("CtorName", (a1, (a2, (..., (ak, ())))))`.
/// We require the tag to be a String AND the body to terminate with the unit
/// sentinel `()` (= empty SetEnum) at the end; otherwise we conservatively
/// decline to render this way.
pub fn render_as_ctor(v: &Value) -> Option<String> {
    let outer = match v {
        Value::Tuple(xs) if xs.len() == 2 => xs,
        _ => return None,
    };
    let name = match &outer[0] {
        Value::Str(s) if !s.is_empty() => s.clone(),
        _ => return None,
    };
    // Walk the body, expecting nested pairs ending in unit / empty enum.
    let mut args: Vec<String> = Vec::new();
    let mut cur = &outer[1];
    loop {
        match cur {
            // unit terminator
            Value::Set(s) if matches!(&**s, SetVal::Enum(xs) if xs.is_empty()) => break,
            Value::Unit => break,
            Value::Tuple(inner) if inner.len() == 2 => {
                args.push(format!("{}", inner[0]));
                cur = &inner[1];
            }
            _ => return None,
        }
    }
    if args.is_empty() {
        return Some(name);
    }
    let mut s = name;
    for a in args {
        s.push(' ');
        // Wrap composite arg displays in parens for readability.
        if needs_paren(&a) {
            s.push('(');
            s.push_str(&a);
            s.push(')');
        } else {
            s.push_str(&a);
        }
    }
    Some(s)
}

fn needs_paren(rendered: &str) -> bool {
    // Composite renders contain spaces (e.g. "Some 5"); wrap them.  Quoted
    // strings and bracketed lists don't need extra parens.
    rendered.contains(' ')
        && !rendered.starts_with('(')
        && !rendered.starts_with('[')
        && !rendered.starts_with('{')
        && !rendered.starts_with('"')
}

/// Try to render `v` as `(node l v r)` / `leaf` when it has the canonical
/// tree-tagged-pair shape: `(2, ())` for leaf, `(3, (l, (v, r)))` for nodes.
pub fn render_as_tree(v: &Value) -> Option<String> {
    fn rec(v: &Value) -> Option<String> {
        let outer = match v {
            Value::Tuple(xs) if xs.len() == 2 => xs,
            _ => return None,
        };
        match (&outer[0], &outer[1]) {
            (Value::Int(t), _) if *t == TAG_LEAF => Some("leaf".to_string()),
            (Value::Int(t), Value::Tuple(body)) if *t == TAG_NODE && body.len() == 2 => {
                let l = &body[0];
                let inner = match &body[1] {
                    Value::Tuple(xs) if xs.len() == 2 => xs,
                    _ => return None,
                };
                let val = &inner[0];
                let r = &inner[1];
                Some(format!("(node {} {} {})", rec(l)?, val, rec(r)?))
            }
            _ => None,
        }
    }
    // Detect either a node directly, or a bare leaf (matching `(2, _)`).
    let outer = match v {
        Value::Tuple(xs) if xs.len() == 2 => xs,
        _ => return None,
    };
    match &outer[0] {
        Value::Int(t) if *t == TAG_NODE || *t == TAG_LEAF => rec(v),
        _ => None,
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

// -- Structural equality of values -----------------------------------------

pub fn value_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Unit, Value::Unit) => true,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Real(x), Value::Real(y)) => x == y,
        // Cross-type Int/Real equality: a Real is considered equal to an
        // Int when the Real has no fractional part and matches the integer.
        (Value::Int(x), Value::Real(y)) | (Value::Real(y), Value::Int(x)) => {
            y.is_finite() && y.fract() == 0.0 && (*x as f64) == *y
        }
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Set(x), Value::Set(y)) => set_eq(x, y),
        (Value::Tuple(xs), Value::Tuple(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(a, b)| value_eq(a, b))
        }
        // Ref equality is by *cell identity*, not contents — two cells that
        // happen to hold equal values are still distinct elements of `Ref T`.
        (Value::Ref(a), Value::Ref(b)) => Arc::ptr_eq(a, b),
        // Dict equality compares contents (functional equality of maps).
        (Value::Dict(a), Value::Dict(b)) => {
            let ma = a.lock().unwrap();
            let mb = b.lock().unwrap();
            ma.len() == mb.len()
                && ma.iter().all(|(k, v)| matches!(mb.get(k), Some(w) if value_eq(v, w)))
        }
        // Handles: reference identity.
        (Value::Handle(a), Value::Handle(b)) => match (a, b) {
            (Handle::Socket(x), Handle::Socket(y)) => Arc::ptr_eq(x, y),
            (Handle::Listener(x), Handle::Listener(y)) => Arc::ptr_eq(x, y),
            (Handle::Atomic(x), Handle::Atomic(y)) => Arc::ptr_eq(x, y),
            (Handle::Thread(x), Handle::Thread(y)) => Arc::ptr_eq(x, y),
            (Handle::Channel(x), Handle::Channel(y)) => Arc::ptr_eq(x, y),
            (Handle::FfiLib(x), Handle::FfiLib(y)) => Arc::ptr_eq(x, y),
            _ => false,
        },
        // closures/builtins: by reference identity (rarely useful)
        _ => false,
    }
}

/// Set equality treats enumerations as set-of-elements (order- and
/// duplicate-agnostic).  Cross-form (Enum vs Comp vs Atomic) equality is
/// only checked when both sides are the same form.  Atomic sets compare by
/// kind.
pub fn set_eq(a: &SetVal, b: &SetVal) -> bool {
    match (a, b) {
        (SetVal::Enum(xs), SetVal::Enum(ys)) => {
            // every x in xs is in ys, vice versa
            xs.iter().all(|x| ys.iter().any(|y| value_eq(x, y)))
                && ys.iter().all(|y| xs.iter().any(|x| value_eq(x, y)))
        }
        (SetVal::Atomic(x), SetVal::Atomic(y)) => x == y,
        (SetVal::Arrow { from: a1, to: b1 }, SetVal::Arrow { from: a2, to: b2 }) => {
            set_eq(a1, a2) && set_eq(b1, b2)
        }
        // DepArrow equality is undecidable in general (we'd need to
        // verify the body expressions are α-equivalent and yield the
        // same set for every input).  Conservatively false except when
        // structurally identical — we don't bother since it doesn't
        // come up in equality-of-types theorems.
        (SetVal::DepArrow { .. }, SetVal::DepArrow { .. }) => false,
        (SetVal::Product(xs), SetVal::Product(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(a, b)| set_eq(a, b))
        }
        (SetVal::ListOf(a), SetVal::ListOf(b)) => set_eq(a, b),
        (SetVal::TreeOf(a), SetVal::TreeOf(b)) => set_eq(a, b),
        // comprehension equality is undecidable in general → conservative false
        _ => false,
    }
}

// -- Environment (immutable cons list, Rc-shared) --------------------------

#[derive(Clone)]
pub struct Env {
    head: Option<Arc<EnvNode>>,
}

struct EnvNode {
    name: String,
    value: Value,
    parent: Option<Arc<EnvNode>>,
}

impl Env {
    pub fn new() -> Self {
        Env { head: None }
    }

    pub fn extend(&self, name: String, value: Value) -> Self {
        Env {
            head: Some(Arc::new(EnvNode {
                name,
                value,
                parent: self.head.clone(),
            })),
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&Value> {
        let mut node = self.head.as_ref()?;
        loop {
            if node.name == name {
                return Some(&node.value);
            }
            match &node.parent {
                Some(p) => node = p,
                None => return None,
            }
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Env::new()
    }
}

// -- Globals ---------------------------------------------------------------

/// Module-level definitions: `def` introduces these.  Looked up after env.
pub struct Globals {
    pub defs: HashMap<String, Value>,
    /// Theorems that have been verified.  Their *type* (proposition) is also
    /// recorded so they can be referenced as proof terms.
    pub theorems: HashMap<String, Value>,
    /// Axioms: untrusted but accepted propositions (their value is the prop).
    pub axioms: HashMap<String, Value>,
    /// Inferred or annotated types for `def` names, stored as Expr (which
    /// evaluates to the type-set at lookup time).  Populated by the
    /// inference pass at definition time.
    pub inferred_types: HashMap<String, Expr>,
    /// Verified theorem propositions, in AST form.  `by simp` reads these
    /// as candidate rewrite rules (LHS == RHS becomes LHS → RHS).
    pub theorem_props: HashMap<String, Expr>,
    /// Axiom propositions, in AST form.  Axioms can be used by `by simp` as
    /// trusted rewrite rules.
    pub axiom_props: HashMap<String, Expr>,
    /// Map from a class method name (e.g. "eq") to the class it belongs
    /// to (e.g. "Eq").  Populated by `Decl::ClassMeta`.  Used at eval
    /// time to recognize a call to a class method and trigger automatic
    /// dictionary resolution.
    pub class_methods: HashMap<String, String>,
    /// Map from class name to the dictionary constructor's tag name
    /// (e.g. "Eq" -> "MkEqDict").  Used to detect "this argument is
    /// already a dictionary; don't re-resolve."
    pub class_ctor: HashMap<String, String>,
    /// Map from `(class_name, type_key)` to the instance binding name
    /// (e.g. ("Eq", "Int") -> "EqInt").  Populated by `Decl::InstanceMeta`.
    pub instances: HashMap<(String, String), String>,
    /// `data` type info: data name → list of (constructor name, argument
    /// type names as text).  Used by `by induction` to dispatch structural
    /// induction on user-defined recursive ADTs.
    pub data_info: HashMap<String, Vec<(String, Vec<String>)>>,
}

impl Globals {
    pub fn new() -> Self {
        Globals {
            defs: HashMap::new(),
            theorems: HashMap::new(),
            axioms: HashMap::new(),
            inferred_types: HashMap::new(),
            theorem_props: HashMap::new(),
            axiom_props: HashMap::new(),
            class_methods: HashMap::new(),
            class_ctor: HashMap::new(),
            instances: HashMap::new(),
            data_info: HashMap::new(),
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&Value> {
        self.defs
            .get(name)
            .or_else(|| self.theorems.get(name))
            .or_else(|| self.axioms.get(name))
    }

    /// Snapshot for use on a spawned thread.  All fields are deep-cloned;
    /// because every `Value` is now `Send + Sync` (Phase 4 Rc→Arc migration),
    /// the resulting `Globals` is also `Send` and can move into a thread
    /// closure.
    pub fn clone_for_thread(&self) -> Globals {
        Globals {
            defs: self.defs.clone(),
            theorems: self.theorems.clone(),
            axioms: self.axioms.clone(),
            inferred_types: self.inferred_types.clone(),
            theorem_props: self.theorem_props.clone(),
            axiom_props: self.axiom_props.clone(),
            class_methods: self.class_methods.clone(),
            class_ctor: self.class_ctor.clone(),
            instances: self.instances.clone(),
            data_info: self.data_info.clone(),
        }
    }
}

impl Default for Globals {
    fn default() -> Self {
        Globals::new()
    }
}

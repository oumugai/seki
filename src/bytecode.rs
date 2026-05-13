//! Bytecode compiler + stack VM for a subset of seki's expression language.
//!
//! Phase 5 goal: deliver a meaningful speed-up over the tree-walking
//! interpreter for the hot path of arithmetic-heavy pure functions.  This
//! covers numeric algorithms, predicate evaluation in refinement checks,
//! and the inner loops of tactics like `by algebra`'s polynomial pass.
//!
//! Scope (what compiles):
//!   * `Int` / `Real` / `Bool` literals and variables
//!   * arithmetic (`+`, `-`, `*`, `/`, `mod`) and unary neg
//!   * comparisons (`==`, `!=`, `<`, `<=`, `>`, `>=`)
//!   * logical and / or (short-circuit) / not
//!   * `if / then / else`
//!   * `let x = ... in ...` (lexical binding via a frame slot)
//!   * direct calls to compiled functions (no closure capture across calls)
//!
//! Out of scope (falls back to AST eval):
//!   * Sets / comprehension / forall / exists
//!   * Tuples / lists / ADT match
//!   * Tactics, simp, induction
//!   * Closures that capture environment (use AST for now)
//!
//! Design notes:
//!   * Stack-based VM — simpler to write than register-based and competitive
//!     in performance for this size of program.
//!   * One instruction = one `Op` enum variant.  No struct-of-arrays.
//!   * `Frame` holds local variables in a `Vec<Value>`; the compiler emits
//!     `Load(idx)` / `Store(idx)` against slot indices it allocates.
//!   * The VM is its own struct; the evaluator dispatches to it when an
//!     expression's shape is in the compilable subset.

use crate::ast::{BinOp, Expr, UnOp};
use crate::value::{BuiltinFn, Globals, Value};

/// Compiled bytecode for one function body.
#[derive(Clone, Debug)]
pub struct Bytecode {
    pub ops: Vec<Op>,
    /// Number of local slots required by the function (parameters + lets).
    pub n_locals: usize,
}

#[derive(Clone, Debug)]
pub enum Op {
    /// Push a literal value onto the operand stack.
    PushInt(i64),
    PushReal(f64),
    PushBool(bool),
    /// Load a local by slot index.
    Load(usize),
    /// Store top of stack into a local; the value is also consumed.
    Store(usize),
    /// Pop and discard.
    Pop,
    /// Numeric / boolean operators.  Each pops 2 operands (rhs on top),
    /// pushes 1 result.
    Add, Sub, Mul, Div, Mod,
    Neg,
    Eq, Neq,
    Lt, Le, Gt, Ge,
    And, Or, Not,
    /// Conditional / unconditional jumps.  Offsets are absolute indices
    /// into `ops` (post-resolution).  `JumpIfFalse` pops the test value.
    Jump(usize),
    JumpIfFalse(usize),
    /// Halt and return top of stack as the function result.
    Ret,

    // ----- Phase 7 additions ------------------------------------------------
    /// Pop `arity` values and push a `Value::Tuple` containing them in stack
    /// order (deepest first).  Supports `(a, b, c)` literals and stdlib's
    /// tagged-pair-based ADTs when their constructors are inlinable.
    Tuple(usize),
    /// Push a `Value::Str` literal — needed once we can build string-keyed
    /// tagged pairs (and useful for any expression that's just a string).
    PushStr(String),
    /// Push the empty-set unit value `()` that seki uses as the terminator
    /// for tagged-pair-encoded lists / ctors.
    PushUnit,
    /// Pop `arity` values, call the snapshotted builtin function with them,
    /// push the result.  Enables compiling `intToStr 42`, `strLen "abc"`,
    /// etc. without falling back to AST evaluation.  Builtin function
    /// pointers are captured at compile time, so this is safe to call
    /// from any thread.
    BuiltinCall(BuiltinFn, usize),
}

#[derive(Debug)]
pub enum CompileErr {
    /// The expression has a shape we don't handle yet — caller should fall
    /// back to AST evaluation.
    Unsupported(&'static str),
}

/// Compiler state.  `slots[name]` maps a bound variable to its frame slot.
struct Compiler<'a> {
    ops: Vec<Op>,
    /// Stack of scopes: each scope maps name → slot index.  Push on entering
    /// a `let` / lambda body, pop on leaving.  Lookup walks from top down.
    scopes: Vec<Vec<(&'a str, usize)>>,
    /// Next free slot index.
    next_slot: usize,
    /// Maximum slots seen — recorded into `Bytecode.n_locals`.
    max_slots: usize,
    /// Optional snapshot of globals for resolving builtin calls.  When
    /// `Some`, `App { func: Var{name}, args }` where `name` resolves to a
    /// builtin can be compiled into a `BuiltinCall` op.  When `None`, all
    /// `App` forms fall back to AST evaluation.
    globals: Option<&'a Globals>,
}

impl<'a> Compiler<'a> {
    fn new() -> Self {
        Self {
            ops: Vec::new(),
            scopes: vec![Vec::new()],
            next_slot: 0,
            max_slots: 0,
            globals: None,
        }
    }
    fn with_globals(globals: &'a Globals) -> Self {
        let mut c = Self::new();
        c.globals = Some(globals);
        c
    }
    fn lookup(&self, name: &str) -> Option<usize> {
        for scope in self.scopes.iter().rev() {
            for (n, slot) in scope.iter().rev() {
                if *n == name {
                    return Some(*slot);
                }
            }
        }
        None
    }
    fn alloc_slot(&mut self, name: &'a str) -> usize {
        let slot = self.next_slot;
        self.next_slot += 1;
        if self.next_slot > self.max_slots {
            self.max_slots = self.next_slot;
        }
        self.scopes.last_mut().unwrap().push((name, slot));
        slot
    }
    fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }
    fn pop_scope(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            // Reuse slots that fell out of scope: rewind `next_slot` to the
            // earliest slot in the popped scope so nested `let`s share frame
            // space.  (Conservative; doesn't matter for correctness.)
            if let Some(first) = scope.first() {
                self.next_slot = first.1;
            }
        }
    }
    fn emit(&mut self, op: Op) -> usize {
        self.ops.push(op);
        self.ops.len() - 1
    }
    fn patch_jump(&mut self, at: usize, to: usize) {
        match &mut self.ops[at] {
            Op::Jump(t) | Op::JumpIfFalse(t) => *t = to,
            _ => panic!("patch_jump: not a jump at {}", at),
        }
    }
    fn here(&self) -> usize {
        self.ops.len()
    }

    fn compile_expr(&mut self, e: &'a Expr) -> Result<(), CompileErr> {
        use BinOp as B;
        match e {
            Expr::Int(n) => { self.emit(Op::PushInt(*n)); Ok(()) }
            Expr::Real(r) => { self.emit(Op::PushReal(*r)); Ok(()) }
            Expr::Bool(b) => { self.emit(Op::PushBool(*b)); Ok(()) }
            Expr::Str(s) => { self.emit(Op::PushStr(s.clone())); Ok(()) }
            Expr::Var { name, .. } => {
                if let Some(slot) = self.lookup(name) {
                    self.emit(Op::Load(slot));
                    return Ok(());
                }
                // Bare global Var with no args — only allowed for builtin
                // *types* (e.g. `Int`) and "unit"-arity values.  For now we
                // refuse anything else; a future Phase 8 pass could push
                // global Value snapshots as constants.
                Err(CompileErr::Unsupported(
                    "global variable references aren't compiled to bytecode yet",
                ))
            }
            // `(a, b, c)` literal — compile each element, then build a tuple.
            Expr::Tuple(items) => {
                for it in items {
                    self.compile_expr(it)?;
                }
                self.emit(Op::Tuple(items.len()));
                Ok(())
            }
            // Direct application of a known global builtin: snapshot the
            // BuiltinFn at compile time so the VM doesn't need to consult
            // globals at run time.  Other application shapes fall back to
            // AST eval (caller handles).
            Expr::App { func, args } => {
                let g = self.globals
                    .ok_or(CompileErr::Unsupported("app: compiler has no globals snapshot"))?;
                let fname = match func.as_ref() {
                    Expr::Var { name, .. } => name.as_str(),
                    _ => return Err(CompileErr::Unsupported(
                        "app: only direct global function calls are compiled",
                    )),
                };
                let value = g.lookup(fname).ok_or(CompileErr::Unsupported(
                    "app: name not in globals",
                ))?;
                let bf = match value {
                    Value::Builtin(b) => b.clone(),
                    _ => return Err(CompileErr::Unsupported(
                        "app: target isn't a builtin (closures need full VM support)",
                    )),
                };
                if args.len() != bf.arity {
                    return Err(CompileErr::Unsupported(
                        "app: wrong arity for direct call (no partial-app in VM yet)",
                    ));
                }
                for a in args {
                    self.compile_expr(a)?;
                }
                self.emit(Op::BuiltinCall(bf, args.len()));
                Ok(())
            }
            Expr::UnOp(UnOp::Neg, x) => {
                self.compile_expr(x)?;
                self.emit(Op::Neg);
                Ok(())
            }
            Expr::UnOp(UnOp::Not, x) => {
                self.compile_expr(x)?;
                self.emit(Op::Not);
                Ok(())
            }
            Expr::BinOp(op, l, r) => {
                // Short-circuit and / or: compile specially.
                match op {
                    B::And => {
                        self.compile_expr(l)?;
                        // duplicate top, jump-if-false to result-is-false branch
                        // simpler: evaluate left, jmp-if-false to end (leave false),
                        //          else pop, evaluate right
                        let jf = self.emit(Op::JumpIfFalse(0)); // placeholder
                        // left was popped by JumpIfFalse; need rhs result on stack
                        self.compile_expr(r)?;
                        let end = self.emit(Op::Jump(0));
                        let false_label = self.here();
                        self.emit(Op::PushBool(false));
                        let after = self.here();
                        self.patch_jump(jf, false_label);
                        self.patch_jump(end, after);
                        return Ok(());
                    }
                    B::Or => {
                        self.compile_expr(l)?;
                        // duplicate-and-test would be cleaner with a Dup op;
                        // emulate: store the left to a scratch slot, test, branch.
                        let tmp = self.alloc_slot("__or_tmp");
                        self.emit(Op::Store(tmp));
                        self.emit(Op::Load(tmp));
                        let jf = self.emit(Op::JumpIfFalse(0));
                        // left is true: push true, jump to end
                        self.emit(Op::PushBool(true));
                        let end = self.emit(Op::Jump(0));
                        let false_label = self.here();
                        self.compile_expr(r)?;
                        let after = self.here();
                        self.patch_jump(jf, false_label);
                        self.patch_jump(end, after);
                        return Ok(());
                    }
                    _ => {}
                }
                self.compile_expr(l)?;
                self.compile_expr(r)?;
                let bcop = match op {
                    B::Add => Op::Add, B::Sub => Op::Sub,
                    B::Mul => Op::Mul, B::Div => Op::Div, B::Mod => Op::Mod,
                    B::Eq => Op::Eq, B::Neq => Op::Neq,
                    B::Lt => Op::Lt, B::Le => Op::Le,
                    B::Gt => Op::Gt, B::Ge => Op::Ge,
                    _ => return Err(CompileErr::Unsupported(
                        "set / in / subset / etc. not in bytecode subset",
                    )),
                };
                self.emit(bcop);
                Ok(())
            }
            Expr::If { cond, then_branch, else_branch } => {
                self.compile_expr(cond)?;
                let jf = self.emit(Op::JumpIfFalse(0)); // placeholder
                self.compile_expr(then_branch)?;
                let jend = self.emit(Op::Jump(0));      // placeholder
                let else_label = self.here();
                self.patch_jump(jf, else_label);
                self.compile_expr(else_branch)?;
                let after = self.here();
                self.patch_jump(jend, after);
                Ok(())
            }
            Expr::Let { name, value, body, .. } => {
                self.compile_expr(value)?;
                self.push_scope();
                let slot = self.alloc_slot(name);
                self.emit(Op::Store(slot));
                self.compile_expr(body)?;
                self.pop_scope();
                Ok(())
            }
            _ => Err(CompileErr::Unsupported(
                "shape not in bytecode subset (set / lambda / app / match / forall)",
            )),
        }
    }
}

/// Compile a top-level function body — `params` are bound to slots 0..n
/// before `body` is compiled.  Returns the bytecode + slot count, or
/// `Unsupported` if the body uses constructs the compiler doesn't handle.
pub fn compile_function<'a>(params: &'a [String], body: &'a Expr)
    -> Result<Bytecode, CompileErr>
{
    let mut c = Compiler::new();
    for p in params {
        c.alloc_slot(p);
    }
    c.compile_expr(body)?;
    c.emit(Op::Ret);
    Ok(Bytecode { ops: c.ops, n_locals: c.max_slots })
}

/// Compile a single closed expression (no parameters) to bytecode.
/// Doesn't have access to globals, so direct calls aren't compiled.
pub fn compile_expr(e: &Expr) -> Result<Bytecode, CompileErr> {
    let mut c = Compiler::new();
    c.compile_expr(e)?;
    c.emit(Op::Ret);
    Ok(Bytecode { ops: c.ops, n_locals: c.max_slots })
}

/// Compile a single closed expression with access to globals.  Allows the
/// compiler to resolve direct builtin function calls (`intToStr 42`) into
/// `BuiltinCall` ops.  Use this from the evaluator where `Globals` is
/// available; pure tests can use `compile_expr` instead.
pub fn compile_expr_with_globals(e: &Expr, globals: &Globals)
    -> Result<Bytecode, CompileErr>
{
    let mut c = Compiler::with_globals(globals);
    c.compile_expr(e)?;
    c.emit(Op::Ret);
    Ok(Bytecode { ops: c.ops, n_locals: c.max_slots })
}

/// Stack-based VM.  Runs a `Bytecode` against initial frame `locals`
/// (which must have length ≥ bc.n_locals; extras are ignored).
pub fn run(bc: &Bytecode, mut locals: Vec<Value>) -> Result<Value, String> {
    // Grow the frame if compiler reserved more slots than provided.
    while locals.len() < bc.n_locals {
        locals.push(Value::Unit);
    }
    let mut stack: Vec<Value> = Vec::with_capacity(32);
    let mut pc: usize = 0;
    macro_rules! pop {
        () => { stack.pop().ok_or_else(|| "VM: stack underflow".to_string())? };
    }
    macro_rules! binop_num {
        ($f_ii:expr, $f_rr:expr, $name:expr) => {{
            let b = pop!();
            let a = pop!();
            let r = match (a, b) {
                (Value::Int(x), Value::Int(y))   => Value::Int($f_ii(x, y)?),
                (Value::Real(x), Value::Real(y)) => Value::Real($f_rr(x, y)),
                (Value::Int(x), Value::Real(y))  => Value::Real($f_rr(x as f64, y)),
                (Value::Real(x), Value::Int(y))  => Value::Real($f_rr(x, y as f64)),
                (a, b) => return Err(format!(
                    "VM: {}: type mismatch ({}, {})", $name, a.type_name(), b.type_name())),
            };
            stack.push(r);
        }};
    }
    macro_rules! binop_cmp {
        ($f_ii:expr, $f_rr:expr, $name:expr) => {{
            let b = pop!();
            let a = pop!();
            let r = match (a, b) {
                (Value::Int(x), Value::Int(y))   => Value::Bool($f_ii(x, y)),
                (Value::Real(x), Value::Real(y)) => Value::Bool($f_rr(x, y)),
                (Value::Int(x), Value::Real(y))  => Value::Bool($f_rr(x as f64, y)),
                (Value::Real(x), Value::Int(y))  => Value::Bool($f_rr(x, y as f64)),
                (a, b) => return Err(format!(
                    "VM: {}: type mismatch ({}, {})", $name, a.type_name(), b.type_name())),
            };
            stack.push(r);
        }};
    }

    while pc < bc.ops.len() {
        let op = bc.ops[pc].clone();
        pc += 1;
        match op {
            Op::PushInt(n)  => stack.push(Value::Int(n)),
            Op::PushReal(r) => stack.push(Value::Real(r)),
            Op::PushBool(b) => stack.push(Value::Bool(b)),
            Op::Pop => { let _ = pop!(); }
            Op::Load(slot) => stack.push(locals[slot].clone()),
            Op::Store(slot) => { locals[slot] = pop!(); }
            Op::Add => binop_num!(
                |x: i64, y: i64| -> Result<i64, String> { Ok(x.wrapping_add(y)) },
                |x: f64, y: f64| x + y,
                "+"
            ),
            Op::Sub => binop_num!(
                |x: i64, y: i64| -> Result<i64, String> { Ok(x.wrapping_sub(y)) },
                |x: f64, y: f64| x - y,
                "-"
            ),
            Op::Mul => binop_num!(
                |x: i64, y: i64| -> Result<i64, String> { Ok(x.wrapping_mul(y)) },
                |x: f64, y: f64| x * y,
                "*"
            ),
            Op::Div => binop_num!(
                |x: i64, y: i64| -> Result<i64, String> {
                    if y == 0 { Err("VM: division by zero".into()) }
                    else { Ok(x / y) }
                },
                |x: f64, y: f64| x / y,
                "/"
            ),
            Op::Mod => {
                let b = pop!();
                let a = pop!();
                match (a, b) {
                    (Value::Int(x), Value::Int(y)) => {
                        if y == 0 { return Err("VM: mod by zero".into()); }
                        stack.push(Value::Int(x.rem_euclid(y)));
                    }
                    (a, b) => return Err(format!(
                        "VM: mod: expected (Int, Int), got ({}, {})",
                        a.type_name(), b.type_name())),
                }
            }
            Op::Neg => match pop!() {
                Value::Int(n) => stack.push(Value::Int(-n)),
                Value::Real(r) => stack.push(Value::Real(-r)),
                v => return Err(format!("VM: neg: expected numeric, got {}", v.type_name())),
            },
            Op::Eq => {
                let b = pop!();
                let a = pop!();
                stack.push(Value::Bool(crate::value::value_eq(&a, &b)));
            }
            Op::Neq => {
                let b = pop!();
                let a = pop!();
                stack.push(Value::Bool(!crate::value::value_eq(&a, &b)));
            }
            Op::Lt => binop_cmp!(|x: i64, y: i64| x <  y, |x: f64, y: f64| x <  y, "<"),
            Op::Le => binop_cmp!(|x: i64, y: i64| x <= y, |x: f64, y: f64| x <= y, "<="),
            Op::Gt => binop_cmp!(|x: i64, y: i64| x >  y, |x: f64, y: f64| x >  y, ">"),
            Op::Ge => binop_cmp!(|x: i64, y: i64| x >= y, |x: f64, y: f64| x >= y, ">="),
            Op::And => {
                let b = pop!();
                let a = pop!();
                match (a, b) {
                    (Value::Bool(x), Value::Bool(y)) => stack.push(Value::Bool(x && y)),
                    _ => return Err("VM: and: expected Bool".into()),
                }
            }
            Op::Or => {
                let b = pop!();
                let a = pop!();
                match (a, b) {
                    (Value::Bool(x), Value::Bool(y)) => stack.push(Value::Bool(x || y)),
                    _ => return Err("VM: or: expected Bool".into()),
                }
            }
            Op::Not => match pop!() {
                Value::Bool(b) => stack.push(Value::Bool(!b)),
                v => return Err(format!("VM: not: expected Bool, got {}", v.type_name())),
            },
            Op::Jump(to) => pc = to,
            Op::JumpIfFalse(to) => match pop!() {
                Value::Bool(false) => pc = to,
                Value::Bool(true) => {}
                v => return Err(format!(
                    "VM: jump-if-false: expected Bool, got {}", v.type_name())),
            },
            // ----- Phase 7 additions ----------------------------------------
            Op::PushStr(s) => stack.push(Value::Str(s)),
            Op::PushUnit => stack.push(Value::Set(std::sync::Arc::new(
                crate::value::SetVal::Enum(vec![])
            ))),
            Op::Tuple(arity) => {
                if stack.len() < arity {
                    return Err(format!(
                        "VM: tuple({}): stack has only {} items", arity, stack.len()
                    ));
                }
                let elems = stack.split_off(stack.len() - arity);
                stack.push(Value::Tuple(elems));
            }
            Op::BuiltinCall(bf, arity) => {
                if stack.len() < arity {
                    return Err(format!(
                        "VM: BuiltinCall({}, {}): stack has only {} items",
                        bf.name, arity, stack.len()
                    ));
                }
                let args: Vec<Value> = stack.split_off(stack.len() - arity);
                let r = (bf.func)(&args)?;
                stack.push(r);
            }
            Op::Ret => return stack.pop().ok_or_else(|| "VM: ret with empty stack".to_string()),
        }
    }
    stack.pop().ok_or_else(|| "VM: fell off the end".to_string())
}

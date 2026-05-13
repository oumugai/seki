//! Lightweight structural-recursion termination check.
//!
//! For each `def f := \p1 .. pk -> body` whose `body` references `f`, we
//! confirm that **every** recursive call to `f` decreases according to one
//! of the following criteria:
//!
//!   * **Per-argument structural smaller**: at least one argument position
//!     is structurally smaller than the corresponding parameter.
//!     Recognised shapes include:
//!     - `pi - C` for an integer literal `C >= 1`
//!     - `pi / C` for an integer literal `C >= 2`
//!     - `e mod pi` (rem_euclid bounds the result by `|pi|`)
//!     - `tail pi`, `snd pi`, `treeLeft pi`, `treeRight pi`
//!     - any chain of `fst`/`snd` accessors on `pi` containing at least one
//!       `snd` — this catches `match`-pattern bindings after desugar
//!   * **Lexicographic order on parameters**: the tuple `(args[π(0)], ...,
//!     args[π(k-1)])` is lex-less than `(p[π(0)], ..., p[π(k-1)])` for some
//!     permutation π of parameter positions.  Lex-less means "weakly less
//!     in a prefix, then strictly less at one position."  This catches
//!     functions like `gcd a b -> gcd b (a mod b)`.
//!
//! `let`-bindings are inlined as a substitution map during traversal so
//! that recursive calls inside `match` arms (which the parser desugars to
//! `let ... in if ... then let ... in ...`) are seen with their effective
//! arguments expressed in terms of the original parameters.
//!
//! The check is intentionally conservative: it reports a *warning* when
//! it can't prove termination — the function is still installed, and the
//! programmer can override the diagnostic by knowing better.
//!
//! Mutual recursion is not considered.  Nested lambdas that re-define `f`
//! shadow the outer binding correctly.

use crate::ast::Expr;
use std::collections::HashMap;

/// Outcome of the termination check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminationStatus {
    /// Every recursive call to `f` was proven to decrease (per-arg or lex).
    Verified,
    /// No recursive call to `f` was found — trivially terminating.
    NonRecursive,
    /// Some recursive call had no provably-smaller argument.  The function
    /// might still terminate (the check is incomplete) but we couldn't
    /// confirm structurally.
    Unknown(String),
}

/// Resolution depth limit for `let`-binding substitution to guarantee the
/// static check terminates even if there are intricate aliasing chains.
const MAX_RESOLVE_DEPTH: usize = 16;

/// A single recursive call site, carrying its argument list AND the
/// `let`-binding context active at that call.
#[derive(Debug, Clone)]
struct CallSite {
    args: Vec<Expr>,
    bindings: HashMap<String, Expr>,
}

/// Inspect `def name := \params -> body` for structural recursion.
pub fn check(name: &str, params: &[String], body: &Expr) -> TerminationStatus {
    let mut calls: Vec<CallSite> = Vec::new();
    let mut env = HashMap::new();
    collect_recursive_calls(body, name, params, &mut env, &mut calls);
    if calls.is_empty() {
        return TerminationStatus::NonRecursive;
    }
    for (i, call) in calls.iter().enumerate() {
        if !call_decreases(&call.args, params, &call.bindings) {
            return TerminationStatus::Unknown(format!(
                "recursive call #{} has no structurally-smaller argument",
                i + 1
            ));
        }
    }
    TerminationStatus::Verified
}

/// Walk `e` collecting every direct recursive call `f a1 .. ak` where the
/// callee is the named global.  Calls under inner lambdas that *shadow*
/// `name` are skipped.  `env` accumulates `let`-bound aliases so the call
/// sites can be analysed in terms of the original parameters.
fn collect_recursive_calls(
    e: &Expr,
    name: &str,
    params: &[String],
    env: &mut HashMap<String, Expr>,
    out: &mut Vec<CallSite>,
) {
    use Expr::*;
    match e {
        App { func, args } => {
            if let Var { name: n, .. } = func.as_ref() {
                if n == name && args.len() == params.len() {
                    out.push(CallSite {
                        args: args.clone(),
                        bindings: env.clone(),
                    });
                }
            }
            collect_recursive_calls(func, name, params, env, out);
            for a in args {
                collect_recursive_calls(a, name, params, env, out);
            }
        }
        Lambda { params: lp, body } => {
            if lp.iter().any(|p| p.name == name) {
                return;
            }
            // Inner lambda parameters shadow any `let`-aliases that share
            // the name, so save+remove them while we traverse.
            let saved: Vec<(String, Option<Expr>)> = lp
                .iter()
                .map(|p| (p.name.clone(), env.remove(&p.name)))
                .collect();
            collect_recursive_calls(body, name, params, env, out);
            for (k, v) in saved {
                if let Some(v) = v {
                    env.insert(k, v);
                } else {
                    env.remove(&k);
                }
            }
        }
        Let { name: ln, value, body, .. } => {
            collect_recursive_calls(value, name, params, env, out);
            if ln == name {
                // Shadow: don't analyse body as containing recursive calls.
                return;
            }
            // Save any prior binding of `ln` before extending.
            let prev = env.remove(ln);
            env.insert(ln.clone(), (**value).clone());
            collect_recursive_calls(body, name, params, env, out);
            env.remove(ln);
            if let Some(v) = prev {
                env.insert(ln.clone(), v);
            }
        }
        If { cond, then_branch, else_branch } => {
            collect_recursive_calls(cond, name, params, env, out);
            collect_recursive_calls(then_branch, name, params, env, out);
            collect_recursive_calls(else_branch, name, params, env, out);
        }
        BinOp(_, l, r) => {
            collect_recursive_calls(l, name, params, env, out);
            collect_recursive_calls(r, name, params, env, out);
        }
        UnOp(_, x) => collect_recursive_calls(x, name, params, env, out),
        SetEnum(xs) | Tuple(xs) | List(xs) => {
            for x in xs {
                collect_recursive_calls(x, name, params, env, out);
            }
        }
        SetComp { domain, pred, .. } => {
            collect_recursive_calls(domain, name, params, env, out);
            collect_recursive_calls(pred, name, params, env, out);
        }
        Arrow(a, b) => {
            collect_recursive_calls(a, name, params, env, out);
            collect_recursive_calls(b, name, params, env, out);
        }
        DepArrow { from, to, .. } => {
            collect_recursive_calls(from, name, params, env, out);
            collect_recursive_calls(to, name, params, env, out);
        }
        Forall { domain, body, .. } | Exists { domain, body, .. } => {
            collect_recursive_calls(domain, name, params, env, out);
            collect_recursive_calls(body, name, params, env, out);
        }
        // leaf nodes
        Int(_) | Real(_) | Bool(_) | Str(_) | Var { .. } => {}
    }
}

/// Resolve a Var through the let-binding environment, with depth bound.
/// Non-Vars are returned unchanged.
fn resolve(e: &Expr, env: &HashMap<String, Expr>) -> Expr {
    let mut cur = e.clone();
    for _ in 0..MAX_RESOLVE_DEPTH {
        if let Expr::Var { name: n, .. } = &cur {
            if let Some(bound) = env.get(n) {
                cur = bound.clone();
                continue;
            }
        }
        break;
    }
    cur
}

/// Per-arg or lex-order check for one recursive call.
fn call_decreases(args: &[Expr], params: &[String], env: &HashMap<String, Expr>) -> bool {
    // Resolve arguments through the let-environment first.
    let resolved: Vec<Expr> = args.iter().map(|a| resolve(a, env)).collect();

    // (1) Per-argument structural smaller.
    for (a, p) in resolved.iter().zip(params.iter()) {
        if is_structurally_smaller(a, p, env) {
            return true;
        }
    }

    // (2) Lexicographic order across parameter permutations.
    if params.len() >= 2 {
        let n = params.len();
        let mut perm: Vec<usize> = (0..n).collect();
        if check_lex_perms(&mut perm, 0, &resolved, params, env) {
            return true;
        }
    }
    false
}

/// Heap's-algorithm-ish permutation enumeration: try every order of
/// parameter positions and check lex-less under it.
fn check_lex_perms(
    perm: &mut Vec<usize>,
    k: usize,
    args: &[Expr],
    params: &[String],
    env: &HashMap<String, Expr>,
) -> bool {
    if k == perm.len() {
        return is_lex_less(perm, args, params, env);
    }
    for i in k..perm.len() {
        perm.swap(k, i);
        if check_lex_perms(perm, k + 1, args, params, env) {
            return true;
        }
        perm.swap(k, i);
    }
    false
}

/// Lex-less under permutation `perm`: the tuple
/// `(args[perm[0]], args[perm[1]], ...)` is strictly less than
/// `(params[perm[0]], params[perm[1]], ...)`.
///
/// Concretely: the first position where they differ must have
/// `args` strictly smaller, and all earlier positions must be equal
/// (textually equal after substitution).
fn is_lex_less(
    perm: &[usize],
    args: &[Expr],
    params: &[String],
    env: &HashMap<String, Expr>,
) -> bool {
    for &i in perm {
        let a = &args[i];
        let p = &params[i];
        if is_structurally_smaller(a, p, env) {
            return true;
        }
        // Equal? Only proceed to the next position if so.
        if !arg_equals_param(a, p) {
            return false;
        }
    }
    false
}

/// Is `e` exactly the parameter variable `param` (no transformation)?
/// Used to walk past unchanged positions in the lex comparison.
fn arg_equals_param(e: &Expr, param: &str) -> bool {
    matches!(e, Expr::Var { name: n, .. } if n == param)
}

/// Is `e` a clearly-smaller form of the variable `param`?
/// `env` is consulted to resolve let-bound aliases that appear inside `e`.
fn is_structurally_smaller(e: &Expr, param: &str, env: &HashMap<String, Expr>) -> bool {
    use Expr::*;
    match e {
        // Resolve through the let-environment if `e` is a bare alias.
        Var { .. } => {
            let r = resolve(e, env);
            if matches!(&r, Var { name: n, .. } if n == param) {
                // Same variable — not smaller.
                return false;
            }
            if matches!(&r, Var { .. }) {
                return false;
            }
            is_structurally_smaller(&r, param, env)
        }
        // Numeric decrement: param - C  where C >= 1
        BinOp(crate::ast::BinOp::Sub, l, r) => {
            let lr = resolve(l, env);
            if let (Var { name: n, .. }, Int(c)) = (&lr, r.as_ref()) {
                if n == param && *c >= 1 {
                    return true;
                }
            }
            false
        }
        // Halving: param / C  where C >= 2
        BinOp(crate::ast::BinOp::Div, l, r) => {
            let lr = resolve(l, env);
            if let (Var { name: n, .. }, Int(c)) = (&lr, r.as_ref()) {
                if n == param && *c >= 2 {
                    return true;
                }
            }
            false
        }
        // Modular reduction: e mod param  (result is bounded by |param|).
        BinOp(crate::ast::BinOp::Mod, _l, r) => {
            let rr = resolve(r, env);
            matches!(&rr, Var { name: n, .. } if n == param)
        }
        // Pair / list / tree destructor or any fst/snd chain on the param.
        App { func, args } => {
            if args.len() == 1 {
                if let Var { name: fname, .. } = func.as_ref() {
                    let fname_str = fname.as_str();
                    let is_fst_or_snd =
                        matches!(fname_str, "fst" | "snd");
                    let is_known_destructor = matches!(
                        fname_str,
                        "tail" | "snd" | "treeLeft" | "treeRight"
                    );
                    let inner = &args[0];
                    let inner_resolved = resolve(inner, env);

                    // (a) named destructors directly on the param (or on
                    //     something already smaller) accept.
                    if is_known_destructor {
                        if matches!(&inner_resolved, Var { name: n, .. } if n == param) {
                            return true;
                        }
                        if is_structurally_smaller(&inner_resolved, param, env) {
                            return true;
                        }
                    }

                    // (b) fst/snd chain on the param.  We accept any chain
                    //     that ends at the param via at least one snd or
                    //     fst step (the resulting expression is part of the
                    //     param's pair-tree, hence structurally smaller).
                    if is_fst_or_snd {
                        if path_to_param(&inner_resolved, param, env) {
                            return true;
                        }
                        if matches!(&inner_resolved, Var { name: n, .. } if n == param) {
                            // Single fst/snd directly on the param: still
                            // structurally smaller.  (e.g. `snd p` is the
                            // tail half; `fst p` is the head/tag — both
                            // sub-components of `p`'s pair structure.)
                            return true;
                        }
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Determine whether `e` is a chain of `fst`/`snd` applications that
/// eventually bottoms out at `Var { name: param, .. }`.  Used to recognise
/// `fst (snd (snd p))` etc as a sub-component of `p`.
fn path_to_param(e: &Expr, param: &str, env: &HashMap<String, Expr>) -> bool {
    use Expr::*;
    let r = resolve(e, env);
    match &r {
        Var { name: n, .. } => n == param,
        App { func, args } if args.len() == 1 => {
            if let Var { name: fname, .. } = func.as_ref() {
                if matches!(fname.as_str(), "fst" | "snd") {
                    return path_to_param(&args[0], param, env);
                }
            }
            false
        }
        _ => false,
    }
}

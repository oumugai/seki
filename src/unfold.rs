//! Unfolding a definition — replacing `f(a, b)` by its body with the
//! arguments substituted in.
//!
//! This is **part of the trusted computing base** (`crate::kernel`), which is
//! why it lives in its own file instead of among `prover.rs`'s tactics.
//!
//! What has to be right here is narrow: every replacement must use the *real*
//! global definition of the name it replaces.  Nothing else about the
//! strategy matters for soundness — unfolding more, less, or in a different
//! order all yield definitionally equal terms, so a bug in
//! [`unfold_nonrec_transitive`]'s choice of what to expand can make a proof
//! *fail*, never make a false one succeed.  Only [`unfold_calls`]'s
//! substitution itself is soundness-critical, and it is a plain structural
//! walk over `Expr` on top of `ast::subst`.

use crate::ast::Expr;
use crate::value::{Globals, Value};
use crate::{SekiError, SekiResult};

/// Unfold the global definition `name` throughout `e`.
///
/// Beta-reduces every direct call to `name`, then transitively expands any
/// *non-recursive* user definition the result calls, so that
/// `by unfold g then algebra` can see through `g x = f x + 1`.  Recursive
/// functions (including mutually recursive ones) stop after one level, which
/// is what keeps the expansion finite.
pub fn unfold_definition(e: &Expr, name: &str, globals: &Globals) -> SekiResult<Expr> {
    let (params, body) = match globals.defs.get(name) {
        Some(Value::Closure { params, body, .. }) => (params.clone(), (**body).clone()),
        Some(other) => {
            return Err(SekiError::Proof(format!(
                "unfold {}: not a function, got {}",
                name,
                other.type_name()
            )))
        }
        None => {
            return Err(SekiError::Proof(format!(
                "unfold {}: no such definition",
                name
            )))
        }
    };
    let one_step = unfold_calls(e, name, &params, &body);
    Ok(unfold_nonrec_transitive(&one_step, globals, &[name]))
}

/// Walk `e` and replace every direct call `name(a1, ..., ak)` with
/// `body[params := args]`.  Only single-level: we don't re-unfold calls
/// produced by the substitution itself (avoids infinite expansion for
/// recursive functions).
pub fn unfold_calls(
    e: &Expr,
    name: &str,
    params: &[String],
    body: &Expr,
) -> Expr {
    use Expr::*;
    match e {
        App { func, args } if matches!(func.as_ref(), Var { name: n, .. } if n == name)
            && args.len() == params.len() =>
        {
            let mut out = body.clone();
            for (p, a) in params.iter().zip(args.iter()) {
                out = crate::ast::subst(&out, p, a);
            }
            out
        }
        App { func, args } => App {
            func: Box::new(unfold_calls(func, name, params, body)),
            args: args
                .iter()
                .map(|a| unfold_calls(a, name, params, body))
                .collect(),
        },
        Lambda { params: lp, body: b } => {
            // The lambda parameter list contains `Param { name, .. }`.  We
            // skip into the body only if none of its params shadow `name`.
            if lp.iter().any(|p| p.name == name) {
                e.clone()
            } else {
                Lambda {
                    params: lp.clone(),
                    body: Box::new(unfold_calls(b, name, params, body)),
                }
            }
        }
        Let { name: ln, ty, value, body: lb, rec } => Let {
            name: ln.clone(),
            ty: ty.clone(),
            value: Box::new(unfold_calls(value, name, params, body)),
            body: if ln == name {
                lb.clone()
            } else {
                Box::new(unfold_calls(lb, name, params, body))
            },
            rec: *rec,
        },
        If { cond, then_branch, else_branch } => If {
            cond: Box::new(unfold_calls(cond, name, params, body)),
            then_branch: Box::new(unfold_calls(then_branch, name, params, body)),
            else_branch: Box::new(unfold_calls(else_branch, name, params, body)),
        },
        BinOp(op, l, r) => BinOp(
            op.clone(),
            Box::new(unfold_calls(l, name, params, body)),
            Box::new(unfold_calls(r, name, params, body)),
        ),
        UnOp(op, x) => UnOp(op.clone(), Box::new(unfold_calls(x, name, params, body))),
        SetEnum(xs) => SetEnum(
            xs.iter()
                .map(|x| unfold_calls(x, name, params, body))
                .collect(),
        ),
        Tuple(xs) => Tuple(
            xs.iter()
                .map(|x| unfold_calls(x, name, params, body))
                .collect(),
        ),
        List(xs) => List(
            xs.iter()
                .map(|x| unfold_calls(x, name, params, body))
                .collect(),
        ),
        SetComp { var, domain, pred } => SetComp {
            var: var.clone(),
            domain: Box::new(unfold_calls(domain, name, params, body)),
            pred: Box::new(unfold_calls(pred, name, params, body)),
        },
        Arrow(a, b) => Arrow(
            Box::new(unfold_calls(a, name, params, body)),
            Box::new(unfold_calls(b, name, params, body)),
        ),
        DepArrow { binder, from, to } => DepArrow {
            binder: binder.clone(),
            from: Box::new(unfold_calls(from, name, params, body)),
            to: Box::new(unfold_calls(to, name, params, body)),
        },
        DepPair { binder, from, to } => DepPair {
            binder: binder.clone(),
            from: Box::new(unfold_calls(from, name, params, body)),
            to: Box::new(unfold_calls(to, name, params, body)),
        },
        Forall { var, domain, body: fb } => Forall {
            var: var.clone(),
            domain: Box::new(unfold_calls(domain, name, params, body)),
            body: Box::new(unfold_calls(fb, name, params, body)),
        },
        Exists { var, domain, body: fb } => Exists {
            var: var.clone(),
            domain: Box::new(unfold_calls(domain, name, params, body)),
            body: Box::new(unfold_calls(fb, name, params, body)),
        },
        Int(_) | Real(_) | Bool(_) | Str(_) | Var { .. } => e.clone(),
    }
}

/// Strip all leading `forall x in T, ...` binders, returning the body.
/// We don't track the bound variable list because in the polynomial encoding
/// every free variable is universally quantified by default.
/// True if `name`'s own definition is recursive — either directly (its body
/// mentions itself) or *mutually*, through a cycle of other user-defined
/// closures (e.g. `isEven` calling `isOdd` calling `isEven`).  Walks the call
/// graph (via `collect_free_var_names` on each visited closure's body) with
/// a `visited` set, so it terminates in O(number of reachable definitions)
/// regardless of cycles.
///
/// This used to only check direct self-reference, leaving mutually-recursive
/// pairs misclassified as "non-recursive" — `unfold_nonrec_transitive` would
/// then try to fully expand them, ping-ponging between the two functions
/// until its iteration cap kicked in, instead of stopping after one
/// meaningful step the way genuine self-recursion does.
pub fn closure_is_recursive(name: &str, globals: &Globals) -> bool {
    let own_body = match globals.defs.get(name) {
        Some(Value::Closure { body, .. }) => body,
        _ => return false,
    };
    let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut stack: Vec<String> = Vec::new();
    let mut seed = std::collections::BTreeSet::new();
    collect_free_var_names(own_body, &mut seed);
    stack.extend(seed);
    while let Some(n) = stack.pop() {
        if n == name {
            return true;
        }
        if !visited.insert(n.clone()) {
            continue;
        }
        if let Some(Value::Closure { body, .. }) = globals.defs.get(&n) {
            let mut names = std::collections::BTreeSet::new();
            collect_free_var_names(body, &mut names);
            stack.extend(names);
        }
    }
    false
}

/// Collect every variable name appearing free in `e` (no scope tracking;
/// over-approximates for binders, which is fine because we only use this
/// to decide which definitions to attempt unfolding).
pub fn collect_free_var_names(e: &Expr, out: &mut std::collections::BTreeSet<String>) {
    use Expr::*;
    match e {
        Var { name, .. } => {
            out.insert(name.clone());
        }
        Lambda { body, .. } => collect_free_var_names(body, out),
        App { func, args } => {
            collect_free_var_names(func, out);
            for a in args {
                collect_free_var_names(a, out);
            }
        }
        Let { value, body, .. } => {
            collect_free_var_names(value, out);
            collect_free_var_names(body, out);
        }
        If { cond, then_branch, else_branch } => {
            collect_free_var_names(cond, out);
            collect_free_var_names(then_branch, out);
            collect_free_var_names(else_branch, out);
        }
        BinOp(_, l, r) => {
            collect_free_var_names(l, out);
            collect_free_var_names(r, out);
        }
        UnOp(_, x) => collect_free_var_names(x, out),
        SetEnum(xs) | Tuple(xs) | List(xs) => {
            for x in xs {
                collect_free_var_names(x, out);
            }
        }
        SetComp { domain, pred, .. } => {
            collect_free_var_names(domain, out);
            collect_free_var_names(pred, out);
        }
        Arrow(a, b) => {
            collect_free_var_names(a, out);
            collect_free_var_names(b, out);
        }
        DepArrow { from, to, .. } | DepPair { from, to, .. } => {
            collect_free_var_names(from, out);
            collect_free_var_names(to, out);
        }
        Forall { domain, body, .. } | Exists { domain, body, .. } => {
            collect_free_var_names(domain, out);
            collect_free_var_names(body, out);
        }
        _ => {}
    }
}

/// Transitively β-unfold every **non-recursive** user-defined function call
/// appearing in `e`.  Continues until a fixed point or until the bound
/// `MAX_UNFOLD_ITERS` is reached.  `seeded` lists the function names
/// already unfolded by the calling tactic (so we don't try them again at
/// the top level — they're handled by `do_unfold` itself).
pub fn unfold_nonrec_transitive(
    e: &Expr,
    globals: &Globals,
    _seeded: &[&str],
) -> Expr {
    const MAX_UNFOLD_ITERS: usize = 32;
    let mut current = e.clone();
    for _ in 0..MAX_UNFOLD_ITERS {
        let mut names = std::collections::BTreeSet::new();
        collect_free_var_names(&current, &mut names);
        let mut changed = false;
        for name in &names {
            if let Some(Value::Closure { params, body, .. }) = globals.defs.get(name) {
                if !closure_is_recursive(name, globals) {
                    let next = unfold_calls(&current, name, params, body);
                    if next != current {
                        current = next;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    current
}

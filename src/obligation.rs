//! Turning a type annotation into a proof obligation.
//!
//! # Why
//!
//! `def f : Int -> Pos := \x -> x * x + 1` claims that `f` lands in
//! `Pos = {x in Int | x > 0}` for *every* integer.  seki checked that claim
//! by applying `f` to a sample of the domain and looking at the results —
//! which is the one hole `docs/spec/06-soundness.md` §6.2 never stopped
//! calling "the biggest remaining" one.  Proof terms did not close it: the
//! theorem side became 95% kernel-checked while the type side stayed a
//! spot check.
//!
//! The claim is an ordinary proposition, though:
//!
//! ```text
//! def f : A -> {y in B | Q y}      ⟹      forall x in A, Q[y := f x]
//! ```
//!
//! So this module reads the annotation and states it, and the caller hands
//! the result to the same prover and the same kernel that theorems go
//! through.  Nothing new has to be trusted: an obligation that is discharged
//! carries a `kernel::Cert` like any other proof, and one that is not falls
//! back on the old sample check and is *recorded as having done so*.
//!
//! What is generated is only the **refinement** part of the annotation.
//! `f x` also has to be in the refinement's base domain (`Int` above), which
//! is a shape question rather than a proof question and stays with the
//! sample check.

use crate::ast::{subst, Expr};
use crate::eval::EvalCtx;
use crate::value::{Env, SetVal, Value};

/// The proposition a type annotation asserts.
#[derive(Debug, Clone)]
pub struct Obligation {
    /// What has to be proved.
    pub goal: Expr,
    /// The refinement the goal came from, for error messages.
    pub refinement: String,
}

/// Build the obligation for `def name : ty`, if the annotation makes a claim
/// worth proving.
///
/// Returns `None` when there is nothing to prove — the annotation has no
/// refinement in return position, or its shape is one this does not read
/// (in which case the sample check remains the only word on it).
pub fn for_definition(
    name: &str,
    ty: &Expr,
    ctx: &EvalCtx,
    env: &Env,
) -> Option<Obligation> {
    let (binders, codomain) = peel_arrows(ty);
    let (pred_var, pred) = refinement_of(&codomain, ctx, env)?;

    // `f x1 x2 ...` — what the annotation says must satisfy the predicate.
    let applied = Expr::App {
        func: Box::new(var(name)),
        args: binders.iter().map(|(n, _)| var(n)).collect(),
    };
    let body = subst(&pred, &pred_var, &applied);

    // A refinement with no arguments (`def v : Pos := 5`) is settled by the
    // ordinary membership check; there is no quantifier to get wrong.
    if binders.is_empty() {
        return None;
    }
    let mut goal = body;
    for (n, domain) in binders.iter().rev() {
        goal = Expr::Forall {
            var: n.clone(),
            domain: Box::new(domain.clone()),
            body: Box::new(goal),
        };
    }
    Some(Obligation {
        goal,
        refinement: format!("{}", codomain),
    })
}

/// Split a curried arrow type into its argument binders and its final
/// codomain.  Each binder gets a name: a dependent arrow already has one,
/// and a plain arrow is given a fresh `__arg<n>`.
fn peel_arrows(ty: &Expr) -> (Vec<(String, Expr)>, Expr) {
    let mut binders = Vec::new();
    let mut cur = ty.clone();
    loop {
        match cur {
            Expr::Arrow(from, to) => {
                binders.push((format!("__arg{}", binders.len() + 1), (*from).clone()));
                cur = *to;
            }
            Expr::DepArrow { binder, from, to } => {
                binders.push((binder, (*from).clone()));
                cur = *to;
            }
            other => return (binders, other),
        }
    }
}

/// Read a codomain as a refinement `{y in B | Q y}`, returning `y` and `Q`.
///
/// The annotation usually names the refinement rather than spelling it out
/// (`Pos`, not `{x in Int | x > 0}`), so a name is evaluated and unwrapped.
fn refinement_of(codomain: &Expr, ctx: &EvalCtx, env: &Env) -> Option<(String, Expr)> {
    if let Expr::SetComp { var, pred, .. } = codomain {
        return Some((var.clone(), (**pred).clone()));
    }
    match ctx.eval(codomain, env) {
        Ok(Value::Set(s)) => match &*s {
            SetVal::Comp { var, pred, .. } => Some((var.clone(), pred.clone())),
            _ => None,
        },
        _ => None,
    }
}

fn var(name: &str) -> Expr {
    Expr::Var { name: name.to_string(), line: 0, col: 0 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::make_prelude;

    fn ty_of(src: &str) -> Expr {
        let decls = crate::parse_program(src).expect("parse");
        match decls.into_iter().next().expect("one decl").decl {
            crate::ast::Decl::Def { ty, .. } => ty.expect("annotated"),
            other => panic!("expected a def, got {:?}", other),
        }
    }

    #[test]
    fn a_refined_return_type_becomes_a_universal_claim() {
        let mut g = make_prelude();
        let decls = crate::parse_program("def Pos := {x in Int | x > 0}").expect("parse");
        if let crate::ast::Decl::Def { name, value, .. } =
            decls.into_iter().next().unwrap().decl
        {
            let ctx = EvalCtx::new(&g);
            let v = ctx.eval(&value, &Env::new()).expect("eval");
            g.defs.insert(name, v);
        }
        let ctx = EvalCtx::new(&g);
        let ty = ty_of("def f : Int -> Pos := \\x -> x");
        let ob = for_definition("f", &ty, &ctx, &Env::new()).expect("an obligation");
        assert_eq!(
            format!("{}", ob.goal),
            "(forall __arg1 in Int, ((f __arg1) > 0))"
        );
    }

    #[test]
    fn several_arguments_become_several_binders() {
        let mut g = make_prelude();
        let decls = crate::parse_program("def Pos := {x in Int | x > 0}").expect("parse");
        if let crate::ast::Decl::Def { name, value, .. } =
            decls.into_iter().next().unwrap().decl
        {
            let ctx = EvalCtx::new(&g);
            let v = ctx.eval(&value, &Env::new()).expect("eval");
            g.defs.insert(name, v);
        }
        let ctx = EvalCtx::new(&g);
        let ty = ty_of("def f : Int -> Int -> Pos := \\x y -> x");
        let ob = for_definition("f", &ty, &ctx, &Env::new()).expect("an obligation");
        let text = format!("{}", ob.goal);
        assert!(text.contains("forall __arg1 in Int"), "{}", text);
        assert!(text.contains("forall __arg2 in Int"), "{}", text);
        assert!(text.contains("(f __arg1 __arg2)"), "{}", text);
    }

    #[test]
    fn an_unrefined_annotation_claims_nothing_to_prove() {
        let g = make_prelude();
        let ctx = EvalCtx::new(&g);
        // No refinement in return position.
        let ty = ty_of("def f : Int -> Int := \\x -> x");
        assert!(for_definition("f", &ty, &ctx, &Env::new()).is_none());
        // A refinement with no arguments is settled by membership alone.
        let ty = ty_of("def v : {x in Int | x > 0} := 5");
        assert!(for_definition("v", &ty, &ctx, &Env::new()).is_none());
    }
}

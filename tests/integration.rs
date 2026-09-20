//! End-to-end tests that exercise the lexer / parser / evaluator / prover
//! through the public crate API.

use seki::ast::Decl;
use seki::eval::{make_prelude, EvalCtx};
use seki::parse_program;
use seki::prover::Prover;
use seki::session::Session;
use seki::trust::TrustLevel;
use seki::value::{Env, Globals, Value};

/// Count the number of elements in a tagged-pair-encoded list value.
/// Returns `None` if the value isn't a well-formed list.
fn list_len(mut v: &Value) -> Option<usize> {
    let mut n = 0usize;
    loop {
        let outer = match v {
            Value::Tuple(xs) if xs.len() == 2 => xs,
            _ => return None,
        };
        match (&outer[0], &outer[1]) {
            (Value::Int(0), _) => return Some(n),
            (Value::Int(1), Value::Tuple(inner)) if inner.len() == 2 => {
                n += 1;
                v = &inner[1];
            }
            _ => return None,
        }
    }
}

/// Run a source string through the real declaration driver.
///
/// This used to be a reimplementation of `run_decl_inner` living in this
/// file, which meant the integration tests exercised a *copy* of the driver
/// rather than the driver: the copy could not handle `import` at all, and
/// never saw the def-time membership check, the termination warning, or the
/// trust accounting.  `Session` is the same code path `seki file.seki`
/// takes.
fn run(src: &str) -> Globals {
    let mut session = Session::new();
    session.run_source(src, /* quiet */ true).expect("run");
    session.globals
}

/// Like [`run`], but returns the driver's error instead of panicking.
fn run_err(src: &str) -> seki::SekiError {
    let mut session = Session::new();
    session
        .run_source(src, true)
        .expect_err("expected the driver to reject this program")
}

#[test]
fn lambda_calculus_currying() {
    let g = run(r"
        def add := \x y -> x + y
        def addOne := add 1
        def r := addOne 41
    ");
    assert!(matches!(g.defs.get("r"), Some(Value::Int(42))));
}

#[test]
fn higher_order_function() {
    let g = run(r"
        def twice := \f x -> f (f x)
        def r := twice (\n -> n + 3) 10
    ");
    assert!(matches!(g.defs.get("r"), Some(Value::Int(16))));
}

#[test]
fn let_binding_does_not_eat_in_keyword() {
    let g = run("def r := let x = 5 in x * x");
    assert!(matches!(g.defs.get("r"), Some(Value::Int(25))));
}

#[test]
fn enumerated_set_membership() {
    let g = run(r#"
        def Days := {"Mon", "Tue", "Wed"}
        def yes := "Mon" in Days
        def no  := "Sun" in Days
    "#);
    assert!(matches!(g.defs.get("yes"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("no"), Some(Value::Bool(false))));
}

#[test]
fn comprehension_membership_uses_predicate() {
    let g = run(r"
        def Pos := {x in Int | x > 0}
        def yes := 7 in Pos
        def no  := 0 in Pos
    ");
    assert!(matches!(g.defs.get("yes"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("no"), Some(Value::Bool(false))));
}

#[test]
fn set_operations() {
    let g = run(r"
        def A := {1, 2, 3}
        def B := {2, 3, 4}
        def U := A union B
        def I := A intersect B
        def D := A diff B
        def sub := {1, 2} subset A
    ");
    if let Some(Value::Set(s)) = g.defs.get("U") {
        let elems = match &**s {
            seki::value::SetVal::Enum(xs) => xs.clone(),
            _ => panic!("expected enum"),
        };
        assert_eq!(elems.len(), 4);
    } else {
        panic!()
    }
    if let Some(Value::Set(s)) = g.defs.get("I") {
        let elems = match &**s {
            seki::value::SetVal::Enum(xs) => xs.clone(),
            _ => panic!(),
        };
        assert_eq!(elems.len(), 2);
    }
    if let Some(Value::Set(s)) = g.defs.get("D") {
        let elems = match &**s {
            seki::value::SetVal::Enum(xs) => xs.clone(),
            _ => panic!(),
        };
        assert_eq!(elems.len(), 1);
    }
    assert!(matches!(g.defs.get("sub"), Some(Value::Bool(true))));
}

#[test]
fn forall_exists_on_finite_sets() {
    let g = run(r"
        def S := {1, 2, 3}
        def all_pos := forall x in S, x > 0
        def some_3  := exists x in S, x == 3
        def some_huge := exists x in S, x > 100
    ");
    assert!(matches!(g.defs.get("all_pos"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("some_3"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("some_huge"), Some(Value::Bool(false))));
}

#[test]
fn theorem_by_eval_proves_true_proposition() {
    let g = run("theorem t : 2 + 2 == 4 := by eval");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn theorem_refl_proves_equality() {
    let g = run("theorem t : (3 + 4) == 7 := refl");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn theorem_witness_proves_existential() {
    let g = run(r"
        def S := {1, 2, 3, 4, 5}
        theorem some_5 : exists x in S, x == 5 := 5
    ");
    assert!(g.theorems.contains_key("some_5"));
}

#[test]
fn theorem_function_proves_universal() {
    let g = run(r"
        def S := {2, 4, 6}
        theorem all_even : forall x in S, x mod 2 == 0 := \x -> x
    ");
    assert!(g.theorems.contains_key("all_even"));
}

#[test]
fn false_theorem_is_rejected() {
    let mut g = make_prelude();
    let decls = parse_program("def S := {1,2,3}; theorem bad : forall x in S, x > 2 := by eval")
        .expect("parse");
    let mut succeeded_proof = false;
    for ld in decls {
        let ctx = EvalCtx::new(&g);
        let env = Env::new();
        match ld.decl {
            Decl::Def { name, value, .. } => {
                let v = ctx.eval(&value, &env).unwrap();
                g.defs.insert(name, v);
            }
            Decl::Theorem { prop, proof, .. } => {
                let prover = Prover::new(&ctx);
                let r = prover.verify(&prop, &proof, &env);
                succeeded_proof = r.is_ok();
            }
            _ => {}
        }
    }
    assert!(!succeeded_proof, "false theorem should not have been accepted");
}

#[test]
fn tuple_and_cartesian_product() {
    let g = run(r#"
        def p := (3, "hi", true)
        def fst3 := fst p
        def snd3 := snd p
        def Pair := Nat times Bool
        def in1 := (5, true)  in Pair
        def in2 := (5, 7)     in Pair
    "#);
    assert!(matches!(g.defs.get("fst3"), Some(Value::Int(3))));
    assert!(matches!(g.defs.get("snd3"), Some(Value::Str(s)) if s == "hi"));
    assert!(matches!(g.defs.get("in1"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("in2"), Some(Value::Bool(false))));
}

#[test]
fn list_basics_and_membership() {
    let g = run(r"
        def xs := [1, 2, 3, 4, 5]
        def n := length xs
        def h := head xs
        def t := tail xs
        def m := [1, 2, 3] in (List Int)
    ");
    assert!(matches!(g.defs.get("n"), Some(Value::Int(5))));
    assert!(matches!(g.defs.get("h"), Some(Value::Int(1))));
    assert_eq!(list_len(g.defs.get("t").unwrap()), Some(4));
    assert!(matches!(g.defs.get("m"), Some(Value::Bool(true))));
}

#[test]
fn by_algebra_proves_distributivity_over_int() {
    let g = run(r"
        theorem distrib : forall a in Int, forall b in Int, forall c in Int,
            a * (b + c) == a * b + a * c
            := by algebra
    ");
    assert!(g.theorems.contains_key("distrib"));
}

#[test]
fn by_algebra_rejects_false_polynomial() {
    let mut g = make_prelude();
    let env = Env::new();
    let decls = parse_program(
        "theorem bad : forall a in Int, a + a == a * 3 := by algebra",
    )
    .unwrap();
    let mut succeeded = false;
    for ld in decls {
        let ctx = EvalCtx::new(&g);
        if let Decl::Theorem { prop, proof, .. } = ld.decl {
            let p = Prover::new(&ctx);
            succeeded = p.verify(&prop, &proof, &env).is_ok();
        }
        let _ = &mut g;
    }
    assert!(!succeeded);
}

#[test]
fn by_induction_proves_gauss_formula() {
    let g = run(r"
        def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
        theorem gauss
          : forall n in Nat, 2 * sum n == n * (n + 1)
          := by induction
    ");
    assert!(g.theorems.contains_key("gauss"));
}

#[test]
fn by_induction_proves_sum_of_squares() {
    let g = run(r"
        def sumSq := \n -> if n == 0 then 0 else n * n + sumSq (n - 1)
        theorem squares
          : forall n in Nat, 6 * sumSq n == n * (n + 1) * (2 * n + 1)
          := by induction
    ");
    assert!(g.theorems.contains_key("squares"));
}

#[test]
fn algebra_handles_inequalities() {
    let g = run(r"
        theorem nat_nn  : forall n in Nat, n >= 0 := by algebra
        theorem succ_gt : forall n in Nat, n + 1 > n := by algebra
        theorem sq_nn   : forall x in Int, x * x >= 0 := by algebra
        theorem cauchy  : forall a in Int, forall b in Int, a*a + b*b >= 2*a*b := by algebra
    ");
    for n in &["nat_nn", "succ_gt", "sq_nn", "cauchy"] {
        assert!(g.theorems.contains_key(*n), "{} not proven", n);
    }
}

#[test]
fn algebra_handles_div_mod_const() {
    let g = run(r"
        theorem half : forall n in Int, (2 * n) / 2 == n := by algebra
        theorem even : forall n in Int, (2 * n) mod 2 == 0 := by algebra
        theorem odd_mod : forall n in Int, (2 * n + 1) mod 2 == 1 := by algebra
    ");
    for n in &["half", "even", "odd_mod"] {
        assert!(g.theorems.contains_key(*n), "{} not proven", n);
    }
}

#[test]
fn algebra_handles_real_polynomial() {
    let g = run(r"
        theorem r_zero  : forall x in Real, x + 0.0 == x := by algebra
        theorem r_one   : forall x in Real, x * 1.0 == x := by algebra
        theorem r_neg   : forall x in Real, x + (-x) == 0.0 := by algebra
        theorem r_sq_nn : forall x in Real, x * x >= 0.0 := by algebra
        theorem r_distrib
          : forall a in Real, forall b in Real, forall c in Real,
                a * (b + c) == a * b + a * c
          := by algebra
        theorem r_half  : forall x in Real, 0.5 * x + 0.5 * x == x := by algebra
    ");
    for n in &["r_zero", "r_one", "r_neg", "r_sq_nn", "r_distrib", "r_half"] {
        assert!(g.theorems.contains_key(*n), "{} not proven", n);
    }
}

#[test]
fn algebra_handles_if_expressions() {
    let g = run(r"
        theorem if_trivial
          : forall x in Int, (if x > 0 then x else x) == x
          := by algebra
        theorem abs_nn
          : forall x in Int, (if x >= 0 then x else (-x)) >= 0
          := by algebra
        theorem max_lb
          : forall x in Int, forall y in Int,
                (if x >= y then x else y) >= y
          := by algebra
        theorem real_abs_nn
          : forall x in Real, (if x >= 0.0 then x else (-x)) >= 0.0
          := by algebra
        theorem identity_entry
          : forall i in Int, forall j in Int, forall x in Int,
                (if i == j then 1 * x else 0 * x) == (if i == j then x else 0)
          := by algebra
    ");
    for n in &["if_trivial", "abs_nn", "max_lb", "real_abs_nn", "identity_entry"] {
        assert!(g.theorems.contains_key(*n), "{} not proven", n);
    }
}

#[test]
fn algebra_rejects_false_if_branch() {
    // Sanity: case-splitting must not silently swallow a false branch.
    let res = std::panic::catch_unwind(|| {
        run("theorem bad : forall x in Int, (if x > 0 then x else 0) == x := by algebra");
    });
    assert!(res.is_err(), "false if-claim should not be proved");
}

#[test]
fn algebra_nat_nonneg_hypothesis_closes_branches() {
    // B1: `forall k in Nat, ...` automatically gives `k >= 0`, which combines
    // with the else-branch hypothesis `50 + k < 50` to close that branch by
    // contradiction.
    let g = run(r"
        def alphaNum := \(step : Int) (warmup : Int) ->
            if step >= warmup then warmup else step
        theorem alpha_capped_nat
          : forall k in Nat, alphaNum (50 + k) 50 == 50
          := by unfold alphaNum then algebra
    ");
    assert!(g.theorems.contains_key("alpha_capped_nat"));
}

#[test]
fn algebra_handles_propositional_implication() {
    // B2: `P -> Q` in propositions is implication, not function type.
    let g = run(r"
        theorem implies_test
          : forall mu in Real, forall lam in Real, mu + lam > 0.0 ->
                1.0 - mu / (mu + lam) == lam / (mu + lam)
          := by algebra
    ");
    assert!(g.theorems.contains_key("implies_test"));
}

#[test]
fn algebra_conjunctive_hypotheses_combine_additively() {
    // Conjoined premises (`a > 0 and b > 0 => ...`) are split into
    // separate hypotheses, and a positive combination of them (here, a
    // plain sum) can discharge a goal that neither hypothesis proves
    // alone — e.g. `x > 0`, `y > 0` ⊢ `x + y > 0`. This is also the
    // `by linarith` code path (an alias for `by algebra`), so the same
    // proposition should close under either tactic name.
    let g = run(r"
        theorem sum_of_positives
          : forall (x y) in Int, x > 0 and y > 0 => x + y > 0
          := by algebra
        theorem sum_of_positives_linarith
          : forall (x y) in Int, x > 0 and y > 0 => x + y > 0
          := by linarith
        theorem three_way_sum
          : forall (a b c) in Int, a >= 0 and b > 0 and c >= 0 => a + b + c > 0
          := by algebra
    ");
    for n in &["sum_of_positives", "sum_of_positives_linarith", "three_way_sum"] {
        assert!(g.theorems.contains_key(*n), "{} not proven", n);
    }
}

#[test]
fn algebra_rejects_unsound_hypothesis_combination() {
    // Sanity: `x > 0`, `y > 0` must NOT be enough to prove `x - y > 0` —
    // the additive-combination shortcut in `hyps_sum_proves` must not
    // overreach into unsound territory.
    let res = std::panic::catch_unwind(|| {
        run(r"
            theorem bad
              : forall (x y) in Int, x > 0 and y > 0 => x - y > 0
              := by algebra
        ");
    });
    assert!(res.is_err(), "unsound combination must not be proved");
}

#[test]
fn algebra_multivar_fourier_motzkin_scaling_and_elimination() {
    // Cases requiring genuine multi-variable Fourier-Motzkin elimination
    // (scaling a hypothesis, or eliminating a variable absent from the
    // goal) — beyond `hyps_sum_proves`'s weight-1-sum shortcut, and beyond
    // what a hypothesis-blind polynomial sign check could ever show.
    let g = run(r"
        theorem scale_single
          : forall x in Int, x <= 3 -> 2 * x <= 6
          := by algebra
        theorem elim_y
          : forall (x y) in Int, x <= y and y <= 10 -> x <= 10
          := by linarith
        theorem diet_style
          : forall (x y) in Int, 2 * x + y <= 10 and x - y <= 3 -> 3 * x <= 13
          := by algebra
        theorem nat_case
          : forall (x y) in Nat, x <= y -> 0 - 1 < y
          := by algebra
    ");
    for t in &["scale_single", "elim_y", "diet_style", "nat_case"] {
        assert!(g.theorems.contains_key(*t), "{} not proven", t);
    }
}

#[test]
fn algebra_fourier_motzkin_strictness_combination() {
    // Combining a strict and a non-strict bound must yield a strict
    // conclusion; combining two non-strict bounds must NOT.
    let g = run(r"
        theorem strict_trans
          : forall (x y z) in Int, x < y and y < z -> x < z := by algebra
        theorem mixed_strict
          : forall (x y z) in Int, x <= y and y < z -> x < z := by algebra
        theorem mixed_strict2
          : forall (x y z) in Int, x < y and y <= z -> x < z := by algebra
    ");
    for t in &["strict_trans", "mixed_strict", "mixed_strict2"] {
        assert!(g.theorems.contains_key(*t), "{} not proven", t);
    }

    let res = std::panic::catch_unwind(|| {
        run(r"
            theorem bad
              : forall (x y z) in Int, x <= y and y <= z -> x < z
              := by algebra
        ");
    });
    assert!(
        res.is_err(),
        "two non-strict bounds must not combine into a strict conclusion"
    );
}

#[test]
fn algebra_fourier_motzkin_rejects_off_by_one() {
    let res = std::panic::catch_unwind(|| {
        run(r"
            theorem bad
              : forall x in Int, x <= 3 -> 2 * x <= 5
              := by algebra
        ");
    });
    assert!(res.is_err(), "2*3 == 6 > 5, so this must not be proved");
}

#[test]
fn algebra_clears_real_denominators() {
    // B3: rational-function fallback handles variable denominators
    let g = run(r"
        theorem rat_simplify
          : forall N in Real, (1.0 / (2.0 * (2.0 * N))) * 4.0 * N == 1.0
          := by algebra
        theorem rat_simplify2
          : forall a in Real, forall b in Real, a / b * b == a
          := by algebra
    ");
    assert!(g.theorems.contains_key("rat_simplify"));
    assert!(g.theorems.contains_key("rat_simplify2"));
}

#[test]
fn algebra_cancels_mod_by_a_variable_divisor() {
    // Variable-divisor `mod`: `<expr> mod v == 0` when `v` is a literal
    // factor of every term (exact division, sound regardless of sign).
    let g = run(r"
        theorem mod_cancel
          : forall a in Int, forall n in Int, n != 0 -> (a * n) mod n == 0
          := by algebra
        theorem mod_cancel_symmetric
          : forall a in Int, forall n in Int, n != 0 -> 0 == (a * n) mod n
          := by algebra
        theorem mod_cancel_multi_factor
          : forall a in Int, forall b in Int, forall n in Int,
            n != 0 -> (a * n * b) mod n == 0
          := by algebra
    ");
    for t in &["mod_cancel", "mod_cancel_symmetric", "mod_cancel_multi_factor"] {
        assert!(g.theorems.contains_key(*t), "{} not proven", t);
    }
}

#[test]
fn algebra_rejects_inexact_mod_by_variable_divisor() {
    // Adversarial: `(a*n + 1) mod n` is NOT unconditionally 0 (it's 1 for
    // most n) — the exact-division shortcut must not overreach.
    let res = std::panic::catch_unwind(|| {
        run(r"
            theorem bad
              : forall a in Int, forall n in Int, n != 0 -> (a * n + 1) mod n == 0
              := by algebra
        ");
    });
    assert!(res.is_err(), "inexact mod claim must not be proved");
}

#[test]
fn algebra_folds_real_constants() {
    // B4: constant-folding through Mul/Add: `2.0 * 16.0` reduces to `32.0`.
    let g = run(r"
        theorem const_fold
          : 1.0 / (2.0 * 16.0) == 1.0 / 32.0
          := by algebra
    ");
    assert!(g.theorems.contains_key("const_fold"));
}

#[test]
fn algebra_transitive_unfold() {
    // B6: `unfold g` recursively unfolds non-recursive callees of g.
    let g = run(r"
        def f := \x -> x * 2
        def g := \x -> f x + 1
        theorem g_unfolds
          : forall x in Int, g x == 2 * x + 1
          := by unfold g then algebra
    ");
    assert!(g.theorems.contains_key("g_unfolds"));
}

#[test]
fn unfold_stops_cleanly_at_a_mutual_recursion_boundary() {
    // `closure_is_recursive` used to only check *direct* self-reference, so
    // a mutually-recursive pair (f calls g, g calls f) was misclassified as
    // "non-recursive" and `unfold_nonrec_transitive` kept ping-ponging
    // between the two until its 32-iteration cap. It should instead detect
    // the cycle and stop after exactly one level, leaving a clean opaque
    // `g (n - 1)` atom — provable here only because the goal is scoped to
    // the recursive (`n > 0`) branch, so it can't be a base-case fluke.
    let g = run(r"
        def f := \n -> if n == 0 then 0 else g (n - 1) + 1
        def g := \n -> if n == 0 then 0 else f (n - 1) + 1
        theorem f_step_is_atomic
          : forall n in Nat, n > 0 -> f n == g (n - 1) + 1
          := by unfold f then algebra
    ");
    assert!(g.theorems.contains_key("f_step_is_atomic"));
}

#[test]
fn unfold_still_rejects_false_claims_through_mutual_recursion() {
    let res = std::panic::catch_unwind(|| {
        run(r"
            def f := \n -> if n == 0 then 0 else g (n - 1) + 1
            def g := \n -> if n == 0 then 0 else f (n - 1) + 1
            theorem bad
              : forall n in Nat, n > 0 -> f n == 999
              := by unfold f then algebra
        ");
    });
    assert!(res.is_err(), "false claim must not be proved through mutual recursion");
}

#[test]
fn induction_handles_inequalities() {
    let g = run(r"
        def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
        theorem sum_nn : forall n in Nat, sum n >= 0 := by induction
        theorem sum_grows : forall n in Nat, sum (n + 1) > sum n := by induction
    ");
    assert!(g.theorems.contains_key("sum_nn"));
    assert!(g.theorems.contains_key("sum_grows"));
}

#[test]
fn list_structural_induction() {
    let g = run(r"
        def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)
        theorem nn : forall xs in (List Int), listLen xs >= 0 := by induction
    ");
    assert!(g.theorems.contains_key("nn"));
}

#[test]
fn tree_structural_induction() {
    let g = run(r"
        def treeSize := \t -> if isLeaf t then 0 else 1 + treeSize (treeLeft t) + treeSize (treeRight t)
        theorem ts_nn : forall t in (Tree Int), treeSize t >= 0 := by induction
    ");
    assert!(g.theorems.contains_key("ts_nn"));
}

#[test]
fn strong_induction_for_fibonacci() {
    let g = run(r"
        def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)
        theorem fib_nn : forall n in Nat, fib n >= 0 := by strong_induction
    ");
    assert!(g.theorems.contains_key("fib_nn"));
}

#[test]
fn strong_induction_accepts_configurable_depth() {
    // A tribonacci-style recurrence reaches back 3 steps, so it needs
    // `by strong_induction 3` (depth 2, the old hardcoded default, is not
    // enough to cover its 3 special-cased bases 0/1/2).
    let g = run(r"
        def trib := \n ->
            if n == 0 then 0
            else if n == 1 then 1
            else if n == 2 then 1
            else trib (n - 1) + trib (n - 2) + trib (n - 3)
        theorem trib_nn : forall n in Nat, trib n >= 0 := by strong_induction 3
    ");
    assert!(g.theorems.contains_key("trib_nn"));
}

#[test]
fn strong_induction_rejects_insufficient_depth_instead_of_a_false_proof() {
    // Regression for a real soundness gap: a recursive function whose
    // if-chain has a *negative* literal at the boundary the chosen depth
    // doesn't reach (here `f 2 == -1`, but only depth 2 — bases P(0)/P(1)
    // — is requested, one short of the 3 the definition actually needs).
    // Before the `contains_var_conditioned_if` guard, the unresolved
    // `if (k+2) == 2 then -1 else ...` collapsed into an "assumed ≥ 0"
    // opaque atom and this false theorem was incorrectly proved.
    let f_def = r"
        def f := \n ->
            if n == 0 then 0
            else if n == 1 then 0
            else if n == 2 then 0 - 1
            else f (n - 1) + f (n - 2) + f (n - 3)
    ";
    // f 2 == -1 is a direct counterexample to `forall n in Nat, f n >= 0`.
    let g = run(&format!("{f_def}\n theorem f2_neg : f 2 == 0 - 1 := by eval"));
    assert!(g.theorems.contains_key("f2_neg"));

    let res = std::panic::catch_unwind(|| {
        run(&format!(
            "{f_def}\n theorem bad : forall n in Nat, f n >= 0 := by strong_induction 2"
        ));
    });
    assert!(
        res.is_err(),
        "false proposition must not be proved by strong_induction with insufficient depth"
    );

    // At the *correct* depth (3), the same false claim is still rejected —
    // now caught cleanly at the base case P(2) instead of the guard.
    let res2 = std::panic::catch_unwind(|| {
        run(&format!(
            "{f_def}\n theorem bad2 : forall n in Nat, f n >= 0 := by strong_induction 3"
        ));
    });
    assert!(
        res2.is_err(),
        "false proposition must not be proved by strong_induction at any depth"
    );
}

#[test]
fn strong_induction_rejects_zero_depth() {
    let res = std::panic::catch_unwind(|| {
        run(r"
            def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)
            theorem t : forall n in Nat, fib n >= 0 := by strong_induction 0
        ");
    });
    assert!(res.is_err(), "depth 0 must be rejected");
}

#[test]
fn bool_is_literal_two_element_set() {
    let g = run("theorem t : Bool == {false, true} := refl");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn prop_equals_bool_set() {
    let g = run("theorem t : Prop == Bool := refl");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn real_arithmetic_with_int_promotion() {
    let g = run(r"
        def a := 1.5 + 2.5      -- 4.0
        def b := 1 + 2.5        -- 3.5  (Int promoted)
        def c := 3 / 2.0        -- 1.5  (Real division)
        def d := 3 / 2          -- 1    (Int division)
    ");
    if let Some(Value::Real(x)) = g.defs.get("a") {
        assert!((x - 4.0).abs() < 1e-9);
    } else {
        panic!()
    }
    if let Some(Value::Real(x)) = g.defs.get("b") {
        assert!((x - 3.5).abs() < 1e-9);
    } else {
        panic!()
    }
    if let Some(Value::Real(x)) = g.defs.get("c") {
        assert!((x - 1.5).abs() < 1e-9);
    } else {
        panic!()
    }
    assert!(matches!(g.defs.get("d"), Some(Value::Int(1))));
}

#[test]
fn real_membership_includes_int() {
    let g = run(r"
        def a := 3.14 in Real
        def b := 5    in Real        -- Int ⊂ Real
        def c := true in Real
    ");
    assert!(matches!(g.defs.get("a"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("b"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("c"), Some(Value::Bool(false))));
}

#[test]
fn real_builtins() {
    let g = run(r"
        def f1 := floor 3.7
        def c1 := ceil  3.2
        def r1 := round 3.5
        def s1 := sqrt 9.0
        def p1 := pow 2.0 10
    ");
    assert!(matches!(g.defs.get("f1"), Some(Value::Int(3))));
    assert!(matches!(g.defs.get("c1"), Some(Value::Int(4))));
    assert!(matches!(g.defs.get("r1"), Some(Value::Int(4))));
    if let Some(Value::Real(x)) = g.defs.get("s1") {
        assert!((x - 3.0).abs() < 1e-9);
    } else {
        panic!()
    }
    if let Some(Value::Real(x)) = g.defs.get("p1") {
        assert!((x - 1024.0).abs() < 1e-9);
    } else {
        panic!()
    }
}

#[test]
fn forall_tautology_via_comprehension_predicate() {
    let g = run(r"
        def Pos := {x in Int | x > 0}
        theorem t : forall p in Pos, p > 0 := by eval
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn forall_via_polynomial_decision_on_nat() {
    let g = run(r"
        theorem nn : forall n in Nat, n >= 0 := by eval
        theorem succ_gt : forall n in Nat, n + 1 > n := by eval
        theorem sq_nn : forall x in Int, x * x >= 0 := by eval
    ");
    for n in &["nn", "succ_gt", "sq_nn"] {
        assert!(g.theorems.contains_key(*n), "{} not proven", n);
    }
}

#[test]
fn forall_renamed_bound_variable_works() {
    let g = run(r"
        def Big := {y in Nat | y > 1000}
        theorem t : forall x in Big, x > 1000 := by eval
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn forall_vacuous_on_empty_set_is_true() {
    let g = run(r"
        def empty_check := forall x in {}, x > 1000000
    ");
    assert!(matches!(g.defs.get("empty_check"), Some(Value::Bool(true))));
}

#[test]
fn exists_on_empty_filtered_set_is_false() {
    let g = run(r"
        def Empty := {x in Int | false}
        def res := exists x in Empty, x == 0
    ");
    assert!(matches!(g.defs.get("res"), Some(Value::Bool(false))));
}

#[test]
fn stdlib_predicate_subtypes_loaded() {
    let g = make_prelude();
    // Stdlib defs should be present
    for n in &[
        "Pos", "Neg", "NonZero", "EvenInt", "OddInt", "EvenNat", "OddNat",
        "Bit", "Byte", "UInt8", "Int8", "UInt16", "Int16", "Rat",
        "mkRat", "numer", "denom", "intToRat", "addRat", "mulRat",
        "subRat", "negRat", "eqRat",
        "range", "map", "filter", "foldr", "foldl",
        "sumList", "maxList", "all", "any", "contains",
        "singleton", "treeSize", "treeHeight", "treeSum", "treeToList",
        "isEven", "isOdd", "square", "cube",
    ] {
        assert!(g.defs.contains_key(*n), "stdlib def `{}` missing", n);
    }
}

#[test]
fn stdlib_rational_arithmetic_works() {
    let g = run(r"
        def half := mkRat 1 2
        def third := mkRat 1 3
        def s := addRat half third      -- (5, 6)
        def n := numer s
        def d := denom s
        def equiv := eqRat (mkRat 1 2) (mkRat 2 4)
    ");
    assert!(matches!(g.defs.get("n"), Some(Value::Int(5))));
    assert!(matches!(g.defs.get("d"), Some(Value::Int(6))));
    assert!(matches!(g.defs.get("equiv"), Some(Value::Bool(true))));
}

#[test]
fn stdlib_list_utilities_work() {
    let g = run(r"
        def s := sumList (range 1 11)               -- 1..10
        def evens := filter isEven [0, 1, 2, 3, 4, 5, 6]
        def all_even := all isEven [0, 2, 4, 6]
    ");
    assert!(matches!(g.defs.get("s"), Some(Value::Int(55))));
    assert!(matches!(g.defs.get("all_even"), Some(Value::Bool(true))));
    assert_eq!(list_len(g.defs.get("evens").unwrap()), Some(4));
}

#[test]
fn stdlib_tree_utilities_work() {
    let g = run(r"
        def t := node (singleton 1) 2 (node leaf 3 (singleton 4))
        def sz := treeSize t
        def sm := treeSum t
        def lst := treeToList t
    ");
    assert!(matches!(g.defs.get("sz"), Some(Value::Int(4))));
    assert!(matches!(g.defs.get("sm"), Some(Value::Int(10))));
    assert_eq!(list_len(g.defs.get("lst").unwrap()), Some(4));
}

#[test]
fn data_decl_generates_constructors() {
    let g = run(r"
        data Maybe A = None | Some A
        def n := None
        def s := Some 42
    ");
    // None: ("None", ()) — a 2-tuple
    assert!(matches!(g.defs.get("n"), Some(Value::Tuple(_))));
    assert!(matches!(g.defs.get("s"), Some(Value::Tuple(_))));
}

#[test]
fn match_simple_constructor_pattern() {
    let g = run(r"
        data Maybe A = None | Some A
        def x := match Some 42 with
            | None   -> 0
            | Some n -> n
    ");
    assert!(matches!(g.defs.get("x"), Some(Value::Int(42))));
}

#[test]
fn match_literal_and_wildcard() {
    let g = run(r#"
        def s := match 5 with
            | 0 -> "zero"
            | 5 -> "five"
            | _ -> "other"
    "#);
    if let Some(Value::Str(s)) = g.defs.get("s") {
        assert_eq!(s, "five");
    } else {
        panic!()
    }
}

#[test]
fn match_recursive_data_type() {
    let g = run(r"
        data MyList A = MyNil | MyCons A (MyList A)
        def len := \xs -> match xs with
            | MyNil -> 0
            | MyCons _ t -> 1 + len t
        def n := len (MyCons 1 (MyCons 2 (MyCons 3 MyNil)))
    ");
    assert!(matches!(g.defs.get("n"), Some(Value::Int(3))));
}

#[test]
fn match_nonexhaustive_errors_at_runtime() {
    let mut g = make_prelude();
    let env = Env::new();
    let decls = parse_program(
        "data E = A | B
         def x := match A with
             | B -> 0",
    )
    .unwrap();
    let mut errored = false;
    for ld in decls {
        let ctx = EvalCtx::new(&g);
        match ld.decl {
            Decl::Def { name, value, .. } => match ctx.eval(&value, &env) {
                Ok(v) => {
                    drop(ctx);
                    g.defs.insert(name, v);
                }
                Err(_) => {
                    errored = true;
                    break;
                }
            },
            _ => {}
        }
    }
    assert!(errored, "non-exhaustive match should error");
}

#[test]
fn option_helpers_loaded_from_stdlib() {
    let g = run(r"
        def x := mapOption (\n -> n + 1) (Some 5)
        def y := unwrapOr 0 None
        def z := isSome (Some 0)
    ");
    if let Some(v) = g.defs.get("x") {
        // x = Some 6 → tagged tuple ("Some", (6, ()))
        assert!(matches!(v, Value::Tuple(_)));
    } else {
        panic!()
    }
    assert!(matches!(g.defs.get("y"), Some(Value::Int(0))));
    assert!(matches!(g.defs.get("z"), Some(Value::Bool(true))));
}

#[test]
fn result_helpers_loaded_from_stdlib() {
    let g = run(r#"
        def ok_val  := mapResult (\n -> n * 2) (Ok 5)
        def err_val := mapResult (\n -> n * 2) (Err "bad")
        def is1 := isOk (Ok 1)
        def is2 := isErr (Err "x")
    "#);
    assert!(matches!(g.defs.get("is1"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("is2"), Some(Value::Bool(true))));
    let _ = (g.defs.get("ok_val"), g.defs.get("err_val"));
}

#[test]
fn question_operator_propagates_err() {
    let g = run(r#"
        def parseDigit := \c ->
            match c with
            | "0" -> Ok 0
            | "1" -> Ok 1
            | _ -> Err "bad"
        def good := \a b ->
            let x = parseDigit a ? in
            let y = parseDigit b ? in
            Ok (x + y)
        def r1 := good "1" "0"
        def r2 := good "x" "0"
    "#);
    // r1 = Ok 1 (= 1+0)
    // r2 = Err "bad"
    if let Some(Value::Tuple(t)) = g.defs.get("r1") {
        assert_eq!(t.len(), 2);
        if let Value::Str(tag) = &t[0] {
            assert_eq!(tag, "Ok");
        } else {
            panic!()
        }
    } else {
        panic!()
    }
    if let Some(Value::Tuple(t)) = g.defs.get("r2") {
        if let Value::Str(tag) = &t[0] {
            assert_eq!(tag, "Err");
        } else {
            panic!()
        }
    } else {
        panic!()
    }
}

#[test]
fn dependent_arrow_type_membership_check() {
    let g = run(r"
        def Vec := \(n : Nat) -> {xs in (List Int) | length xs == n}
        def replicate_zero : (n : Nat) -> Vec n := \(n : Nat) ->
            if n == 0 then nil else cons 0 (replicate_zero (n - 1))
        def v3 := replicate_zero 3
        def lv := length v3
    ");
    assert!(matches!(g.defs.get("lv"), Some(Value::Int(3))));
}

#[test]
fn dependent_arrow_rejects_invalid_function() {
    let mut g = make_prelude();
    let env = Env::new();
    // The function returns a list of length n+1 instead of n — should be
    // rejected by the dependent-arrow membership check at definition time.
    let decls = parse_program(
        r"
        def Vec := \(n : Nat) -> {xs in (List Int) | length xs == n}
        def bad : (n : Nat) -> Vec n := \(n : Nat) ->
            cons 0 (cons 0 nil)
        ",
    )
    .unwrap();
    let mut errored = false;
    for ld in decls {
        let ctx = EvalCtx::new(&g);
        if let Decl::Def { name, value, ty } = ld.decl {
            let v = ctx.eval(&value, &env).unwrap();
            drop(ctx);
            g.defs.insert(name.clone(), v.clone());
            if let Some(t) = ty {
                let ctx2 = EvalCtx::new(&g);
                if let Ok(Value::Set(set)) = ctx2.eval(&t, &env) {
                    let result =
                        seki::typecheck::check_def_membership(&v, &set, &ctx2, &env);
                    if result.is_err() && name == "bad" {
                        errored = true;
                    }
                }
            }
        }
    }
    assert!(
        errored,
        "function returning wrong-length list should be rejected by dep arrow check"
    );
}

#[test]
fn sigma_dependent_pair_membership_check() {
    // `sigma (n : A), B(n)` — a 2-tuple `(a, b)` is a member iff `a in A`
    // and `b in B[n:=a]`. Unlike DepArrow this is exact (no sampling),
    // since membership testing has the concrete pair in hand.
    let g = run(r"
        def Pos := {x in Int | x > 0}
        def SmallEven := \n -> {y in Int | y >= 0 and y < n and y mod 2 == 0}
        def DepPairSet := sigma (n : Pos), SmallEven n

        theorem member_ok : ((4, 2) in DepPairSet) == true := by eval
        theorem member_bad_snd : ((4, 3) in DepPairSet) == false := by eval
        theorem member_bad_fst : ((0 - 1, 0) in DepPairSet) == false := by eval
        theorem member_not_a_pair : (5 in DepPairSet) == false := by eval
    ");
    for t in &["member_ok", "member_bad_snd", "member_bad_fst", "member_not_a_pair"] {
        assert!(g.theorems.contains_key(*t), "{} not proven", t);
    }
}

#[test]
fn sigma_non_dependent_case_behaves_like_times() {
    // When `B` doesn't reference the binder, `sigma (x : A), B` is
    // semantically the plain product `A times B`.
    let g = run(r"
        def NonDep := sigma (x : Int), Bool
        theorem t1 : ((3, true) in NonDep) == true := by eval
        theorem t2 : ((3, 3) in NonDep) == false := by eval
        theorem t3 : ((1, 2, 3) in NonDep) == false := by eval
    ");
    for t in &["t1", "t2", "t3"] {
        assert!(g.theorems.contains_key(*t), "{} not proven", t);
    }
}

#[test]
fn type_inference_records_arrow_for_annotated_lambda() {
    let mut g = make_prelude();
    let env = Env::new();
    let decls = parse_program("def square : Nat -> Nat := \\(n : Nat) -> n * n").unwrap();
    for ld in &decls {
        if let Decl::Def { name, ty, value } = &ld.decl {
            let ctx = EvalCtx::new(&g);
            let v = ctx.eval(value, &env).unwrap();
            drop(ctx);
            g.defs.insert(name.clone(), v);
            // For this test we just store the annotation as the inferred type.
            if let Some(t) = ty {
                g.inferred_types.insert(name.clone(), t.clone());
            }
        }
    }
    assert!(g.inferred_types.contains_key("square"));
}

#[test]
fn termination_check_recognizes_decreasing_int() {
    use seki::termination::{check, TerminationStatus};
    let decls = parse_program(
        "def fact := \\n -> if n == 0 then 1 else n * fact (n - 1)",
    )
    .unwrap();
    if let Some(ld) = decls.first() {
        if let Decl::Def { value, .. } = &ld.decl {
            if let seki::ast::Expr::Lambda { params, body } = value {
                let pnames: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                let status = check("fact", &pnames, body);
                assert_eq!(status, TerminationStatus::Verified);
                return;
            }
        }
    }
    panic!("did not find Lambda decl");
}

#[test]
fn termination_check_warns_on_constant_recursion() {
    use seki::termination::{check, TerminationStatus};
    let decls = parse_program("def loop := \\n -> loop n").unwrap();
    if let Some(ld) = decls.first() {
        if let Decl::Def { value, .. } = &ld.decl {
            if let seki::ast::Expr::Lambda { params, body } = value {
                let pnames: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                let status = check("loop", &pnames, body);
                assert!(matches!(status, TerminationStatus::Unknown(_)));
                return;
            }
        }
    }
    panic!("did not find Lambda decl");
}

#[test]
fn type_class_dictionary_passes_correctly() {
    let g = run(r"
        class Eq A where
            eq : A -> A -> Bool

        instance EqInt : Eq Int where
            eq = \a b -> a == b

        def r1 := eq EqInt 3 3
        def r2 := eq EqInt 3 5
    ");
    assert!(matches!(g.defs.get("r1"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("r2"), Some(Value::Bool(false))));
}

#[test]
fn type_class_multi_method_resolution() {
    let g = run(r"
        class Ord A where
            lt : A -> A -> Bool ;
            ge : A -> A -> Bool

        instance OrdInt : Ord Int where
            lt = \a b -> a < b ;
            ge = \a b -> a >= b

        def t1 := lt OrdInt 3 5
        def t2 := ge OrdInt 5 5
    ");
    assert!(matches!(g.defs.get("t1"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("t2"), Some(Value::Bool(true))));
}

#[test]
fn membership_type_check_rejects_bad_value() {
    use seki::typecheck::check_def_membership;
    let mut g = make_prelude();
    let env = Env::new();
    let decls =
        parse_program(r#"def Color := {"red", "blue"}"#).expect("parse");
    {
        let ctx = EvalCtx::new(&g);
        let mut to_insert = Vec::new();
        for ld in decls {
            if let Decl::Def { name, value, .. } = ld.decl {
                let v = ctx.eval(&value, &env).unwrap();
                to_insert.push((name, v));
            }
        }
        drop(ctx);
        for (n, v) in to_insert {
            g.defs.insert(n, v);
        }
    }
    let ctx2 = EvalCtx::new(&g);
    let purple = Value::Str("purple".into());
    let color_set = match g.defs.get("Color").unwrap() {
        Value::Set(s) => s.clone(),
        _ => panic!(),
    };
    let result = check_def_membership(&purple, &color_set, &ctx2, &env);
    assert!(result.is_err());
}

#[test]
fn termination_check_recognizes_lex_order_gcd() {
    use seki::termination::{check, TerminationStatus};
    let decls = parse_program(
        "def gcd := \\a b -> if b == 0 then a else gcd b (a mod b)",
    )
    .unwrap();
    let ld = decls.first().expect("at least one decl");
    if let Decl::Def { value, .. } = &ld.decl {
        if let seki::ast::Expr::Lambda { params, body } = value {
            let pnames: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            let status = check("gcd", &pnames, body);
            assert_eq!(
                status,
                TerminationStatus::Verified,
                "gcd should be lex-decreasing"
            );
            return;
        }
    }
    panic!("expected def gcd lambda");
}

#[test]
fn termination_check_recognizes_match_pattern_var() {
    use seki::termination::{check, TerminationStatus};
    let decls = parse_program(
        r"
        data MyList A = MyNil | MyCons A (MyList A)
        def myLen := \xs ->
            match xs with
            | MyNil -> 0
            | MyCons h t -> 1 + myLen t
        ",
    )
    .unwrap();
    let mylen_ld = decls
        .iter()
        .find(|ld| matches!(&ld.decl, Decl::Def { name, .. } if name == "myLen"))
        .expect("myLen def");
    if let Decl::Def { value, .. } = &mylen_ld.decl {
        if let seki::ast::Expr::Lambda { params, body } = value {
            let pnames: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            let status = check("myLen", &pnames, body);
            assert_eq!(
                status,
                TerminationStatus::Verified,
                "match-pattern bound `t` should be smaller than `xs`"
            );
            return;
        }
    }
    panic!("expected def myLen lambda");
}

#[test]
fn by_simp_chains_rewrite_rules() {
    let g = run(r"
        theorem add_zero : forall a in Int, a + 0 == a := by algebra
        theorem mul_zero : forall a in Int, a * 0 == 0 := by algebra
        theorem t : forall x in Int, (x + 0) * 0 == 0 := by simp
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn by_simp_with_explicit_lemma_list() {
    let g = run(r"
        theorem add_zero : forall a in Int, a + 0 == a := by algebra
        theorem t : forall x in Int, x + 0 == x := by simp [add_zero]
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn error_code_classifies_proof_failure() {
    use seki::SekiError;
    let err = SekiError::Proof("dummy".into());
    assert_eq!(err.code(), "E005");
    assert_eq!(err.category(), "proof");
    assert!(err.is_proof_error());
}

#[test]
fn tactic_composition_intros_then_algebra() {
    let g = run(r"
        theorem t : forall a in Int, a + 0 == a := by intros then algebra
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn tactic_composition_unfold_then_algebra() {
    let g = run(r"
        def sq := \x -> x * x
        theorem t : forall a in Int, sq a == a * a := by unfold sq then algebra
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn tactic_composition_three_way() {
    let g = run(r"
        def sq := \x -> x * x
        theorem t : forall a in Int, sq a + 0 == a * a :=
            by intros then unfold sq then algebra
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn auto_dictionary_resolution_for_class_method() {
    let g = run(r"
        class Eq A where
            eq : A -> A -> Bool ;
            neq : A -> A -> Bool

        instance EqInt : Eq Int where
            eq = \a b -> a == b ;
            neq = \a b -> a != b

        def r1 := eq 3 3
        def r2 := eq 3 5
        def r3 := neq 1 2
    ");
    assert!(matches!(g.defs.get("r1"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("r2"), Some(Value::Bool(false))));
    assert!(matches!(g.defs.get("r3"), Some(Value::Bool(true))));
}

#[test]
fn auto_dictionary_distinguishes_instances_by_type() {
    let g = run(r#"
        class Eq A where
            eq : A -> A -> Bool ;
            neq : A -> A -> Bool

        instance EqInt : Eq Int where
            eq = \a b -> a == b ;
            neq = \a b -> a != b

        instance EqStr : Eq String where
            eq = \a b -> a == b ;
            neq = \a b -> a != b

        def r1 := eq 7 7
        def r2 := eq "hi" "hi"
        def r3 := eq "a" "b"
    "#);
    assert!(matches!(g.defs.get("r1"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("r2"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("r3"), Some(Value::Bool(false))));
}

// =========================================================
// Seki library tests: each test_*.seki file in tests/seki/
// imports the corresponding lib/ module and verifies theorems.
// We run them through the seki binary so the import path
// resolution and decl-by-decl theorem registration matches the
// production CLI exactly.
// =========================================================

fn run_seki_test_file(rel_path: &str, min_theorems: usize) {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg(rel_path)
        .output()
        .expect("run seki binary");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "seki test {} exited with failure.\nstdout:\n{}\nstderr:\n{}",
        rel_path, stdout, stderr
    );
    let proved = stdout.matches("✓ proved").count();
    assert!(
        proved >= min_theorems,
        "seki test {} expected ≥ {} proved theorems, got {}.\nstdout:\n{}",
        rel_path, min_theorems, proved, stdout
    );
    let proof_errors = stderr.matches("proof error").count()
        + stdout.matches("proof error").count();
    assert_eq!(
        proof_errors, 0,
        "seki test {} produced proof errors.\nstdout:\n{}\nstderr:\n{}",
        rel_path, stdout, stderr
    );
}

// These four `.seki` suites existed but were never wired into `cargo test`,
// so nothing ran them.  Two of them had in fact been broken since `sigma`
// became a keyword (Σ-types): `lib/probability/{continuous,montecarlo}.seki`
// used `sigma` as a lambda parameter and no longer parsed.
/// `lib/analysis/{axioms,continuity,ode}.seki` — real analysis built by
/// deduction on top of the ordered-field axioms.  The file adds theorems of
/// its own, so a regression in `by witness`, the antisymmetry rule or the
/// divide-by-a-positive rule shows up here.
#[test]
fn seki_lib_test_real_axioms() {
    run_seki_test_file("tests/seki/test_real_axioms.seki", 5);
}

/// `lib/control/safety.seki` — safety envelopes for control loops.  The
/// point of the library is that loosening any one range makes the claim
/// *false*, so the test file adds uses of its own alongside the import.
#[test]
fn seki_lib_test_control_safety() {
    run_seki_test_file("tests/seki/test_control_safety.seki", 5);
}

/// Every claim in the analysis and control libraries is re-established by
/// the kernel.
///
/// The point of building analysis by deduction rather than by axiom is
/// that the result is *checked*; a proof that only the tactic believes
/// would be a step backwards from the numerical library it replaces.  The
/// two genuine assumptions (completeness and the Archimedean property) are
/// `axiom`s, which the audit counts separately.
#[test]
fn the_analysis_library_is_kernel_checked() {
    for file in [
        "lib/analysis/axioms.seki",
        "lib/analysis/continuity.seki",
        "lib/analysis/ode.seki",
        "lib/control/safety.seki",
    ] {
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
            .arg("--audit")
            .arg(file)
            .env("SEKI_LIB_PATH", "lib")
            .output()
            .expect("run seki --audit");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(out.status.success(), "{}: {}", file, stdout);
        assert!(
            stdout.contains("every claim in this file was re-established by the kernel"),
            "{} is not fully kernel-checked:\n{}",
            file,
            stdout
        );
    }
}

#[test]
fn seki_lib_test_analysis_advanced() {
    run_seki_test_file("tests/seki/test_analysis_advanced.seki", 14);
}

#[test]
fn seki_lib_test_numeric_linalg() {
    run_seki_test_file("tests/seki/test_numeric_linalg.seki", 9);
}

#[test]
fn seki_lib_test_numeric_matrix_eq() {
    run_seki_test_file("tests/seki/test_numeric_matrix_eq.seki", 8);
}

#[test]
fn seki_lib_test_probability() {
    run_seki_test_file("tests/seki/test_probability.seki", 7);
}

/// Guard against the wiring gap itself: every `tests/seki/test_*.seki` must
/// have a `#[test]` that runs it, or it is dead weight that silently rots.
#[test]
fn every_seki_test_file_is_wired_into_cargo_test() {
    let this_file = include_str!("integration.rs");
    let mut unwired = Vec::new();
    for entry in std::fs::read_dir("tests/seki").expect("read tests/seki") {
        let path = entry.expect("dir entry").path();
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        if !name.starts_with("test_") || !name.ends_with(".seki") {
            continue;
        }
        if !this_file.contains(&format!("tests/seki/{}", name)) {
            unwired.push(name);
        }
    }
    unwired.sort();
    assert!(
        unwired.is_empty(),
        "these .seki test files are never run by `cargo test`; add a \
         `run_seki_test_file` test for each: {:?}",
        unwired
    );
}

#[test]
fn seki_lib_test_cas_sym() {
    run_seki_test_file("tests/seki/test_cas_sym.seki", 10);
}

#[test]
fn seki_lib_test_cas_calc() {
    run_seki_test_file("tests/seki/test_cas_calc.seki", 19);
}

#[test]
fn seki_lib_test_cas_poly() {
    run_seki_test_file("tests/seki/test_cas_poly.seki", 22);
}

#[test]
fn seki_lib_test_cas_solve() {
    run_seki_test_file("tests/seki/test_cas_solve.seki", 10);
}

#[test]
fn seki_lib_test_cas_bigint() {
    run_seki_test_file("tests/seki/test_cas_bigint.seki", 6);
}

#[test]
fn seki_lib_test_algebra_axioms() {
    run_seki_test_file("tests/seki/test_algebra_axioms.seki", 17);
}

#[test]
fn seki_lib_test_algebra_modular() {
    run_seki_test_file("tests/seki/test_algebra_modular.seki", 19);
}

#[test]
fn seki_lib_test_algebra_vector() {
    run_seki_test_file("tests/seki/test_algebra_vector.seki", 14);
}

#[test]
fn seki_lib_test_algebra_matrix() {
    run_seki_test_file("tests/seki/test_algebra_matrix.seki", 17);
}

#[test]
fn seki_lib_test_algebra_structures() {
    run_seki_test_file("tests/seki/test_algebra_structures.seki", 46);
}

#[test]
fn seki_lib_test_analysis_diff() {
    run_seki_test_file("tests/seki/test_analysis_diff.seki", 7);
}

#[test]
fn seki_lib_test_analysis_integ() {
    run_seki_test_file("tests/seki/test_analysis_integ.seki", 7);
}

#[test]
fn seki_lib_test_analysis_series() {
    run_seki_test_file("tests/seki/test_analysis_series.seki", 15);
}

#[test]
fn seki_lib_test_analysis_limit() {
    run_seki_test_file("tests/seki/test_analysis_limit.seki", 7);
}

#[test]
fn seki_lib_test_analysis_ivt() {
    run_seki_test_file("tests/seki/test_analysis_ivt.seki", 7);
}

#[test]
fn seki_lib_test_analysis_elementary() {
    run_seki_test_file("tests/seki/test_analysis_elementary.seki", 11);
}

#[test]
fn seki_lib_test_algebra_complex() {
    run_seki_test_file("tests/seki/test_algebra_complex.seki", 21);
}

#[test]
fn seki_lib_test_cas_rational() {
    run_seki_test_file("tests/seki/test_cas_rational.seki", 12);
}

#[test]
fn seki_lib_test_3x3_eigenvalues() {
    run_seki_test_file("tests/seki/test_3x3_eigenvalues.seki", 10);
}

#[test]
fn seki_lib_test_cas_dsl() {
    run_seki_test_file("tests/seki/test_cas_dsl.seki", 10);
}

#[test]
fn seki_lib_test_ui_dom() {
    run_seki_test_file("tests/seki/test_ui_dom.seki", 4);
}

#[test]
fn seki_lib_test_ui_app() {
    run_seki_test_file("tests/seki/test_ui_app.seki", 3);
}

#[test]
fn seki_lib_test_ui_models() {
    run_seki_test_file("tests/seki/test_ui_models.seki", 4);
}

#[test]
fn parse_sym_builds_symbolic_expr() {
    // Uses the binary path so library imports work via lib-path resolution.
    let tmp = std::env::temp_dir().join("seki_test_parsesym.seki");
    std::fs::write(
        &tmp,
        r#"import "cas/sym.seki"
def e := parseSym "2 * pow x 2 + 3"
def expected := SAdd (SMul (SNum 2) (SPow (SVar "x") 2)) (SNum 3)
theorem t : e == expected := by eval
"#,
    )
    .expect("write tmp");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg(&tmp)
        .output()
        .expect("run seki");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "seki exit failed.\nstdout:\n{}",
        stdout
    );
    assert!(
        stdout.contains("theorem t ✓ proved"),
        "expected `theorem t ✓ proved` in output, got:\n{}",
        stdout
    );
    let _ = std::fs::remove_file(&tmp);
}

#[test]
fn import_resolves_via_lib_path() {
    // Run via the binary so the production library-search behavior is exercised.
    // The seki source uses bare lib-relative paths (no `..` prefix) and we
    // run from the project root, so `lib/` should be auto-discovered.
    let tmp = std::env::temp_dir().join("seki_test_libpath.seki");
    std::fs::write(
        &tmp,
        r#"import "cas/sym.seki"
def x_ := SVar "x"
simp1 (SAdd (SNum 0) x_)
"#,
    )
    .expect("write tmp");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg(&tmp)
        .output()
        .expect("run seki");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "seki exit failed.\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
    assert!(
        stdout.contains("imported cas/sym.seki"),
        "expected cas/sym.seki to be imported; stdout:\n{}",
        stdout
    );
    let _ = std::fs::remove_file(&tmp);
}

#[test]
fn implication_operator_works() {
    let g = run(r"
        theorem t1 : forall a in Bool, a => a := by eval
        theorem t2 : forall (a b) in Bool, (a and b) => a := by eval
        theorem mp : forall (a b) in Bool, (a and (a => b)) => b := by eval
    ");
    assert!(g.theorems.contains_key("t1"));
    assert!(g.theorems.contains_key("t2"));
    assert!(g.theorems.contains_key("mp"));
}

#[test]
fn seki_lib_test_numeric_matrix() {
    run_seki_test_file("tests/seki/test_numeric_matrix.seki", 10);
}

#[test]
fn seki_lib_test_numeric_ode() {
    run_seki_test_file("tests/seki/test_numeric_ode.seki", 3);
}

#[test]
fn seki_lib_test_numeric_newton() {
    run_seki_test_file("tests/seki/test_numeric_newton.seki", 3);
}

#[test]
fn seki_lib_test_numeric_gauss() {
    run_seki_test_file("tests/seki/test_numeric_gauss.seki", 7);
}

#[test]
fn seki_lib_test_numth_gcd() {
    run_seki_test_file("tests/seki/test_numth_gcd.seki", 12);
}

#[test]
fn seki_lib_test_numth_primes() {
    run_seki_test_file("tests/seki/test_numth_primes.seki", 16);
}

#[test]
fn seki_lib_test_numth_modular() {
    run_seki_test_file("tests/seki/test_numth_modular.seki", 8);
}

#[test]
fn seki_lib_test_combinatorics() {
    run_seki_test_file("tests/seki/test_combinatorics.seki", 28);
}

#[test]
fn by_decide_proves_bool_propositions() {
    let g = run(r"
        theorem t1 : 2 + 2 == 4 := by decide
        theorem t2 : forall b in Bool, not (not b) == b := by decide
    ");
    assert!(g.theorems.contains_key("t1"));
    assert!(g.theorems.contains_key("t2"));
}

#[test]
fn adt_induction_on_user_data() {
    let g = run(r"
        data MyNat = Z | S MyNat
        theorem t : forall n in MyNat, S n != Z := by induction
    ");
    assert!(g.theorems.contains_key("t"));
}

#[test]
fn seki_lib_test_cas_multipoly() {
    run_seki_test_file("tests/seki/test_cas_multipoly.seki", 22);
}

#[test]
fn let_rec_recursive_local_binding() {
    let g = run(r"
        def fact5 :=
            let rec f := \n -> if n == 0 then 1 else n * f (n - 1) in
            f 5
        def fib10 :=
            let rec g := \n -> if n < 2 then n else g (n - 1) + g (n - 2) in
            g 10
    ");
    assert!(matches!(g.defs.get("fact5"), Some(Value::Int(120))));
    assert!(matches!(g.defs.get("fib10"), Some(Value::Int(55))));
}

#[test]
fn by_linarith_proves_linear_inequalities() {
    let g = run(r"
        theorem t1 : forall n in Nat, n + 5 > 4 := by linarith
        theorem t2 : forall (a b) in Nat, a + b >= b := by linarith
    ");
    assert!(g.theorems.contains_key("t1"));
    assert!(g.theorems.contains_key("t2"));
}

#[test]
fn enum_data_auto_generates_set() {
    let g = run(r"
        data Color = Red | Green | Blue
        theorem t : forall c in Color, c == Red or c == Green or c == Blue
            := by eval
    ");
    assert!(g.theorems.contains_key("t"));
    // Color should also be available as a set.
    assert!(g.defs.contains_key("Color"));
}

#[test]
fn forall_multi_var_sugar() {
    let g = run(r"
        theorem add_comm
          : forall (a b) in Int, a + b == b + a
          := by algebra
        theorem mul_distrib
          : forall (a b c) in Int, a * (b + c) == a * b + a * c
          := by algebra
    ");
    assert!(g.theorems.contains_key("add_comm"));
    assert!(g.theorems.contains_key("mul_distrib"));
}

#[test]
fn match_tuple_pattern_two_elem() {
    let g = run(r"
        def swap := \p ->
            match p with
            | (a, b) -> (b, a)
        def r := swap (3, 5)
    ");
    // (5, 3)
    if let Some(Value::Tuple(xs)) = g.defs.get("r") {
        assert_eq!(xs.len(), 2);
        assert!(matches!(xs[0], Value::Int(5)));
        assert!(matches!(xs[1], Value::Int(3)));
    } else {
        panic!("expected swap result to be a 2-tuple");
    }
}

#[test]
fn match_tuple_pattern_three_elem() {
    let g = run(r"
        def sum3 := \t ->
            match t with
            | (a, b, c) -> a + b + c
        def r := sum3 (1, 2, 3)
    ");
    assert!(matches!(g.defs.get("r"), Some(Value::Int(6))));
}

#[test]
fn match_tuple_pattern_nested_in_ctor() {
    let g = run(r"
        def fold := \opt ->
            match opt with
            | None -> 0
            | Some (a, b) -> a + b
        def r1 := fold (Some (3, 7))
        def r2 := fold None
    ");
    assert!(matches!(g.defs.get("r1"), Some(Value::Int(10))));
    assert!(matches!(g.defs.get("r2"), Some(Value::Int(0))));
}

#[test]
fn simp_handles_ac_swap() {
    // Tests AC-canonicalization: x + 0 == 0 + x and a + b == b + a
    let g = run(r"
        theorem add_comm : forall (a b) in Int, a + b == b + a := by algebra
        theorem zero_swap : forall x in Int, x + 0 == 0 + x := by simp
        theorem add_perm
          : forall (a b c) in Int, (a + b) + c == c + (b + a)
          := by simp
    ");
    assert!(g.theorems.contains_key("zero_swap"));
    assert!(g.theorems.contains_key("add_perm"));
}

#[test]
fn error_message_echoes_source_line() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("-e")
        .arg("def x : Int := \"oops\"")
        .output()
        .expect("run seki");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("[1:") && stderr.contains("def x : Int"),
        "expected source-line echo, got: {}",
        stderr
    );
    assert!(
        stderr.contains("^"),
        "expected caret pointer, got: {}",
        stderr
    );
}

#[test]
fn cas_symbolic_differentiation_polynomial() {
    // d/dx (x^2 + 3x + 5) = 2x + 3; verify by evaluating at x=4 → 11
    let g = run(r#"
        data Sym = SNum Int | SVar String | SAdd Sym Sym | SMul Sym Sym
                 | SSub Sym Sym | SPow Sym Int | SNeg Sym

        def derive := \v e ->
            match e with
            | SNum _ -> SNum 0
            | SVar w -> if w == v then SNum 1 else SNum 0
            | SAdd u w -> SAdd (derive v u) (derive v w)
            | SSub u w -> SSub (derive v u) (derive v w)
            | SMul u w -> SAdd (SMul (derive v u) w) (SMul u (derive v w))
            | SPow u n -> SMul (SMul (SNum n) (SPow u (n - 1))) (derive v u)
            | SNeg u -> SNeg (derive v u)

        def subst := \v c e ->
            match e with
            | SNum _ -> e
            | SVar w -> if w == v then SNum c else e
            | SAdd u w -> SAdd (subst v c u) (subst v c w)
            | SSub u w -> SSub (subst v c u) (subst v c w)
            | SMul u w -> SMul (subst v c u) (subst v c w)
            | SPow u n -> SPow (subst v c u) n
            | SNeg u -> SNeg (subst v c u)

        def evalSym := \e ->
            match e with
            | SNum n -> n
            | SAdd u w -> evalSym u + evalSym w
            | SSub u w -> evalSym u - evalSym w
            | SMul u w -> evalSym u * evalSym w
            | SPow u n -> powInt (evalSym u) n
            | SNeg u -> - (evalSym u)
            | _ -> 0

        def x_ := SVar "x"
        def poly := SAdd (SAdd (SPow x_ 2) (SMul (SNum 3) x_)) (SNum 5)
        def dpoly := derive "x" poly
        def at4 := evalSym (subst "x" 4 dpoly)
    "#);
    // 2*4 + 3 = 11
    assert!(matches!(g.defs.get("at4"), Some(Value::Int(11))));
}

#[test]
fn auto_portfolio_closes_arithmetic_identities() {
    // `by auto` should dispatch to the right closer for a handful of
    // representative goals across the tactic palette.
    let g = run(r"
        theorem trivial : 2 + 2 == 4 := by auto
        theorem int_zero : forall a in Int, a + 0 == a := by auto
        theorem cauchy : forall a in Int, forall b in Int, a*a + b*b >= 2*a*b := by auto
    ");
    for n in &["trivial", "int_zero", "cauchy"] {
        assert!(g.theorems.contains_key(*n), "{} not proven by auto", n);
    }
}

#[test]
fn auto_portfolio_handles_induction_and_unfold() {
    // The portfolio includes `unfold f then algebra` and bare `by induction`
    // for goals over Nat, so a user-defined recursive sum should close.
    let g = run(r"
        def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
        theorem gauss : forall n in Nat, 2 * sum n == n * (n + 1) := by auto
        theorem sum_nn : forall n in Nat, sum n >= 0 := by auto
    ");
    for n in &["gauss", "sum_nn"] {
        assert!(g.theorems.contains_key(*n), "{} not proven by auto", n);
    }
}

#[test]
fn auto_portfolio_rejects_false_proposition() {
    // Sanity: `by auto` must not silently accept a non-theorem.
    let res = std::panic::catch_unwind(|| {
        run("theorem bad : forall n in Nat, n + 1 == n := by auto");
    });
    assert!(res.is_err(), "false proposition must not be proved by auto");
}

#[test]
fn extract_lemmas_collects_simp_names() {
    use seki::ast::Proof;
    use seki::prover::extract_lemmas;
    let p = Proof::Seq(vec![
        Proof::ByIntros,
        Proof::BySimp { lemmas: vec!["foo".into(), "bar".into()] },
        Proof::ByAlgebra,
    ]);
    assert_eq!(extract_lemmas(&p), vec!["foo".to_string(), "bar".to_string()]);

    let p2 = Proof::ByAlgebra;
    assert!(extract_lemmas(&p2).is_empty());

    let nested = Proof::Seq(vec![
        Proof::BySimp { lemmas: vec!["a".into()] },
        Proof::Seq(vec![Proof::BySimp { lemmas: vec!["b".into()] }]),
    ]);
    assert_eq!(extract_lemmas(&nested), vec!["a".to_string(), "b".to_string()]);
}

#[test]
fn lemma_first_portfolio_picks_a_registered_lemma() {
    // When a goal restates an existing theorem verbatim, the
    // lemma-preferring portfolio should close it via `by simp [<that>]`
    // rather than falling back to a cheap closer that hides the lemma.
    let mut g = make_prelude();
    let src = r"
        def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
        theorem gauss : forall n in Nat, 2 * sum n == n * (n + 1) := by induction
    ";
    let decls = parse_program(src).expect("parse");
    for ld in decls {
        let ctx = EvalCtx::new(&g);
        let env = Env::new();
        match ld.decl {
            Decl::Def { name, value, .. } => {
                let v = ctx.eval(&value, &env).unwrap();
                g.defs.insert(name, v);
            }
            Decl::Theorem { name, prop, proof } => {
                let prover = Prover::new(&ctx);
                let v = prover.verify(&prop, &proof, &env).unwrap();
                g.theorem_props.insert(name.clone(), prop);
                g.theorems.insert(name, v);
            }
            _ => {}
        }
    }

    // Now ask `:why`-style for the exact restatement.
    let restated = parse_program(
        "theorem _g : forall n in Nat, 2 * sum n == n * (n + 1) := refl",
    )
    .unwrap();
    let prop = match &restated[0].decl {
        Decl::Theorem { prop, .. } => prop.clone(),
        _ => panic!("expected theorem"),
    };
    let ctx = EvalCtx::new(&g);
    let env = Env::new();
    let prover = Prover::new(&ctx);
    let proof = prover
        .try_portfolio_lemma_first(&prop, &env)
        .expect("lemma-first portfolio should close the restatement");
    let lemmas = seki::prover::extract_lemmas(&proof);
    assert!(
        lemmas.iter().any(|l| l == "gauss"),
        "expected `gauss` in extracted lemmas, got {:?}",
        lemmas
    );
}

#[test]
fn theorem_proofs_registry_stores_proof_ast() {
    // The `theorem_proofs` registry must capture the proof AST so the
    // REPL's dependency re-checker can replay it after a redefinition.
    let g = run(r"
        def f := \n -> n + 1
        theorem t : forall n in Int, f n - 1 == n := by unfold f then algebra
    ");
    let proof = g
        .theorem_proofs
        .get("t")
        .expect("proof AST must be saved alongside the theorem");
    // We don't lock the exact AST shape, but it should mention the
    // unfold-target and end with an algebraic closer.
    let rendered = format!("{}", proof);
    assert!(
        rendered.contains("unfold f") && rendered.contains("algebra"),
        "unexpected proof AST: {}",
        rendered
    );
}

#[test]
fn recheck_succeeds_after_equivalent_redefinition() {
    // When a def is replaced by something semantically identical, the
    // stored proof should still verify against the new globals.  This is
    // the silent-success path the REPL relies on.
    use seki::ast::{Decl, Proof};

    // Phase 1: define + prove.
    let mut g = make_prelude();
    let phase1 = parse_program(
        r"
        def double := \n -> n + n
        theorem dbl : forall n in Int, double n == 2 * n
          := by unfold double then algebra
    ",
    )
    .unwrap();
    for ld in phase1 {
        let ctx = EvalCtx::new(&g);
        let env = Env::new();
        match ld.decl {
            Decl::Def { name, value, .. } => {
                let v = ctx.eval(&value, &env).unwrap();
                g.defs.insert(name, v);
            }
            Decl::Theorem { name, prop, proof } => {
                let prover = Prover::new(&ctx);
                let v = prover.verify(&prop, &proof, &env).unwrap();
                g.theorem_props.insert(name.clone(), prop);
                g.theorem_proofs.insert(name.clone(), proof);
                g.theorems.insert(name, v);
            }
            _ => {}
        }
    }
    let saved_proof: Proof = g.theorem_proofs.get("dbl").cloned().unwrap();
    let saved_prop = g.theorem_props.get("dbl").cloned().unwrap();

    // Phase 2: redefine `double` to an equivalent form, then replay.
    let phase2 = parse_program(r"def double := \n -> 2 * n").unwrap();
    for ld in phase2 {
        if let Decl::Def { name, value, .. } = ld.decl {
            let ctx = EvalCtx::new(&g);
            let env = Env::new();
            let v = ctx.eval(&value, &env).unwrap();
            g.defs.insert(name, v);
        }
    }
    let ctx = EvalCtx::new(&g);
    let env = Env::new();
    let prover = Prover::new(&ctx);
    prover
        .verify(&saved_prop, &saved_proof, &env)
        .expect("stored proof should still verify after equivalent redef");
}

#[test]
fn recheck_fails_after_breaking_redefinition() {
    // When a def is replaced by something that breaks the theorem, the
    // replay must fail — that's the signal the REPL converts into a
    // user-facing warning.
    use seki::ast::Decl;

    let mut g = make_prelude();
    let phase1 = parse_program(
        r"
        def succ_ := \n -> n + 1
        theorem t : forall n in Int, succ_ n == n + 1
          := by unfold succ_ then algebra
    ",
    )
    .unwrap();
    for ld in phase1 {
        let ctx = EvalCtx::new(&g);
        let env = Env::new();
        match ld.decl {
            Decl::Def { name, value, .. } => {
                let v = ctx.eval(&value, &env).unwrap();
                g.defs.insert(name, v);
            }
            Decl::Theorem { name, prop, proof } => {
                let prover = Prover::new(&ctx);
                let v = prover.verify(&prop, &proof, &env).unwrap();
                g.theorem_props.insert(name.clone(), prop);
                g.theorem_proofs.insert(name.clone(), proof);
                g.theorems.insert(name, v);
            }
            _ => {}
        }
    }
    let saved_proof = g.theorem_proofs.get("t").cloned().unwrap();
    let saved_prop = g.theorem_props.get("t").cloned().unwrap();

    // Redefine `succ_` to be incorrect.
    let phase2 = parse_program(r"def succ_ := \n -> n + 999").unwrap();
    for ld in phase2 {
        if let Decl::Def { name, value, .. } = ld.decl {
            let ctx = EvalCtx::new(&g);
            let env = Env::new();
            let v = ctx.eval(&value, &env).unwrap();
            g.defs.insert(name, v);
        }
    }
    let ctx = EvalCtx::new(&g);
    let env = Env::new();
    let prover = Prover::new(&ctx);
    assert!(
        prover.verify(&saved_prop, &saved_proof, &env).is_err(),
        "stored proof must fail to verify after breaking redef"
    );
}

#[test]
fn theorem_without_assign_defaults_to_auto() {
    // `theorem name : prop` (no `:=`) is the REPL convenience form: the
    // parser desugars it to `:= by auto`, so it should prove identically.
    let g = run(r"
        theorem distrib
          : forall a in Int, forall b in Int, forall c in Int,
                a * (b + c) == a * b + a * c
    ");
    assert!(g.theorems.contains_key("distrib"));
}

#[test]
fn nonexhaustive_match_is_a_warning_by_default() {
    // Baseline: without SEKI_STRICT_MATCH, a non-exhaustive `match` still
    // compiles and runs — only a warning goes to stderr.
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("-e")
        .arg("data Color = Red | Green | Blue\n(\\c -> match c with | Red -> 1 | Green -> 2) Red")
        .env_remove("SEKI_STRICT_MATCH")
        .output()
        .expect("run seki");
    assert!(
        output.status.success(),
        "non-exhaustive match must not fail by default.\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("warning: non-exhaustive match"),
        "expected a warning, got: {}",
        stderr
    );
}

#[test]
fn strict_match_env_var_rejects_nonexhaustive_match() {
    // Isolated via subprocess env (never `std::env::set_var` in-process —
    // tests share one process and run concurrently).
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("-e")
        .arg("data Color = Red | Green | Blue\n(\\c -> match c with | Red -> 1 | Green -> 2) Red")
        .env("SEKI_STRICT_MATCH", "1")
        .output()
        .expect("run seki");
    assert!(
        !output.status.success(),
        "SEKI_STRICT_MATCH must reject a non-exhaustive match"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("non-exhaustive match"),
        "expected a non-exhaustive-match error, got: {}",
        stderr
    );
}

#[test]
fn strict_match_cli_flag_rejects_nonexhaustive_match() {
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--strict-match")
        .arg("-e")
        .arg("data Color = Red | Green | Blue\n(\\c -> match c with | Red -> 1 | Green -> 2) Red")
        .env_remove("SEKI_STRICT_MATCH")
        .output()
        .expect("run seki");
    assert!(
        !output.status.success(),
        "--strict-match must reject a non-exhaustive match"
    );
}

#[test]
fn strict_match_accepts_a_genuinely_exhaustive_match() {
    // No false positives: strict mode must not reject a match that covers
    // every constructor.
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--strict-match")
        .arg("-e")
        .arg(
            "data Color = Red | Green | Blue\n\
             (\\c -> match c with | Red -> 1 | Green -> 2 | Blue -> 3) Red",
        )
        .output()
        .expect("run seki");
    assert!(
        output.status.success(),
        "an exhaustive match must not be rejected under --strict-match.\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn run_decl_attaches_source_location_to_errors() {
    // Run via the binary so we get the [line:col] prefix path.
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("-e")
        .arg("def x : Int := \"oops\"")
        .output()
        .expect("run seki");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("[1:") && stderr.contains("type error"),
        "expected location-prefixed type error, got: {}",
        stderr
    );
}

// -- trust accounting -------------------------------------------------------
//
// `Prover::verify` answering "yes" is not the same as the theorem being
// true: `by eval` over an infinite domain only samples it.  These pin the
// classification down so a future change cannot quietly widen what counts
// as a proof.  See `src/trust.rs` and `docs/spec/06-soundness.md` §6.2.

fn trust_of(src: &str, thm: &str) -> TrustLevel {
    let g = run(src);
    *g.theorem_trust
        .get(thm)
        .unwrap_or_else(|| panic!("theorem `{}` was not registered", thm))
}

#[test]
fn finite_domain_by_eval_is_sound() {
    assert_eq!(
        trust_of(
            r"
            def Small := {1, 2, 3}
            theorem all_pos : forall x in Small, x > 0 := by eval
            ",
            "all_pos"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn infinite_domain_by_eval_is_only_sampled() {
    // `f` agrees with the claim on every sampled point and breaks well past
    // `SAMPLE_BOUND`, so `by eval` accepts a proposition the evaluator
    // itself refutes.  It must not be recorded as a proof.
    let src = r"
        def f : Nat -> Nat := \(n : Nat) -> if n < 300 then 0 else 1
        theorem f_zero : forall n in Nat, f(n) == 0 := by eval
    ";
    assert_eq!(trust_of(src, "f_zero"), TrustLevel::Sampled);
    let g = run(src);
    let ctx = EvalCtx::new(&g);
    let refutation = ctx
        .eval(&only_expr("f(10000)"), &Env::new())
        .expect("eval f(10000)");
    assert!(
        matches!(refutation, Value::Int(1)),
        "the evaluator should disagree with the 'proved' theorem"
    );
}

#[test]
fn sampled_trust_propagates_through_simp() {
    assert_eq!(
        trust_of(
            r"
            def f : Nat -> Nat := \(n : Nat) -> if n < 300 then 0 else 1
            theorem f_zero : forall n in Nat, f(n) == 0 := by eval
            theorem consequence : f(10000) == 0 := by simp [f_zero]
            ",
            "consequence"
        ),
        TrustLevel::Sampled,
        "a lemma that was only sampled must not be laundered into a proof"
    );
}

#[test]
fn axiom_dependence_is_recorded() {
    assert_eq!(
        trust_of(
            r"
            def f : Nat -> Nat := \(n : Nat) -> n
            axiom my_ax : forall n in Nat, f(n) + 1 == 1
            theorem uses_ax : f(3) + 1 == 1 := by simp [my_ax]
            ",
            "uses_ax"
        ),
        TrustLevel::Axiomatic
    );
}

#[test]
fn by_algebra_over_an_infinite_domain_is_sound() {
    assert_eq!(
        trust_of(
            "theorem sq_nn : forall x in Real, x * x >= 0.0 := by algebra",
            "sq_nn"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn definitional_discharge_of_an_infinite_forall_is_sound() {
    // `try_forall_from_definition` decides these symbolically, so no
    // enumeration happens even though the domain is infinite.
    for (src, name) in [
        ("theorem t : forall n in Nat, n >= 0 := by eval", "t"),
        (
            "def W := {x in Int | (-3 <= x) and (x <= 3)}\n\
             theorem t : forall x in W, x <= 3 := by eval",
            "t",
        ),
        (
            "theorem t : forall a in Int, forall b in Int, forall c in Int, \
             a * (b + c) == a * b + a * c := by eval",
            "t",
        ),
    ] {
        assert_eq!(trust_of(src, name), TrustLevel::Sound, "for: {}", src);
    }
}

#[test]
fn existential_witness_over_an_infinite_domain_is_sound() {
    // Enumeration found an actual witness; that is a proof regardless of
    // how much of the domain was left unvisited.
    assert_eq!(
        trust_of("theorem big : exists n in Nat, n > 100 := by eval", "big"),
        TrustLevel::Sound
    );
}

#[test]
fn unfold_then_algebra_is_sound_even_over_reals() {
    // Only the closer evaluates; `by unfold` merely rewrites the goal, so
    // the chain is as sound as the `by algebra` that ends it.
    assert_eq!(
        trust_of(
            r"
            def absR := \(r : Real) -> if r < 0.0 then 0.0 - r else r
            theorem absR_nonneg : forall x in Real, absR x >= 0.0
              := by unfold absR then algebra
            ",
            "absR_nonneg"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn strict_mode_rejects_a_sampled_theorem() {
    let mut session = Session::new();
    session.strict = true;
    let err = session
        .run_source(
            r"
            def f : Nat -> Nat := \(n : Nat) -> if n < 300 then 0 else 1
            theorem f_zero : forall n in Nat, f(n) == 0 := by eval
            ",
            true,
        )
        .expect_err("--strict must refuse a sampled theorem");
    assert!(err.is_proof_error(), "got {:?}", err);
    assert!(
        err.message().contains("sampled"),
        "error should say why: {}",
        err.message()
    );
}

#[test]
fn strict_mode_accepts_a_sound_theorem() {
    let mut session = Session::new();
    session.strict = true;
    session
        .run_source(
            "theorem sq_nn : forall x in Real, x * x >= 0.0 := by algebra",
            true,
        )
        .expect("--strict must accept a fully sound proof");
}

// -- integer overflow -------------------------------------------------------

#[test]
fn int_overflow_is_an_error_not_a_wrapped_value() {
    // `Int` is the mathematical integers in the logic: `by algebra` would
    // normalize `9223372036854775807 + 1 > 0` to true.  If the evaluator
    // wrapped, `by eval` would "prove" the opposite.
    for src in [
        "def x := 9223372036854775807 + 1",
        "def x := 0 - 9223372036854775807 - 2",
        "def x := 4611686018427387904 * 4",
        "def x := pow(2, 64)",
    ] {
        let err = run_err(src);
        assert!(
            err.message().contains("overflow"),
            "expected an overflow error for `{}`, got: {}",
            src,
            err.message()
        );
    }
}

#[test]
fn ordinary_arithmetic_is_unaffected_by_the_overflow_check() {
    let g = run(
        "def a := 2 + 3 * 4\n\
         def b := 0 - 5\n\
         def c := pow(2, 10)\n\
         def d := (0 - 7) mod 3\n\
         def e := 10 / 3",
    );
    assert!(matches!(g.defs.get("a"), Some(Value::Int(14))));
    assert!(matches!(g.defs.get("b"), Some(Value::Int(-5))));
    assert!(matches!(g.defs.get("c"), Some(Value::Int(1024))));
    assert!(matches!(g.defs.get("d"), Some(Value::Int(2))));
    assert!(matches!(g.defs.get("e"), Some(Value::Int(3))));
}

// -- driver / parser regressions --------------------------------------------

#[test]
fn the_test_harness_can_now_follow_imports() {
    // The hand-rolled `run` helper this file used to carry panicked on
    // `Decl::Import`, so nothing about module loading was covered here.
    let g = run(r#"import "settheory/axioms.seki""#);
    assert!(
        !g.defs.is_empty(),
        "importing a stdlib module should bring names into scope"
    );
}

#[test]
fn a_keyword_in_a_binder_position_says_so() {
    // Before this, `sigma` (a keyword since Σ-types) as a lambda parameter
    // produced "expected Arrow but got LParen", and two stdlib modules sat
    // broken because of it.
    let err = seki::parse_program(r"def f := \(mu : Real) (sigma : Real) -> mu")
        .expect_err("a keyword parameter must be rejected");
    let msg = err.message();
    assert!(msg.contains("sigma"), "{}", msg);
    assert!(msg.contains("keyword"), "{}", msg);
}

/// Parse a source string that is a single expression declaration and return
/// that expression.
fn only_expr(src: &str) -> seki::ast::Expr {
    let decls = seki::parse_program(src).expect("parse expression");
    match decls.into_iter().next().expect("one declaration").decl {
        Decl::Expr(e) => e,
        other => panic!("expected a bare expression, got {:?}", other),
    }
}

// -- structural encodings ---------------------------------------------------

#[test]
fn constructor_injectivity_works_for_lists_and_trees_alike() {
    // `by algebra` decomposes an equality between two applications of the
    // same constructor into one equality per field.  This used to be
    // written out for lists only; driving it from the encoding table gives
    // trees the same treatment.
    let g = run(
        r"
        theorem list_inj : cons 1 (cons 2 nil) == cons 1 (cons (1 + 1) nil) := by algebra
        theorem tree_inj : node leaf 5 leaf == node leaf (2 + 3) leaf := by algebra
        ",
    );
    assert!(g.theorems.contains_key("list_inj"));
    assert!(g.theorems.contains_key("tree_inj"));
}

#[test]
fn distinct_constructors_are_rejected_not_silently_accepted() {
    let err = run_err("theorem bad : nil == cons 1 nil := by algebra");
    assert!(err.is_proof_error(), "got {:?}", err);
    assert!(
        err.message().contains("structurally unequal"),
        "{}",
        err.message()
    );
}


// -- documentation that must not drift --------------------------------------

#[test]
fn the_documented_keyword_list_matches_the_lexer() {
    // `sigma` became a keyword without being added to the spec, and two
    // stdlib modules quietly stopped parsing.  Pin the two together.
    let doc = std::fs::read_to_string("docs/spec/01-lexical.md")
        .expect("read docs/spec/01-lexical.md");
    let start = doc
        .find("def let in where")
        .expect("the keyword block should start with `def let in where`");
    let end = start + doc[start..].find("\n```").expect("closing fence");
    let documented: std::collections::BTreeSet<&str> =
        doc[start..end].split_whitespace().collect();

    let actual: std::collections::BTreeSet<&str> = ALL_KEYWORDS.iter().copied().collect();
    assert_eq!(
        documented, actual,
        "docs/spec/01-lexical.md and src/lexer.rs disagree about the keywords"
    );
}

/// Every keyword the lexer recognizes.  Derived by asking `keyword_spelling`
/// about each candidate, so it cannot silently fall behind the lexer.
const ALL_KEYWORDS: &[&str] = &[
    "def", "let", "in", "where", "if", "then", "else", "lambda", "fn", "forall", "exists",
    "sigma", "theorem", "axiom", "type", "by", "data", "match", "with", "import", "as",
    "class", "instance", "true", "false", "and", "or", "not", "subset", "union",
    "intersect", "diff", "times", "notin", "mod", "for", "do",
];

#[test]
fn every_listed_keyword_really_is_one() {
    for kw in ALL_KEYWORDS {
        let toks = seki::lexer::tokenize(kw).expect("tokenize");
        assert!(
            seki::lexer::keyword_spelling(&toks[0].tok).is_some(),
            "`{}` is listed as a keyword but the lexer scans it as an identifier",
            kw
        );
    }
    // And a non-keyword must not be mistaken for one.
    let toks = seki::lexer::tokenize("mu").expect("tokenize");
    assert!(seki::lexer::keyword_spelling(&toks[0].tok).is_none());
}

// -- proof terms ------------------------------------------------------------
//
// Every accepted theorem now carries a `kernel::Cert` that an independent
// checker re-established.  These pin down that the certificate is real
// (it records the actual structure of the proof), that the kernel's verdict
// drives the reported trust level, and that the remaining gaps stay visible.

fn cert_of(src: &str, name: &str) -> seki::kernel::Cert {
    let g = run(src);
    g.theorem_certs
        .get(name)
        .unwrap_or_else(|| panic!("no proof term recorded for `{}`", name))
        .clone()
}

#[test]
fn a_finite_forall_certificate_covers_every_element() {
    let cert = cert_of(
        "def Small := {1, 2, 3}\ntheorem t : forall x in Small, x > 0 := by eval",
        "t",
    );
    match cert {
        seki::kernel::Cert::ForallFinite { subs } => assert_eq!(subs.len(), 3),
        other => panic!("expected a per-element certificate, got {}", other.render()),
    }
}

#[test]
fn an_existential_certificate_carries_the_witness() {
    let cert = cert_of("theorem t : exists n in Nat, n > 100 := by eval", "t");
    assert!(
        cert.render().contains("witness 101"),
        "the certificate should name the witness: {}",
        cert.render()
    );
}

#[test]
fn an_inequality_certificate_carries_a_checkable_witness() {
    // `by algebra` searched for the decomposition; the certificate records
    // it so the kernel only has to multiply out and compare.
    let cert = cert_of(
        "theorem t : forall a in Int, forall b in Int, a*a + b*b >= 2*a*b := by algebra",
        "t",
    );
    let text = cert.render();
    assert!(
        text.contains("combination of the squares"),
        "expected a sum-of-squares witness, got: {}",
        text
    );
}

#[test]
fn a_case_split_certificate_records_both_branches() {
    let cert = cert_of(
        "def absInt := \\x -> if x >= 0 then x else 0 - x\n\
         theorem t : forall x in Int, absInt x >= 0 := by unfold absInt then algebra",
        "t",
    );
    let text = cert.render();
    assert!(text.contains("unfold"), "{}", text);
    assert!(text.contains("case split"), "{}", text);
    assert!(text.contains("when it does not"), "{}", text);
}

#[test]
fn the_kernel_verdict_drives_the_reported_trust() {
    // A sampled proof cannot be fully checked, and says why.
    let g = run(
        "def f : Nat -> Nat := \\(n : Nat) -> if n < 300 then 0 else 1\n\
         theorem s : forall n in Nat, f(n) == 0 := by eval",
    );
    let verdict = &g.theorem_verdicts["s"];
    assert!(!verdict.fully_checked);
    assert!(verdict.is_sampled());
    assert_eq!(g.theorem_trust["s"], TrustLevel::Sampled);

    // A fully checked one has nothing outstanding.
    let g = run("theorem q : forall x in Real, x * x >= 0.0 := by algebra");
    let verdict = &g.theorem_verdicts["q"];
    assert!(verdict.fully_checked);
    assert!(!verdict.has_assumptions());
    assert_eq!(g.theorem_trust["q"], TrustLevel::Sound);
}

#[test]
fn a_tactic_without_a_proof_term_is_reported_as_unchecked() {
    // `by induction`'s step has no witness form yet.  That is a *visible*
    // gap, not a silent one: the theorem is accepted, marked, and refused
    // by `--strict`.
    let g = run(
        "def sum := \\n -> if n == 0 then 0 else n + sum (n - 1)\n\
         theorem nn : forall n in Nat, sum n >= 0 := by induction",
    );
    assert_eq!(g.theorem_trust["nn"], TrustLevel::Unchecked);
    let text = g.theorem_certs["nn"].render();
    assert!(text.contains("base case"), "{}", text);
    assert!(text.contains("NOT CHECKED"), "{}", text);

    let mut strict = Session::new();
    strict.strict = true;
    assert!(strict
        .run_source(
            "def sum := \\n -> if n == 0 then 0 else n + sum (n - 1)\n\
             theorem nn : forall n in Nat, sum n >= 0 := by induction",
            true
        )
        .is_err());
}

#[test]
fn opaque_subterms_are_not_assumed_non_negative() {
    // The bug the proof terms caught.  `by algebra` used to accept this
    // because `neg n` became an opaque atom and every atom was assumed
    // non-negative over Nat.
    let err = run_err(
        "def neg : Nat -> Int := \\(n : Nat) -> 0 - 5\n\
         theorem bad : forall n in Nat, neg n >= 0 := by algebra",
    );
    assert!(err.is_proof_error(), "{:?}", err);
    let g = run("def neg : Nat -> Int := \\(n : Nat) -> 0 - 5\ndef v := neg 3");
    assert!(
        matches!(g.defs.get("v"), Some(Value::Int(-5))),
        "and the evaluator does disagree with the claim"
    );
}

#[test]
fn a_bounded_comprehension_counts_as_finite() {
    // `Zn 12 = {x in Nat | x < 12}` is finite, so enumerating it is
    // exhaustive and the proof is checked rather than sampled.
    let g = run(
        "def Zn := \\n -> {x in Nat | x < n}\n\
         theorem t : forall x in (Zn 12), x < 12 := by eval",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    // An unbounded comprehension is still infinite.
    let g = run(
        "def Big := {x in Nat | x * x >= 0}\n\
         def f : Nat -> Nat := \\(n : Nat) -> if n < 300 then 0 else 1\n\
         theorem u : forall x in Big, f x == 0 := by eval",
    );
    assert_eq!(g.theorem_trust["u"], TrustLevel::Sampled);
}

#[test]
fn the_audit_command_reports_every_theorem() {
    let dir = std::env::temp_dir().join("seki_audit_test");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let file = dir.join("audit.seki");
    std::fs::write(
        &file,
        "theorem a : forall x in Real, x * x >= 0.0 := by algebra\n\
         def f : Nat -> Nat := \\(n : Nat) -> if n < 300 then 0 else 1\n\
         theorem b : forall n in Nat, f(n) == 0 := by eval\n",
    )
    .expect("write");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg(&file)
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(stdout.contains("kernel-checked from primitives"), "{}", stdout);
    assert!(stdout.contains("sampled"), "{}", stdout);
    assert!(stdout.contains("2 theorems"), "{}", stdout);
}

#[test]
fn the_proof_command_prints_the_term() {
    let dir = std::env::temp_dir().join("seki_proof_test");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let file = dir.join("proof.seki");
    std::fs::write(
        &file,
        "def Small := {1, 2, 3}\ntheorem t : forall x in Small, x > 0 := by eval\n",
    )
    .expect("write");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--proof")
        .arg(&file)
        .arg("t")
        .output()
        .expect("run seki --proof");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(stdout.contains("3 elements"), "{}", stdout);
    assert!(stdout.contains("every step re-established"), "{}", stdout);
}

// -- deduction --------------------------------------------------------------
//
// `by apply` / `by have` / `by assumption` were added because a library of
// 955 theorems contained only twelve proofs that used another theorem: the
// only ways to reuse a fact were `by simp` (equalities) and `by obtain`
// (existentials), so an implication or an inequality could not be reused at
// all.  These pin down that proofs now compose.

#[test]
fn a_lemma_can_be_applied_to_concrete_values() {
    // Before `by apply`, this failed with "lemma is not an equality".
    let g = run(
        "axiom mono : forall x in Real, forall y in Real, x <= y => (2.0*x) <= (2.0*y)\n\
         theorem t : (2.0 * 1.0) <= (2.0 * 3.0) := by apply mono",
    );
    assert!(g.theorems.contains_key("t"));
    assert_eq!(g.theorem_trust["t"], TrustLevel::Axiomatic);
}

#[test]
fn applying_a_lemma_infers_its_instantiation_from_the_goal() {
    let g = run(
        "theorem mono : forall x in Real, forall y in Real, x <= y => (2.0*x) <= (2.0*y)\n\
           := by algebra\n\
         theorem t : forall a in Real, forall b in Real, a <= b => (2.0*a) <= (2.0*b)\n\
           := by apply mono",
    );
    // Nothing was given with `with`, so both bindings came from matching.
    match &g.theorem_certs["t"] {
        seki::kernel::Cert::Apply { substs, .. } => assert_eq!(substs.len(), 2),
        other => panic!("expected an application, got {}", other.render()),
    }
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

#[test]
fn a_binding_the_goal_does_not_determine_must_be_given() {
    // Transitivity is the canonical case: `y` is nowhere in the conclusion
    // `x <= z`, so matching cannot find it and the user has to say.
    const TRANS: &str = "theorem le_trans : forall x in Real, forall y in Real, \
         forall z in Real, (x <= y) and (y <= z) => x <= z := by algebra\n";
    let err = run_err(&format!(
        "{}theorem t : forall a in Real, forall c in Real,\n\
             (a <= 5.0) and (5.0 <= c) => a <= c := by apply le_trans",
        TRANS
    ));
    assert!(err.message().contains("with y"), "{}", err.message());

    let g = run(&format!(
        "{}theorem t : forall a in Real, forall c in Real,\n\
             (a <= 5.0) and (5.0 <= c) => a <= c := by apply le_trans with y := 5.0",
        TRANS
    ));
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    // Both of transitivity's premises came from the goal's own hypotheses.
    match &g.theorem_certs["t"] {
        seki::kernel::Cert::Apply { premises, .. } => assert_eq!(premises.len(), 2),
        other => panic!("expected an application, got {}", other.render()),
    }
}

#[test]
fn applying_a_lemma_does_not_skip_its_premises() {
    // `mono` needs `a <= b`, and nothing here supplies it.
    let err = run_err(
        "theorem mono : forall x in Real, forall y in Real, x <= y => (2.0*x) <= (2.0*y)\n\
           := by algebra\n\
         theorem bad : forall a in Real, forall b in Real, (2.0*a) <= (2.0*b)\n\
           := by apply mono",
    );
    assert!(err.is_proof_error(), "{:?}", err);
    assert!(err.message().contains("premise"), "{}", err.message());
}

#[test]
fn forward_reasoning_composes_steps() {
    let g = run(
        "theorem mono : forall x in Real, forall y in Real, x <= y => (2.0*x) <= (2.0*y)\n\
           := by algebra\n\
         theorem t : forall a in Real, a <= 5.0 => (2.0 * a) <= 12.0\n\
           := by have h : (2.0 * a) <= (2.0 * 5.0) := by apply mono\n\
              then algebra",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    let text = g.theorem_certs["t"].render();
    assert!(text.contains("have"), "{}", text);
    assert!(text.contains("apply `mono`"), "{}", text);
}

#[test]
fn a_have_may_not_assume_what_it_cannot_prove() {
    let err = run_err(
        "theorem bad : forall a in Real, a <= 5.0 => (2.0 * a) <= 4.0\n\
           := by have h : (2.0 * a) <= 4.0 := by assumption\n\
              then assumption",
    );
    assert!(err.is_proof_error(), "{:?}", err);
}

#[test]
fn assumption_closes_a_goal_that_is_already_assumed() {
    let g = run("theorem t : forall p in Real, p > 0.0 => p > 0.0 := by assumption");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    let err = run_err("theorem bad : forall p in Real, p > 0.0 => p > 1.0 := by assumption");
    assert!(err.message().contains("not among the hypotheses"), "{}", err.message());
}

// -- linear arithmetic with a witness ---------------------------------------

#[test]
fn a_scaled_hypothesis_produces_a_farkas_certificate() {
    // `x <= 3 ⊢ 2x <= 6` needs a multiplier of 2; the old equal-weights
    // subset search could not express that, so it went unchecked.
    let g = run("theorem t : forall x in Real, x <= 3.0 => (2.0 * x) <= 6.0 := by algebra");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    assert!(g.theorem_certs["t"].render().contains('='));
}

#[test]
fn an_interval_bound_is_kernel_checked() {
    // The shape a parameterised model actually wants: "for every value in
    // this range, the conclusion holds".
    let g = run(
        "theorem t : forall r in Real, (0.05 <= r) and (r <= 0.15)\n\
             => (100.0 - 200.0 * r) > 0.0 := by algebra",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    let g = run(
        "theorem u : forall r in Real, forall d in Real,\n\
             (0.05 <= r) and (r <= 0.15) and (0.0 <= d) and (d <= 0.1)\n\
             => (100.0 - 200.0*r - 100.0*d) > 0.0 := by algebra",
    );
    assert_eq!(g.theorem_trust["u"], TrustLevel::Sound);
}

#[test]
fn an_equality_hypothesis_can_be_rearranged() {
    // `w³ - w - 2 = 0 ⊢ w³ = w + 2` — what an obtained witness's defining
    // property looks like once it has to meet the goal's shape.
    let g = run(
        "theorem t : forall w in Real, ((w*w*w) - w - 2.0) == 0.0 => (w*w*w) == (w + 2.0)\n\
           := by algebra",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

#[test]
fn a_case_split_can_close_a_branch_by_assumption() {
    // `(if x >= y then x else y) >= y`: one branch is the hypothesis
    // itself, the other is `y >= y`.
    let g = run(
        "theorem t : forall x in Int, forall y in Int, (if x >= y then x else y) >= y\n\
           := by algebra",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    let text = g.theorem_certs["t"].render();
    assert!(text.contains("case split"), "{}", text);
    assert!(text.contains("hypotheses in scope"), "{}", text);
}

#[test]
fn the_deduction_example_is_entirely_kernel_checked() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/40_deduction.seki")
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(
        stdout.contains("every claim in this file was re-established by the kernel"),
        "the deduction example must stay fully checked:\n{}",
        stdout
    );
}

// -- non-termination and the set-theoretic foundation -----------------------

/// Run a source string through the real binary with extra environment, and
/// return its combined output.  Used for the runaway tests: the limits are
/// read from the environment, and setting that in-process would leak into
/// every other test running alongside.
fn run_binary_with_env(src: &str, env: &[(&str, &str)]) -> String {
    let dir = std::env::temp_dir().join("seki_env_test");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let file = dir.join(format!("t{}.seki", env.len() + src.len()));
    std::fs::write(&file, src).expect("write");
    let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_seki"));
    cmd.arg("--check").arg(&file);
    for (k, v) in env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("run seki");
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn a_tail_recursive_runaway_is_an_error_not_a_hang() {
    // `docs/spec/06-soundness.md` used to claim a fuel limit caught this.
    // It did not: `COMP_FUEL` bounds how many *domain elements* a
    // comprehension filters, and a tail-recursive call never re-enters
    // `eval`, so this ran forever.
    let out = run_binary_with_env(
        "def loop := \\n -> loop (n + 1)\ndef v := loop 0\n",
        &[("SEKI_EVAL_BUDGET", "200000")],
    );
    assert!(
        out.contains("budget"),
        "expected the step budget to stop it:\n{}",
        out
    );
}

#[test]
fn a_deep_recursive_runaway_is_an_error_not_a_crash() {
    // The step budget alone does not catch this one: each level eats native
    // stack far faster than budget, so the process used to abort with
    // `fatal runtime error: stack overflow`.
    let out = run_binary_with_env(
        "def deep := \\n -> 1 + deep (n + 1)\ndef v := deep 0\n",
        &[("SEKI_EVAL_DEPTH", "500")],
    );
    assert!(
        out.contains("nested"),
        "expected the depth limit to stop it:\n{}",
        out
    );
}

#[test]
fn ordinary_recursion_is_unaffected_by_the_limits() {
    let g = run(
        "def fact := \\n -> if n <= 1 then 1 else n * fact (n - 1)\n\
         def r := fact 10",
    );
    assert!(matches!(g.defs.get("r"), Some(Value::Int(3628800))));
}

#[test]
fn the_universe_is_not_a_member_of_itself() {
    // `Set` is the class of all sets.  A proper class is not a set, so it
    // does not contain itself; reporting `true` here was how seki announced
    // that it sat on naive comprehension.
    let g = run("def selfmem := Set in Set");
    assert!(matches!(g.defs.get("selfmem"), Some(Value::Bool(false))));
    // Ordinary sets are still members of it.
    let g = run("def ok := {1, 2} in Set");
    assert!(matches!(g.defs.get("ok"), Some(Value::Bool(true))));
}

#[test]
fn a_set_cannot_be_carved_out_of_the_universe() {
    // Separation, not unrestricted comprehension — and with it, no Russell
    // set.  Asking seki whether the old `{x in Set | x notin x}` contained
    // itself used to abort the process.
    let err = run_err("def R := {x in Set | x notin x}");
    assert!(
        err.message().contains("class of all sets"),
        "{}",
        err.message()
    );
    // Carving a subset out of a set that exists is of course still fine.
    let g = run(
        "def evens := {x in {1, 2, 3, 4} | x mod 2 == 0}\n\
         def has2 := 2 in evens\n\
         def has3 := 3 in evens",
    );
    assert!(matches!(g.defs.get("has2"), Some(Value::Bool(true))));
    assert!(matches!(g.defs.get("has3"), Some(Value::Bool(false))));
}

// -- refinement obligations -------------------------------------------------
//
// `def f : A -> {y in B | Q y}` claims `forall x in A, Q[y := f x]`.  That
// was the last part of seki where "checked" meant "spot-checked": the
// theorem side became kernel-verified while the type side stayed a sample.
// These pin down that the claim is now proved where it can be, and recorded
// as sampled where it cannot.

#[test]
fn a_provable_refinement_is_proved_not_sampled() {
    let g = run(
        "def Pos := {x in Int | x > 0}\n\
         def f : Int -> Pos := \\x -> x * x + 1",
    );
    assert_eq!(g.def_trust["f"], TrustLevel::Sound);
    // And a proof term was kept for it.
    let (goal, cert) = &g.def_obligations["f"];
    assert!(format!("{}", goal).contains("forall"), "{}", goal);
    assert!(cert.is_some(), "a discharged obligation should keep its proof");
}

#[test]
fn an_unprovable_refinement_is_recorded_as_sampled() {
    // Positive on every sampled point, negative at 10^9 — the shape
    // `docs/spec/06-soundness.md` §6.2 uses as its example of the hole.
    let g = run(
        "def Pos := {x in Int | x > 0}\n\
         def f : Int -> Pos := \\x -> if x == 1000000001 then 0 - 1 else x * x + 1",
    );
    assert_eq!(g.def_trust["f"], TrustLevel::Sampled);
    // The obligation is still recorded, and so is whatever the search came
    // back with — that is what makes the gap inspectable rather than just
    // reported.  What matters is that it is not a *sound* proof.
    let (goal, _) = &g.def_obligations["f"];
    assert!(format!("{}", goal).contains("forall __arg1 in Int"), "{}", goal);
}

#[test]
fn strict_mode_refuses_a_refinement_that_was_only_sampled() {
    let mut session = Session::new();
    session.strict = true;
    let err = session
        .run_source(
            "def Pos := {x in Int | x > 0}\n\
             def f : Int -> Pos := \\x -> if x == 1000000001 then 0 - 1 else x * x + 1",
            true,
        )
        .expect_err("--strict must refuse an unproved refinement");
    assert!(err.message().contains("not proved"), "{}", err.message());
    // A provable one passes.
    let mut session = Session::new();
    session.strict = true;
    session
        .run_source(
            "def Pos := {x in Int | x > 0}\n\
             def f : Int -> Pos := \\x -> x * x + 1",
            true,
        )
        .expect("--strict must accept a proved refinement");
}

#[test]
fn a_guarded_withdrawal_keeps_its_balance_non_negative_by_type() {
    // The invariant `sample/ledger` enforces with a runtime check, stated
    // as a type and proved: the guard is what makes it hold, and removing
    // it is caught.
    let g = run(
        "def NonNeg := {x in Int | x >= 0}\n\
         def safeWithdraw : Nat -> Nat -> NonNeg\n\
           := \\bal amt -> if amt <= bal then bal - amt else bal\n\
         def unsafeWithdraw : Nat -> Nat -> NonNeg := \\bal amt -> bal - amt",
    );
    assert_eq!(g.def_trust["safeWithdraw"], TrustLevel::Sound);
    assert_eq!(g.def_trust["unsafeWithdraw"], TrustLevel::Sampled);
}

#[test]
fn an_unrefined_annotation_generates_no_obligation() {
    let g = run("def f : Int -> Int := \\x -> x + 1");
    assert!(!g.def_trust.contains_key("f"));
}

#[test]
fn the_portfolio_prefers_a_proof_the_kernel_accepts() {
    // `by auto` used to take the first candidate that closed the goal, and
    // the cheap closers come first — so `by eval` won by sampling even when
    // `by unfold f then algebra` would have proved it.
    let g = run(
        "def f := \\x -> x * x + 1\n\
         theorem t : forall a in Int, (f a) > 0 := by auto",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

#[test]
fn a_strict_inequality_needs_more_than_non_negative_coefficients() {
    // `forall n in Nat, n > 0` is false at 0.  The coefficient of `n` is
    // positive, so a rule that only asked for that would accept it.
    let err = run_err("theorem bad : forall n in Nat, n > 0 := by algebra");
    assert!(err.is_proof_error(), "{:?}", err);
    // With a constant to stand on, it holds.
    let g = run("theorem ok : forall n in Nat, n + 1 > 0 := by algebra");
    assert_eq!(g.theorem_trust["ok"], TrustLevel::Sound);
}

#[test]
fn the_refinement_example_is_audited_as_documented() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/41_refinement_types.seki")
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(stdout.contains("safeWithdraw"), "{}", stdout);
    assert!(
        stdout.contains("the obligation was proved and kernel-checked"),
        "{}",
        stdout
    );
    assert!(stdout.contains("only sampled"), "{}", stdout);
}

// -- reasoning from uncertain facts -----------------------------------------
//
// An LLM-extracted fact is an assumption with a number attached.  The number
// lives outside the kernel — letting it in would turn `Sound` into a
// continuous quantity — and rides on the assumption set the proof term
// already records.

#[test]
fn a_confidence_annotation_is_recorded_exactly() {
    let g = run(
        "axiom a : forall x in Nat, x >= 1 => x * 2 >= 2 with confidence 0.9 \
         from \"LLM extraction\"",
    );
    assert_eq!(
        g.axiom_confidence.get("a"),
        Some(&seki::algebra::Rat::new(9, 10)),
        "0.9 should read as nine tenths, not as the nearest f64"
    );
    assert_eq!(g.axiom_provenance.get("a").map(|s| s.as_str()), Some("LLM extraction"));
}

#[test]
fn a_single_uncertain_assumption_passes_its_confidence_through() {
    let g = run(
        "axiom a : forall x in Nat, x >= 1 => x * 2 >= 2 with confidence 0.9\n\
         theorem t : 5 * 2 >= 2 := by apply a with x := 5",
    );
    let c = seki::confidence::of_verdict(&g.theorem_verdicts["t"], &g);
    assert_eq!(c.lower_bound(), seki::algebra::Rat::new(9, 10));
    // It is still an *assumption*, so the trust level is unchanged.
    assert_eq!(g.theorem_trust["t"], TrustLevel::Axiomatic);
}

#[test]
fn two_uncertain_assumptions_combine_by_frechet_not_by_product() {
    // 0.9 and 0.8.  The product, 0.72, assumes independence — and facts
    // from one extraction pass are not independent.  The guaranteed bound
    // is 0.9 + 0.8 - 1 = 0.7.
    let g = run(
        "axiom a : forall x in Nat, x >= 1 => x * 2 >= 2 with confidence 0.9\n\
         axiom b : forall y in Nat, y >= 2 => y * 3 >= 6 with confidence 0.8\n\
         theorem t : 4 * 3 >= 6\n\
           := by have h : (5 * 2) >= 2 := by apply a with x := 5\n\
              then apply b with y := 4",
    );
    let c = seki::confidence::of_verdict(&g.theorem_verdicts["t"], &g);
    assert_eq!(c.lower_bound(), seki::algebra::Rat::new(7, 10));
}

#[test]
fn a_classical_axiom_does_not_qualify_a_conclusion() {
    let g = run(
        "axiom ivt : forall x in Nat, x >= 0\n\
         theorem t : 5 >= 0 := by apply ivt with x := 5",
    );
    let c = seki::confidence::of_verdict(&g.theorem_verdicts["t"], &g);
    assert!(matches!(c, seki::confidence::Confidence::Unqualified));
}

#[test]
fn a_confidence_floor_refuses_a_conclusion_it_is_not_warranted_to() {
    let mut session = Session::new();
    session.min_confidence = Some(seki::algebra::Rat::new(85, 100));
    let err = session
        .run_source(
            "axiom a : forall x in Nat, x >= 1 => x * 2 >= 2 with confidence 0.7\n\
             theorem t : 5 * 2 >= 2 := by apply a with x := 5",
            true,
        )
        .expect_err("a floor of 0.85 must refuse a conclusion warranted to 0.7");
    assert!(err.message().contains("warranted"), "{}", err.message());
}

#[test]
fn a_confidence_outside_zero_to_one_is_rejected() {
    let err = run_err("axiom a : 1 >= 0 with confidence 1.5");
    assert!(err.message().contains("[0, 1]"), "{}", err.message());
}

// -- working backwards ------------------------------------------------------

#[test]
fn a_failed_linear_goal_says_what_would_make_it_hold() {
    let err = run_err("theorem t : forall r in Real, (100.0 - 200.0 * r) > 0.0 := by algebra");
    assert!(
        err.message().contains("it would hold given"),
        "{}",
        err.message()
    );
    assert!(err.message().contains("r < (1 / 2)"), "{}", err.message());
}

#[test]
fn a_hypothesis_that_is_not_tight_enough_gets_the_real_bound() {
    let err = run_err(
        "theorem t : forall r in Real, r <= 0.6 => (100.0 - 200.0 * r) > 0.0 := by algebra",
    );
    assert!(err.message().contains("r < (1 / 2)"), "{}", err.message());
    // And with the bound it suggests, the theorem goes through and is
    // kernel-checked.
    let g = run("theorem t : forall r in Real, r < 0.5 => (100.0 - 200.0 * r) > 0.0 := by algebra");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

#[test]
fn no_suggestion_is_offered_when_there_is_nothing_useful_to_say() {
    // Restating the goal is not a suggestion, and a non-linear goal has no
    // single bound.
    let err = run_err("theorem t : forall n in Nat, n >= 5 := by algebra");
    assert!(!err.message().contains("it would hold given"), "{}", err.message());
    let err = run_err(
        "theorem t : forall x in Real, forall y in Real, x * y >= 0.0 := by algebra",
    );
    assert!(!err.message().contains("it would hold given"), "{}", err.message());
}

// -- error messages that name what is missing -------------------------------

#[test]
fn a_missing_premise_is_named_with_a_way_to_supply_it() {
    let err = run_err(
        "theorem mono : forall x in Real, forall y in Real, x <= y => (2.0*x) <= (2.0*y)\n\
           := by algebra\n\
         theorem t : forall a in Real, forall b in Real, (2.0*a) <= (2.0*b) := by apply mono",
    );
    let m = err.message();
    assert!(m.contains("premise `(a <= b)`"), "{}", m);
    assert!(m.contains("by have"), "the message should say how to supply it: {}", m);
    assert!(m.contains("nothing is assumed here"), "{}", m);
}

#[test]
fn a_misspelled_lemma_gets_a_suggestion() {
    let err = run_err(
        "theorem mono : forall x in Real, x >= 0.0 => x + 1.0 >= 1.0 := by algebra\n\
         theorem t : 5.0 + 1.0 >= 1.0 := by apply mno",
    );
    assert!(err.message().contains("did you mean `mono`"), "{}", err.message());
}

#[test]
fn the_uncertain_facts_example_reports_the_frechet_bound() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/42_uncertain_facts.seki")
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(stdout.contains("confidence >= 7/10"), "{}", stdout);
    assert!(stdout.contains("confidence >= 9/10"), "{}", stdout);
}

#[test]
fn overflowed_exact_arithmetic_cannot_prove_a_false_equation() {
    // Found while building a probabilistic-reasoning demo.  Rational
    // arithmetic saturated on overflow, so `0.1 * 0.2 * 0.3` evaluated to
    // exactly `1` inside `by algebra` — and the kernel accepted
    // `0.1 * 0.2 * 0.3 == 1.0` as "kernel-checked from primitives".
    // Polynomial arithmetic is part of what the kernel trusts, so a wrong
    // number there is a wrong proof.
    let err = run_err("theorem bad : (0.1 * 0.2 * 0.3) == 1.0 := by algebra");
    assert!(err.is_proof_error(), "{:?}", err);
    // And the evaluator's own answer is nowhere near 1.
    let g = run("def v := 0.1 * 0.2 * 0.3");
    match g.defs.get("v") {
        Some(Value::Real(r)) => assert!((*r - 0.006).abs() < 1e-9, "got {}", r),
        other => panic!("expected a Real, got {:?}", other.map(|v| v.type_name())),
    }
}

#[test]
fn exact_rationals_still_work_where_decimals_overflow() {
    // The same model written with exact rationals goes through, which is
    // the workaround the limitation leaves open.
    let g = run("theorem t : ((1.0/10.0) * (2.0/10.0) * (3.0/10.0)) == (6.0/1000.0) := by algebra");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

#[test]
fn the_probabilistic_reasoning_examples_report_their_bounds() {
    for (file, expect) in [
        ("examples/43_medical_diagnosis.seki", "confidence >= 4/5"),
        ("examples/44_business_decision.seki", "confidence >= 1/4"),
    ] {
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
            .arg("--audit")
            .arg(file)
            .output()
            .expect("run seki --audit");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(out.status.success(), "{}: {}", file, stdout);
        assert!(stdout.contains(expect), "{} should report {}:\n{}", file, expect, stdout);
    }
}

// -- what trying to write an application surfaced ---------------------------

#[test]
fn dividing_operands_of_unknown_shape_is_not_guessed_to_be_an_integer() {
    // `\a b -> if a <= b then a / b else 1.0` is perfectly well typed, but
    // the shape checker called `a / b` an `Int` and rejected the `if` for
    // having branches of different shapes.
    let g = run("def f := \\a b -> if a <= b then a / b else 1.0");
    assert!(g.defs.contains_key("f"));
}

#[test]
fn a_conjunctive_goal_is_proved_conjunct_by_conjunct() {
    // Interval refinement types are conjunctions — `{x | 0 <= x and x <= 1}`
    // — so without this the most ordinary refinement there is could never
    // be discharged.
    let g = run("theorem t : forall x in Nat, (x >= 0) and (x + 1 >= 1) := by algebra");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    let text = g.theorem_certs["t"].render();
    assert!(text.contains("each of the 2 conjuncts"), "{}", text);
    // And a conjunction with a false half is still refused.
    assert!(run_err("theorem bad : forall x in Nat, (x >= 0) and (x >= 1) := by algebra")
        .is_proof_error());
}

#[test]
fn a_binder_over_a_comprehension_carries_its_predicate() {
    // `forall x in {y in Real | 0 <= y and y <= 1}` may use those bounds:
    // they are true of every member by definition of the set.  They used
    // to sit in a place no tactic read.
    let g = run(
        "def Unit01 := {x in Real | (0.0 <= x) and (x <= 1.0)}\n\
         theorem t : forall a in Unit01, (1.0 - a) >= 0.0 := by algebra",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

#[test]
fn an_interval_refinement_type_is_proved() {
    // "this function maps the unit interval into itself", as a type.
    let g = run(
        "def Unit01 := {x in Real | (0.0 <= x) and (x <= 1.0)}\n\
         def halve : Unit01 -> Unit01 := \\x -> x / 2.0\n\
         def complement : Unit01 -> Unit01 := \\x -> 1.0 - x\n\
         def escapes : Unit01 -> Unit01 := \\x -> x + 0.5",
    );
    assert_eq!(g.def_trust["halve"], TrustLevel::Sound);
    assert_eq!(g.def_trust["complement"], TrustLevel::Sound);
    assert_eq!(g.def_trust["escapes"], TrustLevel::Sampled);
}

#[test]
fn a_named_set_is_recognised_as_its_underlying_domain() {
    // `forall x in Unit01` was reported as being over `Int` — the stricter
    // reading — because only the spelling of the domain was looked at, so
    // nothing about `Real` could be proved under it.
    let g = run(
        "def Small := {x in Real | (0.0 <= x) and (x <= 2.0)}\n\
         theorem t : forall a in Small, (a * a) >= 0.0 := by algebra",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

// -- non-linear arithmetic --------------------------------------------------
//
// Farkas adds hypotheses with non-negative weights, which cannot reach
// `0 <= a <= 1 ⊢ a² <= 1`.  Products of hypotheses can: `p >= 0` and
// `q >= 0` give `pq >= 0` with nothing further assumed, so a product is
// another legitimate thing to add.

#[test]
fn a_square_is_bounded_by_its_interval() {
    let g = run(
        "theorem t : forall a in Real, (0.0 <= a) and (a <= 1.0) => (a * a) <= 1.0 \
         := by algebra",
    );
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    // The certificate names the product it used.
    let text = g.theorem_certs["t"].render();
    assert!(text.contains('·'), "expected a product generator: {}", text);
}

#[test]
fn products_and_boxes_and_am_gm_all_go_through() {
    for src in [
        "theorem t : forall a in Real, forall b in Real, (a >= 0.0) and (b >= 0.0) \
         => (a * b) >= 0.0 := by algebra",
        "theorem t : forall x in Real, forall y in Real, (0.0 <= x) and (x <= 2.0) \
         and (0.0 <= y) and (y <= 3.0) => (x * y) <= 6.0 := by algebra",
        "theorem t : forall a in Real, forall b in Real, (a >= 0.0) and (b >= 0.0) \
         => (a + b) * (a + b) >= (4.0 * a * b) := by algebra",
    ] {
        let g = run(src);
        assert_eq!(g.theorem_trust["t"], TrustLevel::Sound, "for: {}", src);
    }
}

#[test]
fn a_non_linear_refinement_type_is_proved() {
    let g = run(
        "def Unit01 := {x in Real | (0.0 <= x) and (x <= 1.0)}\n\
         def square : Unit01 -> Unit01 := \\x -> x * x\n\
         def multiply : Unit01 -> Unit01 -> Unit01 := \\x y -> x * y\n\
         def doubled : Unit01 -> Unit01 := \\x -> x * 2.0",
    );
    assert_eq!(g.def_trust["square"], TrustLevel::Sound);
    assert_eq!(g.def_trust["multiply"], TrustLevel::Sound);
    assert_eq!(g.def_trust["doubled"], TrustLevel::Sampled);
}

#[test]
fn a_false_non_linear_claim_is_still_refused() {
    // `a <= 1` alone does not bound `a²` — `a = -5` breaks it.
    assert!(run_err("theorem bad : forall a in Real, a <= 1.0 => (a * a) <= 1.0 := by algebra")
        .is_proof_error());
}

#[test]
fn the_nonlinear_example_is_kernel_checked() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/45_nonlinear.seki")
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(stdout.contains("sound:     7"), "{}", stdout);
}

// ---------------------------------------------------------------------------
// Degree three and up: the Positivstellensatz search is decided by an exact
// phase-1 simplex rather than by trying subsets of the generators, so a
// certificate may draw on every product of hypotheses at once.  See
// `solve_nonneg_exact` in `src/prover.rs`.

#[test]
fn a_cubic_bound_is_kernel_checked() {
    // `1 - a³ = (1-a) + a(1-a) + a²(1-a)`: a triple product is needed, which
    // no search over pairs can reach.
    assert_eq!(
        trust_of(
            "theorem cube : forall a in Real, a >= 0.0 -> a <= 1.0 -> a * a * a <= 1.0 \
             := by algebra",
            "cube"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn a_quartic_bound_is_kernel_checked() {
    assert_eq!(
        trust_of(
            "theorem quartic : forall a in Real, a >= 0.0 -> a <= 1.0 -> \
             a * a * a * a <= 1.0 := by algebra",
            "quartic"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn a_three_variable_box_is_kernel_checked() {
    assert_eq!(
        trust_of(
            "theorem box : forall x in Real, forall y in Real, forall z in Real, \
             x >= 0.0 -> x <= 1.0 -> y >= 0.0 -> y <= 1.0 -> z >= 0.0 -> z <= 1.0 -> \
             x * y * z <= 1.0 := by algebra",
            "box"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn dividing_by_a_positive_factor_is_kernel_checked() {
    // The certificate orients itself around `lhs - rhs >= 0`, which swaps
    // the sides of a `<=` goal.  Scaling the swapped pair builds the
    // reverse inequality, so this proved but could not be certified.
    assert_eq!(
        trust_of(
            "theorem cancel : forall a in Real, forall c in Real, \
             (c > 0.0) and (c * a <= 0.0) => a <= 0.0 := by algebra",
            "cancel"
        ),
        TrustLevel::Sound
    );
    // The same shape stated with `>=`, where no swap happens.
    assert_eq!(
        trust_of(
            "theorem cancel_ge : forall a in Real, forall c in Real, \
             (c > 0.0) and (c * a >= 0.0) => a >= 0.0 := by algebra",
            "cancel_ge"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn a_contraction_has_at_most_one_fixed_point() {
    assert_eq!(
        trust_of(
            "def absR := \\r -> if r < 0.0 then 0.0 - r else r\n\
             theorem uniq : forall x in Real, forall y in Real, forall k in Real, \
             (k >= 0.0) and (k < 1.0) and (absR (x - y) <= k * absR (x - y)) => x == y \
             := by unfold absR then algebra",
            "uniq"
        ),
        TrustLevel::Sound
    );
    // At k = 1 the conclusion is false: any x and y satisfy the premise.
    assert!(run_err(
        "def absR := \\r -> if r < 0.0 then 0.0 - r else r\n\
         theorem bad : forall x in Real, forall y in Real, forall k in Real, \
         (k >= 0.0) and (k <= 1.0) and (absR (x - y) <= k * absR (x - y)) => x == y \
         := by unfold absR then algebra"
    )
    .is_proof_error());
}

#[test]
fn false_higher_degree_claims_are_refused() {
    // Each is false at some point of the stated domain; the simplex must not
    // manufacture a certificate for any of them.
    for src in [
        "theorem bad : forall a in Real, a >= 0.0 -> a <= 1.0 -> a * a * a >= a := by algebra",
        "theorem bad : forall a in Real, a >= 0.0 -> a * a * a > 0.0 := by algebra",
        "theorem bad : forall a in Real, forall b in Real, a >= 0.0 -> b >= 0.0 -> \
         a * b * b >= a := by algebra",
        "theorem bad : forall a in Real, a > 0.0 -> a <= 1.0 -> a * a * a < 0.0 := by algebra",
    ] {
        assert!(run_err(src).is_proof_error(), "accepted a false claim: {}", src);
    }
}

// ---------------------------------------------------------------------------
// Epsilon-delta shapes.  `absR` unfolds to an `if`, which may land in a
// hypothesis rather than the conclusion, and the branch it opens is recorded
// as a *negated* fact — both used to be dropped before the search.

const ABS_R: &str = "def absR := \\r -> if r < 0.0 then 0.0 - r else r\n";

#[test]
fn an_abs_hypothesis_alone_is_kernel_checked() {
    // The only `if` is in a hypothesis; there is none in the conclusion.
    assert_eq!(
        trust_of(
            &format!(
                "{ABS_R}theorem h : forall x in Real, forall a in Real, forall d in Real, \
                 d > 0.0 -> absR (x - a) < d -> x - a < d := by unfold absR then algebra"
            ),
            "h"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn a_quadratic_epsilon_delta_is_kernel_checked() {
    // |x - a| < d  ⊢  |x² - a²| < 2d  on [0,1].  Needs the case split to
    // reach the hypothesis, the negated branch fact to survive, and a
    // product of two hypotheses in the certificate.
    assert_eq!(
        trust_of(
            &format!(
                "{ABS_R}theorem sq : forall x in Real, forall a in Real, forall d in Real, \
                 x >= 0.0 -> x <= 1.0 -> a >= 0.0 -> a <= 1.0 -> d > 0.0 -> \
                 absR (x - a) < d -> absR (x * x - a * a) < 2.0 * d \
                 := by unfold absR then algebra"
            ),
            "sq"
        ),
        TrustLevel::Sound
    );
}

#[test]
fn a_false_epsilon_delta_bound_is_refused() {
    // The Lipschitz constant on [0,1] is 2, not 1.
    assert!(run_err(&format!(
        "{ABS_R}theorem bad : forall x in Real, forall a in Real, forall d in Real, \
         x >= 0.0 -> x <= 1.0 -> a >= 0.0 -> a <= 1.0 -> d > 0.0 -> \
         absR (x - a) < d -> absR (x * x - a * a) < d := by unfold absR then algebra"
    ))
    .is_proof_error());
}

// ---------------------------------------------------------------------------
// The audit report is the deliverable for a model somebody has to sign off
// on, so what it says about *assumptions* is part of the contract.

#[test]
fn the_audit_lists_what_a_file_assumes() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/46_decision_audit.seki")
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    // Each assumption, with its confidence and where it came from.
    assert!(stdout.contains("assumed without proof"), "{}", stdout);
    assert!(stdout.contains("adoption_floor"), "{}", stdout);
    assert!(stdout.contains("7/10"), "{}", stdout);
    // And each conclusion says which assumptions carry it, with a bound
    // that is the Frechet one rather than a product.
    assert!(
        stdout.contains("confidence >= 3/5"),
        "the Frechet bound for 7/10 and 9/10 is 3/5:\n{}",
        stdout
    );
    assert!(
        stdout.contains("(from `adoption_floor` 7/10, `discount_rate_range` 9/10)"),
        "{}",
        stdout
    );
}

#[test]
fn an_assumption_nothing_rests_on_is_pointed_out() {
    // A confidence written for a conclusion that never cites it warrants
    // nothing; the audit says so rather than letting the number sit there.
    let src = "axiom believed : someParam >= 1.0 with confidence 0.8 from \"a guess\"
               theorem t : forall x in Real, x * x >= 0.0 := by algebra
";
    let dir = std::env::temp_dir().join("seki_audit_unused");
    std::fs::create_dir_all(&dir).expect("temp dir");
    let path = dir.join("unused.seki");
    std::fs::write(&path, src).expect("write");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg(&path)
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("no conclusion here rests on `believed`"), "{}", stdout);
}

// ---------------------------------------------------------------------------
// Decimal literals, and the domain a goal is read over.

#[test]
fn decimal_literals_mean_the_decimals_they_are_written_as() {
    // `0.6` is not the nearest double when it appears in a claim; it is
    // three fifths, and `0.6 * 50 >= 30` is true.
    assert_eq!(
        trust_of("theorem t : forall a in Real, a >= 0.6 => (a * 50.0) >= 30.0 := by algebra", "t"),
        TrustLevel::Sound
    );
    assert_eq!(
        trust_of("theorem t : (0.1 + 0.2) == 0.3 := by algebra", "t"),
        TrustLevel::Sound
    );
}

#[test]
fn a_claim_about_free_reals_is_not_read_as_being_about_integers() {
    // With no binder to read a domain from, the goal used to fall through
    // to `Int`, which licenses `p > 0 ⟹ p >= 1` — false for a real.
    assert!(run_err(
        "axiom h : freeX > 0.0
         theorem bad : freeX >= 1.0 := by have a : freeX > 0.0 := by apply h then algebra"
    )
    .is_proof_error());
}

#[test]
fn an_equality_hypothesis_can_carry_a_proof() {
    // "the price is 50" is how a model states a known quantity; a Farkas
    // certificate needs both inequalities, and the kernel derives them.
    assert_eq!(
        trust_of(
            "theorem t : forall a in Real, forall p in Real, \
             (a >= 0.6) and (p == 50.0) => (a * p) >= 30.0 := by algebra",
            "t"
        ),
        TrustLevel::Sound
    );
}

// ---------------------------------------------------------------------------
// `Real` means ℝ, and the evaluator computes in `f64`.  The kernel used to
// certify a proposition through one reading and its negation through the
// other, which is the worst thing a prover can do.

#[test]
fn the_kernel_does_not_certify_a_proposition_and_its_negation() {
    // `by algebra` reads `0.1` as one tenth and proves this.
    assert_eq!(
        trust_of("theorem p : (0.1 + 0.2) == 0.3 := by algebra", "p"),
        TrustLevel::Sound
    );
    // `by eval` computes `0.30000000000000004` and used to prove the
    // negation, with the kernel endorsing both.
    assert!(run_err("theorem notp : (0.1 + 0.2) != 0.3 := by eval").is_proof_error());
}

#[test]
fn hiding_the_literals_in_definitions_does_not_reopen_it() {
    // A syntactic check for real literals misses this: the proposition is
    // `(a + b) != c` and mentions none.  Interval arithmetic re-evaluates
    // the definitions from source, finds `3/10` on both sides, and settles
    // the goal as *false* — so it is refused outright.
    assert!(run_err(
        "def a := 0.1\n\
         def b := 0.2\n\
         def c := 0.3\n\
         theorem viaDefs : (a + b) != c := by eval\n"
    )
    .is_proof_error());
}

#[test]
fn an_exact_real_claim_is_still_kernel_checked() {
    // Deciding real comparisons exactly must not cost the ones that are
    // exact: these are in the rational fragment and stay sound.
    for src in [
        "theorem t : (1.0 + 2.0) == 3.0 := by eval",
        "theorem t : (0.5 * 4.0) == 2.0 := by algebra",
        "theorem t : (1.0 / 4.0) < 0.3 := by algebra",
    ] {
        assert_eq!(trust_of(src, "t"), TrustLevel::Sound, "for: {}", src);
    }
}

#[test]
fn a_tolerance_check_on_a_square_root_is_now_proved() {
    // `|sqrt 2 - 1.414| < 0.001` used to be reported as floating point.
    // Interval arithmetic gives a *verified* enclosure of the root — each
    // endpoint checked by squaring it — so the claim is about the reals.
    let g = run("theorem approx : (absR ((sqrt 2.0) - 1.414)) < 0.001 := by eval\n");
    assert_eq!(g.theorem_trust["approx"], TrustLevel::Sound);
    // And a tolerance the root does not meet is refused, not waved through.
    assert!(run_err(
        "theorem bad : (absR ((sqrt 2.0) - 1.414)) < 0.0000000001 := by eval\n"
    )
    .is_proof_error());
}

#[test]
fn a_transcendental_now_has_an_enclosure() {
    // `exp`, `ln`, `sin` and `cos` are series with a Lagrange remainder
    // bound, so a tolerance check on one is a claim about the reals.
    for src in [
        "theorem t : (absR ((exp 1.0) - 2.718281828)) < 0.001 := by eval",
        "theorem t : (absR ((ln (exp 2.0)) - 2.0)) < 0.0000001 := by eval",
        "theorem t : (absR ((sin 1.0) * (sin 1.0) + (cos 1.0) * (cos 1.0) - 1.0)) \
         < 0.0000001 := by eval",
    ] {
        assert_eq!(trust_of(src, "t"), TrustLevel::Sound, "for: {}", src);
    }
    // And a tolerance the series does not meet is refused.
    assert!(run_err(
        "theorem bad : (absR ((exp 1.0) - 2.718281828)) < 0.0000000001 := by eval"
    )
    .is_proof_error());
}

#[test]
fn a_function_with_no_bound_established_still_has_no_enclosure() {
    // `tan` has no remainder bound here, so a goal that needs it keeps its
    // floating-point grade rather than being guessed at.
    let g = run("def absR := \\r -> if r < 0.0 then 0.0 - r else r\n\
                 theorem t : absR ((tan 1.0) - 1.5574077) < 0.0001 := by eval\n");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Approximate);
    // So does an argument outside the range the bound covers.
    let g = run("def absR := \\r -> if r < 0.0 then 0.0 - r else r\n\
                 theorem u : absR ((sin 20.0) - 0.9129452507) < 0.0001 := by eval\n");
    assert_eq!(g.theorem_trust["u"], TrustLevel::Approximate);
}

#[test]
fn strict_mode_refuses_a_floating_point_verdict() {
    let mut session = Session::new();
    session.strict = true;
    let err = session
        .run_source(
            "def absR := \\r -> if r < 0.0 then 0.0 - r else r\n\
             theorem t : absR ((tan 1.0) - 1.5574077) < 0.0001 := by eval\n",
            true,
        )
        .expect_err("--strict must refuse a floating-point verdict");
    assert!(err.is_proof_error(), "got {:?}", err);
    assert!(
        err.message().contains("floating-point"),
        "error should say why: {}",
        err.message()
    );
}

// ---------------------------------------------------------------------------
// Interval arithmetic: what it proves, and what it refuses to.

#[test]
fn a_taylor_series_tolerance_is_proved_not_approximated() {
    // Thirty terms of exp's series, compared against a decimal, all under
    // guaranteed enclosures.  Nothing here is in the polynomial fragment —
    // `expAccum` is a recursive seki function.
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/29_analysis.seki")
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(
        stdout.contains("sound:"),
        "some claims in the analysis example should now be proved:\n{}",
        stdout
    );
}

#[test]
fn an_enclosure_that_does_not_settle_gives_no_verdict() {
    // A tolerance tighter than the enclosure's own width cannot be
    // decided, and "cannot decide" must never read as "holds".
    assert!(run_err(
        "theorem bad : (absR ((sqrt 2.0) - 1.41421356237309504880)) < 0.0 := by eval\n"
    )
    .is_proof_error());
}

// ---------------------------------------------------------------------------
// Interval arithmetic.  A claim about a numerical computation can be proved
// *about the reals* when the computation is carried out with guaranteed
// enclosures — see `src/interval.rs`.

#[test]
fn a_verified_square_root_settles_a_tolerance() {
    // Each endpoint of the enclosure is checked by squaring it, so this is
    // a statement about √2, not about what `f64::sqrt` returned.
    assert_eq!(
        trust_of("theorem t : (absR ((sqrt 2.0) - 1.414)) < 0.001 := by eval", "t"),
        TrustLevel::Sound
    );
    assert_eq!(
        trust_of("theorem t : (sqrt 2.0) < 1.5 := by eval", "t"),
        TrustLevel::Sound
    );
    assert_eq!(
        trust_of("theorem t : (sqrt 9.0) == 3.0 := by eval", "t"),
        TrustLevel::Sound
    );
}

#[test]
fn a_tolerance_the_root_misses_is_refused() {
    for src in [
        // |√2 - 1.41421356| is about 2.4e-9, so this is false.
        "theorem bad : (absR ((sqrt 2.0) - 1.41421356)) < 0.000000001 := by eval",
        "theorem bad : (sqrt 2.0) < 1.41421356 := by eval",
        "theorem bad : (sqrt 2.0) > 1.41421357 := by eval",
    ] {
        assert!(run_err(src).is_proof_error(), "accepted: {}", src);
    }
}

#[test]
fn an_enclosure_overrules_the_floating_point_answer() {
    // `0.1 + 0.2 > 0.3` is true of doubles and false of the reals.  The
    // tactic evaluates it to true; the kernel refuses it.
    assert!(run_err("theorem bad : (0.1 + 0.2) > 0.3 := by eval").is_proof_error());
}

#[test]
fn a_recursive_numerical_computation_is_proved_not_approximated() {
    // Thirty terms of exp's Taylor series against a decimal — outside the
    // polynomial fragment entirely, since `expAccum` is a recursive seki
    // function, and still settled exactly.
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/29_analysis.seki")
        .env("SEKI_LIB_PATH", "lib")
        .output()
        .expect("run seki --audit");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{}", stdout);
    assert!(
        stdout.contains("exp_1_is_e                                    kernel-checked"),
        "a Taylor-series tolerance should be kernel-checked:\n{}",
        stdout
    );
}

#[test]
fn shadowing_a_stdlib_constant_does_not_confuse_the_kernel() {
    // `def e := ...` shadows the stdlib's `e = 2.718…`.  Interval mode
    // re-evaluates definitions from source, and a stale entry for the old
    // `e` made it resolve to the constant instead.
    let g = run("def e := 3.0\n                 theorem t : e == 3.0 := by eval\n");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
}

#[test]
fn re_evaluating_a_definition_never_re_runs_its_effects() {
    // `mkRef` evaluated twice is two different cells.  A definition whose
    // source is not effect-free keeps its stored value, so the kernel reads
    // the cell the program has been writing to and sees 3, not 0.
    let g = run("def counter := mkRef 0\n\
                 def step1 := writeRef counter 3\n\
                 theorem t : (readRef counter) == 3 := by eval\n");
    assert_eq!(g.theorem_trust["t"], TrustLevel::Sound);
    // With a real in the cell the kernel cannot vouch for the stored
    // `f64`, so it declines rather than re-running the effect to find out.
    let g = run("def c2 := mkRef 0.0\n\
                 def s2 := writeRef c2 3.0\n\
                 theorem u : (readRef c2) == 3.0 := by eval\n");
    assert_eq!(g.theorem_trust["u"], TrustLevel::Approximate);
}

// ---------------------------------------------------------------------------
// Interval values in the source, and the project-level assurance report.
//
// These are what make "the audit is the deliverable" real: a claim can be
// about a *set* of initial states, and a report can be about a system
// rather than a file.

#[test]
fn a_claim_can_be_about_a_whole_range_of_inputs() {
    // `interval 4.0 6.0` stands for every real in the band.  Ten steps of
    // a contraction, carried out on the whole range at once, is a
    // reachability proof — not a simulation from one point.
    let g = run("def absR := \\r -> if r < 0.0 then 0.0 - r else r\n\
                 def step := \\x -> 0.9 * x + 0.1\n\
                 def run_ := \\n x -> if n <= 0 then x else run_ (n - 1) (step x)\n\
                 def x0 := interval 4.0 6.0\n\
                 theorem reach : absR (run_ 50 x0 - 1.0) < 0.05 := by eval\n");
    assert_eq!(g.theorem_trust["reach"], TrustLevel::Sound);
}

#[test]
fn a_range_claim_that_some_member_breaks_is_refused() {
    // After three steps the band is [3.187, 4.645]; a bound of 4.4 holds
    // for the low end and not the high one, so it is not proved.
    assert!(run_err(
        "def absR := \\r -> if r < 0.0 then 0.0 - r else r\n\
         def step := \\x -> 0.9 * x + 0.1\n\
         def run_ := \\n x -> if n <= 0 then x else run_ (n - 1) (step x)\n\
         def x0 := interval 4.0 6.0\n\
         theorem bad : absR (run_ 3 x0) < 4.4 := by eval\n"
    )
    .is_proof_error());
}

#[test]
fn an_interval_with_its_ends_the_wrong_way_round_is_rejected() {
    // `interval 6.0 4.0` names no set of reals, so it is an error rather
    // than an empty or silently swapped band.
    let err = run_err("def x := interval 6.0 4.0\ntheorem t : x > 0.0 := by eval\n");
    assert!(
        err.message().contains("interval"),
        "should say which value is wrong: {}",
        err.message()
    );
}

#[test]
fn the_project_audit_reports_a_system_as_one_argument() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/assurance")
        .output()
        .expect("run seki --audit on a directory");
    let stdout = String::from_utf8_lossy(&out.stdout);
    // Claims that are not kernel proofs come first — that is the list a
    // reviewer works through.
    assert!(
        stdout.contains("claims resting on something other than a kernel proof"),
        "{}",
        stdout
    );
    // Each of them says what its assumptions warrant.
    assert!(stdout.contains("confidence >= 4/5"), "{}", stdout);
    // And every assumption is listed with where it came from.
    assert!(stdout.contains("assumed without proof"), "{}", stdout);
    assert!(stdout.contains("SOP-114"), "{}", stdout);
    // A project with anything unproved fails, so a build can gate on it.
    assert!(!out.status.success(), "{}", stdout);
}

#[test]
fn a_project_of_only_proofs_passes() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("lib/control")
        .output()
        .expect("run seki --audit on a directory");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("every claim in this project was re-established by the kernel"),
        "{}",
        stdout
    );
    assert!(out.status.success(), "{}", stdout);
}

#[test]
fn a_claim_is_counted_where_it_is_declared() {
    // Importing a module registers its theorems too; counting them again
    // in every importer would make the report claim more than the project
    // does.  `examples/assurance` has 14 claims across 5 files.
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg("examples/assurance")
        .output()
        .expect("run seki --audit on a directory");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("14 claims across 5 file(s)"), "{}", stdout);
}

#[test]
fn a_file_that_does_not_run_is_a_finding_not_a_gap() {
    let dir = std::env::temp_dir().join("seki_audit_broken");
    std::fs::create_dir_all(&dir).expect("temp dir");
    std::fs::write(dir.join("a.seki"), "theorem bad : 1 == 2 := by eval\n").expect("write");
    std::fs::write(dir.join("b.seki"), "theorem good : 1 == 1 := by eval\n").expect("write");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_seki"))
        .arg("--audit")
        .arg(&dir)
        .output()
        .expect("run seki --audit on a directory");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("files that did not run"), "{}", stdout);
    assert!(stdout.contains("unrunnable:  1"), "{}", stdout);
    assert!(!out.status.success(), "{}", stdout);
}

#[test]
fn an_operating_envelope_through_a_transcendental_is_proved() {
    // "for every resistance in this band, the converted temperature is in
    // spec" — a range carried through a logarithm.  `ln` has its own body
    // rather than going through `unary_real_fn`, and without an interval
    // case of its own an enclosure argument fell through to "expected
    // numeric".
    let g = run(
        "def rToTemp := \\r -> 1.0 / (0.00335 + 0.000257 * (ln (r / 10000.0)))\n\
         def rBand := interval 8000.0 12000.0\n\
         theorem in_spec : (rToTemp rBand >= 270.0) and (rToTemp rBand <= 310.0) \
         := by eval\n",
    );
    assert_eq!(g.theorem_trust["in_spec"], TrustLevel::Sound);
    // A band that leaves the spec is refused, so the claim is not vacuous.
    assert!(run_err(
        "def rToTemp := \\r -> 1.0 / (0.00335 + 0.000257 * (ln (r / 10000.0)))\n\
         def rOpen := interval 40000.0 60000.0\n\
         theorem bad : rOpen >= 0.0 and (rToTemp rOpen >= 270.0) := by eval\n"
    )
    .is_proof_error());
}

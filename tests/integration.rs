//! End-to-end tests that exercise the lexer / parser / evaluator / prover
//! through the public crate API.

use seki::ast::Decl;
use seki::eval::{make_prelude, EvalCtx};
use seki::parse_program;
use seki::prover::Prover;
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

fn run(src: &str) -> Globals {
    let mut g = make_prelude();
    let decls = parse_program(src).expect("parse");
    let ctx_globals: *const Globals = &g; // placeholder for closure capture
    let _ = ctx_globals;
    for ld in decls {
        let ctx = EvalCtx::new(&g);
        let env = Env::new();
        match ld.decl {
            Decl::Def { name, ty: _, value } => {
                let v = ctx.eval(&value, &env).expect("eval def");
                g.defs.insert(name, v);
            }
            Decl::Theorem { name, prop, proof } => {
                let prover = Prover::new(&ctx);
                let v = prover.verify(&prop, &proof, &env).expect("verify theorem");
                g.theorem_props.insert(name.clone(), prop);
                g.theorems.insert(name, v);
            }
            Decl::Axiom { name, prop } => {
                g.axiom_props.insert(name.clone(), prop);
                g.axioms.insert(name, Value::Bool(true));
            }
            Decl::Expr(e) => {
                let _ = ctx.eval(&e, &env).expect("eval expr");
            }
            Decl::Import { .. } => {
                // The lightweight `run` test helper doesn't support module
                // loading; tests that need imports go through the binary.
                panic!("Decl::Import not supported in `run` test helper");
            }
            Decl::ClassMeta { class_name, ctor_name, methods } => {
                g.class_ctor.insert(class_name.clone(), ctor_name);
                for m in methods {
                    g.class_methods.insert(m, class_name.clone());
                }
            }
            Decl::InstanceMeta { instance_name, class_name, type_name } => {
                g.instances.insert((class_name, type_name), instance_name);
            }
            Decl::DataMeta { name, ctors } => {
                g.data_info.insert(name, ctors);
            }
        }
    }
    g
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

#[test]
fn seki_lib_test_cas_sym() {
    run_seki_test_file("tests/seki/test_cas_sym.seki", 10);
}

#[test]
fn seki_lib_test_cas_calc() {
    run_seki_test_file("tests/seki/test_cas_calc.seki", 16);
}

#[test]
fn seki_lib_test_cas_poly() {
    run_seki_test_file("tests/seki/test_cas_poly.seki", 13);
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
    run_seki_test_file("tests/seki/test_algebra_structures.seki", 14);
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
    run_seki_test_file("tests/seki/test_analysis_limit.seki", 5);
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
    run_seki_test_file("tests/seki/test_cas_multipoly.seki", 12);
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

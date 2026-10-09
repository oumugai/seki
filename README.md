# seki

**English** | [日本語](README.jp.md)

A set-theory based proof language that is also a programming language.
Written in Rust, zero external dependencies, a single binary.

**The unit of seki is not a "proof" but "a claim and the grade of its evidence."**

Running a computation and making a claim about that computation are the same
act, and the toolchain reports, claim by claim, **what kind of evidence it
obtained**. The deliverable is the table that `seki --audit` prints; a
`theorem` is just the means of producing one of its rows.

```seki
def consume := \tokens cost -> if tokens >= cost then tokens - cost else tokens

theorem consume_never_goes_negative
  : forall tokens in Real, forall cost in Real,
      (tokens >= 0.0) and (cost >= 0.0) => consume tokens cost >= 0.0
  := by unfold consume then algebra
```

`consume` is ordinary code. The only thing added is the `theorem`. Get the
boundary wrong (write `tokens > 0.0` instead of `tokens >= cost`) and a
handful of representative test cases **all still pass** — while this theorem
fails:

```
proof error: by algebra (then-branch of `if (tokens > 0)`):
  cannot prove (tokens - cost) >= 0 over Real
```

A test says "it worked for this input." A theorem says "it holds **for every
input in this range**."

## `--audit` — what is proved, what is computed, what is assumed

```
$ seki --audit examples/assurance/system.seki

theorem                                       how it was verified
------------------------------------------------------------------------------
calibration_stays_in_spec                     kernel-checked from primitives
control_effort_within_rating                  axiom `disturbance_bounded`
                                              confidence >= 9/10 (from `disturbance_bounded` 9/10)
displayed_temperature_is_trustworthy          axiom `sensor_drift_bounded`
                                              confidence >= 4/5 (from `sensor_drift_bounded` 4/5)
gain_envelope                                 kernel-checked from primitives
```

Trust is a five-level lattice. The bottom two are explicitly marked as
**able to let a false claim through** — seki does not ban unsound tactics, it
**grades and tracks them**. That is the difference from a pure proof system,
and it is what lets seki also be a practical language.

| Level | Meaning | Shown as |
|---|---|---|
| `sound` | The kernel re-established it from primitive inference rules | (no mark) |
| `axiomatic` | The proof is correct but rests on an `axiom` | `[axiomatic]` |
| `unchecked` | The tactic closed the goal but produced no proof term | `[unchecked — no proof term]` |
| `approximate` | Decided in floating point — **can accept a false claim** | `[approximate — floating point]` |
| `sampled` | A finite sample of an infinite domain — **not a proof** | `[sampled — NOT a proof]` |

`--strict` rejects anything below `sound`, and `--min-confidence 0.8` puts a
floor under the confidence of the assumptions. Pass a directory and you get one
report for the whole system, starting with the claims that rest on something
other than a proof (that list is what a reviewer actually reads, so it is not
buried under the good news). If weak claims remain, the exit code is non-zero,
so it works as a build gate.

```
$ seki --audit examples/services

claims resting on something other than a kernel proof
------------------------------------------------------------------------------
  axiomatic   serial_availability_meets_slo  (sla.seki)
              axiom `auth_availability`; axiom `cdn_availability`; axiom `db_availability`
              confidence >= 13/20 (from `auth_availability` 9/10, ...)

assumed without proof
------------------------------------------------------------------------------
  auth_availability     9/10 — ベンダー SLA + 12か月の実測 (2025-09〜2026-08)
  db_availability       4/5 — 自社運用、計画停止を除外した集計

==============================================================================
18 claims across 5 file(s), 3 assumption(s)
  sound:       17
  axiomatic:   1
```

(The provenance strings in the examples are in Japanese: "vendor SLA + 12
months of measurements" and "in-house operations, excluding planned
downtime".)

## Three ways to say "for every value in this set"

seki has three mechanisms for the same job, and `--audit` records **which one
carried each claim**.

| Method | How you write it | Reach | Cost |
|---|---|---|---|
| Symbolic | `forall x in Real, hyp => concl` + `by algebra` | Polynomial relations up to degree 4. **Exact** | Cannot leave polynomials |
| Numeric | `lo .. hi` / `center +- tol` + `by eval` | **Any computation**, including recursion, branches, `exp`/`ln`/`sin`/`cos` | Enclosures widen (dependency) |
| Enumeration | finite set + `by eval` | Finite domains | Becomes a sample on infinite ones |

```seki
-- Symbolic: polynomial, so it is decided exactly
theorem gain_box : forall a in Real, forall b in Real,
  (a >= 0.0) and (a <= 1.0) and (b >= 0.0) and (b <= 1.0) => a * b <= 1.0 := by algebra

-- Numeric: contains a logarithm, so it is not polynomial. Carry the whole range through the proof
def rToTemp := \r -> 1.0 / (0.00335 + 0.000257 * (ln (r / 10000.0)))
theorem temp_in_spec
  : (rToTemp (8000.0 .. 12000.0) >= 270.0) and (rToTemp (8000.0 .. 12000.0) <= 310.0)
  := by eval

-- You can also claim the analysis is tight enough to be conclusive
theorem enclosure_is_tight : width (evolve 50 (22.5 +- 7.5)) < 0.2 := by eval
```

The numeric method computes with **guaranteed enclosures** (`src/interval.rs`).
Every operation rounds outward, so an enclosure can only grow, and a comparison
answers only when the whole range decides it. `exp`/`ln`/`sin`/`cos` are series
bounded by the Lagrange remainder; outside the range where the bound is
guaranteed, they **refuse rather than estimate**.

`width` matters because it lets you **claim that the enclosure did not blow
up**. Without it you cannot tell "met the spec" apart from "the enclosure
happened to fit."

## Separating search from checking

A tactic saying "proved" is not a proof. Tactics **generate** a proof term, and
a small **kernel** that never calls a tactic re-establishes it from primitive
inference rules. Search is hard and can be buggy; checking is easy, and it is
the only part that has to be right
([docs/spec/06-soundness.md](docs/spec/06-soundness.md)).

```
$ seki --proof examples/13_advanced_tactics.seki abs_int_nonneg
theorem abs_int_nonneg : (forall x in Int, ((if (x >= 0) then x else (- x)) >= 0))
case split on the goal's first `if`:
  when the condition holds:
    this is one of the hypotheses in scope
  when it does not:
    `(- x)` - `0` = ((x < 0)) (over Int)

kernel verdict: every step re-established from primitives
```

The kernel evaluates through `EvalCtx::finite_only`, so it **structurally
cannot accept sampling of an infinite domain**. The TCB (kernel + rewrite +
unfold + interval) is **4,974 lines**, 17% of the roughly 28,700-line
toolchain. The TCB is treated not as "smaller is nicer" but as a **budget**:
every new feature is judged by whether it grows what has to be trusted.

On the day it was introduced, the kernel found a **real soundness bug** in
`by algebra` — for `f n = -5`, `forall n in Nat, f n >= 0` was being proved.

## Track assumptions instead of erasing them

Not "prove everything," but "you may assume — as long as the assumption is
carried all the way to the conclusion."

```seki
axiom db_availability : dbA >= 0.9990
  with confidence 0.8 from "in-house operations, excluding planned downtime"
```

Confidences are combined with the **Fréchet lower bound**
`max(0, Σpᵢ − (n−1))`, not by multiplication. `0.9 × 0.8 = 0.72` assumes
independence, and facts that came out of the same extraction pass are not
independent. Probabilities are kept out of the kernel — putting them in would
turn `sound` into a continuous quantity and "kernel-verified" would stop
meaning anything.

## Failures return information

A proof usually fails not because the claim is false but because an
assumption is missing.

```
$ seki capacity.seki
proof error: by algebra: cannot prove (perNode * nodes) >= rps over Real
  it would hold given `(perNode >= 625)` — add it as a hypothesis ...
```

5000 rps ÷ 8 nodes = 625. seki runs Farkas backwards to find the bound and
picks the **weakest** one (the bound is a ratio of two unknowns, so this needs
the Charnes–Cooper transformation). For nonlinear goals it asks the prover
directly. Contradictory suggestions are dropped, since ex falso would "prove"
anything from them.

When an enclosure cannot decide a claim, you also get **the width and the
reason**:

```
interval arithmetic does not settle this claim
  ([-1, 1] and [1/2, 1/2] overlap — the left enclosure is 2 wide).
  An enclosure widens wherever a value appears more than once, so this
  shows neither that the claim holds nor that it fails
```

The point is that it reads as "**this method does not decide it**," not as
"this is false."

## Limits — with names and reasons

```
$ for f in $(find examples tests/seki lib -name '*.seki'); do
    seki --audit "$f" | grep -oE '^  [a-z]+: +[0-9]+'
  done | awk -F'[: ]+' '{t[$2]+=$3} END {for (k in t) print k, t[k]}'

sound        1148
unchecked      22
sampled        20
axiomatic      16
approximate     8
```

- **All 8 `approximate`** claims are **interval dependency in iterative
  algorithms** (the wrapping effect). Newton's step `x - (x³-8)/(3x²)`
  mentions `x` three times, so the enclosure widens where the real iteration
  contracts. Closing them needs the interval Newton method, which grows the
  TCB further.
- **Most of the 22 `unchecked`** claims are `by induction` steps (the kernel
  checks the base case, but step normalization has no witness format yet).
- **The 20 `sampled`** claims are sample checks over infinite domains and are
  **not proofs**. `--strict` rejects them.
- When the initial condition is a set, `by algebra` cannot leave polynomials
  and intervals widen through dependency. The middle ground (interval Newton,
  mean-value forms) is not implemented yet.

## Quick start

```sh
cargo build --release                                # Rust 1.70+, zero dependencies
cargo run -- examples/04_proofs.seki                 # run a file
cargo run -- --audit examples/services               # audit a project
cargo run -- -e 'theorem t : 2 + 2 == 4 := by eval'  # one-liner
cargo run                                            # REPL
```

## Tactics

| Tactic | Kind | Use |
|---|---|---|
| `by eval` | closer | Reduce the proposition (`sound` only for finite domains / exact rationals / intervals) |
| `refl` | closer | Structural equality |
| `by algebra` / `by linarith` | closer | Polynomial normalization + Positivstellensatz (products of hypotheses, degree 4), antisymmetry, division by positive quantities |
| `by induction` | closer | Structural induction over Nat / List / Tree / any `data` |
| `by strong_induction <N>` | closer | Strong induction with configurable depth |
| `by decide` | closer | Force a decision on propositions that reduce to Bool |
| `by auto` | closer | Portfolio search over tactics |
| `by apply L [with x := e]` | closer | Modus ponens — cite a theorem/axiom |
| `by assumption` | closer | The conclusion is already a hypothesis |
| `by have h : P := <proof>` | transformer | Cut rule (build up forwards) |
| `by witness v := <term>` | transformer | Existential introduction — without it ε-δ can be stated but not proved |
| `by obtain c from L` | transformer | Existential elimination |
| `by unfold f` | transformer | One step of β-unfolding of a definition |
| `by intros` | transformer | Strip the leading `forall` |
| `by simp [l1, l2]` | both | Chain equational theorems as rewrite rules |
| `tac1 then tac2 ...` | combinator | Composition |

## seki as a language

This README has mostly been about proofs, but seki is **an ordinary working
programming language**. `lib/` has 653 `def`s against 52 `theorem`s; it is not
a math library.

- **Sets are types** — any set `T` is a type, and `v : T` essentially means
  `v in T`. `Bool == {false, true}` is a literal set equality, provable by
  `refl`.
- **The stdlib is written in seki itself** — List / Tree / Option / Result /
  Rat are built as tagged pairs. The Rust layer provides only minimal
  primitives.
- **ADTs and `match`**, `data` declarations, error propagation with `?`,
  modules (`import`), dependent types `(x : A) -> B(x)`, Σ types, type classes,
  type inference, termination checking.
- **Systems features** — strings, file I/O, `Ref`, `Dict`, time, randomness,
  bit operations, process execution, JSON, TCP, HTTP (codec / client /
  `httpServe`), atomic integers and real concurrency (`spawn` / `join` /
  channels), FFI (dlopen), a bytecode VM, an LSP server.
- **Symbols are words** — `forall`, `exists`, `in`, `union`, `subset`,
  `times`, and so on. No Unicode symbols.

Type annotations are proved too. `def f : A -> {y in B | Q y}` is the claim
"for any argument, the result satisfies `Q`," and it goes through the same
prover and the same kernel as a theorem.

## What it is good for

Domains where (a) a mix of proof, computation and assumption is unavoidable,
and (b) someone acts differently depending on which one it was.

- **Verifying operating envelopes** — prove, on the code as you normally wrote
  it, that the spec holds wherever inputs, parameters and initial state fall
  within their ranges
- **Assurance cases** — the output of `--audit DIR` becomes a fragment of a
  safety argument ([`examples/assurance/`](examples/assurance/))
- **Invariants in systems development** — conservation of money, resource
  ceilings, deadline budgets, capacity planning, SLA composition
  ([`examples/services/`](examples/services/))
- **A verification layer for LLM output** — reason from facts that carry
  confidences, and get back a lower bound on each conclusion's confidence plus
  the assumptions that are missing

Not good for: **mathematics** (the answer should be binary there and grades do
not help — Lean's design is the right one). **Ordinary testing** (if nobody
reads the grades, it is just a slow assert).

## Layout

```
seki/
├── src/             Rust implementation
│   ├── kernel.rs      proof-term checking (TCB)
│   ├── interval.rs    guaranteed enclosures (TCB)
│   ├── rewrite.rs     rewriting and case splits (TCB)
│   ├── unfold.rs      definition unfolding (TCB)
│   ├── prover.rs      tactics (search — not trusted)
│   ├── abduce.rs      inferring missing assumptions
│   ├── confidence.rs  Fréchet lower bound
│   └── stdlib.seki    auto-loaded stdlib
├── lib/             reusable seki modules (analysis / control / algebra / cas / numeric / ui)
├── examples/        walking tour (01–46) + assurance/ + services/
├── sample/          small service-style apps (calc / wordcount / ledger / todo_api)
├── tests/           Rust integration tests + seki tests mirroring lib/
└── docs/            documentation
```

## Documentation

The documentation is currently written in Japanese.

**For users**: [docs/tutorial.md](docs/tutorial.md) · [docs/cheatsheet.md](docs/cheatsheet.md) · [docs/cookbook.md](docs/cookbook.md)

**Reference**: [docs/language.md](docs/language.md) · [docs/proofs.md](docs/proofs.md) · [docs/spec/](docs/spec/)

**The soundness argument**: [docs/spec/06-soundness.md](docs/spec/06-soundness.md) —
what is sound, what is not, and why it was designed that way. Real bugs found
by the kernel are recorded there too.

**For implementers**: [docs/internals.md](docs/internals.md)

## Weaknesses of this design

The five-level lattice **only stands on honesty**. Each boundary between levels
is a place where an overclaim can hide. Examples actually found during
development:

- `Real` had two readings, ℝ and `f64`, and the kernel accepted **both**
  `0.1 + 0.2 == 0.3` and its negation
- `certify` in `by witness` did not run the tactic, so false goals came out as
  "proved [sampled]"
- Integer discreteness was missing on the certificate side, so equalities
  coming out of the else branch of `if i < r` got no certificate

There are only two defenses: `--strict`, and **continuing to attack your own
system**. That is why `tests/integration.rs` contains tests that line up false
propositions and check that they are rejected.

## License

[MIT](LICENSE)

# 5. 証明戦術

seki は **9 種類のタクティク + コンビネータ** を持ちます。それぞれの
意味論と健全性条件をまとめます。

タクティクは `theorem` の `:=` の後に `by <tactic>` 形式で書きます。
複数を `then` で合成できます。

```
theorem t : P := by tac1 then tac2 then tac3
```

## 5.1 `by eval`

**意味**: 命題を完全簡約して `Bool::true` になるか確認する。

**健全性**: 列挙集合 / 内包の有限ドメインに対して健全。
無限ドメイン上の `forall` は `SAMPLE_BOUND` (200) でのサンプル検査になり
**健全ではない**。

```seki
theorem t1 : 1 + 1 == 2 := by eval                    -- ✅
theorem t2 : forall x in {1,2,3}, x > 0 := by eval     -- ✅
theorem t3 : forall n in Nat, n + 1 > 0 := by eval     -- 🟡 sampled
```

## 5.2 `refl`

**意味**: 命題が `Refl: x == x` 形に構造一致するか。**型項としても使える** (Curry-Howard)。

**健全性**: ✅ 完全に健全 (構造的等価のみ)。

```seki
theorem t : 42 == 42 := refl
```

## 5.3 `by algebra`

**意味**: 多項式正規化 + 符号解析 + 定数 div/mod + PSD 2 次形式判定。
無限ドメインの多項式恒等式 / 不等式を扱える。

**健全性**: ✅ `Int` / `Rat` 上の多項式について健全。`Real` は扱わない。

```seki
theorem distrib : forall (a b c) in Int, a * (b + c) == a * b + a * c
    := by algebra
theorem cauchy : forall (a b) in Int, a*a + b*b >= 2 * a * b
    := by algebra
```

## 5.4 `by induction`

**意味**: 構造帰納法。`Nat` / `List` / `Tree` / user `data` ADT に対応。
recursive constructor の引数は IH (帰納仮説) として扱う。

**健全性**: ✅ 構造帰納法は健全 (整列性原理 + ADT の有限構築可能性に依存)。

```seki
def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)
theorem nn : forall xs in (List Int), listLen xs >= 0 := by induction
```

## 5.5 `by strong_induction`

**意味**: 深さ 2 の強帰納法 (`P(n-1) ∧ P(n-2) ⊢ P(n)`)。Fibonacci など。

**健全性**: ✅ Nat 上で健全。深さ 3 以上は未対応 (Phase 7 候補)。

```seki
def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)
theorem fib_nn : forall n in Nat, fib n >= 0 := by strong_induction
```

## 5.6 `by simp` / `by simp [theorem1, theorem2]`

**意味**: 既存の theorem を方向付き書換え規則として連鎖適用。
AC-canonicalization により可換和 / 可換積に対応 (対称規則も oscillate しない)。

**健全性**: ✅ 各 rewrite 規則自体が健全な theorem なので chain も健全。

```seki
theorem t : x + 0 == x := by simp [add_zero]
```

## 5.7 `by unfold f`

**意味**: 関数 `f` の定義を 1 段 β-展開する transformer。
通常は closer (`eval`, `algebra`, ...) と組み合わせる。

**健全性**: ✅ 定義の展開は意味保存。

```seki
def square := \x -> x * x
theorem t : square 3 == 9 := by unfold square then eval
```

## 5.8 `by intros`

**意味**: 先頭の `forall x in S, P(x)` を剥がして `x` を free var として
証明文脈に入れる transformer。

**健全性**: ✅ 全称除去は健全。

```seki
theorem t : forall n in Nat, n + 0 == n
    := by intros then algebra
```

## 5.9 `by decide`

**意味**: 命題を強制的に `Bool` に落として真偽を判定。
古典論理を仮定 (排中律と LEM 系)。

**健全性**: ✅ Bool に reduce できるならば健全。それ以外はエラー。

## 5.10 `by linarith`

**意味**: 線形不等式の決定手続き。`by algebra` のサブセットだが軽量。
Phase 5 で **SMT-lite** (single-variable Fourier-Motzkin) が追加された
(`linarithProve` builtin として exposed)。

**健全性**: ✅ 線形整数 / 有理数算術に対して健全
(property test `linarith_never_proves_a_falsehood` で 400 例検証)。

```seki
theorem t : forall (x y) in Int, x > 0 and y > 0 => x + y > 0
    := by linarith
```

## 5.11 証明項 (Curry-Howard)

タクティクなしで Curry-Howard 風に書ける場合:
- `forall x in S, P(x)` は関数として、適用すると証明を返す
- `exists x in S, P(x)` は witness + 証明のタプル

```seki
theorem t : forall x in Nat, x == x := \x -> refl
theorem e : exists x in Nat, x > 5 := (6, refl)  -- 略式
```

## 5.12 タクティク合成 (`then`)

```
proof := tac1 then tac2 then tac3
```

`tac1` で命題を変形し、`tac2` でさらに変形し、最後の `tacN` (closer) で
閉じる。慣用例:

```seki
theorem mul_add : forall (x y z) in Int, x * (y + z) == x * y + x * z
    := by intros then algebra
```

## 5.13 健全性の総まとめ

| 戦術 | 種別 | 健全性 |
|---|---|---|
| `eval` | closer | ✅ 有限のみ |
| `refl` | closer / 項 | ✅ |
| `algebra` | closer | ✅ Int / Rat 上の多項式 |
| `induction` | closer | ✅ 構造帰納 |
| `strong_induction` | closer | ✅ Nat 深さ 2 |
| `simp` | both | ✅ 既存定理の連鎖 |
| `unfold` | transformer | ✅ 定義展開 |
| `intros` | transformer | ✅ 全称除去 |
| `decide` | closer | ✅ Bool reduce |
| `linarith` | closer | ✅ 線形 |
| Curry-Howard 項 | closer | ✅ |

タクティク 9 種 (decide を含む 10 種) すべて、想定範囲内では健全。
**全体としての健全性の弱点** は型システムの sample-based dep type check
であり、タクティクではない。`06-soundness.md` 参照。

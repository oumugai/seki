# 9. テスト哲学 — 「点」ではなく「集合全体の振る舞い」

> *xUnit 流の例示テストは seki でも書けるが、それは集合論ベース言語の*
> *強みを活かしていない。seki でテストを書くということは、その関数が*
> ***入力集合全体でどう振る舞うか** を記述することである。*

## 9.1 検証の 3 階層

seki では「テスト」は強さの異なる 3 つの形で書ける。

### 階層 1 — 完全証明 (✅ 健全、無限域)

特定の `forall` を **`by algebra` / `by induction` / `by strong_induction`** で
証明する。任意の Int / Nat / List / Tree について成立する。

```seki
theorem total_preserved
  : forall (a b amt) in Int, (a - amt) + (b + amt) == a + b
  := by algebra
```

これは「**1 つの取引で全アカウント合計は不変**」を **全 Int 領域で証明** している。
入力数 ≈ ∞。これより強いテストは原理的に存在しない。

### 階層 2 — 有限完全 (✅ 健全、列挙された集合のみ)

`forall x in {finite set}, P x` を **`by eval`** で決定する。

```seki
theorem fp_matches_expected_on_range
  : forall x in {0 - 5, 0 - 4, 0 - 3, 0 - 2, 0 - 1, 0, 1, 2, 3, 4, 5},
      evalAt "x" x fp == evalAt "x" x (parseSym "3 * pow x 2 - 2")
  := by eval
```

これは **11 点全部** で記号微分の正しさを **証明** する。一個の theorem で
11 個の点アサーションを統合している。

### 階層 3 — 性質列挙 (🟡 列挙されたケースのみ)

ランタイムで「リストに与えた入力すべてに対して assertion が成立する」と確認する。
有限完全との違い: 静的 theorem ではなく実行時 `Result`、入力に副作用結果も
混ぜられる、出力を集合に属しているか確かめられる。

```seki
def multiples_of_6 := {-30, -24, -18, -12, -6, 0, 6, 12, 18, 24, 30}

def test_fpp_in_set :=
    forAllInList [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]
        (\x -> assertMember (eval_fpp x) multiples_of_6)
```

これは **f''(x) ∈ 6の倍数集合** という性質を集合論的に表現している。

### 階層 0 — 点での例示 (❌ 弱い、避けるべき)

```seki
def test_fpp_at_2 := assertEq 12 (eval_fpp 2)   -- ← これは避ける
```

これは **「f''(2) = 12」しか言っていない**。一般性が全くない。
**唯一の正当な用途**: 仕様書のドキュメント目的、または階層 1-3 で表現できない
ピンポイントなレグレッションテスト。

## 9.2 階層を選ぶ手順 (decision rule)

書こうとしている test について、以下を順番に問う:

1. **`by algebra` / `by induction` / `by linarith` で完全証明できるか?**
   - 多項式恒等式? → `by algebra` (階層 1)
   - 構造帰納で済む? → `by induction` (階層 1)
   - 線形整数不等式 (一変数)? → `by linarith` (階層 1)
   - **できれば階層 1 を選ぶ。これより強いテストは無い。**
2. 不可能なら **`forall x in {小さな代表集合}, P x` を `by eval`** で?
   - `evalAt`、stdlib 経由の関数評価など、関数呼出を含む性質はここ
   - **階層 2 を選ぶ。点 5 個より 11 点の forall theorem が安い。**
3. 不可能なら **`forAllInList xs f`** で動的 property test
   - 副作用 (Ref 読書きなど) を含む、テスト fixture が必要、ADT の構造的検査
   - **階層 3 を選ぶ。例示の集まりとして書く。**
4. それでも不可能なら点 assertion (階層 0)
   - **避けるべきだが、ドキュメンタリー / regression test として最小限**

## 9.3 例: 旧 vs 新 (`sample/calc/`)

旧 `tests.seki` (xUnit 流):

```seki
theorem fp_at_neg2 : evalAt "x" (0 - 2) fp == Some 10 := by eval
theorem fp_at_neg1 : evalAt "x" (0 - 1) fp == Some 1  := by eval
theorem fp_at_0    : evalAt "x" 0       fp == Some (0 - 2) := by eval
theorem fp_at_1    : evalAt "x" 1       fp == Some 1  := by eval
theorem fp_at_2    : evalAt "x" 2       fp == Some 10 := by eval
-- 5 個の theorem、5 点だけカバー
```

新 `tests_property.seki` (property-first):

```seki
theorem fp_matches_expected_on_range
  : forall x in {0 - 5, 0 - 4, 0 - 3, 0 - 2, 0 - 1, 0, 1, 2, 3, 4, 5},
      evalAt "x" x fp == evalAt "x" x (parseSym "3 * pow x 2 - 2")
  := by eval
-- 1 個の theorem、11 点をカバー、「予想多項式と一致」を明示
```

しかも「**fp は何の多項式と等しいか**」が theorem の中で表現されている (`parseSym
"3 * pow x 2 - 2"`)。旧版は **値が一致する** を示すが、それが「**3x² - 2** だから
一致する」というセマンティクスを伝えない。

## 9.4 集合論的アサーション

階層 3 では、`Bool` 値の `==` ではなく、**集合操作** で性質を表現する:

| 性質 | seki 表現 |
|---|---|
| 値が想定範囲にある | `assertMember v expected_set` |
| 出力部分集合 ⊆ 入力部分集合 | `assertSubset out_set in_set` |
| 順序非依存等価 | `assertSetEq a b` |
| すべての要素が refinement に属する | `forAllInList xs (\x -> assertMember x Pos)` |
| 重複を含まない (count = unique count) | `assertEq (length xs) (length (toSet xs))` |

例: HTTP ステータスコード集合の検証 (`sample/todo_api/tests.seki`):

```seki
def validStatuses := {200, 201, 204, 400, 404}

def test_all_statuses_valid :=
    forAllInList all_responses
        (\r -> assertMember (statusOf r) validStatuses)
```

これは「**全レスポンスのステータスは valid 集合に属する**」という universally-
quantified claim を、有限なレスポンスリストに対して decide している。

## 9.5 他言語との比較

| 言語/フレームワーク | 階層 1 (完全) | 階層 2 (有限完全) | 階層 3 (property) | 階層 0 (点) |
|---|---|---|---|---|
| **seki** | ✅ `by algebra` | ✅ `forall` + `by eval` | ✅ `forAllInList` | ✅ `assertEq` |
| pytest | ❌ | ❌ | 🟡 Hypothesis (外部) | ✅ |
| RSpec | ❌ | ❌ | 🟡 (外部) | ✅ |
| Jest | ❌ | ❌ | 🟡 (外部) | ✅ |
| QuickCheck (Haskell) | 🟡 limited | ❌ | ✅ | ✅ |
| Lean / Coq | ✅ | ✅ | 🟡 | ✅ |
| F\* | ✅ | ✅ | 🟡 | ✅ |

**seki は 4 階層すべてを言語ネイティブで提供する** 数少ない言語のひとつ。
特に階層 1 (`by algebra` の射程) は Lean / F\* と並ぶ。

## 9.6 結論: seki のテストは「振る舞い全体の記述」

xUnit 流の例示テスト (`assertEq output_at_specific_input expected`) は seki でも
書けるが、これは **集合論ベース言語の能力の使い損ない**。

seki でテストを書く際の **デフォルト** は:

1. **「すべての入力で何が成立するか」を `forall` で記述**
2. **可能なら `by algebra` / `by induction` で証明、不可能なら `by eval` で**
   **有限ドメインを decide、最後の手段が `forAllInList` での列挙**
3. **出力の性質は `集合所属` / `部分集合関係` で表現**

これにより:
- テストは **行数が減り** (5 個の点 theorem → 1 個の forall theorem)
- カバレッジは **増える** (5 点 → 11 点)
- 意図は **明確化** ("3x² - 2 と一致" が theorem に直接書ける)
- 健全性は **強化** (階層 1 で証明されたものは完全)

これが「**点ではなく振る舞い全体でテストする**」の意味。

## 9.7 移行戦略

既存コードベースに対しては:

1. 既存の point-wise theorem (`assertEq`、`by eval` での点単一) を残しつつ、
2. **`forall x in S, ...` または `forAllInList xs (\x -> ...)`** で再表現する
   property 版を追加
3. 新しい test は **property-first** で書く
4. 段階的に point assertion を property に統合する

`sample/calc/` では `tests.seki` (旧) と `tests_property.seki` (新) が共存し、
property 版が **同じ性質をより少ない行数 + より広いカバレッジで** 検証している
ことを示している。

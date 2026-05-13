# 定理証明ガイド

このドキュメントは seki で命題を表現し検証する方法を説明する。

## 目次

1. [基本概念: 命題と証明](#1-基本概念-命題と証明)
2. [theorem の構文](#2-theorem-の構文)
3. [9 つの証明戦術 + 合成](#3-9-つの証明戦術--合成)
4. [反例の検出](#4-反例の検出)
5. [axiom の使い所](#5-axiom-の使い所)
6. [パターン集](#6-パターン集)
7. [限界と運用上の注意](#7-限界と運用上の注意)

---

## 1. 基本概念: 命題と証明

seki では**命題は `Bool` に評価される式**。`Prop` 型は `Bool` の別名。

```seki
2 + 2 == 4                     -- 命題: 真
forall x in Bool, not (not x) == x   -- 命題: 真 (二重否定除去)
exists x in {1,2,3}, x > 5     -- 命題: 偽 (反例: どの要素も≤3)
```

これらを単独で書くと REPL では `true` / `false` が表示される。`theorem` で名前付きの**検証済み事実**として登録すると、後段で再利用できる (現状はマーカーとしての登録のみで、自動証明連携はない)。

---

## 2. theorem の構文

```seki
theorem NAME : PROPOSITION := PROOF
```

- `NAME` は識別子。グローバル名前空間に登録される。
- `PROPOSITION` は `Bool` に評価される式 (= 命題)。
- `PROOF` は次のいずれか:
  - `by eval` / `refl` / `by algebra` / `by induction` / `by strong_induction` / `by simp [...]` / `by unfold f` / `by intros` / 任意の式 (証明項)
  - **合成**: `by t1 then t2 [then t3 ...]` (`then` で連鎖)

成功すれば `theorem NAME ✓ proved`、失敗すれば `proof error: ...` が出る。失敗時は登録されない。

---

## 3. 9 つの証明戦術 + 合成

| 戦術 | 種別 | 用途 | 健全性 | 定義域 |
|---|---|---|---|---|
| `by eval` | closer | 命題を簡約 | 有限のみ健全 | 有限集合 |
| `refl` | closer | 等式の構造的等価 | 健全 | 任意 |
| `by algebra` | closer | 多項式正規化 + 符号解析 + div/mod (定数) | **健全** | **ℤ / ℕ 全体 (無限)** |
| `by induction` | closer | Nat / List / Tree 上の構造帰納法 (==, ≤, ≥, <, >) | **健全** | **無限** |
| `by strong_induction` | closer | 深さ2 強帰納法 (Fibonacci 等) | **健全** | **ℕ 全体 (無限)** |
| `by simp [l1, ...]` | both | 既存等式 theorem の書換え規則として連鎖適用 | 規則の健全性に依存 | 規則 LHS にマッチするサブ式 |
| `by unfold f` | transformer | 関数 f を 1 段 β-展開 (closer と組合せる) | 健全 (定義は信頼) | 任意 |
| `by intros` | transformer | 先頭の forall を剥がし free var 化 | 健全 | 任意 |
| 証明項 | closer | Curry-Howard 風 | 部分的 | 有限定義域 |
| **`t1 then t2`** | combinator | 戦術を順次適用、最後の `tn` は closer | 各戦術の合成 | — |

**closer** は goal を閉じる戦術、**transformer** は goal を書き換えるだけで closer を後続に必要とする。`by simp` は両性質を持ち、規則で goal が `true` まで畳めれば closer、途中で止まれば transformer として次戦術に渡される。

### 3.1 `by eval` — 命題を簡約して `true` を確認

`by eval` は単純な評価ベースの戦術ですが、内部で **集合の定義からの自明判定** を行うため、想像以上に強力です。具体的には:

- **内包の述語が body と一致**: `forall x in {y in S | P(y)}, P(x)` は要素を列挙せず即座に `true` 判定 (述語と body が α-同値)。
- **多項式関係の代数判定**: `forall x in Nat/Int, polynomial-relation` は `by algebra` と同じ符号解析で判定。`by eval` だけで `forall n in Nat, n >= 0` や `forall x in Int, x*x >= 0` が**ℕ/ℤ 全体に対して**証明される。
- **vacuous truth**: 空集合上の forall は `true`、空集合上の exists は `false`。

これらが効かない場合のみ、要素の列挙にフォールバックします (atomic 無限集合では SAMPLE_BOUND までの標本検証で**健全ではない**点に注意)。



最も基本的な戦術。命題を seki の評価器で評価し、結果が `Value::Bool(true)` であれば証明成立。

```seki
theorem two_plus_two : 2 + 2 == 4 := by eval

theorem demorgan
  : forall a in Bool, forall b in Bool,
        not (a and b) == (not a or not b)
  := by eval
```

#### 何ができるか

- 算術等式・不等式
- ブール代数の恒等式 (`Bool` は 2 元なので完全列挙)
- **有限定義域上の** `forall` / `exists`
- 集合の所属・部分集合・濃度に関する具体的な事実

#### できないこと

- 無限定義域 (`Nat`, `Int`) 上の `forall` の真の証明 → SAMPLE_BOUND までの標本検証になり、健全ではない
- 含意 `P -> Q` の一般証明 (関数値の挙動に依存するので決定不能)
- 帰納法を本質的に必要とする命題

### 3.2 `refl` — 等式の両辺を簡約して構造的等価を確認

命題が `a == b` 形のときに使う。両辺を別々に評価し、`value_eq` で構造的に比較する。

```seki
theorem dbl_3 : (3 + 3) == 6 := refl

theorem set_idem : ({1, 2, 3} union {1, 2, 3}) == {1, 2, 3} := refl

theorem demorgan_set
  : (U diff (A intersect B)) == ((U diff A) union (U diff B))
  := refl
```

`by eval` でも同じ命題は通るが、`refl` は意図 (「これは reflexivity による等式」) を明示できる利点がある。

### 3.3 `by algebra` — 多項式正規化による無限域の証明

`forall` で量化された等式 `lhs == rhs` を、両辺を**多項式の正規形 (sum-of-monomials)** に変換して比較する。等しければ「ℤ 上の環恒等式」として証明完了 — つまり**任意の整数値**で成立する。

```seki
theorem add_comm
  : forall a in Int, forall b in Int, a + b == b + a
  := by algebra                              -- ℤ × ℤ 全体で成立

theorem distrib
  : forall a in Int, forall b in Int, forall c in Int,
        a * (b + c) == a * b + a * c
  := by algebra

theorem cube_expansion
  : forall x in Int,
        (x + 1) * (x + 1) * (x + 1) == x*x*x + 3*x*x + 3*x + 1
  := by algebra
```

#### 対応する関係

`==`, `!=`, `<`, `<=`, `>`, `>=` の 6 つすべて。

#### 不等式の判定

- **Nat 上**: 多項式の係数がすべて非負なら ≥0、定数項 > 0 かつ全係数 ≥0 なら > 0。
- **Int 上**:
  1. 全変数の指数が偶数 (例: `x²+y²`) かつ係数が非負 → ≥ 0
  2. 多項式の **2 次部分が半正定値** (PSD) かつ低次部が非負 → ≥ 0
     ([Sylvester 基準](https://en.wikipedia.org/wiki/Sylvester%27s_criterion): 対称行列の主対角小行列式がすべて非負)
  - これにより Cauchy-Schwarz の特殊版 `a²+b² ≥ 2ab`、完全平方 `(x+y)² ≥ 0` 等が証明可能

```seki
theorem cauchy : forall a in Int, forall b in Int,
    a*a + b*b >= 2 * a * b := by algebra

theorem psd_3var : forall a in Int, forall b in Int, forall c in Int,
    a*a + b*b + c*c >= 0 := by algebra
```

#### 整数除算と mod (定数除数)

`e / c` および `e mod c` で `c` が整数定数の場合、多項式範囲内で扱える:

```seki
theorem half_double : forall n in Int, (2 * n) / 2 == n := by algebra
theorem div_floor   : forall n in Int, (3 * n + 6) / 3 == n + 2 := by algebra
theorem even_mod    : forall n in Int, (2 * n) mod 2 == 0 := by algebra
theorem odd_mod     : forall n in Int, (2 * n + 1) mod 2 == 1 := by algebra
```

仕組み: `(2n) / 2` を polynomial 化する際、係数 2 が約数 2 で割り切れるので `n` に化ける。
`(2n+1) mod 2` は係数を 2 で reduce して `(0n + 1) = 1`。

#### 何ができないか

- 変数除数 (`/n`, `mod n`): 値を不透明原子として扱うのみで、両辺で textually 同一でない限り何も推論しない
- 高次 (3 次以上) の不等式 — 2 次までの PSD 判定が限界
- 関数適用を含む等式は両辺で対称な場合のみキャンセル

#### 健全性

`by algebra` は**任意の値で成立する代数恒等式**だけを通す。これが本物の "infinite-case verification" として機能する所以。

### 3.4 `by induction` — Nat / List / Tree 上の構造帰納法

定義域に応じて自動的に適切な帰納原理が選ばれる:

| 定義域 | 基底 | ステップ |
|---|---|---|
| `Nat` | `P(0)` | `P(k) → P(k+1)` |
| `List T` | `P([])` | `P(ys) → P(cons x ys)` |
| `Tree T` | `P(leaf)` | `P(l) ∧ P(r) → P(node l v r)` |

体は `==`, `<=`, `>=`, `<`, `>` のいずれの**関係式**でもよい。

**ステップ判定の仕組み**: 等号と不等号で判定式が異なる:

| 関係 | ステップ条件 (`lhs_diff` ≡ lhs(succ) − lhs(prev) など) |
|---|---|
| `==` | `lhs_diff == rhs_diff` (多項式等価) |
| `>=`, `>` | `lhs_diff >= rhs_diff` (帰納仮定の保存) |
| `<=`, `<` | `lhs_diff <= rhs_diff` |

`>` のステップが **`>=` で済む**のは、帰納仮定 `lhs(k) > rhs(k)` が整数では `≥1` のスラックを与えるため。

```seki
def sum := \n -> if n == 0 then 0 else n + sum (n - 1)

theorem gauss
  : forall n in Nat, 2 * sum n == n * (n + 1)
  := by induction
-- 基底: 2 * sum 0 = 0,  0 * (0+1) = 0      ✓
-- 帰納段: lhs(k+1) - lhs(k) = 2*(k+1),
--         rhs(k+1) - rhs(k) = (k+1)(k+2) - k(k+1) = 2(k+1)  ✓
```

#### Nat の検証例 (`examples/12_infinite_proofs.seki`)

- Gauss 公式 `2*Σk = n(n+1)`
- 平方和 `6*Σk² = n(n+1)(2n+1)`
- 立方和 `4*Σk³ = (n(n+1))²`

#### List 構造帰納法

```seki
def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)
theorem nn  : forall xs in (List Int), listLen xs >= 0 := by induction

def appendL := \xs ys -> if null xs then ys else cons (head xs) (appendL (tail xs) ys)
theorem app_id : forall xs in (List Int), listLen (appendL xs nil) == listLen xs := by induction
```

仕組み: `xs := cons x ys` を代入し、組込関数 `null/head/tail` の cons 上の簡約 (`null (cons _ _) → false` 等) を実行してから、関数定義を unfold。残った式の差を多項式判定する。

#### Tree 構造帰納法

```seki
def treeSize := \t ->
    if isLeaf t then 0
    else 1 + treeSize (treeLeft t) + treeSize (treeRight t)

theorem ts_nn : forall t in (Tree Int), treeSize t >= 0 := by induction
```

仕組み: `t := node l v r` を代入し、組込 `isLeaf/treeVal/treeLeft/treeRight` の node 上の簡約を実行してから unfold。両子木 `l`、`r` の帰納仮定が同形の不透明原子としてキャンセルされる。

### 3.5 `by strong_induction` — 強帰納法 (深さ 2)

複数前段を参照する漸化式 (Fibonacci 等) のための深さ 2 の強帰納法。`P(0)` と `P(1)` を基底として確認したあと、`P(k+2)` のステップを **直接** 多項式判定する。`f k` と `f (k+1)` は不透明な非負原子として扱われる (帰納仮定として ≥ 0)。

```seki
def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)

theorem fib_nonneg : forall n in Nat, fib n >= 0 := by strong_induction
-- 基底: fib 0 = 0 ≥ 0,  fib 1 = 1 ≥ 0
-- 帰納段: fib (k+2) = fib (k+1) + fib k = (≥0) + (≥0) ≥ 0
```

通常の `by induction` ではここで step が一段の差分に還元できないため成立しないが、`by strong_induction` なら直接 polynomial sign 判定で処理できる。

### 3.6 `by simp` — 等式の連鎖書換え

既存の **proven な等式 theorem (および axiom)** を方向付き書換え規則 (LHS → RHS) として収集し、目標 (goal) に対して反復的に適用する。

```seki
theorem add_zero  : forall a in Int, a + 0 == a := by algebra
theorem mul_zero  : forall a in Int, a * 0 == 0 := by algebra
theorem mul_one   : forall a in Int, a * 1 == a := by algebra

-- 連鎖適用: (y * 1) + 0 → y + 0 → y
theorem t : forall y in Int, (y * 1) + 0 == y := by simp
```

`forall x1 in T1, ..., forall xn in Tn, lhs == rhs` 形式の theorem は `lhs[xi := ?]` を **メタ変数パターン** として登録され、目標式中で構造的にマッチするサブ式を `rhs` に書き換える。

#### 形式

- **`by simp`**: 全ての proven theorem / axiom (= 等式形のもの) を規則として使う
- **`by simp [lemma1, lemma2, ...]`**: 指定した補題のみを使う (typo・スコープ確認が確実)

#### 成功条件

書換えの結果が次のいずれかであれば成功:

1. `Bool(true)` リテラルに reduce
2. `a == b` で両辺が **alpha-同値** (構造的に同じ式)
3. eval で `true` を返す (定数まで簡約された場合)

#### 限界

- **対称的な規則** (`add_comm : a + b == b + a` など) は書換えが両側で発火して oscillation を起こす。`simp` 内では不動点が見つからないため、対称規則だけで通せる目標は限定的。
- **条件付き等式** (forall の述語に追加の仮定 — 例: "a > 0 ⇒ ...") は未対応。
- マッチングは **alpha-renaming なし**: `Lambda { params, body }` は引数名が完全一致する必要あり。

#### いつ使うか

- 既に証明済みの基本恒等式が複数あって、それらの **組み合わせ** で証明したい
- `by algebra` が直接通せない (e.g. 関数定義の unfold が要る) が、補助 lemma を経由すれば通る場合
- Lean / mathlib の `@[simp]` lemma に近い感覚で「補助補題の集積場所」として使いたい

### 3.7 `by unfold f` — 関数定義の 1 段 β-展開

`by unfold f` は goal AST 内に現れる `f a1 ... ak` をすべて `body[params := args]` に置換する **transformer**。単独で goal を閉じることもあるが、典型的には `then` で他の closer と組み合わせる:

```seki
def sq := \x -> x * x

theorem sq_is_mul : forall n in Int, sq n == n * n
    := by unfold sq then algebra
-- 1. unfold sq: sq n を n*n に展開 → goal は `n*n == n*n`
-- 2. algebra: 多項式恒等式として証明
```

#### 性質

- **1 段のみ**: 置換結果に含まれる `f` の再帰呼び出しは展開されない。これにより再帰関数も無限ループしない。
- **すべての出現を同時に展開**: `f a` と `f b` が同じ goal にあれば一度に処理される。
- **shadow を尊重**: 内側の lambda が `f` と同名のパラメータを持てば、その lambda 内は展開しない。

#### いつ使うか

- 関数定義の β-簡約を `by algebra` や `by simp` の前段として走らせたい
- 抽象を剥がして「中身は単なる多項式」を露わにしたい
- ヘルパ関数 (`sq`, `double`, `cube` 等) を経由した不等式・等式の証明

### 3.8 `by intros` — forall 束縛子の剥離

先頭の `forall x in S, ...` をすべて剥がして、束縛変数を自由変数として残す **transformer**。`by algebra` などの closer は元から先頭 forall を strip するので、`by intros` 単独はしばしば冗長だが、`by simp` と組み合わせると効く:

```seki
theorem add_zero : forall a in Int, a + 0 == a := by algebra
theorem mul_one  : forall a in Int, a * 1 == a := by algebra

theorem t : forall y in Int, (y * 1) + 0 == y
    := by intros then simp
-- 1. intros: forall を剥がして `(y * 1) + 0 == y`
-- 2. simp: mul_one で `y * 1 → y`、add_zero で `y + 0 → y`、両辺一致
```

### 3.9 タクティク合成 `t1 then t2`

戦術を `then` で連結して順次適用できる。各戦術は (a) goal を閉じる (Closed)、(b) goal を書き換えて次に渡す (NewGoal)、または (c) 失敗、のいずれか。

```seki
theorem complex : forall n in Int, sq n + 0 == n * n
    := by intros then unfold sq then algebra
```

#### 規則

- **左から右** に評価する。
- 途中の戦術が goal を閉じれば成功 (残りは無視される)。
- 最後の戦術が **必ず closer** でなければならない。transformer で終わると `tactic sequence ended with an unclosed goal` エラー。
- ネストした `then` (` (t1 then t2) then t3 `) は禁止 — フラットな列で書く。

#### 典型パターン

| 形 | 用途 |
|---|---|
| `intros then algebra` | algebra が strip 済みでも明示的に剥がしたいとき |
| `unfold f then algebra` | f を展開して多項式に落とす |
| `intros then unfold f then algebra` | forall + 展開 + 多項式 |
| `intros then simp [l1, l2]` | 仮定を free 化してから補助補題で書換え |
| `unfold f then simp [l1]` | 展開後の式に simp 規則を適用 |
| `simp [l1] then algebra` | 補助補題で部分的に書換え、残りは algebra |

### 3.10 証明項 (Curry-Howard 風)

第 3 の戦術は、命題のかたちに応じて意味が変わる。

#### `forall x in S, P(x)` の証明 = 関数

S の各要素に対して P を満たす根拠を返す関数。検証器は

1. 証明項を評価して関数値であることを確認
2. S を列挙して各要素に証明項を適用 (副作用なし)
3. 各要素 `e` で命題本体 `P[x := e]` を `true` に評価できるか確認

```seki
theorem all_pos
  : forall x in {1, 2, 3, 4, 5}, x > 0
  := \x -> x      -- 関数なら何でもよい (中身は使われない)
```

証明項の本体に意味はなく、**関数であることと有限列挙の検証が成立すること**が条件。本格的な型システムでは `\x -> proof_of_P_at_x` のような依存的な型付けが要るが、現状の seki ではプレースホルダ程度の役割。

#### `exists x in S, P(x)` の証明 = 証拠 (witness)

具体的な要素を提示する。検証器は:

1. 証明項を評価して値 `w` を得る
2. `w in S` を確認
3. `P[x := w]` を評価して `true` を確認

```seki
def Range := {1, 2, 3, ..., 20}
theorem prime_in_range : exists p in Range, isPrime p
  := 7                       -- 7 が素数であることを示す witness
```

witness が範囲外、あるいは命題を満たさない場合は `proof error`。

#### その他の命題

`a in S` や複合論理式に対しては、証明項は単に「タグ」として扱われ、命題は普通に評価される (実質 `by eval` と同じ)。

```seki
theorem mem_5 : 5 in {1,2,3,4,5} := () -- 任意の値で OK
```

---

## 4. 反例の検出

検証器は反例があれば具体的に報告する。

```seki
def S := {1, 2, 3, 4, 5}
theorem bad : forall x in S, x > 3 := by eval
-- proof error: proposition reduced to false

theorem bad2 : forall x in S, x > 3 := \x -> x
-- proof error: counterexample: with x = 1 the body is not true (got false)
```

`exists` の witness が外れた場合:

```seki
theorem bad3 : exists x in {1,2,3}, x == 5 := 5
-- proof error: witness 5 is not in declared domain {1, 2, 3}

theorem bad4 : exists x in {1,2,3}, x > 100 := 2
-- proof error: with witness x = 2 body did not hold (got false)
```

これらは debug に役立つ。

---

## 5. axiom の使い所

`axiom` は検証なしに命題を真として登録する。

```seki
axiom Choice : forall S in Set, true
axiom ExtNonEmpty : exists s in Set, true
```

主な用途:

- 表現できない命題 (依存型を要するなど) を仮定として使いたい
- 後で証明するつもりの補題を `axiom` で前置きしておく (TODO マーカー)
- 言語に未実装の概念 (例: 帰納法の原理) を公理として導入する

`axiom` は**信頼の境界**を作る。本物の Lean のように `Sorry` を見つけてレビューするのと同様、`axiom` は手作業で検査されるべき。

---

## 6. パターン集

### 6.1 ブール代数の恒等式は `forall x in Bool` + `by eval`

`Bool = {false, true}` は 2 元なので完全列挙が常に可能。

```seki
theorem dn   : forall a in Bool, not (not a) == a := by eval
theorem em   : forall a in Bool, a or (not a)    := by eval
theorem distr_and_or
  : forall a in Bool, forall b in Bool, forall c in Bool,
        (a and (b or c)) == ((a and b) or (a and c))
  := by eval
```

### 6.2 有限部分集合に絞った代数法則

無限の `Int` での性質を有限部分で確認:

```seki
def Sx := {-3, -2, -1, 0, 1, 2, 3}
theorem int_distrib
  : forall a in Sx, forall b in Sx, forall c in Sx,
        a * (b + c) == a * b + a * c
  := by eval
```

完全な証明ではないが、反例があれば検出されるので回帰テストとして有用。

### 6.3 帰納的アルゴリズムの仕様検証

実装の正しさを数学公式で確認する。

```seki
def sum := \n -> if n == 0 then 0 else n + sum (n - 1)

def S20 := {0, 1, 2, ..., 20}
theorem gauss
  : forall n in S20, sum n == n * (n + 1) / 2
  := by eval
```

帰納法ではなく**全列挙**による検証なので、`S20` の範囲外までは保証されない。だが、計算式と再帰実装の整合性を機械的に確認する非常に強いテストになる。

### 6.4 制約充足の存在証明

```seki
theorem ages_solvable
  : exists a in Ages, exists b in Ages, exists c in Ages,
        (a + b + c == 27) and (a == b + 3) and (c == 2 * b)
  := 9                       -- Alice = 9 が解の一つ
```

witness を提示することで「解が存在する」ことを示す。一意性は `forall ... == (a == 9)` で別途証明できる。

### 6.5 群の公理を有限群で検証

```seki
def Z12 := {0, 1, ..., 11}
def addM := \a b -> (a + b) mod 12

theorem addM_assoc
  : forall a in Z12, forall b in Z12, forall c in Z12,
        addM (addM a b) c == addM a (addM b c)
  := by eval
```

12³ = 1728 ケースを全列挙する。完全な検証。

### 6.6 無限環の代数恒等式は `by algebra`

```seki
theorem distrib : forall a in Int, forall b in Int, forall c in Int,
    a * (b + c) == a * b + a * c := by algebra

theorem cube : forall x in Int,
    (x + 1) * (x + 1) * (x + 1) == x*x*x + 3*x*x + 3*x + 1 := by algebra
```

`by eval` で `Int` 上の forall を書くと SAMPLE_BOUND の標本検査になり健全でない。代数恒等式は `by algebra` を使うこと。

### 6.7 不等式と PSD 形式

```seki
-- AM-GM 系
theorem cauchy : forall a in Int, forall b in Int,
    a*a + b*b >= 2 * a * b := by algebra

-- Nat 上の単純不等式
theorem succ_gt : forall n in Nat, n + 1 > n := by algebra
theorem nat_nn  : forall n in Nat, n >= 0 := by algebra
```

### 6.8 整数除算と剰余の判定

定数除数なら多項式断片に組み込める:

```seki
theorem half       : forall n in Int, (2 * n) / 2 == n := by algebra
theorem even_mod   : forall n in Int, (2 * n) mod 2 == 0 := by algebra
theorem div_floor  : forall n in Int, (3 * n + 6) / 3 == n + 2 := by algebra
```

### 6.9 Σ系の公式は `by induction`

```seki
def sum := \n -> if n == 0 then 0 else n + sum (n - 1)

theorem gauss
  : forall n in Nat, 2 * sum n == n * (n + 1)
  := by induction
```

仕様の正しさを**ℕ 全体に対して**機械検証できる。`by eval` の有限範囲版より強い。

### 6.10 リスト・木の構造帰納法

```seki
def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)
theorem ll_nn : forall xs in (List Int), listLen xs >= 0 := by induction

def treeSize := \t ->
    if isLeaf t then 0
    else 1 + treeSize (treeLeft t) + treeSize (treeRight t)
theorem ts_nn : forall t in (Tree Int), treeSize t >= 0 := by induction
```

### 6.11 Fibonacci 系は `by strong_induction`

複数前段を参照する漸化式は弱帰納法で届かない:

```seki
def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)
theorem fib_nn : forall n in Nat, fib n >= 0 := by strong_induction
```

---

## 7. 限界と運用上の注意

### 7.1 健全でないケース (および回避策)

- **無限 atomic 集合上の `by eval`**: `forall x in Nat, P(x) := by eval` は `SAMPLE_BOUND` (デフォルト 200) までしか確認しない。これで通っても**真であることを意味しない**。

  **回避策**: 多項式恒等式なら `by algebra`、再帰関数の仕様なら `by induction` を使う。これらは健全な無限ケース証明戦術。

  ```seki
  theorem fake : forall x in Nat, x < 1000 := by eval   -- 通ってしまう
  ```

  確実な保証が必要なら、有限の明示的な定義域を使う。

- **関数型 `A -> B` の所属検査**: 関数値が `A -> B` に属するかは標本でしか確認しない。コーナーケースは漏れる可能性がある。

- **比較不能な集合**: 2 つの内包集合 `{x in S | P}` と `{x in S | Q}` が等しいかは一般に決定不能。`set_eq` は同じかたちの集合のみ比較する。

### 7.2 計算量

- `forall x in S, forall y in T, P(x,y)` のコストは `|S| * |T| * cost(P)`。3 重ネストの 20×20×20 = 8000 ケースは早いが、定義域サイズが上がると指数的に増える。
- 内包集合 `{x in S | P(x)}` の列挙は `S` を列挙して `P` でフィルタ。`S` が `Nat` なら `SAMPLE_BOUND` まで。

### 7.3 推奨ワークフロー (戦術選択フロー)

```
            命題は…
              ↓
        ┌──────┴──────┐
       等式          不等式/関係式
        ↓                ↓
   両辺定数のみ?     forall x in T, ...?
    yes / no            ↓ yes
     ↓ ↓        定義域 T は…
   refl 多項式?      ┌────┼─────┐
        ↓ yes      Nat   List   Tree
    by algebra      ↓     ↓      ↓
                  ┌─┴─┐   by induction (構造帰納法)
              再帰関数?  ↓
                ↓ yes / no
           複数前段?    by algebra (定数恒等式)
            ↓ yes
        by strong_induction
```

ステップごとの実践:

1. **試しに評価**: REPL や式宣言で `forall ..., P` を書いて結果を見る。`true` が返るなら証明可能性が高い。
2. **戦術を選ぶ** (上のフロー参照)。健全な無限域証明が必要なら `by algebra` / `by induction` / `by strong_induction` を優先。
3. **失敗したら情報を得る**: 検証器は反例 (`counterexample: with x = 3 ...`) を返すので、それを手がかりに命題を見直す。
4. **未証明の前提は `axiom`**: 後で証明する補題は明示的に区別。`axiom` は信頼境界。

### 7.4 `examples/` で見られる検証可能事実の規模

| ファイル | 検証された theorem 数 | 主な戦術 |
|---|---:|---|
| 04_proofs.seki | 6 + 1 axiom | by eval / refl / 証明項 |
| 05_number_theory.seki | 6 | by eval (有限) |
| 06_boolean_algebra.seki | 22 | by eval (Bool 完全列挙) |
| 07_modular.seki | 10 | by eval (Z12 全列挙) |
| 08_set_identities.seki | 18 | refl / by eval |
| 09_algorithms.seki | 9 | by eval (有限範囲) |
| 10_puzzles.seki | 7 | witness / by eval |
| 11_tuples_lists.seki | 1 | by eval (有限直積) |
| 12_infinite_proofs.seki | 20 | by algebra / by induction (∞) |
| 13_advanced_tactics.seki | 24 | 不等式 / div / mod / list / tree / strong (∞) |
| 14_types_and_real.seki | 13 | 型の集合論的実装・Real (Bool=={false,true} 含む) |
| 15_set_definition_proofs.seki | 17 | 集合の定義からの自明判定 (by eval が無限域で健全に) |
| 16_stdlib_constructions.seki | 13 | stdlib 構築 (Pos/Rat/range/map/treeSize…) |
| 17_pair_encoded_adt.seki | 6 | リスト/木のタグ付きペア符号化 |
| 18_data_match.seki | 0 | `data`/`match` の使い方 (proof は含まず) |
| 19_modules_and_errors.seki | 0 | Option/Result/`?`/import の使い方 |
| 20_dependent_types.seki | 2 | 依存関数型 `(x : A) -> B(x)` |
| **計** | **174** + 1 axiom | |

---

## 関連

- 言語仕様: [language.md](language.md)
- 実装: [internals.md](internals.md) の `prover` 節

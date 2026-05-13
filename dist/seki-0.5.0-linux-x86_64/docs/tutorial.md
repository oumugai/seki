# seki チュートリアル

このチュートリアルは seki を初めて触る人向けの段階的な入門です。30〜60 分で seki の主要機能を一通り体験できることを目標にしています。

各節のコードはそのまま `.seki` ファイルに貼り付けるか、REPL で 1 行ずつ試せます。

## 目次

1. [インストールと REPL](#1-インストールと-repl)
2. [式と関数](#2-式と関数)
3. [集合を作る](#3-集合を作る)
4. [集合の所属と演算](#4-集合の所属と演算)
5. [型としての集合](#5-型としての集合)
6. [タプル・リスト・木](#6-タプル--リスト--木)
7. [量化子で命題を表現する](#7-量化子で命題を表現する)
8. [はじめての theorem](#8-はじめての-theorem)
9. [無限域での証明 (by algebra)](#9-無限域での証明-by-algebra)
10. [数学的帰納法 (by induction)](#10-数学的帰納法-by-induction)
11. [Fibonacci と強帰納法](#11-fibonacci-と強帰納法)
12. [次のステップ](#12-次のステップ)

---

## 1. インストールと REPL

### ビルド

Rust 1.70 以降が入っていれば:

```sh
git clone <this-repo>
cd seki
cargo build --release
```

`target/release/seki` または `cargo run --release --` でバイナリが起動します。

### REPL

引数なしで起動:

```sh
$ cargo run -q
seki repl — type :q to exit, :help for commands
seki> 1 + 2 * 3
7
seki> "hello, " == "hello, "
true
seki>
```

REPL の主なコマンド:

| コマンド | 内容 |
|---|---|
| `:q` | 終了 |
| `:help` | ヘルプ |
| `:defs` | 定義済みの値・theorem 一覧 |
| `:type EXPR` | 式の shape |
| `:load FILE` | `.seki` ファイル読込 |

ファイル実行:

```sh
cargo run -q -- examples/01_basic.seki
```

ワンライナー:

```sh
cargo run -q -- -e 'forall x in {1,2,3}, x > 0'
```

---

## 2. 式と関数

### リテラルと算術

```seki
42                       -- 整数
true                     -- 真偽
"hello"                  -- 文字列
1 + 2 * 3                -- 7  (*  が + より優先)
10 mod 3                 -- 1  (mod は剰余、Euclid)
not (1 == 2)             -- true
```

文字列のエスケープ: `\n`、`\t`、`\\`、`\"`。

### 関数定義

最も短い形:

```seki
def double := \x -> x * 2
double 21                -- 42
```

`\x ->` はラムダ抽象。`fn` や `lambda` も同義。

複数引数 (自動でカリー化):

```seki
def add := \x y -> x + y
add 3 4                  -- 7

def addOne := add 1      -- 部分適用
addOne 41                -- 42
```

型注釈付き:

```seki
def square : Nat -> Nat := \(n : Nat) -> n * n
square 7                 -- 49
```

引数を型注釈つきで `def` の左側に書く糖衣構文:

```seki
def square (n : Nat) : Nat := n * n   -- 上と同じ意味
```

### let と if

```seki
let x = 5 in x * x       -- 25

if 3 > 2 then "yes" else "no"     -- "yes"
```

### 再帰

`def` で定義した関数は自分自身を呼び出せます (グローバルから解決):

```seki
def fact := \n -> if n == 0 then 1 else n * fact (n - 1)
fact 6                   -- 720
```

> ローカルな `let f := \... -> f ...` は再帰しません。グローバルな `def` が必要です。

### 高階関数

```seki
def twice := \f x -> f (f x)
twice double 5           -- 20  (= double (double 5))
twice (\n -> n + 3) 10   -- 16
```

---

## 3. 集合を作る

集合は seki の中心概念です。**2 つの作り方**があります:

### 列挙

```seki
def Days     := {"Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"}
def Small    := {1, 2, 3, 4, 5}
def Empty    := {}
```

要素は任意の値でよく、評価されてから登録されます。重複は自動で吸収されます (集合論セマンティクス)。

### 内包 (述語)

`{x in S | P(x)}` は **`S` の要素のうち `P` を満たすもの** を集めた集合です:

```seki
def Pos       := {x in Int | x > 0}                    -- 正整数
def EvenNat   := {x in Nat | x mod 2 == 0}             -- 偶数
def Vowels    := {c in Days | c == "Mon" or c == "Sun"} -- 月日
def Squares10 := {n in {0,1,2,3,4,5,6,7,8,9} |
                  exists k in {0,1,2,3}, n == k * k}
```

述語は `Bool` を返さなければなりません。

---

## 4. 集合の所属と演算

### 所属

```seki
"Mon" in Days            -- true
"Foo" in Days            -- false
4 in EvenNat             -- true
3 in EvenNat             -- false
0 notin Pos              -- true
```

### 集合演算

```seki
def A := {1, 2, 3, 4}
def B := {3, 4, 5, 6}

A union B                -- {1, 2, 3, 4, 5, 6}
A intersect B            -- {3, 4}
A diff B                 -- {1, 2}
{1, 2} subset A          -- true

card A                   -- 4 (列挙集合の濃度)
```

`union` は両辺とも列挙集合のときに動きます。`intersect` / `diff` / `subset` は左辺が列挙可能ならよく、右辺は内包でも構いません:

```seki
{1, 2, 3, 4, 5, 6, 7, 8, 9, 10} intersect EvenNat
-- {2, 4, 6, 8, 10}
```

---

## 5. 型としての集合

seki では **型 = 集合** です。値 `v` が型 `T` を持つとは `v in T` のこと:

```seki
3 in Nat                 -- true (3 は自然数)
"x" in Nat               -- false (文字列は Nat の元ではない)
```

組込集合: `Nat`、`Int`、`Real`、`Bool`、`String`、`Prop`、`Set`。

特筆すべきは **`Bool` が文字通りの集合** `{false, true}` として実装されている点です:

```seki
theorem bool_def : Bool == {false, true} := refl
-- ✓ proved
```

これは「型は集合である」という言語の世界観をそのまま体現しています。

`Real` は IEEE-754 `f64` の集合で、整数を包含 (`Int ⊂ Real`):

```seki
1.5 in Real              -- true
3 in Real                -- true (Int は Real の元)
"x" in Real              -- false
```

算術は **Int↔Real 自動昇格**:

```seki
1 + 2.5                  -- 3.5  (Int → Real に昇格)
3 / 2.0                  -- 1.5  (Real division)
3 / 2                    -- 1    (両 Int なので整数除算)
```

関数型 `A -> B` は集合 A から B への関数全体:

```seki
def f : Nat -> Bool := \(n : Nat) -> n > 0
f 5                      -- true
```

型注釈付きで宣言した関数は、定義時に**サンプル検査**されます:

```seki
def Color := {"red", "green", "blue"}

def fav : Bool -> Color := \(b : Bool) -> if b then "red" else "blue"   -- OK

-- 下記はエラー: "purple" は Color に属さない
-- def bad : Bool -> Color := \(b : Bool) -> if b then "red" else "purple"
```

---

## 6. タプル・リスト・木

### タプル

ヘテロな組:

```seki
def p := (3, "hello", true)
fst p                    -- 3
snd p                    -- "hello"

def Pair := Nat times Bool
(5, true)  in Pair       -- true
(5, 7)     in Pair       -- false
```

`A times B` は直積集合。3 項以上もOK (`A times B times C`)。

### リスト

```seki
def xs := [1, 2, 3, 4, 5]
length xs                -- 5
head xs                  -- 1
tail xs                  -- [2, 3, 4, 5]
cons 0 xs                -- [0, 1, 2, 3, 4, 5]
reverse xs               -- [5, 4, 3, 2, 1]
append xs [10, 20]       -- [1, 2, 3, 4, 5, 10, 20]
toSet xs                 -- {1, 2, 3, 4, 5}
```

リスト型: `List T`。

```seki
[1, 2, 3] in (List Int)         -- true
[1, "two", 3] in (List Int)     -- false
```

`map` / `filter` / `foldr` は組込ではありませんが、再帰で簡単に書けます:

```seki
def map := \f xs ->
    if null xs then nil
    else cons (f (head xs)) (map f (tail xs))

map (\n -> n * n) [1, 2, 3, 4, 5]    -- [1, 4, 9, 16, 25]
```

### 二分木

```seki
def t := node (node leaf 1 leaf) 2 (node leaf 3 leaf)

isLeaf leaf              -- true
isLeaf t                 -- false
treeVal t                -- 2
treeLeft t               -- (node leaf 1 leaf)
treeRight t              -- (node leaf 3 leaf)
```

木のサイズを数える関数:

```seki
def treeSize := \t ->
    if isLeaf t then 0
    else 1 + treeSize (treeLeft t) + treeSize (treeRight t)

treeSize t               -- 3
```

`Tree T` は値が `T` の二分木全体の集合です。

---

## 7. 量化子で命題を表現する

`forall x in S, P` (∀x ∈ S. P) と `exists x in S, P` (∃x ∈ S. P):

```seki
forall x in {1, 2, 3, 4, 5}, x > 0       -- true
exists x in {1, 2, 3, 4, 5}, x > 4       -- true
exists x in {1, 2, 3, 4, 5}, x > 100     -- false
```

ネストして多変数:

```seki
forall a in Bool, forall b in Bool, (a and b) == (b and a)   -- true
```

> 有限集合上の forall / exists は**全要素を実際に評価**して結果を返します。Bool は 2 元集合なので 4 ケース全列挙、`{1..10}` は 10 ケース、など。

> **集合の定義から判定できる場合**は、列挙せず即座に答えが返ります:
> ```seki
> def Pos := {x in Int | x > 0}
> forall p in Pos, p > 0          -- true (述語と body が一致 → 即時)
> forall n in Nat, n >= 0          -- true (Nat の定義から代数的判定)
> ```
> これは**健全**な判定で、無限集合上でも正しい結果が返ります。

`Nat` や `Int` のような無限集合上で代数判定できない命題 (例: `forall n in Nat, n < 1000`) は標本検証 (デフォルト 0..200) になり、健全ではありません。確実な無限域証明には次節以降の戦術 (`by algebra` / `by induction` 等) を使います。

---

## 8. はじめての theorem

`theorem 名前 : 命題 := 証明` で命題を機械検証します:

```seki
theorem two_plus_two : 2 + 2 == 4 := by eval
-- ✓ proved
```

`by eval` は「命題を評価して `true` になることを確認する」戦術です。Bool 上の forall を含む命題でも有効:

```seki
theorem demorgan
  : forall a in Bool, forall b in Bool,
        not (a and b) == (not a or not b)
  := by eval
-- ✓ proved (Bool × Bool = 4 ケース全列挙)
```

等式は `refl` (反射律) でも証明できます:

```seki
theorem dbl_3 : (3 + 3) == 6 := refl
```

`exists` の証明は **witness** (証拠) を提示します:

```seki
def Small := {1, 2, 3, 4, 5}
theorem some_big : exists x in Small, x >= 5 := 5
```

ここでの `5` は「x = 5 が `x >= 5` を満たす」という証拠です。

### 証明の失敗

検証器は反例を返します:

```seki
theorem bad : forall x in {1,2,3,4,5}, x > 3 := by eval
-- proof error: proposition reduced to false
```

---

## 9. 無限域での証明 (by algebra)

`forall x in Int, ...` を `by eval` で書くと SAMPLE_BOUND までの標本検査になり、健全ではありません。

代数恒等式を**ℤ 全体**で証明するには `by algebra`:

```seki
theorem add_comm
  : forall a in Int, forall b in Int, a + b == b + a
  := by algebra

theorem distrib
  : forall a in Int, forall b in Int, forall c in Int,
        a * (b + c) == a * b + a * c
  := by algebra

theorem cube
  : forall x in Int,
        (x + 1) * (x + 1) * (x + 1) == x*x*x + 3*x*x + 3*x + 1
  := by algebra
```

両辺を多項式の正規形 (sum-of-monomials) に変換し、構造的に比較します。任意の整数値で成立する**真の証明**です。

### 不等式

```seki
-- Nat 上の単純な不等式
theorem nat_nn  : forall n in Nat, n >= 0 := by algebra
theorem succ_gt : forall n in Nat, n + 1 > n := by algebra

-- Int 上の二次形式
theorem square_nn : forall x in Int, x * x >= 0 := by algebra

-- Cauchy-Schwarz の特殊版
theorem cauchy
  : forall a in Int, forall b in Int, a*a + b*b >= 2 * a * b
  := by algebra
```

### 整数除算と剰余

定数除数なら扱えます:

```seki
theorem half_double
  : forall n in Int, (2 * n) / 2 == n
  := by algebra

theorem odd_mod
  : forall n in Int, (2 * n + 1) mod 2 == 1
  := by algebra
```

可変除数 (`n / m` で `m` が変数) は対象外です。

---

## 10. 数学的帰納法 (by induction)

再帰関数の仕様を全自然数に対して証明できます:

```seki
def sum := \n -> if n == 0 then 0 else n + sum (n - 1)

theorem gauss
  : forall n in Nat, 2 * sum n == n * (n + 1)
  := by induction
```

検証器は:

1. **基底**: `2 * sum 0 == 0 * 1` → `0 == 0` ✓
2. **帰納段階**: `lhs(k+1) - lhs(k) == rhs(k+1) - rhs(k)` を多項式として確認

体は等式だけでなく不等式も OK:

```seki
theorem sum_nonneg : forall n in Nat, sum n >= 0 := by induction
theorem sum_grows  : forall n in Nat, sum (n + 1) > sum n := by induction
```

### リスト構造帰納法

`forall xs in (List T), P(xs)` の形なら自動的にリスト帰納法になります:

```seki
def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)

theorem list_len_nonneg
  : forall xs in (List Int), listLen xs >= 0
  := by induction
```

検証器は:

1. **基底**: `listLen [] >= 0` → `0 >= 0` ✓
2. **帰納段階**: `xs := cons x ys` を代入し、`null/head/tail` を簡約してから多項式判定

### 木構造帰納法

```seki
def treeSize := \t ->
    if isLeaf t then 0
    else 1 + treeSize (treeLeft t) + treeSize (treeRight t)

theorem tree_size_nonneg
  : forall t in (Tree Int), treeSize t >= 0
  := by induction
```

---

## 11. Fibonacci と強帰納法

Fibonacci は `f(n-1)` と `f(n-2)` の両方を参照します。普通の帰納法 (depth=1) では届かない場合があります:

```seki
def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)

fib 10                   -- 55

theorem fib_nonneg : forall n in Nat, fib n >= 0 := by strong_induction
```

`by strong_induction` (深さ 2):

1. **基底**: `fib 0 = 0 >= 0`、`fib 1 = 1 >= 0` をそれぞれ確認
2. **帰納段階**: `fib (k+2)` を unfold して `fib (k+1) + fib k`。`fib k` と `fib (k+1)` は IH により非負。`(≥0) + (≥0) >= 0` ✓

---

## 12. 次のステップ

このチュートリアルでカバーしたのは seki の中核機能の主要な使い方です。さらに学ぶには:

### 例題を読む

`examples/` には 29 ファイル / 351 件の theorem があります:

| ファイル | テーマ | おすすめ |
|---|---|---|
| `01_basic.seki` | 数値・関数・let・if | チュートリアル後の復習 |
| `02_sets.seki` | 集合の定義と演算 | 集合論を学ぶ |
| `03_lambda.seki` | カリー化・高階関数・型注釈 | ラムダ計算 |
| `04_proofs.seki` | theorem の 3 戦術 | 証明の入口 |
| `05_number_theory.seki` | 階乗・素数集合・gcd | 再帰関数の検証 |
| `06_boolean_algebra.seki` | De Morgan 等の証明 | 論理の自動検証 |
| `07_modular.seki` | Z/12Z 加法群 | 群論の有限ケース |
| `08_set_identities.seki` | 集合論恒等式 | 構造的等価 |
| `09_algorithms.seki` | Gauss公式・パスカル | 帰納法による検証 |
| `10_puzzles.seki` | ピタゴラス数・年齢パズル | 制約充足 |
| `11_tuples_lists.seki` | タプル・直積・リスト | 表現力 |
| `12_infinite_proofs.seki` | by algebra / by induction | 無限域証明の集大成 |
| `13_advanced_tactics.seki` | 不等式・木・強帰納法 | 全戦術カバー |
| `14_types_and_real.seki` | 型の集合論的実装・実数型 | 集合 = 型の証明と Real |
| `15_set_definition_proofs.seki` | 集合の定義からの自明判定 | by eval が無限域でも健全に |
| `16_stdlib_constructions.seki` | stdlib (Pos/Rat/range/map/treeSize…) | seki 自身で書かれた標準ライブラリ |
| `17_pair_encoded_adt.seki` | リスト/木のタグ付きペア符号化 | 集合論的構築の確認 |
| `18_data_match.seki` | `data` 宣言と `match` 式 | 代数的データ型を綺麗に書く |
| `19_modules_and_errors.seki` | Option/Result/`?`/`import` | エラーハンドリングとモジュール |
| `20_dependent_types.seki` | 依存関数型 `(x : A) -> B(x)` | Vec n / refinement 型 |
| `21_inference_termination_classes.seki` | 型推論 / 終了性検査 / 型クラス | 静的解析のサンプル |
| `22_group_theory.seki` | 群・モノイド・環の公理ベース検証 + Z12 + xor + by simp | 数学ライブラリの形 |
| `23_indexed_adts.seki` | 値添字付き ADT (Vec n / Fin n) を refinement で表現 | 依存型の応用 |
| `24_rings_fields.seki` | 環・可換環・整域・有限体 GF(5) + 二項定理 | 代数構造の検証 |
| `25_linear_algebra.seki` | ℤ³ ベクトル空間 + 内積 + 標準基底 + 2x2 行列・行列式 | 線形代数の基礎 |
| `26_cas.seki` | 記号式 ADT + 代数簡約 + 記号微分・積分 + 微積分学の基本定理 | seki で書く計算機代数 |
| `27_cas_advanced.seki` | 多項式正規化/展開 + GCD + 有理根因数分解 + solve + Taylor + 部分分数 + BigInt | CAS の核アルゴリズム集 |
| `28_cas_linalg_ode.seki` | 2x2 固有値 + 行列式 (Laplace) + Euler/RK4 ODE + Newton 法 + Gauss 消去 + モノミアル順序 | 線形代数 & 数値解析 |

### リファレンス

- [language.md](language.md) — 構文・型・演算子の完全リファレンス
- [proofs.md](proofs.md) — 9 戦術 + 合成の詳細・パターン集・限界
- [cheatsheet.md](cheatsheet.md) — 1 ページのクイック参照
- [cookbook.md](cookbook.md) — 「~したい」レシピ集

### 練習問題

簡単なものから挑戦してみてください:

1. `forall n in Nat, n + 1 > 0` を証明する (1 戦術)
2. `forall a in Int, forall b in Int, (a + b) * (a - b) == a*a - b*b` を証明する
3. リストの逆向きの長さは元と同じ: `forall xs in (List Int), length (reverse xs) == length xs` (これは難問)
4. 偶数と奇数を分離する関数を書いて、結合した時の長さの和が元のリストの長さと等しいことを示す

詰まったら `examples/` を参考にしてください。

# seki クックブック

「~したい」「~を証明したい」という具体的な目的別レシピ集。各レシピは独立したスニペットで、そのまま REPL や `.seki` ファイルに貼り付けて動かせます。

## 目次

- [基本テクニック](#基本テクニック)
  - [集合の特定の要素だけ取り出したい](#集合の特定の要素だけ取り出したい)
  - [集合の要素数を数えたい](#集合の要素数を数えたい)
  - [集合を別の集合に変換したい](#集合を別の集合に変換したい)
  - [実数 (Real) を使いたい](#実数-real-を使いたい)
  - [標準ライブラリの述語サブタイプを使いたい](#標準ライブラリの述語サブタイプを使いたい)
  - [有理数を扱いたい](#有理数を扱いたい)
  - [リスト/木の標準操作を使いたい](#リスト木の標準操作を使いたい)
  - [エラー伝播を綺麗に書きたい (`?` 演算子)](#エラー伝播を綺麗に書きたい--演算子)
  - [コードを複数ファイルに分けたい (モジュール)](#コードを複数ファイルに分けたいモジュール)
  - [代数的データ型を定義してパターンマッチしたい](#代数的データ型を定義してパターンマッチしたい)
  - [引数の値で返り値の型が変わる関数を書きたい (依存型)](#引数の値で返り値の型が変わる関数を書きたい-依存型)
  - [Bool が {false, true} に等しいことを示したい](#bool-が-false-true-に等しいことを示したい)
  - [複数集合を一気に組み合わせたい](#複数集合を一気に組み合わせたい)
- [関数定義のパターン](#関数定義のパターン)
  - [再帰関数の書き方](#再帰関数の書き方)
  - [リストを畳み込みたい](#リストを畳み込みたい)
  - [部分適用で関数を作りたい](#部分適用で関数を作りたい)
  - [既存関数を組み合わせたい](#既存関数を組み合わせたい)
  - [型クラスでアドホック多相を表現したい](#型クラスでアドホック多相を表現したい)
  - [再帰関数の終了性 warning が出る](#再帰関数の終了性-warning-が出る)
- [証明のレシピ](#証明のレシピ)
  - [集合の定義から forall を即座に得たい](#集合の定義から-forall-を即座に得たい)
  - [単純な等式を証明したい](#単純な等式を証明したい)
  - [すべての要素について成り立つことを示したい](#すべての要素について成り立つことを示したい)
  - [反例があるかを確認したい](#反例があるかを確認したい)
  - [代数恒等式を ℤ 全体で証明したい](#代数恒等式を-ℤ-全体で証明したい)
  - [不等式を証明したい](#不等式を証明したい)
  - [整数除算/剰余の性質を証明したい](#整数除算剰余の性質を証明したい)
  - [Σ系の公式を証明したい](#σ系の公式を証明したい)
  - [リストの性質を証明したい](#リストの性質を証明したい)
  - [木の性質を証明したい](#木の性質を証明したい)
  - [Fibonacci など多段階漸化式を扱いたい](#fibonacci-など多段階漸化式を扱いたい)
  - [関数定義を展開してから証明したい](#関数定義を展開してから証明したい)
  - [補助補題を集めて証明したい](#補助補題を集めて証明したい)
  - [戦術を連鎖したい](#戦術を連鎖したい)
  - [数式を記号的に操作したい (微分・簡約)](#数式を記号的に操作したい-微分簡約)
  - [exists の証拠を提示したい](#exists-の証拠を提示したい)
- [トラブルシューティング](#トラブルシューティング)

---

## 基本テクニック

### 集合の特定の要素だけ取り出したい

`intersect` で具体化、`{x in S | P}` でフィルタ:

```seki
def UpTo30 := {x in Nat | x <= 30}
def Primes := {x in UpTo30 | isPrime x}

-- 30 以下の素数を列挙
Primes intersect {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
```

`intersect` を使うと内包集合 (無限定義域から派生) を具体的な列挙集合に変換できます。

### 集合の要素数を数えたい

```seki
card {1, 2, 3, 4, 5}             -- 5

-- 内包集合は intersect で列挙化してから
def Even10 := {x in Nat | x mod 2 == 0} intersect
              {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
card Even10                       -- 6
```

`card` は列挙集合のみ動きます。

### 集合を別の集合に変換したい

リスト経由が手っ取り早い:

```seki
def squares := toSet (map (\n -> n * n) [1, 2, 3, 4, 5])
-- {1, 4, 9, 16, 25}

-- map は自分で書く必要があります (例)
def map := \f xs ->
    if null xs then nil
    else cons (f (head xs)) (map f (tail xs))
```

### 実数 (Real) を使いたい

リテラルは小数点付き、Int は自動昇格:

```seki
1.5 + 2.0                    -- 3.5
1 + 2.5                      -- 3.5  (Int → Real)
3 / 2.0                      -- 1.5  (Real division)
3 / 2                        -- 1    (整数除算は変わらず)

-- 組込関数
floor 3.7                    -- 3
ceil  3.2                    -- 4
round 3.5                    -- 4
abs   (-2.5)                 -- 2.5
sqrt  2.0                    -- ≈1.414
pow   2.0 10                 -- 1024.0
intToReal 5                  -- 5.0

pi                           -- 3.14159...
e                            -- 2.71828...
```

Real 関数の型注釈:

```seki
def quad : Real -> Real := \(x : Real) -> x * x + 2.0 * x + 1.0
quad 0.0      -- 1.0  (= (x+1)² when x=0)
quad (-1.0)   -- 0.0
```

### 標準ライブラリの述語サブタイプを使いたい

stdlib (起動時自動ロード) で次の集合が利用可能:

```seki
def x := 5
x in Pos                        -- true (Pos = {x in Int | x > 0})
x in EvenInt                    -- false
x in Byte                       -- true (Byte = {x in Int | 0 <= x <= 255})
0 in Bit                        -- true (Bit = {0, 1})
255 in UInt8                    -- true
-129 in Int8                    -- false (Int8 = -128..127)
```

`Pos` / `Neg` / `EvenInt` / `OddInt` / `Bit` / `Byte` / `Int8` / `UInt8` / `Int16` / `UInt16` などが定義済み。

### 有理数を扱いたい

`Rat = Int × Pos` として stdlib で構築済み:

```seki
def half  := mkRat 1 2          -- (1, 2)
def third := mkRat 1 3          -- (1, 3)

addRat half third               -- (5, 6)   = 1/2 + 1/3
mulRat half third               -- (1, 6)   = 1/2 * 1/3
negRat half                     -- (-1, 2)
eqRat (mkRat 1 2) (mkRat 2 4)   -- true     (cross-multiplication)
```

代数性も検証可能:

```seki
def TestRat := {(1, 1), (1, 2), (2, 3)}
theorem rat_add_comm
  : forall p in TestRat, forall q in TestRat,
        eqRat (addRat p q) (addRat q p)
  := by eval
```

### リスト/木の標準操作を使いたい

stdlib に `map` / `filter` / `foldr` / `foldl` / `range` / `sumList` / `maxList` / `all` / `any` / `contains` / `singleton` / `treeSize` / `treeHeight` / `treeSum` / `treeToList` が定義されている:

```seki
range 1 6                          -- [1, 2, 3, 4, 5]
map (\n -> n * n) (range 1 6)      -- [1, 4, 9, 16, 25]
filter isEven (range 0 10)         -- [0, 2, 4, 6, 8]
sumList (range 1 11)               -- 55  (= Σ 1..10)

def t := node (singleton 1) 2 (singleton 3)
treeSize t                         -- 3
treeSum t                          -- 6
treeToList t                       -- [1, 2, 3]   (中順序)
```

### エラー伝播を綺麗に書きたい (`?` 演算子)

stdlib に `Option` と `Result` が定義済み:

```seki
def parseDigit := \c ->
    match c with
    | "0" -> Ok 0
    | "1" -> Ok 1
    | _ -> Err "not a digit"
```

ネストした match の代わりに `?` で平坦化:

```seki
-- 以下と等価:
--   match parseDigit a with
--   | Err e -> Err e
--   | Ok x -> match parseDigit b with
--       | Err e -> Err e
--       | Ok y -> Ok (x + y)
def add := \a b ->
    let x = parseDigit a ? in
    let y = parseDigit b ? in
    Ok (x + y)
```

ヘルパも豊富:

```seki
mapResult (\n -> n * 2) (Ok 5)         -- Ok 10
bindResult (Ok 5) (\x -> Ok (x + 1))   -- Ok 6
isOk (Ok 1) / isErr (Err "x")
unwrapResultOr 0 (Err "fallback")      -- 0
okOr "missing" None                     -- Err "missing"
resultToOption (Ok 5)                   -- Some 5
```

### コードを複数ファイルに分けたい (モジュール)

`math.seki`:
```seki
def square := \n -> n * n
def cube := \n -> n * n * n
```

`main.seki` (同じディレクトリ):
```seki
import "math.seki" as M

M.square 5       -- 25
M.cube 3         -- 27
```

または unqualified:
```seki
import "math.seki"
square 5         -- 25
```

パスはインポートするファイルのディレクトリを基準に解決されます。同じファイルを 2 回 import しても 1 回しかロードされず、循環は実行時エラーになります。

### 代数的データ型を定義してパターンマッチしたい

`data` 宣言で構築子を定義し、`match` 式で分解できます:

```seki
data Maybe A = None | Some A

def safeDiv := \a b ->
    if b == 0 then None else Some (a / b)

def fromMaybe := \def_val m ->
    match m with
    | None   -> def_val
    | Some x -> x

fromMaybe 0 (safeDiv 10 2)        -- 5
fromMaybe 0 (safeDiv 10 0)        -- 0
```

エラー型 (Result/Either):

```seki
data Result E A = Err E | Ok A

def parseDigit := \c ->
    match c with
    | "0" -> Ok 0
    | "1" -> Ok 1
    | _   -> Err "not a digit"
```

再帰的 ADT もOK:

```seki
data MyList A = MyNil | MyCons A (MyList A)

def myLen := \xs -> match xs with
    | MyNil -> 0
    | MyCons _ t -> 1 + myLen t
```

**注意点**:
- 構築子は **大文字始まり** (`Some`, `None`, `Cons`)、変数は **小文字始まり** (`x`, `n`, `xs`)
- 型名 (`Maybe` 等) 自体は集合として自動定義されない (型注釈には使えない)
- 内部はタグ付きペア — `Some 5` の実体は `("Some", (5, ()))`

### 引数の値で返り値の型が変わる関数を書きたい (依存型)

`(x : A) -> B(x)` で**依存関数型**を表現できます。型レベル関数を組合せて型族 (type family) を作る:

```seki
-- 長さ n の整数リスト全体の集合
def Vec := \(n : Nat) -> {xs in (List Int) | length xs == n}

-- 任意の n に対して長さ n のゼロ埋めリストを返す
def replicate_zero : (n : Nat) -> Vec n := \(n : Nat) ->
    if n == 0 then nil else cons 0 (replicate_zero (n - 1))

replicate_zero 3                  -- [0, 0, 0]
[0, 0, 0] in (Vec 3)              -- true
```

refinement 型 (`{x : T | P(x)}` 形の型) も使えます:

```seki
def Pos := {x in Int | x > 0}
def succ_pos : Pos -> Pos := \(n : Pos) -> n + 1   -- 0 や負数は受け付けない
```

複数引数の依存関数 (連鎖):

```seki
def replicate : (n : Nat) -> Int -> Vec n := \(n : Nat) (v : Int) ->
    if n == 0 then nil else cons v (replicate (n - 1) v)

replicate 4 7                     -- [7, 7, 7, 7]
```

**注意**: 依存型の所属判定はサンプリングベース (Nat だと 0..5 の標本)。完全保証ではないですが、定義時の明らかなミスは捕まえられます。

### Bool が {false, true} に等しいことを示したい

組込 `Bool` は文字通り 2 元集合として実装されているので、`refl` で証明できる:

```seki
theorem bool_def : Bool == {false, true} := refl
theorem prop_def : Prop == {false, true} := refl
theorem prop_eq_bool : Prop == Bool := refl
```

これは seki の「集合 = 型」哲学の最も具体的な例です。

### 複数集合を一気に組み合わせたい

直積で組合せを生成:

```seki
def Days := {"Mon", "Tue", "Wed"}
def Slots := {1, 2, 3}

-- (曜日, 時間) の全組合せが Days times Slots
forall p in (Days times Slots),
    (fst p) in Days and (snd p) in Slots   -- true
```

直積上の forall は完全列挙されます (有限集合の場合)。

---

## 関数定義のパターン

### 再帰関数の書き方

`def` で名前づけすればグローバルから自分自身を呼べます:

```seki
def fact := \n -> if n == 0 then 1 else n * fact (n - 1)

def gcd  := \a b -> if b == 0 then a else gcd b (a mod b)

def fib  := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)
```

> ローカル `let f := \... f ...` は再帰しない (f はスコープ外)。

### リストを畳み込みたい

`foldr` を再帰で定義:

```seki
def foldr := \f init xs ->
    if null xs then init
    else f (head xs) (foldr f init (tail xs))

-- 合計
foldr (\x acc -> x + acc) 0 [1, 2, 3, 4, 5]    -- 15

-- 階乗 (1..n の積)
foldr (\x acc -> x * acc) 1 [1, 2, 3, 4, 5]    -- 120

-- 最大値
def max := \a b -> if a > b then a else b
foldr max 0 [3, 1, 4, 1, 5, 9, 2, 6]            -- 9
```

### 部分適用で関数を作りたい

カリー化された関数の引数を一部だけ与えると、残りを取る関数になります:

```seki
def add := \x y -> x + y
def addOne := add 1
def addTen := add 10

addOne 41           -- 42
addTen 5            -- 15
```

### 既存関数を組み合わせたい

合成も自分で書きます:

```seki
def compose := \f g x -> f (g x)
def doublePlusOne := compose (\n -> n + 1) (\n -> n * 2)

doublePlusOne 5     -- 11   (= (5*2) + 1)
```

### 型クラスでアドホック多相を表現したい

`class`/`instance` で「同じメソッド名を複数の型で実装する」構図を書けます。
内部的には辞書 record と projection 関数に desugar されます:

```seki
class Eq A where
    eq  : A -> A -> Bool ;
    neq : A -> A -> Bool

instance EqInt : Eq Int where
    eq  = \a b -> a == b ;
    neq = \a b -> a != b

instance EqStr : Eq String where
    eq  = \a b -> a == b ;
    neq = \a b -> a != b

eq 3 3                                -- true   (自動: Int → EqInt)
eq "hello" "hello"                    -- true   (自動: String → EqStr)
eq EqInt 3 3                          -- true   (明示的辞書も可)
```

メソッド呼び出しの **辞書は自動的に解決** されます: 第 1 引数の runtime 型 (Int/Bool/String/...) と class 名から `(class, type) → instance` テーブルを引いてインスタンス辞書を補完。
既に辞書値を渡した場合 (`eq EqInt 3 3` のように) は介入せずそのまま使う。
辞書を引数として持ち回す汎用関数も書けます:

```seki
class Ord A where
    lt : A -> A -> Bool ;
    le : A -> A -> Bool ;
    gt : A -> A -> Bool ;
    ge : A -> A -> Bool

instance OrdInt : Ord Int where
    lt = \a b -> a < b ;
    le = \a b -> a <= b ;
    gt = \a b -> a > b ;
    ge = \a b -> a >= b

def maxBy := \ord a b ->
    if (gt ord a b) then a else b

maxBy OrdInt 3 7                      -- 7
```

### 再帰関数の終了性 warning が出る

構造的に減少していると静的に確認できないと:

```
warning: termination of `myfn` not verified
         (recursive call #1 has no structurally-smaller argument)
```

これは false positive を含みます (= 実際は終了する関数でも検出できないことがある)。
減少として認識されるパターン:

| パターン | 例 |
|---|---|
| `p - C` (`C ≥ 1`) | `fact (n - 1)` |
| `p / C` (`C ≥ 2`) | `lg (n / 2)` |
| `e mod p` | `gcd b (a mod b)` (rem_euclid の結果は `|p|` 未満) |
| `tail p` / `snd p` | `listLen (tail xs)` |
| `treeLeft p` / `treeRight p` | tree 再帰 |
| `fst`/`snd` チェイン | `match xs with \| Cons h t -> f t` (desugar 後の `let t = fst (snd xs)` を辿る) |
| **辞書順 (lex)**: パラメータ並び替えで厳密に小さい引数タプル | `gcd a b -> gcd b (a mod b)` |

```seki
def fact := \n -> if n == 0 then 1 else n * fact (n - 1)            -- ✓ verified
def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)  -- ✓ verified
def gcd := \a b -> if b == 0 then a else gcd b (a mod b)            -- ✓ verified (lex)
def lg := \n -> if n <= 1 then 0 else 1 + lg (n / 2)                -- ✓ verified
def ack := \m n -> if m == 0 then n + 1
                   else if n == 0 then ack (m - 1) 1
                   else ack (m - 1) (ack m (n - 1))                 -- ✓ verified (lex)
def loop := \n -> loop n                                            -- warning
```

警告は実行を妨げないので、自分で終了することを確認できているなら無視して構いません。相互再帰、内側 lambda での shadow を経た減少は現状未対応。

---

## 証明のレシピ

### 集合の定義から forall を即座に得たい

集合の述語と命題の本体が一致する場合、`by eval` が**列挙せずに即座に真**を返します:

```seki
def Pos := {x in Int | x > 0}
theorem all_pos : forall p in Pos, p > 0 := by eval         -- ✓ 即時

def Even := {x in Nat | x mod 2 == 0}
theorem all_even : forall n in Even, n mod 2 == 0 := by eval -- ✓ 即時
```

`Nat`、`Int` 上の多項式関係も `by eval` だけで代数判定されます (無限域でも健全):

```seki
theorem nat_nn : forall n in Nat, n >= 0 := by eval          -- ✓
theorem sq_nn  : forall x in Int, x * x >= 0 := by eval      -- ✓ (PSD)
theorem distrib : forall a in Int, forall b in Int, forall c in Int,
    a * (b + c) == a * b + a * c := by eval                   -- ✓
```

`by algebra` を陽に書く必要はなくなりました (内部で同じ判定が走ります)。ただし `by eval` は決定不能な場合に**サンプル検証**にフォールバックして真を返すことがあるので、確実な無限域証明には `by algebra` / `by induction` を陽に使う方が安全です。

### 単純な等式を証明したい

`by eval` または `refl`:

```seki
theorem t1 : 2 + 2 == 4         := by eval
theorem t2 : (3 + 4) * 2 == 14  := refl
```

両者ほぼ同じですが、`refl` は意図 (「両辺を簡約して反射律で」) を明示できます。

### すべての要素について成り立つことを示したい

有限集合なら `by eval`:

```seki
def Range := {1, 2, 3, 4, 5}
theorem all_pos : forall x in Range, x > 0 := by eval
```

複数変数のネスト:

```seki
theorem demorgan
  : forall a in Bool, forall b in Bool,
        not (a and b) == (not a or not b)
  := by eval
-- Bool × Bool = 4 ケース全列挙
```

### 反例があるかを確認したい

検証器がエラーで反例を返してくれます:

```seki
theorem bad : forall x in {1,2,3,4,5}, x > 3 := by eval
-- proof error: proposition reduced to false
```

具体的な反例 (関数で範囲指定):

```seki
theorem bad2 : forall x in {1,2,3,4,5}, x > 3 := \x -> x
-- proof error: counterexample: with x = 1 the body is not true (got false)
```

### 代数恒等式を ℤ 全体で証明したい

`by algebra` を使う (`by eval` だと SAMPLE_BOUND までの標本検査になる):

```seki
theorem add_comm
  : forall a in Int, forall b in Int, a + b == b + a
  := by algebra

theorem distrib
  : forall a in Int, forall b in Int, forall c in Int,
        a * (b + c) == a * b + a * c
  := by algebra

theorem cube_expand
  : forall x in Int,
        (x + 1) * (x + 1) * (x + 1) == x*x*x + 3*x*x + 3*x + 1
  := by algebra
```

多変数・高次でも `+ - *` だけで書ければ通ります。

### 不等式を証明したい

`by algebra` は `==` だけでなく `<= >= < > !=` も扱います:

```seki
-- Nat 上
theorem nat_nn  : forall n in Nat, n >= 0 := by algebra
theorem succ_gt : forall n in Nat, n + 1 > n := by algebra

-- Int 上 (二次形式 PSD)
theorem cauchy
  : forall a in Int, forall b in Int, a*a + b*b >= 2 * a * b
  := by algebra

theorem perfect_square
  : forall x in Int, forall y in Int, x*x + 2*x*y + y*y >= 0
  := by algebra
```

3 次以上の不等式は (一般には) 通りません。`(a-b)²` のような完全平方系を狙うのがコツ。

### 整数除算/剰余の性質を証明したい

定数除数なら多項式断片で扱えます:

```seki
theorem half_double
  : forall n in Int, (2 * n) / 2 == n
  := by algebra

theorem div_floor
  : forall n in Int, (3 * n + 6) / 3 == n + 2
  := by algebra

theorem even_mod
  : forall n in Int, (2 * n) mod 2 == 0
  := by algebra

theorem odd_mod
  : forall n in Int, (2 * n + 1) mod 2 == 1
  := by algebra

theorem mod7_pattern
  : forall n in Int, (7 * n + 3) mod 7 == 3
  := by algebra
```

可変除数 (`/n`、`mod n` で `n` が変数) は対象外です。

### Σ系の公式を証明したい

再帰関数の仕様を ℕ 全体で証明するなら `by induction`:

```seki
def sum   := \n -> if n == 0 then 0 else n + sum (n - 1)
def sumSq := \n -> if n == 0 then 0 else n * n + sumSq (n - 1)

-- Gauss: 2*Σk = n(n+1)
theorem gauss
  : forall n in Nat, 2 * sum n == n * (n + 1)
  := by induction

-- 平方和: 6*Σk² = n(n+1)(2n+1)
theorem squares
  : forall n in Nat, 6 * sumSq n == n * (n + 1) * (2 * n + 1)
  := by induction
```

`by induction` は基底 `P(0)` と帰納段階 `P(k+1)` を多項式で自動判定します。

### リストの性質を証明したい

`forall xs in (List T), P(xs)` で構造帰納法が走ります:

```seki
def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)
def listSum := \xs -> if null xs then 0 else (head xs) + listSum (tail xs)

theorem ll_nn
  : forall xs in (List Int), listLen xs >= 0
  := by induction

-- append (右恒等元): xs ++ [] = xs
def appendL := \xs ys ->
    if null xs then ys
    else cons (head xs) (appendL (tail xs) ys)

theorem app_len_id
  : forall xs in (List Int), listLen (appendL xs nil) == listLen xs
  := by induction

theorem app_sum_id
  : forall xs in (List Int), listSum (appendL xs nil) == listSum xs
  := by induction
```

### 木の性質を証明したい

`forall t in (Tree T), P(t)` で 2 子木構造帰納法が走ります:

```seki
def treeSize := \t ->
    if isLeaf t then 0
    else 1 + treeSize (treeLeft t) + treeSize (treeRight t)

def treeSum := \t ->
    if isLeaf t then 0
    else (treeVal t) + treeSum (treeLeft t) + treeSum (treeRight t)

theorem ts_nn
  : forall t in (Tree Int), treeSize t >= 0
  := by induction

theorem ts_self
  : forall t in (Tree Int), treeSize t == treeSize t
  := by induction
```

### Fibonacci など多段階漸化式を扱いたい

`fib(n) = fib(n-1) + fib(n-2)` のような複数前段参照は `by strong_induction`:

```seki
def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)

theorem fib_nn : forall n in Nat, fib n >= 0 := by strong_induction
-- 基底: fib 0 = 0 ≥ 0, fib 1 = 1 ≥ 0
-- ステップ: fib (k+2) = fib (k+1) + fib k = (≥0) + (≥0) ≥ 0
```

普通の `by induction` (深さ 1) では `fib(k-1)` への参照を扱えないので失敗します。

### 関数定義を展開してから証明したい

ヘルパ関数を経由した命題は `by algebra` に直接渡すと「`sq` という関数が分からない」と怒られます。`by unfold` で 1 段 β-展開してから algebra に渡します:

```seki
def sq := \x -> x * x

theorem sq_is_mul
  : forall n in Int, sq n == n * n
  := by unfold sq then algebra
-- 1. unfold sq: `sq n` を `n * n` に展開 → goal は `n*n == n*n`
-- 2. algebra: 多項式恒等式 (両辺一致)
```

`by unfold` は **1 段のみ** なので再帰関数でも無限ループしません (置換後の本体に残った再帰呼び出しはそのまま)。複数の関数を展開したいときは `then` で連結:

```seki
def double := \x -> x + x
def quad   := \x -> double (double x)

theorem quad_is_4x
  : forall n in Int, quad n == 4 * n
  := by unfold quad then unfold double then algebra
```

### 補助補題を集めて証明したい

複数の基本恒等式を組み合わせて、`by algebra` では届かない命題を証明できます。`by simp [lemma1, lemma2]` で **方向付き書換え** として連鎖適用:

```seki
theorem add_zero : forall a in Int, a + 0 == a := by algebra
theorem mul_one  : forall a in Int, a * 1 == a := by algebra

theorem combined
  : forall y in Int, (y * 1) + 0 == y
  := by simp [mul_one, add_zero]
-- mul_one で `y * 1 → y`, add_zero で `y + 0 → y`、両辺一致
```

`by simp` (引数なし) は **proven な全等式 theorem** を使います。スコープを絞りたいときは `[...]` で明示。

### 戦術を連鎖したい

`then` で戦術を順次適用できます。**最後の戦術は closer** で goal を閉じる必要があります:

```seki
def sq := \x -> x * x
theorem add_zero : forall a in Int, a + 0 == a := by algebra

theorem chained
  : forall n in Int, sq n + 0 == n * n
  := by intros then unfold sq then algebra
-- 1. intros: forall を剥がす → goal: `sq n + 0 == n * n`
-- 2. unfold sq: → goal: `n*n + 0 == n*n`
-- 3. algebra: 多項式恒等式
```

組合せ典型:

| パターン | 用途 |
|---|---|
| `intros then algebra` | forall を明示的に剥がす |
| `unfold f then algebra` | 関数展開 + 多項式 |
| `intros then unfold f then algebra` | forall + 展開 + 多項式 |
| `intros then simp [l1]` | 仮定を free 化 + 規則書換え |
| `simp [l1] then algebra` | 部分書換え後 algebra |

### 数式を記号的に操作したい (微分・簡約)

`data` で数式を表現する Sym 型を定義し、`match` + 再帰で代数簡約・微分・積分を実装できます。詳細は `examples/26_cas.seki` 参照:

```seki
data Sym = SNum Int | SVar String | SAdd Sym Sym | SMul Sym Sym
         | SPow Sym Int | SSin Sym | SCos Sym

-- 記号微分: 連鎖律含む
def derive := \v e ->
    match e with
    | SNum _ -> SNum 0
    | SVar w -> if w == v then SNum 1 else SNum 0
    | SAdd u w -> SAdd (derive v u) (derive v w)
    | SMul u w -> SAdd (SMul (derive v u) w) (SMul u (derive v w))
    | SPow u n -> SMul (SMul (SNum n) (SPow u (n - 1))) (derive v u)
    | SSin u -> SMul (SCos u) (derive v u)
    | _ -> SNum 0

-- 例: d/dx (x^2 + sin x) = 2x + cos x
def f := SAdd (SPow (SVar "x") 2) (SSin (SVar "x"))
derive "x" f
```

代入による数値検証も書ける:

```seki
def subst := \v c e ->
    match e with
    | SVar w -> if w == v then SNum c else e
    | SAdd u w -> SAdd (subst v c u) (subst v c w)
    ...

-- 微分結果を x=3 で数値評価
evalAt "x" 3 (derive "x" f)
```

これにより **微積分学の基本定理** (∫f' = f) を数値テストで検証する theorem も書けます。

### exists の証拠を提示したい

`exists x in S, P(x)` は **witness** (証拠) を `:=` の後に書きます:

```seki
def Range := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}

theorem ex5     : exists x in Range, x >= 5 := 5
theorem some_ev : exists x in Range, x mod 2 == 0 := 4

-- 検証器は: x = 5 が Range に属するか + 5 >= 5 が真か を確認
```

witness が範囲外、あるいは命題を満たさないとエラー:

```seki
theorem bad : exists x in {1,2,3}, x == 5 := 5
-- proof error: witness 5 is not in declared domain {1, 2, 3}
```

連立条件 (パズル):

```seki
def Ages := {1, 2, 3, ..., 20}
theorem ages_solvable
  : exists a in Ages, exists b in Ages, exists c in Ages,
        (a + b + c == 27)
            and (a == b + 3)
            and (c == 2 * b)
  := 9   -- a (Alice) = 9 が連立解の 1 つ
```

外側の exists の witness を提示すると、内側の exists は自動列挙で確認されます。

---

## トラブルシューティング

### 「unbound identifier 'foo'」

`foo` が `def` されていない、あるいはタイプミスです。`:defs` で登録済みの名前を確認してください。再帰関数を書くときは `def` でグローバル登録すること (ローカル `let` は再帰しません)。

### 「proof error: proposition reduced to false」

命題が偽です。命題を REPL で評価して反例を探すと早い:

```seki
forall x in {1,2,3,4,5}, x > 3   -- false が表示される
```

### 「by algebra: cannot prove ... over Int」

多項式の符号判定で証明できなかった命題。考えられる原因:

- 不等式が常には成立しない (反例がある)
- 3 次以上で PSD 判定の対象外
- 関数適用が両辺で textually 異なる原子になっている

回避策: 命題を別の形に書き直す (例: `(a-b)*(a-b) >= 0` を `a*a + b*b - 2*a*b >= 0` に展開)、または `by induction` を試す。

### 「by induction: step case fails」

帰納段階の差分が多項式として一致しなかった。次を確認:

- 関数の再帰定義が **`if n == 0 then base else step n (f (n-1))`** の形か (典型的な primitive recursion)
- LHS と RHS の両方に同じ再帰関数が現れているなら原子が対称的にキャンセルするはず
- そうでない場合、命題の整理を見直す

### 「runtime error: cannot enumerate ...」

`Nat`、`Int`、`String` のような無限集合 / 関数空間 / `List T` などを `forall` で総当たりしようとしています。

- 多項式恒等式なら `by algebra`、再帰仕様なら `by induction` を使う
- 列挙したいなら有限部分集合で囲む: `{x in Nat | x <= 100}` など

### REPL での複数行入力

REPL は構文エラーで未完了と判断したら自動で複数行モードに移ります (`....` プロンプト)。空行を入れるとあきらめます。

### 大文字/小文字の予約語

`Nat`, `Int`, `Bool`, `String`, `Prop`, `Set`, `Tree`, `List` などは大文字で始まる**型**。識別子としても使えますが、上書きすると組込が見えなくなるので避けるのが無難。

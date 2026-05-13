# 言語仕様

このドキュメントは seki 言語の構文と意味論を網羅する。具体例は `examples/` を参照。

## 目次

1. [字句要素](#1-字句要素)
2. [トップレベル宣言](#2-トップレベル宣言)
3. [式](#3-式)
4. [演算子と優先順位](#4-演算子と優先順位)
5. [型 = 集合](#5-型--集合)
6. [集合の定義](#6-集合の定義)
7. [タプル・リスト・直積](#7-タプル--リスト--直積)
8. [ラムダ計算](#8-ラムダ計算)
9. [量化子](#9-量化子)
10. [型注釈と検査](#10-型注釈と検査)
11. [組込関数とプレリュード](#11-組込関数とプレリュード)

---

## 1. 字句要素

### コメント

```seki
-- 行コメント
{- ブロックコメント (開きの後に空白が必須) -}
```

ブロック開きの `{-` の直後は空白でなければならない。`{-3, ...}` のような負数始まりの集合リテラルと衝突しないため。

### リテラル

| 種類 | 例 |
|---|---|
| 整数 | `0`, `42`, `-7` (`-7` は単項マイナス) |
| 実数 | `1.5`, `0.0`, `3.14`, `1.0e10` |
| 真偽 | `true`, `false` |
| 文字列 | `"hello"`, `"line\nbreak"` |

整数は 64 ビット符号付き、実数は IEEE-754 `f64`。実数リテラルは小数点 `.` の前後に必ず数字が要る (`1.0` は OK、`1.` は不可)。文字列のエスケープは `\n \t \r \\ \"`。

### 識別子

英字または `_` で始まり、英数字・`_`・`'` を含む。`xs'`, `n_0`, `Foo` など。

### 予約語

```
def     theorem  axiom    type     by
let     in       where    if       then     else
lambda  fn       forall   exists
true    false    and      or       not
subset  union    intersect diff    times    notin    mod
data    match    with      import   as
Prop    Set      Nat      Int      Real     Bool     String
```

`Prop`, `Set`, `Nat`, `Int`, `Bool`, `String` は組込集合の名前として予約されているが、識別子として現れる場面では同名のグローバルとして解決される。

### 演算子トークン

`->`, `=>`, `:=`, `==`, `!=`, `<=`, `>=`, `<`, `>`, `+`, `-`, `*`, `/`,
`(`, `)`, `{`, `}`, `[`, `]`, `,`, `;`, `:`, `|`, `\`, `.`, `=`, `?`

`=` 単独はパーサ上は `:=` と等価に扱われる場面がある (`let x = 5 in ...`)。`?` は `let x = expr ? in body` の形でのみ意味を持ち (Result 伝播)、それ以外の文脈では使えない。`.` は `Module.name` の修飾アクセスのみ。

---

## 2. トップレベル宣言

プログラムは宣言の列。各宣言の終端は次の宣言のキーワード、または改行 (関数適用の同行制約による暗黙終端)、または `;`。

### `def` — 値・関数・集合の定義

```seki
def name := expression                       -- 型推論
def name : Type := expression                -- 型注釈
def name (p1 : T1) (p2 : T2) : R := body     -- 関数定義 (糖衣)
def name p1 p2 := body                       -- 引数あり、型省略
```

引数構文は `\p1 p2 -> body` への糖衣。`def f x y := body` は `def f := \x y -> body` と等価。型注釈付きの場合、各パラメータと戻り値型を `T1 -> T2 -> R` にカリー化して構築する。

### `theorem` — 定理

```seki
theorem name : Proposition := proof
```

`proof` は次のいずれか:

| 戦術 | 形式 | 概要 |
|---|---|---|
| 簡約 | `by eval` | 命題を `true` に簡約 |
| 反射 | `refl` | 等式 `a == b` の両辺の構造的等価 |
| 代数 | `by algebra` | 多項式正規化 + 符号解析 (`==`/`!=`/`<`/`<=`/`>`/`>=` + 定数 div/mod + PSD 2次形式) |
| 帰納 | `by induction` | Nat / List / Tree 上の構造帰納法 |
| 強帰納 | `by strong_induction` | 深さ 2 の強帰納法 (ℕ 専用、Fibonacci 等) |
| 書換え | `by simp` または `by simp [l1, l2]` | 既存の等式 theorem を方向付き書換え規則として連鎖適用 |
| 展開 | `by unfold f` | 関数 f の定義を 1 段 β-展開 (transformer; closer と組合せる) |
| 導入 | `by intros` | 先頭の forall を剥がし free var 化 (transformer) |
| 合成 | `by t1 then t2 [then t3 ...]` | 戦術を順次適用、最後の `tn` は closer で閉じる |
| 証明項 | 任意の式 | Curry-Howard 風 (forall は関数、exists は witness) |

詳細は [proofs.md](proofs.md)。

### `data` — 代数的データ型

```seki
data Maybe A = None | Some A
data Result E A = Err E | Ok A
data Tree A = Leaf | Node (Tree A) A (Tree A)
data Color = Red | Green | Blue | Mix Int
```

`data` は **構築子** (constructor) を自動的に `def` として定義します:
- 0 引数構築子 → 直接の値: `def None := ("None", ())`
- n 引数構築子 → 関数: `def Some := \x -> ("Some", (x, ()))`

内部はタグ付きペア (タグ = 構築子名の文字列)。型名 (`Maybe` 等) 自体は集合として自動定義されません — 必要なら手動で comprehension で定義できます。

### `match` — パターンマッチ

```seki
match expr with
| Pattern1 -> body1
| Pattern2 -> body2
...
```

サポートするパターン:

| パターン | 例 | 意味 |
|---|---|---|
| ワイルドカード | `_` | 何にでもマッチ、束縛なし |
| 変数 (lowercase) | `x`, `n`, `xs` | 何にでもマッチ、`x` に束縛 |
| 構築子 (Capitalized) | `None`, `Some x`, `Cons h t` | 構築子名のタグでマッチ、引数を束縛 |
| リテラル | `0`, `5`, `true`, `"hello"` | 値の同値でマッチ |
| 括弧付き | `(Cons (Some x) ys)` | ネストパターン |

**規約**: 大文字始まりの識別子は構築子、小文字始まりは変数束縛。命名で区別。

`match` は内部的に `if`/`let` 連鎖に desugar されます:

```seki
match m with | None -> 0 | Some n -> n
-- becomes:
let __match_0 = m in
if (fst __match_0) == "None" then 0
else if (fst __match_0) == "Some" then
    let n = fst (snd __match_0) in n
else error "non-exhaustive match"
```

### `import` — モジュール読込

```seki
import "path/to/module.seki"             -- 全名を現在のスコープに展開
import "path/to/module.seki" as M        -- M.name 形式の修飾アクセス
```

パスは現在のファイルのディレクトリからの相対 (絶対パスもサポート)。同じファイルの重複 import は無視され、循環 import は実行時エラー。`as` を付けると `M.name` 形式の修飾名も追加される (元の bare name も残る)。

### `?` 演算子 — Result のエラー伝播

```seki
let x = expr ? in body
```

`expr` が `Err e` なら `Err e` を即返却 (現在の式をその値に置き換え)、`Ok v` なら `v` を `x` に束縛して `body` 続行。形式上は次の desugar:

```seki
match expr with
| Err __qe -> Err __qe
| Ok x -> body
```

`?` は **let-value 位置でのみ** 有効。任意の式コンテキストでの使用は未サポート。

### `class` / `instance` — 型クラス

```seki
class Eq A where
    eq  : A -> A -> Bool ;
    neq : A -> A -> Bool

instance EqInt : Eq Int where
    eq  = \a b -> a == b ;
    neq = \a b -> a != b
```

これらはパース段階で純粋に desugar される:

- `class C A where m1 : T1 ; m2 : T2 ; ...` →
  - `data CDict A = MkCDict T1 T2 ...` (辞書 record)
  - 各メソッド `mi` のトップレベル projection 関数  
    `def m1 := \dict -> match dict with | MkCDict f1 f2 ... -> f1`
- `instance Inst : C T where m1 = e1 ; m2 = e2 ; ...` →
  - `def Inst := MkCDict e1 e2 ...`

使用時には辞書は **自動解決** されます (第 1 引数の runtime 型で `(class, type) → instance` テーブルを引く):

```seki
eq 3 3                   -- true   (自動: Int → EqInt)
eq 3 5                   -- false
eq "x" "y"               -- false  (自動: String → EqStr)
eq EqInt 3 3             -- true   (明示的辞書渡しも引き続き有効)
```

第 1 引数が既存の辞書値 (`MkCDict` タグ付き Tuple) なら介入せず、それ以外 (リテラル値・他の型の値) なら instance テーブルからの自動補完。複数メソッドは `;` で区切る (`;` を境にメソッド宣言を解釈)。

辞書を引数として持ち回す汎用関数も書ける:

```seki
def maxBy := \ord a b -> if (gt ord a b) then a else b
maxBy OrdInt 3 7         -- 7
```

### `axiom` — 公理

```seki
axiom name : Proposition
```

検証なしに命題を真として登録する。証明項は不要。表現の都合・未実装機能・前提条件などに使う。

### 式宣言

トップレベルに直接式を書くと、評価して結果を出力する (REPL 風)。

```seki
1 + 2 * 3            -- 7
"Mon" in Days        -- true
```

---

## 3. 式

### 基本式

```seki
42                       -- Int リテラル
true                     -- Bool リテラル
"hello"                  -- String リテラル
x                        -- 変数参照
(expr)                   -- 括弧
```

### 関数適用 (juxtaposition)

```seki
f x                      -- 単純適用
f x y z                  -- 多引数 (左結合: ((f x) y) z)
```

**重要:** 関数適用の引数は、**関数の頭と同じ行か、より深くインデント**されている必要がある。これがないと

```seki
1 + 2
10 mod 3
```

が `(1 + 2) 10 mod 3` と解釈されてしまう。

複数行の関数適用が必要な場合はインデントすること:

```seki
f x
  y    -- OK: より深いインデント
```

### `let` 束縛

```seki
let name = expr in body
let name : Type = expr in body
let name := expr in body          -- := も使える
```

`let` の値式中で `in` は集合所属演算子として扱われない (`let x = (5 in S) in ...` のような曖昧さを回避)。所属を let 値で使いたい場合は括弧で明示する。

### `if` 式

```seki
if cond then a else b
```

両分岐は同じ shape を持つ必要がある (Int と Bool を混ぜられない、ただし `Unknown` shape は許容される)。

### ラムダ抽象

```seki
\x -> body
\x y z -> body                                    -- 多引数 (カリー化)
\(x : Nat) (y : Bool) -> body                     -- 型注釈付き
lambda x y -> body                                -- lambda キーワード
fn x y -> body                                    -- fn (短い別名) も使える
```

### 集合リテラル

[6 章](#6-集合の定義)を参照。

### 量化子

```seki
forall x in Domain, body
exists x in Domain, body
```

[8 章](#8-量化子)を参照。

---

## 4. 演算子と優先順位

低 → 高の順。各段は左結合 (注釈のあるものを除く)。

| # | 演算子 | 説明 |
|---|---|---|
| 1 | `->` | 型矢印 (右結合) |
| 2 | `or` | 論理和 (短絡) |
| 3 | `and` | 論理積 (短絡) |
| 4 | `not` | 論理否定 (前置) |
| 5 | `==` `!=` `<` `<=` `>` `>=` `in` `notin` `subset` | 比較 (連鎖不可) |
| 6 | `union` `diff` | 集合の和・差 |
| 7 | `intersect` | 集合の積 (和より優先) |
| 7.5 | `times` | 直積 (intersect より優先) |
| 8 | `+` `-` | 加減 |
| 9 | `*` `/` `mod` | 乗除剰余 |
| 10 | `-` | 単項マイナス |
| 11 | (juxtaposition) | 関数適用 (左結合) |
| 12 | atom | リテラル・変数・括弧式・集合リテラル |

例:

```seki
-- 5 集合演算と算術: A ∪ ({1,2,3} ∩ {2,3})
def E := A union ({1, 2, 3} intersect {2, 3})

-- 6 -> は最も弱い: Nat -> Nat -> Bool は Nat -> (Nat -> Bool)
def cmp : Nat -> Nat -> Bool := \x y -> x < y

-- 7 比較は連鎖不可: a < b < c は書けない (a < b は Bool で、Bool < c は型エラー)
```

`/` は整数除算。剰余 `mod` は Rust の `rem_euclid` (常に非負) を使う。

---

## 5. 型 = 集合

seki では型は集合と同義。値 `v` が型 `T` を持つとは `v in T` のこと。

組込集合:

| 名前 | 内容 | 表現 |
|---|---|---|
| `Nat` | `{0, 1, 2, ...}` | atomic (内部表現は `i64`) |
| `Int` | 整数全体 | atomic (`i64`) |
| `Real` | 実数 (IEEE-754 `f64`) | atomic (`Int ⊂ Real`) |
| `Bool` | `{false, true}` | **literal Enum 集合** (`Bool == {false, true}` が `refl` で成立) |
| `String` | 文字列全体 | atomic |
| `Prop` | `Bool` のエイリアス | literal Enum 集合 |
| `Set` | すべての集合の集合 (universe) | atomic |

`Nat`, `Int`, `Real`, `String` は無限集合のため**列挙不可**。これらに対する `forall`/`exists` は `SAMPLE_BOUND` (デフォルト 200、Real は 7 個の標本値) までの標本検証となり、注意が必要 (健全な無限域証明には `by algebra` / `by induction` 等を使う)。

`Bool` は文字通り **2 元の Enum 集合**として実装されており、`Bool == {false, true}` は `refl` で証明可能。同様に `Prop == Bool == {false, true}`。これにより組込型が真に集合論的に基礎づけられている。

関数型は集合の関数空間として表される:

```seki
Nat -> Bool                  -- Nat から Bool への関数の集合
(Nat -> Nat) -> Nat -> Nat   -- 高階関数の型
```

関数値 (closure) が `A -> B` に属するかどうかは、`A` の標本要素を関数に適用して結果が `B` に属するか確認する**サンプル検査**で近似する。

### 依存関数型 `(x : A) -> B(x)`

引数の値に応じて返り値の型が変わる関数:

```seki
-- Vec n: 長さ n の整数リスト全体の集合 (型の家族)
def Vec := \(n : Nat) -> {xs in (List Int) | length xs == n}

-- (n : Nat) -> Vec n   ← 依存関数型
def replicate_zero : (n : Nat) -> Vec n := \(n : Nat) ->
    if n == 0 then nil else cons 0 (replicate_zero (n - 1))

replicate_zero 3                -- [0, 0, 0]   ∈ Vec 3
```

依存関数型 `(x : A) -> B(x)` の所属判定: 関数 `f` が属するとは「全 `a in A` に対し `f a in B[x:=a]`」。実装では `A` から数個の標本を取り、各標本で `B` を評価して member 判定する。任意の `a` で正しい保証は無いが、有限定義域では完全。

refinement 型 `{x : T | P(x)}` も依存型の特殊形 (B が x を「述語の真偽」に使うだけ):

```seki
def Pos := {x in Int | x > 0}
def succ_pos : Pos -> Pos := \(n : Pos) -> n + 1
```

連鎖した依存関数:

```seki
def append_typed : (n : Nat) -> (m : Nat) -> Vec n -> Vec m -> Vec (n + m)
    := \n m xs ys -> append xs ys
```

複合型は集合演算と組込関数で構成する:

| 型構成子 | 構文 | 意味 |
|---|---|---|
| 関数 | `A -> B` | A から B への関数の集合 |
| 直積 | `A times B times C` | n 項組 `(a, b, c)` の集合 (左結合でフラット化) |
| リスト | `List T` | T の有限リスト全体 (組込関数 `List : Set -> Set`) |
| 木 | `Tree T` | T の値を持つ二分木全体 (組込関数 `Tree : Set -> Set`) |
| 列挙 | `{1, 2, 3}` | 列挙される要素の集合 |
| 内包 | `{x in S \| P(x)}` | 述語を満たす要素 |

---

## 6. 集合の定義

### 列挙

```seki
def Days := {"Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"}
def Empty := {}
def Pair  := {1, 1, 2}    -- 重複は等価判定で吸収される
```

要素は任意の式で構わない (評価される)。等価性は値レベルの構造的等価。

### 内包 (述語)

```seki
def Pos      := {x in Int | x > 0}
def EvenNat  := {x in Nat | x mod 2 == 0}
def Vowels   := {c in {"a","e","i","o","u","b","c"} | c == "a" or c == "e"}
def Squares  := {n in {0,1,2,3,4,5,6,7,8,9} | exists k in {0,1,2,3}, n == k * k}
```

述語は `Bool` に評価される必要がある。所属判定 `v in S` は

1. `v` が `S` の domain に属するか
2. domain の文脈で述語を評価して `true` か

の両方を確認する。

### 集合演算

| 演算 | 意味 | 制約 |
|---|---|---|
| `A union B` | 和集合 | 両辺とも列挙集合のとき |
| `A intersect B` | 積集合 | 左辺が列挙可能 |
| `A diff B` | 差集合 | 左辺が列挙可能 |
| `A subset B` | 部分集合判定 (Bool) | 左辺が列挙可能 |
| `v in A` | 所属判定 (Bool) | 常に可 (内包なら述語評価) |
| `v notin A` | `not (v in A)` | 同上 |

無限の atomic 集合 (`Nat` 等) との `union` は現状サポートされていない。`intersect` / `diff` は左辺を列挙すれば右辺が無限でも動く (例: `{1,2,3,4} intersect EvenNat`)。

### 補集合

組込ではない。普遍集合 `U` を定義して `U diff X` で表現する慣習が examples/08 で使われている:

```seki
def U := {1, 2, 3, 4, 5, 6, 7, 8}
def comp := \X -> U diff X
```

---

## 7. タプル / リスト / 直積

### タプル

```seki
def p := (3, "hello", true)             -- ヘテロ三つ組
fst p                                    -- 3
snd p                                    -- "hello"
```

`()` は単位値、`(e)` は括弧付き式、`(e1, e2, …)` がタプル (要素 ≥ 2)。等価性は要素ごとに構造的。

### 二分木

```seki
def t := node (node leaf 1 leaf) 2 (node leaf 3 leaf)
isLeaf t           -- false
treeVal t          -- 2
treeLeft t         -- (node leaf 1 leaf)
treeRight t        -- (node leaf 3 leaf)
```

組込: `leaf : Tree`、`node : Tree -> A -> Tree -> Tree`、`isLeaf / treeVal / treeLeft / treeRight`。`Tree T` は要素集合 `T` を持つ二分木全体の集合 (組込関数 `Tree : Set -> Set`)。

```seki
def IntTree := Tree Int
leaf in IntTree                        -- true
node leaf 5 leaf in IntTree            -- true
```

### リスト

```seki
def xs := [1, 2, 3, 4, 5]
head xs           -- 1
tail xs           -- [2, 3, 4, 5]
cons 0 xs         -- [0, 1, 2, 3, 4, 5]
length xs         -- 5
append xs [10]    -- [1, 2, 3, 4, 5, 10]
reverse xs        -- [5, 4, 3, 2, 1]
toSet xs          -- {1, 2, 3, 4, 5}
nil               -- []
null nil          -- true
```

`map`、`filter`、`foldr` は組込ではないが、`cons / head / tail / null` で seki 自体で定義できる (examples/11)。

### 直積集合 (cartesian product)

```seki
def Pair := Nat times Bool
(5, true) in Pair                       -- true
(5, 7)    in Pair                       -- false (7 ∉ Bool)

def Coloring := Nat times {"red","blue"}
def Box := Nat times Nat times Nat      -- 三項以上もOK (左結合でフラット化)
```

直積上の `forall` は完全列挙される (有限なら):

```seki
forall p in (Small times Tags), (fst p) in Small
```

### List 型 (要素集合)

```seki
def IntList := List Int                  -- 整数の有限リスト全体
[1, 2, 3] in IntList                    -- true
```

`List : Set -> Set` は組込関数。要素集合に対して「その上の有限リスト全体」を返す。所属判定は要素ごとに再帰的に行われる。

---

## 8. ラムダ計算

評価戦略は **eager** (call-by-value)。`let`、関数適用、if 条件などの評価順は左から右、引数は呼び出し前に評価される。

### カリー化と部分適用

```seki
def add := \x y -> x + y
def addOne := add 1          -- 部分適用; addOne : Int -> Int
addOne 41                    -- 42
```

引数が足りない呼び出しは残りパラメータを持つクロージャを返す。引数が多すぎる場合、結果を再適用する。

```seki
((\x -> x) (\y -> y + 1)) 10    -- 11
```

### 再帰

`def name := body` ではグローバル登録が body 評価より**前**に行われるため、body 中の `name` 参照はグローバルから解決される (再帰可能)。

```seki
def fact := \n -> if n == 0 then 1 else n * fact (n - 1)
```

ローカル `let f := \... -> f ...` のような再帰は名前が外側のスコープに無いので動作しない。グローバル `def` を使うこと。

### 高階関数

```seki
def twice := \f x -> f (f x)
twice (\n -> n + 1) 5           -- 7
```

### 値の種類 (内部表現)

| 値 | 表示 |
|---|---|
| 整数 | `42` |
| 実数 | `1.5`, `3.14`, `0.0` (整数値の Real は `5.0` のように小数点付き) |
| 真偽 | `true` / `false` |
| 文字列 | `"hello"` |
| 集合 | `{...}`、`{x in S \| P}`、`Nat`、`A times B`、`List Int` 等 |
| タプル | `(a, b, c)` (要素 ≥ 2) |
| リスト | `[1, 2, 3]` |
| 二分木 | `leaf` / `(node l v r)` |
| クロージャ | `<fn:x,y>` |
| 組込関数 | `<builtin:name>` |
| Unit | `()` (空集合と同じ表記) |

---

## 9. 量化子

```seki
forall x in S, P              -- 全称 ∀x ∈ S. P
exists x in S, P              -- 存在 ∃x ∈ S. P
```

`,` の後はトップレベル式 (含意/等式/再ネストされた量化子など何でも可)。

### 評価規則

- `S` を列挙する。`SetVal::Enum` ならそのまま、`SetVal::Comp` なら domain を列挙して述語でフィルタ。
- 各要素 `e` で `x = e` の環境拡張下で `P` を評価。
- `forall`: 全要素で `true` なら `true`、いずれかで `false` なら `false`。
- `exists`: いずれかで `true` なら `true`、全要素で `false` なら `false`。

無限 atomic 集合は `SAMPLE_BOUND` までの標本で評価される (eval.rs の定数、デフォルト 200)。

```seki
forall x in Nat, x >= 0       -- true (0..199 の標本で確認)
exists x in Nat, x > 1000     -- false が返る (標本外なので不正確!)
```

確実な検証には**有限の定義域**を使うか、`by algebra` / `by induction` / `by strong_induction` 戦術を用いること (`docs/proofs.md` 参照)。これらは定義域全体に対して健全に証明する。

### ネスト

多変数の量化子はネストして書く:

```seki
forall a in Bool, forall b in Bool, (a and b) == (b and a)
```

3 変数以上のネストは計算量が積に増えるので、定義域サイズに注意。`by eval` で完全列挙する場合のみ留意点で、`by algebra` 等の代数的戦術では量化子の数は問題にならない。

---

## 10. 型注釈と検査

### 静的 shape 検査

すべての式に対して粗い shape (`Int` / `Bool` / `Str` / `Set` / `Tuple` / `List` / `Tree` / `Fn` / `Unit` / `Unknown`) を推論し、`1 + true` のような明らかな型エラーをパース直後に検出する。これは健全性のためではなく、エラーの早期発見のため。

### 集合所属による検査

`def name : T := value` という宣言があると:

1. `T` を評価して集合値を得る。
2. `value` を評価して値を得る。
3. `value in T` を `member` 関数で判定する。
4. 偽なら **type error** として宣言を拒否する。

```seki
def x : Pos := 7              -- OK
def x : Pos := -3             -- type error: -3 ∉ Pos
```

関数型 `A -> B` に対しては、`A` から数個の標本要素を取って関数に適用し、結果が `B` に属するかをチェックする。これは**完全な検査ではない**点に注意 (反例が見つからなければ通る)。

### 検査の限界

- 内包集合 `{x in S | P}` の中で `P` が複雑な場合、所属判定は述語評価時間に比例する。
- 関数型の検査は標本ベースなのでサウンドではない。健全性は別途 theorem で保証する設計。
- 依存型はない (戻り値型が引数値に依存する関数は表現できない)。

### 軽量な型推論

`def name := body` で型注釈が省略されたとき、`body` から最も具体的な型を推論する:

- ラムダ `\(x : T) -> e` のように引数注釈付きなら、戻り値の型を本体から推論し `T -> R` を構築。
- 注釈のないパラメータは `Set` (任意型) として残す。
- 本体が定数式や算術ならその結果の型 (`Int`, `Real`, `Bool`, `String`) を採る。

推論結果は `def double : (Set -> Int) = <fn:x>` のように出力に反映され、内部的には `Globals.inferred_types` に記録される。REPL では `:type expr` で式の推論型を直接問い合わせ可能。

### 終了性検査

`def f := \p1 .. pk -> body` で `body` 内に `f` への再帰呼び出しがあるとき、各呼び出しに対し
次のいずれかが成立することを確認する:

1. **少なくとも 1 つの引数が、対応するパラメータより構造的に小さい**。
2. **辞書順 (lex order)** で、パラメータの何らかの並び替えにおいて引数タプルが厳密に小さい。

小さいと認識されるパターン:

| パターン | 例 |
|---|---|
| `pi - C` (`C ≥ 1`) | `fact (n - 1)` |
| `pi / C` (`C ≥ 2`) | `lg (n / 2)` |
| `e mod pi` | `gcd b (a mod b)` (rem_euclid 結果が `|pi|` 未満) |
| `tail pi`, `snd pi` | `listLen (tail xs)` |
| `treeLeft pi`, `treeRight pi` | tree 子木への再帰 |
| `fst`/`snd` 任意チェイン (少なくとも 1 つ) | match パターン desugar 後の `let h = fst (snd xs)` 等で束縛された変数 |

`let`-束縛はチェイン的に解決される: `let t = fst (snd (snd xs)) in f t` の中の `t` は `xs` の構造より小さいと認識される。これにより `match xs with | Cons h t -> ... f t` の構造帰納が verified になる。

辞書順例: `gcd a b → gcd b (a mod b)` は `a, b` のどちらも単独では減少しないが、パラメータを `[1, 0]` の順に並べると `(b, a mod b)` が `(b, a)` より厳密に小さい (第一位置 `b == b`、第二位置 `a mod b < b`)。

確認できない場合 stderr に `warning: termination of \`f\` not verified ...` を出すが **定義は受理される** (false positive を許容)。相互再帰、内側 lambda での `f` shadow は現状未対応。

---

## 11. 組込関数とプレリュード

プレリュードは **2 層構造**:

1. **Rust 実装の低レベル組込** (atomic 集合・算術・比較・I/O・コンストラクタ/デストラクタ) — seki では表現できない原始関数。
2. **seki 言語で書かれた標準ライブラリ** (`src/stdlib.seki`) — 集合論的構築の上層。起動時に自動ロードされ、ユーザコードからは組込同様に使える。

### Rust 実装の組込関数 (真にミニマルなコア)

| 名前 | 型 | 内容 |
|---|---|---|
| `print` | `* -> Unit` | 値を改行付きで標準出力に書く |
| `error` | `Str -> *` | メッセージ付きで実行を panic させる |
| `card` | `Set -> Nat` | 列挙集合の濃度 (内包・無限集合では実行時エラー) |
| `fst` / `snd` | `Tuple -> *` | タプルの第 1/第 2 成分 (タプル原始演算) |
| `pair` | `* -> * -> Tuple` | 2 引数からタプルを作る |
| `intToReal` | `Int -> Real` | 整数→実数キャスト |
| `floor` / `ceil` / `round` | `Real -> Int` | 床・天井・四捨五入 |
| `sqrt` | `Real -> Real` | 平方根 (負引数は実行時エラー) |
| `pow` | `Num -> Num -> Num` | べき乗 (Int・Real 混在 OK) |
| `List` | `Set -> Set` | 要素集合から「その上の有限リスト全体」の集合を作る |
| `Tree` | `Set -> Set` | 「要素集合 A の二分木全体」の集合を作る |

そのほか:
- 算術演算子 `+ - * / mod`、比較演算子、Bool 演算子は **構文レベル** (式の評価で直接処理、関数ではない)
- 組込 atomic 集合 `Nat` / `Int` / `Real` / `String` / `Set` (Rust 値)、および `Bool = Prop = {false, true}` (literal Enum)
- `succ`/`pred`/`abs`/`id`/`pi`/`e` 等はすべて stdlib に移譲

> Rust と seki の分離基準は [internals.md の「Rust 層と seki 層の分離基準」](internals.md) を参照。要点: **(a) I/O・panic、(b) Value variant 操作、(c) 新 SetVal variant 生成、(d) 無限 atomic 集合、(e) f64 機械演算 — のいずれかに該当する場合のみ Rust**。それ以外はすべて `stdlib.seki`。

### seki で書かれた標準ライブラリ (`src/stdlib.seki`)

述語サブタイプ:

| 名前 | 定義 |
|---|---|
| `NatP` | `{x in Int \| x >= 0}` |
| `Pos` | `{x in Int \| x > 0}` |
| `Neg` | `{x in Int \| x < 0}` |
| `NonZero` | `{x in Int \| x != 0}` |
| `EvenInt` / `OddInt` | `{x in Int \| x mod 2 == 0/1}` |
| `EvenNat` / `OddNat` | 同上を Nat に絞ったもの |
| `Bit` / `Trit` | `{0,1}` / `{-1,0,1}` |
| `Byte` / `UInt8` | `{0..255}` |
| `Int8` | `{-128..127}` |
| `UInt16` / `Int16` | 16-bit 範囲 |

有理数 `Rat = Int × Pos`:

| 名前 | 説明 |
|---|---|
| `Rat` | 有理数集合 (= `Int times Pos`) |
| `mkRat n d` | コンストラクタ |
| `numer q` / `denom q` | アクセサ |
| `intToRat n` | 整数の有理数化 |
| `addRat` / `subRat` / `mulRat` / `negRat` | 算術 |
| `eqRat p q` | 同値判定 (cross-multiplication) |

リスト・木のコンストラクタ・デストラクタ + ユーティリティ:

リストはタグ付きペア符号化:
- `nil := (0, ())`
- `cons x xs := (1, (x, xs))`
- `null xs := fst xs == 0`
- `head xs := fst (snd xs)`
- `tail xs := snd (snd xs)`

木も同様:
- `leaf := (2, ())`
- `node l v r := (3, (l, (v, r)))`
- `isLeaf t := fst t == 2`
- `treeLeft / treeVal / treeRight` — fst/snd の組合せ

`[a, b, c]` 構文は parser が `cons a (cons b (cons c nil))` に desugar し、すべて stdlib 定義の関数で処理される。

| 名前 | 説明 |
|---|---|
| `length` / `append` / `reverse` / `toSet` | 基本リスト操作 |
| `range a b` | `[a, a+1, …, b-1]` |
| `map` / `filter` / `foldr` / `foldl` | 高階関数 |
| `sumList` / `maxList` | 集約 |
| `all` / `any` / `contains` | 述語クエリ |
| `singleton v` | `node leaf v leaf` |
| `treeSize` / `treeHeight` / `treeSum` | 木の集約 |
| `treeToList` | 中順序のリスト化 |

算術ヘルパ:

| 名前 | 説明 |
|---|---|
| `id` | 恒等関数 |
| `succ` / `pred` | `+1` / `-1` |
| `abs` / `absI` / `absR` | 絶対値 (Int / Real) |
| `maxOf` / `minOf` | 二項最大・最小 |
| `isEven` / `isOdd` | 偶奇判定 |
| `square` / `cube` | 二乗・三乗 |
| `powInt` | 整数べき乗 (非負指数のみ) |

組込集合: `Nat`, `Int`, `Bool`, `String`, `Prop`, `Set` (5 章参照)。

REPL では追加で次のコマンドが使える:

| コマンド | 内容 |
|---|---|
| `:q` / `:quit` / `:exit` | 終了 |
| `:help` | ヘルプ |
| `:defs` | 定義一覧 |
| `:type EXPR` | 式の推論型を表示 (Arrow 型まで再構築) |
| `:load FILE` | ファイルを読み込む |

---

## 文法 BNF (簡略)

```
program     ::= decl*
decl        ::= def | theorem | axiom | data | import
              | class_decl | instance_decl | expr
def         ::= 'def' ident param* (':' expr)? ':=' expr
theorem     ::= 'theorem' ident ':' expr ':=' proof
axiom       ::= 'axiom' ident ':' expr
data        ::= 'data' ident ident* ('='|':=') ctor ('|' ctor)*
ctor        ::= ident atom*
import      ::= 'import' string ('as' ident)?
class_decl  ::= 'class' ident ident+ 'where' method_sig (';' method_sig)*
method_sig  ::= ident ':' expr
instance_decl ::= 'instance' ident ':' ident expr 'where'
                  method_def (';' method_def)*
method_def  ::= ident ('='|':=') expr
proof       ::= 'by' tac_seq | 'refl' | expr
tac_seq     ::= tactic ('then' tactic)*
tactic      ::= 'eval' | 'algebra' | 'induction' | 'strong_induction'
              | 'simp' ('[' ident (',' ident)* ']')?
              | 'unfold' ident
              | 'intros'
param       ::= ident | '(' ident ':' expr ')'
expr        ::= lambda | let | if | forall | exists | arrow
arrow       ::= dep_arrow | or ('->' arrow)?       -- dep_arrow は (x : A) -> B 形
dep_arrow   ::= '(' ident ':' or ')' '->' arrow    -- 依存関数型
or          ::= and ('or' and)*
and         ::= not ('and' not)*
not         ::= 'not' not | cmp
cmp         ::= setadd (cmpop setadd)?
cmpop       ::= '==' | '!=' | '<' | '<=' | '>' | '>='
              | 'in' | 'notin' | 'subset'
setadd      ::= setmul (('union'|'diff') setmul)*
setmul      ::= times ('intersect' times)*
times       ::= add ('times' add)*                  -- 直積、左結合
add         ::= mul (('+'|'-') mul)*
mul         ::= unary (('*'|'/'|'mod') unary)*
unary       ::= '-' unary | app
app         ::= atom atom*                          -- 同行 or インデント継続
atom        ::= int | bool | string | ident
              | '(' expr ')' | '(' expr ',' expr (',' expr)* ')'    -- 括弧 or タプル
              | '[' (expr (',' expr)*)? ']'                          -- リスト
              | setlit
setlit      ::= '{' (expr (',' expr)*)? '}'
              | '{' ident 'in' expr '|' expr '}'
lambda      ::= ('\\'|'lambda'|'fn') param+ '->' expr
let         ::= 'let' ident (':' expr)? ('='|':=') expr '?'? 'in' expr
                                                          -- '?' triggers Result desugar
if          ::= 'if' expr 'then' expr 'else' expr
forall      ::= 'forall' ident 'in' expr ',' expr
exists      ::= 'exists' ident 'in' expr ',' expr
match       ::= 'match' expr 'with' arm+
arm         ::= '|' pattern '->' expr
pattern     ::= '_' | ident | int | real | string | bool
              | ident pattern*                       -- ctor with sub-patterns
              | '(' pattern ')'
```

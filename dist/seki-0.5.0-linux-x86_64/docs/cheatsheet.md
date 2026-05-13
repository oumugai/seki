# seki チートシート

1ページの構文・演算子・組込関数・戦術の早見表。詳細は [language.md](language.md) と [proofs.md](proofs.md) へ。

## 起動

```sh
cargo run -q -- file.seki      # ファイル実行
cargo run -q -- -e 'EXPR'      # ワンライナー
cargo run -q                   # REPL
```

REPL: `:q` `:help` `:defs` `:type EXPR` `:load FILE`

## リテラル

```seki
42        1.5        true        "string"        ()        nil        leaf
```

文字列エスケープ: `\n \t \\ \"`。`-3` は単項マイナス。Real は `1.5` / `3.14` / `1.0e10` (小数点必須)。

## コメント

```seki
-- 行コメント
{- ブロックコメント (開始の後に空白必須) -}
```

## 宣言

```seki
def name := expr                          -- 値
def name : Type := expr                   -- 型注釈付き
def name p1 p2 := expr                    -- 関数糖衣 (= def name := \p1 p2 -> expr)
def name (x : Nat) (y : Nat) : Bool := …  -- 完全注釈

data Foo A = Bar | Baz Int A              -- 代数的データ型
                                          -- (Bar / Baz が def として自動生成される)

class Eq A where                          -- 型クラス
    eq : A -> A -> Bool ;                 -- (辞書 record と projection に desugar)
    neq : A -> A -> Bool

instance EqInt : Eq Int where             -- インスタンス
    eq = \a b -> a == b ;                 -- (= 辞書値の def)
    neq = \a b -> a != b

import "path/file.seki"                    -- 全名を現在スコープへ
import "path/file.seki" as M               -- M.name で修飾アクセス

axiom name : Prop                         -- 検証なし公理
theorem name : Prop := proof              -- 機械検証
expr                                      -- トップレベル評価 (REPL風)
```

## 式

```seki
x                          -- 変数
\x y -> body               -- ラムダ (fn / lambda も可)
\(x : T) -> body           -- 型注釈付きパラメータ
f x y                      -- 関数適用 (左結合)
let x = e in body          -- let
let x : T = e in body
let x = e ? in body        -- Result 伝播 (? は let-value 専用)
if c then a else b
match e with | Pat -> body | Pat -> body  -- パターンマッチ
forall x in S, body
forall (x y z) in S, body  -- 多変数 sugar (共通ドメイン)
exists x in S, body
exists (x y) in S, body
(a, b, c)                  -- タプル
[1, 2, 3]                  -- リスト
{1, 2, 3}                  -- 列挙集合
{x in S | P}               -- 内包集合
A -> B                     -- 関数型 (右結合)
(x : A) -> B               -- 依存関数型 (B は x を参照可能)
A times B times C          -- 直積集合
```

## パターン

```seki
match e with
| _              -> ...    -- ワイルドカード
| x              -> ...    -- 変数束縛
| 0              -> ...    -- リテラル (Int/Real/Bool/Str)
| None           -> ...    -- 0-arg ctor
| Some x         -> ...    -- ctor + 変数束縛
| Some (a, b)    -> ...    -- ctor + tuple pattern (ネスト可)
| (a, b)         -> ...    -- 2-tuple
| (a, b, c)      -> ...    -- 3-tuple 以降も OK
| ((a, b), c)    -> ...    -- ネストタプル
```

match が `data` 型の全構築子を網羅していない場合、parse 時に warning が出る (実行は継続)。

## 演算子優先順位 (低 → 高)

| 段 | 演算子 | 例 |
|---:|---|---|
| 1 | `->` (右結合) | `Nat -> Bool` |
| 2 | `or` | `a or b` |
| 3 | `and` | `a and b` |
| 4 | `not` | `not a` |
| 5 | `==` `!=` `<` `<=` `>` `>=` `in` `notin` `subset` | `x in S` |
| 6 | `union` `diff` | `A union B` |
| 7 | `intersect` | `A intersect B` |
| 8 | `times` | `A times B` |
| 9 | `+` `-` | `1 + 2` |
| 10 | `*` `/` `mod` | `n mod 2` |
| 11 | 単項 `-` | `-x` |
| 12 | 関数適用 | `f x` |

## 組込集合 (型)

| 名前 | 内容 |
|---|---|
| `Nat` | `{0, 1, 2, …}` (無限) |
| `Int` | 整数全体 (無限) |
| `Real` | 実数 / `f64` (無限、`Int ⊂ Real`) |
| `Bool` | `{false, true}` (literal 2 元集合) |
| `String` | 文字列全体 (無限) |
| `Prop` | 命題 = `Bool` の別名 |
| `Set` | すべての集合の集合 |

## 集合演算

| 演算 | 意味 |
|---|---|
| `v in S` | 所属 |
| `v notin S` | 非所属 |
| `A subset B` | 部分集合判定 |
| `A union B` | 和集合 (両辺 Enum 限定) |
| `A intersect B` | 積集合 |
| `A diff B` | 差集合 |
| `A times B` | 直積集合 |
| `card S` | 列挙集合の濃度 |

## 組込関数

### エラー

```seki
error msg     -- panic with message      (Str -> *)
```

### 数値

```seki
succ n        -- n + 1                   (Int -> Int)
pred n        -- n - 1                   (Int -> Int)
n mod m       -- 剰余 (Int のみ、rem_euclid: 常に非負)
abs x         -- 絶対値                   (Int/Real -> Int/Real)
intToReal n   -- 整数→実数キャスト       (Int -> Real)
floor r       -- 床                       (Real -> Int)
ceil r        -- 天井                     (Real -> Int)
round r       -- 四捨五入                 (Real -> Int)
sqrt r        -- 平方根 (負はエラー)      (Real -> Real)
pow b n       -- べき乗                   (Num -> Num -> Num)
pi, e         -- 数学定数                 (Real)
```

Int + Real は **自動昇格**: `1 + 2.5 == 3.5`、`3 / 2.0 == 1.5`。`3 / 2` (両 Int) は整数除算で `1`。

### 関数操作

```seki
id x          -- 恒等
print x       -- 標準出力
```

### タプル

```seki
fst p         -- 第1成分
snd p         -- 第2成分
pair a b      -- (a, b) を作る
```

### リスト

```seki
nil                     -- []
cons x xs               -- 先頭追加
head xs / tail xs       -- 分解
null xs                 -- 空判定 (Bool)
length xs               -- 要素数
append xs ys            -- 連結
reverse xs              -- 反転
toSet xs                -- 重複削除→集合に変換
List T                  -- 要素集合 T のリスト全体
```

### 二分木

```seki
leaf                    -- 空木
node l v r              -- 内部ノード
isLeaf t                -- 葉判定 (Bool)
treeVal t               -- 根ノードの値
treeLeft t / treeRight t -- 子木
Tree T                  -- 値が T の二分木全体
```

### Option / Result (stdlib)

```seki
data Option A = None | Some A
data Result E A = Err E | Ok A

mapOption / bindOption / unwrapOr / isSome / isNone
mapResult / bindResult / isOk / isErr / unwrapResultOr
okOr / resultToOption
```

`?` 演算子: `let x = expr ? in body` で Result の Err を即返却。

### 標準ライブラリ (stdlib.seki — seki で書かれ自動ロード)

述語サブタイプ (集合):

```seki
NatP / Pos / Neg / NonZero
EvenInt / OddInt / EvenNat / OddNat
Bit / Trit / Byte / UInt8 / Int8 / UInt16 / Int16
```

有理数 `Rat = Int × Pos`:

```seki
mkRat n d / numer q / denom q / intToRat n
addRat / subRat / mulRat / negRat / eqRat
```

リスト・木操作 (高階関数):

```seki
range a b / map f xs / filter p xs / foldr / foldl
sumList xs / maxList xs / all p xs / any p xs / contains x xs
singleton v / treeSize t / treeHeight t / treeSum t / treeToList t
isEven / isOdd / square / cube / maxOf
```

## パターンマッチ

```seki
match e with
| _          -> ...      -- ワイルドカード (any)
| x          -> ...      -- 変数 (lowercase) で束縛
| Some x     -> ...      -- 構築子 (Capitalized) + 引数束縛
| None       -> ...      -- 引数なし構築子
| 0          -> ...      -- リテラル
| (Cons (Some x) ys) -> ...  -- ネスト (要括弧)
```

規約: 大文字始まり = 構築子、小文字始まり = 変数。マッチしないと `error "non-exhaustive match"`。

## 量化子の意味論

| 集合 | 評価方法 |
|---|---|
| 列挙 `{a, b, c}` | 全要素を列挙 (厳密) |
| 内包 `{x in S \| P}` | domain を列挙して P でフィルタ |
| `Bool` / `Prop` | 2 元完全列挙 |
| `Nat` | `0..200` までの標本検査 |
| `Int` | `-200..200` までの標本検査 |
| `String` / `Set` | 列挙不可 (エラー) |
| `Arrow` | 列挙不可 (エラー) |

無限集合上の forall を本気で証明したいときは `by algebra` / `by induction` / `by strong_induction` を使う。

## 9 つの戦術 + 合成

| 戦術 | 形式 | 種別 | 用途 |
|---|---|---|---|
| 簡約 | `by eval` | closer | 命題を `true` に簡約 |
| 反射 | `refl` | closer | 等式 `a == b` の構造的等価 |
| 代数 | `by algebra` | closer | 多項式 + 符号 + 定数 div/mod (∞ ✓) |
| 帰納 | `by induction` | closer | Nat / List / Tree 構造帰納法 (∞ ✓) |
| 強帰納 | `by strong_induction` | closer | 深さ 2 の Nat 強帰納法 |
| 書換え | `by simp` / `by simp [l1, l2]` | both | 等式 theorem を方向付き書換え規則として |
| 展開 | `by unfold f` | transformer | 関数 f の定義を 1 段 β-展開 |
| 導入 | `by intros` | transformer | 先頭の forall を剥がし free var 化 |
| 証明項 | `<expr>` | closer | forall→関数 / exists→witness |
| **合成** | `t1 then t2 [then t3 ...]` | — | 戦術を順次適用、最後は closer で閉じる |

```seki
theorem t1 : forall a in Int, a + 0 == a := by intros then algebra
theorem t2 : forall x in Int, sq x == x*x := by unfold sq then algebra
theorem t3 : forall n in Int, sq n + 0 == n*n := by intros then unfold sq then algebra
```

`by eval` は内部で次の自明判定を順に試す: (a) 内包述語 ≡ body → 即真、(b) 多項式関係の符号解析 (Nat/Int)、(c) 空集合 → vacuous、それでも判定できなければ要素列挙にフォールバック。

### 戦術選択フロー

```
命題が…
├─ 等式 (==) で両辺定数 → refl
├─ 多項式 / 不等式 / div mod by const   → by algebra
├─ 再帰関数の仕様 (∀n in Nat / List / Tree) → by induction
├─ Fibonacci 系 (多段階漸化式)         → by strong_induction
├─ 有限集合上の forall                  → by eval
├─ 既存補題の組み合わせで自明           → by simp [lemma1, lemma2]
├─ exists                              → witness を式として渡す
└─ それ以外                             → 命題を見直す or axiom
```

### `by simp` の使い方

```seki
theorem add_zero : forall a in Int, a + 0 == a := by algebra
theorem mul_zero : forall a in Int, a * 0 == 0 := by algebra

-- 引数なし: 全ての proven theorem/axiom を規則として使う
theorem t1 : forall x in Int, (x + 0) * 0 == 0 := by simp

-- 引数あり: 指定した補題のみを使う (添字符号も引っかけられる)
theorem t2 : forall x in Int, x + 0 == x := by simp [add_zero]
```

成功条件: 書換え後の goal が (a) `true`、(b) `e == e` 形 (両辺 alpha-同値)、または (c) eval で `true`。
注意: `add_comm` のような対称的な規則は両側に適用されて oscillate するため `by simp` は弱い。経由した全状態を覗くので 1 ステップ案件は通る。

## by algebra が扱える関係

`==`, `!=`, `<`, `<=`, `>`, `>=` のすべて。

| 領域 | sufficiency 条件 (≥ 0) |
|---|---|
| Nat | 全係数 ≥ 0 |
| Int | (a) 全変数偶指数 + 全係数 ≥ 0、または (b) 2 次形式 PSD (Sylvester 基準、最大 4 変数) |

定数除数 / mod 対応:

```seki
(2*n)/2 == n              -- ✓
(2*n+1) mod 2 == 1        -- ✓
n / 2                     -- 不透明原子化 (両辺で同形なら通る)
```

## by induction の関係対応

| 関係 | ステップ条件 |
|---|---|
| `==` | `lhs_diff == rhs_diff` (多項式等価) |
| `>=`, `>` | `lhs_diff >= rhs_diff` (IH スラックを利用) |
| `<=`, `<` | `lhs_diff <= rhs_diff` |
| `!=` | 非対応 |

## 反例の読み方

```
proof error: counterexample: with x = 3 the body is not true (got false)
                                  ↑反例の値    ↑命題本体    ↑実際の評価値
```

```
proof error: witness 5 is not in declared domain {1, 2, 3}
                  ↑提示した witness     ↑exists の domain
```

## 予約語 (識別子に使えない)

```
def let in where if then else
lambda fn forall exists theorem axiom type by
true false and or not
subset union intersect diff times notin mod
class instance import as data match with
Prop Set Nat Int Bool String
```

## 型クラスの使い方

```seki
class Show A where show : A -> String

instance ShowBool : Show Bool where
    show = \b -> if b then "true" else "false"

show true                           -- "true"  (自動辞書解決: Bool → ShowBool)
show ShowBool true                  -- "true"  (明示渡しも可)
```

複数メソッドは `;` 区切り。projection 関数 (`show`, `eq` 等) はトップレベルに自動定義され、引数の型から **インスタンス辞書が自動補完**される。第1引数が既存の辞書値ならそのまま使用、リテラル値 (Int/Bool/String/...) なら `(class, type) -> instance` テーブルで解決。

## 終了性検査

`def f := \p1 .. pk -> body` で `body` 内に再帰呼び出しがあると、各呼び出しに対し構造的減少を確認する。
減少として認識されるパターン:

| パターン | 例 |
|---|---|
| `p - C` (`C ≥ 1`) | `fact (n - 1)` |
| `p / C` (`C ≥ 2`) | `lg (n / 2)` |
| `e mod p` | `gcd b (a mod b)` |
| `tail p` | `listLen (tail xs)` |
| `snd p`, `fst (snd p)`, ... | match パターン束縛変数 (desugar 後の `fst`/`snd` チェイン) |
| `treeLeft p` / `treeRight p` | tree 構造再帰 |
| **辞書順 (lex)** | `gcd a b -> gcd b (a mod b)` (パラメータ並び替えで OK) |

`let`-束縛は再帰中に引数の正体まで辿られる (`let t = fst (snd xs) in f t` の `t` は `xs` より小と認識)。
確認できないと `warning: termination of \`f\` not verified ...` が stderr に出るが、**定義は受理される** (false positive 許容)。

## 型推論

```seki
def double := \x -> x * 2
-- 出力: def double : (Set -> Int) = <fn:x>
```

引数注釈 (`\(n : Nat) -> ...`) を付ければ Arrow 型が推論される。推論できなかったパラメータ部は `Set` (任意) として残る。
REPL: `:type expr` で式の推論型を直接表示。

## クイックレシピ

```seki
-- 集合と所属
def Pos := {x in Int | x > 0}
3 in Pos                         -- true

-- 関数 (型注釈)
def double : Nat -> Nat := \(n : Nat) -> n * 2

-- 再帰
def fact := \n -> if n == 0 then 1 else n * fact (n - 1)

-- forall 証明 (有限)
theorem dn : forall a in Bool, not (not a) == a := by eval

-- 代数恒等式 (無限)
theorem dist : forall a in Int, forall b in Int, forall c in Int,
    a * (b + c) == a * b + a * c := by algebra

-- 帰納法
def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
theorem gauss : forall n in Nat, 2 * sum n == n * (n + 1) := by induction

-- exists witness
theorem ex5 : exists x in {1,2,3,4,5}, x >= 5 := 5
```

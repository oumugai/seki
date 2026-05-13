# 7. stdlib の集合論的解釈

`src/stdlib.seki` で seki 自身が定義しているデータ構造の意味付け。
すべてタプル (= 順序対) のみを Rust プリミティブとし、それ以外は seki の中で
構築している。

## 7.1 List

```seki
data List A
-- 実装: タグ付きペア
def nil  := (0, ())
def cons := \x xs -> (1, (x, xs))
```

集合論的に:
```
List(A) = ⋃_{n ∈ ℕ} A^n
        = {nil} ∪ A × List(A)
```

各 `cons x xs` は順序対 `(1, (x, xs))`、`nil` は `(0, ())`。
有限再帰で構築されるため、`List(A)` の任意の元は **有限の構成過程** を持つ。

メンバ判定 `member(v, ListOf(T))`:
1. `v` がペアエンコードの list shape を持つ
2. 各要素 (recursively) が `T` のメンバ

## 7.2 Tree (二分木)

```seki
def leaf      := (2, ())
def node l v r := (3, (l, (v, r)))
```

集合論的に:
```
Tree(A) = {leaf} ∪ (Tree(A) × A × Tree(A))
```

タグ 2 / 3 を使うのは List の 0 / 1 と区別するため。

## 7.3 Option

```seki
data Option A = None | Some A
-- 脱糖: None = ("None", ()), Some x = ("Some", (x, ()))
```

集合論的に: `Option(A) = {nothing} ⊔ A`。

## 7.4 Result

```seki
data Result E A = Err E | Ok A
```

集合論的に: `Result(E, A) = E ⊔ A` (disjoint union)。

## 7.5 Rat (有理数)

```seki
data Pos := {x in Int | x > 0}
type Rat := Int times Pos
```

集合論的に: `ℚ = ℤ × ℕ⁺`、ただし通常の `(p, q) = (p', q')` 同一視 (`pq' == p'q`)
は seki では実装していない (canonical form を要求)。

## 7.6 Json

Phase 2 で追加された ADT:
```
data Json
  = JNull
  | JBool Bool
  | JNum Real
  | JStr String
  | JArr (List Json)
  | JObj (List (String × Json))
```

集合論的に:
```
Json = {null} ⊔ Bool ⊔ Real ⊔ String ⊔ List(Json) ⊔ FinMap(String, Json)
```

`FinMap(K, V)` は有限関数 K → V (の関数的部分集合 K × V)。

## 7.7 HttpRequest / HttpResponse

Phase 3:
```
HttpRequest  = Method × Path × Headers × Body
HttpResponse = Status × Headers × Body
```

各成分:
- Method = String
- Path = String
- Headers = List (String × String)
- Body = String
- Status = Int

## 7.8 Sym (CAS)

`lib/cas/sym.seki` で定義:
```
data Sym
  = SVar String
  | SNum Int
  | SAdd Sym Sym
  | SSub Sym Sym
  | SMul Sym Sym
  | SDiv Sym Sym
  | SPow Sym Int
  | SNeg Sym
  | SSin Sym | SCos Sym | SExp Sym | SLn Sym
```

集合論的に `Sym` は **記号式の集合**:
- atomic: 変数名 ∪ 整数
- 二項: `Sym × Sym` (+ ラベル付け)
- 単項: `Sym` (+ ラベル付け)

これは abstract syntax tree の集合論的記述で、seki から見るとタグ付きペア。

## 7.9 BigInt

`lib/cas/bigint.seki`:
```
data BigInt = BigInt Bool (List Int)
            -- 符号と桁配列 (1 桁 = 0..10^9-1)
```

集合論的に: `BigInt ≅ ℤ` (canonical form を持つ)。

## 7.10 Vector / Matrix

`lib/algebra/vector.seki` / `matrix.seki`:
```
type Vec(T) := List T               -- n-次元ベクトル (n は値レベル)
type Mat(T) := List (List T)        -- m×n 行列
```

集合論的に: ベクトルは `T^n` の元 (n は有限)、行列は `T^{m×n}` の元。

## 7.11 group / Ring / Field

`lib/algebra/structures.seki`:
```
data Group A      = MkGroup A (A -> A -> A) A (A -> A)
                    -- (要素集合, 演算, 単位元, 逆元)
data Ring A       = MkRing A (A -> A -> A) (A -> A -> A) A A (A -> A)
data Field A      = MkField ... (with inverse)
```

これらは **代数構造の bundle**。集合論的には:
```
Group ⊂ (Set, Op, Identity, Inverse) such that group axioms hold
```

axioms は `isGroup`/`isAbelianGroup`/`isRing`/`isField` 述語で検査
(`lib/algebra/axioms.seki`)。

## 7.12 補助関数

stdlib にはタグ付きペア操作のための helper が多数あります:

```
length / append / reverse / map / filter / foldl / foldr / range / take / drop
treeSize / treeMap / treeFold
isSome / isNone / mapOption / bindOption / unwrapOr
isOk / isErr / mapResult / bindResult / okOr
```

これらは Phase 1-5 で追加された system 開発系も含む:
- `forEach` (`mapM_` 相当)
- `readLines` / `writeLines` (`readFile` + `strSplit "\n"`)
- `newCounter` / `incr` / `decr` (Ref 上のヘルパ)
- `dictFromList` / `dictMap`
- `httpServe` (TCP listen + accept ループ)
- `httpOk` / `httpJson` / `httpHtml` / `httpNotFound`

## 7.13 まとめ

stdlib は **seki 自身で書かれている** ため:
- 実装が透明 — どう動くか読める
- 同じ集合論セマンティクスを共有
- 拡張は他の seki コード同様

タプル (Rust の `Value::Tuple`) は唯一の Rust 由来 ADT プリミティブ。
List / Tree / Option / Result / Json / Sym など、すべてはそこから集合論的に
構築されている。

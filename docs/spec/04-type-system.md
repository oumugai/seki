# 4. 型システム

## 4.1 基本原則: 型 = 集合

seki では型は集合と同一視される。
- `v : T` ≡ `v ∈ T`
- `Bool` は文字通り `{false, true}` (列挙集合)、`refl` で証明可能
- 関数型 `A -> B` は「A から B への関数の集合」
- 直積型 `A × B` は Cartesian product

## 4.2 型の構成子

| 構成子 | 例 | 意味 |
|---|---|---|
| Atomic   | `Nat`, `Int`, `Real`, `Bool`, `String` | 組込集合 |
| 列挙     | `{1, 2, 3}` | 有限集合 |
| 内包     | `{x in S \| P x}` | refinement type |
| 関数型   | `A -> B` | 非依存関数 |
| 依存型   | `(x : A) -> B(x)` | dependent function |
| 直積     | `A times B` | tuple type |
| List     | `List T` | T 上の有限リストの集合 |
| Tree     | `Tree T` | T 上の二分木の集合 |
| データ   | `data Maybe A = None | Some A` | ADT (列挙の sum + 直積) |

## 4.3 部分型 (Subtyping)

seki は **構造的部分型** を持たない (TypeScript / OCaml row poly のような
ものはない)。ただし以下の **集合包含** は自動的に効く:

- `Nat ⊂ Int` (自然数は整数)
- `Int ⊂ Real` (整数 → 実数自動昇格、例: `1 + 2.5 == 3.5`)

`v ∈ Real` は `v` が `Int` または `Real` (f64) のとき真。
`v ∈ Nat` は `v` が `Int` かつ `v ≥ 0` のとき真。

## 4.4 型推論

seki は **bidirectional な型推論** を持つ:

- リテラルから具体型を取得 (`42` は `Int`, `3.14` は `Real`)
- ラムダ + 引数型注釈 → 結果型推論
- `def f := \(x : Int) -> x * 2` で `f : Int -> Int` が推論される
- 注釈なしの場合は `Set` (universe) で fallback

推論器は `:type expr` REPL コマンドで起動できる。

## 4.5 型注釈 (`:`)

```seki
def double : Nat -> Nat := \(n : Nat) -> n * 2
```

注釈は **チェックされる** (実行時にサンプル検査ベース)。具体的に:

1. `T` の RHS を評価して set 値 `S` を得る
2. `value` を評価して値 `v` を得る
3. `member(v, S)` を実行
4. 失敗すれば `Type` エラー

依存型 `(x : A) -> B(x)` は `from = A` をサンプリングして
`apply(v, x) ∈ B[x:=v]` を確認する。これは **健全ではない**
(Phase 6+ で SMT 委譲予定)。

例外: `B(x)` が `IO X` 形のとき、サンプリングが副作用を発火するのを避けるため
**スキップ** される (Phase 5 IO 強制)。

## 4.6 Refinement Types

```seki
def Pos := {x in Int | x > 0}
def safeDiv : Pos -> Pos -> Real := \a b -> intToReal a / intToReal b
```

`Pos` は `Int` の述語付きサブセット。`safeDiv 3 0` は `b ∈ Pos` のサンプル
検査で fail する可能性がある (b = 0 は Pos ではない)。

**現状の不健全性**:
- `forall n in Nat, P(n)` のサンプリングは `n ∈ [0, 200)` のみ
- 巨大整数に対する反例は検出されない
- Phase 5 で `linarithProve` が一変数線形整数の健全な判定を提供 → これを
  refinement check に統合するのが Phase 6

## 4.7 代数的データ型 (`data`)

```
data Maybe A = None | Some A
data Tree A = Leaf | Node (Tree A) A (Tree A)
data Either A B = Left A | Right B
```

実装はタグ付きペア (`("CtorName", (a1, (a2, ..., ())))` 形式) への脱糖。

`enum-style` のデータ型 (引数なしコンストラクタのみ):

```
data Color = Red | Green | Blue
```

これは自動的に `Color := {Red, Green, Blue}` の set 化されるため
`forall c in Color, P(c)` がそのまま動く。

## 4.8 パターンマッチ

```
match e with
| Some x -> ...
| None   -> ...
```

- リテラル / 変数バインディング / コンストラクタ / `_` ワイルドカード
- タプルパターン: `Some (a, b)` で `Some` の引数を分解
- 網羅性 **警告** (エラーではない、Phase 6+ でエラー化検討)

## 4.9 型クラス (`class` / `instance`)

```seki
class Eq A where
    eq : A -> A -> Bool

instance EqInt : Eq Int where
    eq = \a b -> a == b
```

実装: `data EqDict` (record) と projection 関数への脱糖。
**辞書の自動解決**: `eq 3 3` で `Eq Int` インスタンスを自動補完。
明示的辞書渡し (`eq EqInt 3 3`) もサポート。

未対応:
- superclass constraints (`class Ord A where ... super Eq A`)
- multi-parameter type classes
- higher-kinded types

## 4.10 IO 型

```
IO : Set -> Set
```

現状は **恒等関数** (`IO A == A`)。型注釈時のサンプル検査をスキップする
マーカとして機能。

将来 (Phase 6+) の想定:
- effect tracking (`IO ⊥ Pure`)
- `do` notation
- `>>=` / `pure` の代数的法則

## 4.11 健全性 sumamry

| 構成子 | 健全性 |
|---|---|
| Atomic, Enum, 列挙集合 | ✅ |
| 関数型 (Arrow) | 🟡 sample-based |
| 依存型 (DepArrow) | 🟡 sample-based |
| Refinement | 🟡 sample-based、線形整数で linarith 強化 |
| Product (Tuple) | ✅ |
| ListOf, TreeOf | 🟡 sample 一定数 |
| ADT (`data`) | ✅ (構造一致なので健全) |
| Type Class | ✅ (辞書化なので健全) |

🟡 は将来の Phase で改善予定。詳細は `06-soundness.md` 参照。

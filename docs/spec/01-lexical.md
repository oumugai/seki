# 1. 字句構造

## 1.1 ソースエンコーディング

ソースファイルは **UTF-8** で記述。ただし識別子は ASCII のみ。
文字列リテラル中は任意の UTF-8 を含めて良い。

## 1.2 トークンの種類

```
Token  := Ident | Number | StringLit | Keyword | Operator | Punct | Eof
```

### 識別子 (Ident)

```
Ident      := IdentStart IdentCont*
IdentStart := ASCII-letter | '_'
IdentCont  := ASCII-letter | ASCII-digit | '_'
```

ただし以下のキーワードは識別子にならない:

```
def let in if then else match with
forall exists data class instance
import as theorem axiom by then
true false
and or not in notin union intersect subset times
mod
```

### 数値リテラル (Number)

```
IntLit   := ASCII-digit+
RealLit  := IntLit '.' IntLit              -- 0.1, 3.14
```

`-3` は `UnOp::Neg` 適用、リテラルそのものは無符号。
**16 進や指数表記は現状サポートしない** (Phase 7 で検討)。

### 文字列リテラル (StringLit)

```
StringLit := '"' StringChar* '"'
StringChar := AnyCharExceptQuoteAndBackslash | '\\' EscChar
EscChar    := '"' | '\\' | 'n' | 'r' | 't' | '0'
```

未対応: `\u{XXXX}` (Phase 7 候補)、行継続。

### 演算子 (Operator)

```
+ - * /                                  -- 算術
== != < <= > >=                          -- 比較
and or not                               -- 論理 (キーワード扱い)
in notin                                 -- 集合所属
union intersect                          -- 集合演算
times                                    -- 直積 (Cartesian product)
subset                                   -- ⊆
mod                                      -- 整数剰余
:=                                       -- 定義
->                                       -- 関数型矢印
=>                                       -- 命題含意
|                                        -- match の枝、内包の predicate 区切り
\                                        -- ラムダ (\x -> body)
?                                        -- Result/Option 早期 return
:                                        -- 型注釈
```

### 区切り (Punct)

```
( ) { } [ ] , ;
```

### コメント

```
LineComment  := '--' AnythingButNewline*
BlockComment := '{-' AnythingExceptCloseBlock* '-}'
```

ブロックコメントはネスト可能。

## 1.3 ホワイトスペース

スペース・タブ・改行・キャリッジリターンはホワイトスペース。
**インデントは構文に意味を持たない** (Python とは異なる)。

## 1.4 位置情報

各トークンには **1-indexed の line, col, end_col** が付随する。
パーサはこれを `LocatedDecl` の `line` / `col` フィールドに伝播する。
Phase 6 では Expr-level の span (失敗した式に対応する line:col + 長さ)
を一部の variant (Var/App/BinOp) に追加した。

**`end_col`** は **トークン直後の列**.  Phase 11 で導入され、`f(a, b)` (隣接)
と `f (a, b)` (空白あり) を区別するために使われる: パーサは
`prev.end_col == cur.col` を確認することで「直後」を判定する。

## 1.5 例

```seki
def factorial := \n ->         -- def 宣言
    if n == 0 then 1
    else n * factorial (n - 1)

theorem fact_5 : factorial 5 == 120 := by eval

def Evens := {x in Nat | x mod 2 == 0}  -- 集合 (内包)
def small_evens : Set := {0, 2, 4, 6, 8}  -- 集合 (列挙)
```

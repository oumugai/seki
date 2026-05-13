# 2. 構文 (BNF Grammar)

このページは seki 0.5.0 の構文を **BNF + 操作子優先順位表** で記述します。

## 2.1 プログラム

```
Program  := Decl*
Decl     := DefDecl | TheoremDecl | AxiomDecl | DataDecl
          | ClassDecl | InstanceDecl | ImportDecl | Expr

DefDecl       := 'def' Ident OptTypeAnnot ':=' Expr
TheoremDecl   := 'theorem' Ident ':' Expr ':=' ProofTerm
AxiomDecl     := 'axiom' Ident ':' Expr
DataDecl      := 'data' Ident TyParam* '=' DataAlt ('|' DataAlt)*
DataAlt       := Ident TypeArg*
ClassDecl     := 'class' Ident TyParam 'where' (Ident ':' Type)*
InstanceDecl  := 'instance' Ident ':' Ident Ident 'where' (Ident '=' Expr)*
ImportDecl    := 'import' StringLit ('as' Ident)?
OptTypeAnnot  := (':' Type)?
TyParam       := Ident
TypeArg       := Type
```

トップレベルの裸の式 (`1 + 2`) は REPL / ファイルどちらでも値を表示する
expression statement として扱われる。

## 2.2 式 (Expr)

優先順位は低い (緩い) → 高い (タイト) の順:

| 優先度 | 結合性 | 構文 |
|---|---|---|
| 1 | right | `=>`             (含意) |
| 2 | right | `or` |
| 3 | right | `and` |
| 4 | non    | `==`, `!=`, `<`, `<=`, `>`, `>=` |
| 5 | non    | `in`, `notin`, `subset` |
| 6 | left   | `union`, `intersect` (and 同義の差) |
| 7 | left   | `+`, `-` |
| 8 | left   | `*`, `/`, `mod` |
| 9 | non    | `times`           (直積、右結合) |
| 10 | right | `->`              (関数型矢印) |
| 11 | prefix | `not`, unary `-` |
| 12 | left   | application       (`f x y` = `(f x) y`) |
| —   | —      | atoms             (リテラル、`(...)`, `[...]`, `{...}`) |

```
Expr := IfExpr | LetExpr | LambdaExpr | MatchExpr | ForallExpr | ExistsExpr | ForExpr | OpExpr

IfExpr      := 'if' Expr 'then' Expr 'else' Expr
LetExpr     := 'let' Ident '=' Expr 'in' Expr
             | 'let' '_' '=' Expr 'in' Expr               -- 副作用専用
             | 'let' 'rec' Ident ':=' Expr 'in' Expr      -- 再帰
LambdaExpr  := '\' (Param)* '->' Expr
Param       := Ident | '(' Ident ':' Type ')'
MatchExpr   := 'match' Expr 'with' ('|' Pattern '->' Expr)+
ForallExpr  := 'forall' Quant ',' Expr
ExistsExpr  := 'exists' Quant ',' Expr
Quant       := Ident 'in' Expr
             | '(' Ident+ ')' 'in' Expr            -- 多変数 sugar

OpExpr     := LowPrec (Op LowPrec)*
LowPrec    := ...    -- 上記の優先順位表に従う

Pattern    := '_' | Ident | Ctor Pattern* | '(' Pattern+ ')'

ProofTerm  := 'by' Tactic ('then' Tactic)*
            | Expr                          -- Curry-Howard 風
Tactic     := 'eval' | 'refl' | 'algebra' | 'induction'
            | 'strong_induction' | 'simp' (Ident*)?
            | 'unfold' Ident | 'intros' | 'decide' | 'linarith'
```

## 2.3 型

```
Type     := 'forall' Ident 'in' Expr ',' Type        -- dep arrow (理論)
         | '(' Ident ':' Type ')' '->' Type           -- dep arrow (実用)
         | Type '->' Type                              -- 関数型
         | Type 'times' Type                           -- 直積
         | Expr                                         -- set 値の任意式
```

注: `Type` は実体としては Expr の subset。eval すると `SetVal` を返す式すべて
が型として通用する。

## 2.4 集合構築

```
Expr := '{' '}'                                   -- 空集合
      | '{' ExprList '}'                           -- 列挙
      | '{' Ident 'in' Expr '|' Expr '}'           -- 内包

ExprList := Expr (',' Expr)*
```

## 2.5 リスト / タプル

```
Expr := '[' ']'                                   -- 空リスト
      | '[' ExprList ']'                           -- リスト
      | '(' Expr ')'                                -- 括弧
      | '(' Expr ',' Expr (',' Expr)* ')'           -- タプル
```

リストはパーサが脱糖して `cons x (cons y (cons z nil))` のタグ付きペアに
展開する (`stdlib.seki` 参照)。

## 2.5a For-loop sugar (Phase 12)

Python 風の反復構文:

```
Expr := 'for' Ident 'in' Expr 'do' Expr
```

`for x in xs do body` は `forEach xs (\x -> body)` の脱糖.
意味的に等価で、副作用ループの慣用形.

```seki
for x in [1, 2, 3] do println(x)
for i in rangeTo(10) do println(intToStr(i * i))
for k in dictKeys(d) do match dictGet(k, d) with | Some v -> ... | None -> ()
```

複数式の body は `let _ = stmt1 in stmt2` チェーン or 括弧:

```seki
for i in rangeTo(3) do
    let _ = println(strConcat("iter ", intToStr(i))) in
    println(intToStr(i * 100))
```

ネストも自然:

```seki
for i in rangeTo(3) do
    for j in rangeTo(3) do
        println(strJoin("", [intToStr(i), ",", intToStr(j)]))
```

## 2.5b 関数呼出 (Phase 11)

seki は **2 種類の呼出構文** を持つ。両者は意味的に等価:

### Juxtaposition (ML/Haskell 流、空白区切り)

```
f a b c     -- App(f, [a, b, c]) — curried
```

### C 流 (Phase 11 で追加)

```
f(a, b, c)  -- App(f, [a, b, c]) — 同等
```

**`f` と `(` が隣接** (間に空白なし) であることが識別子になる。
これは `f (a, b)` (タプル 1 引数) との曖昧さを避けるため:

| 構文 | パース結果 |
|---|---|
| `f(a, b)`  | `App(f, [a, b])` — C 流 2-引数呼出 |
| `f (a, b)` | `App(f, [Tuple(a, b)])` — タプル 1-引数 |
| `f()`      | `App(f, [()])` — Unit 引数呼出 |
| `f ()`     | `App(f, [()])` — 同上 (空白あり) |
| `f(a)(b)`  | `App(App(f, [a]), [b])` — 高階呼出のチェーン |
| `(\x -> x*2)(5)` | 即時呼出 (lambda → 直接呼ぶ) |

混在可能:

```seki
-- 混在例
strJoin(",", ["a", "b", "c"])      -- C 流
strJoin "," ["a", "b", "c"]         -- curried、結果同じ

let f = \x y -> x + y in f(3, 4)    -- C 流
let f = \x y -> x + y in f 3 4      -- curried、結果同じ
```

## 2.6 例

```seki
-- def + type annotation + lambda
def double : Nat -> Nat := \(n : Nat) -> n * 2

-- match
def safeDiv := \a b ->
    if b == 0 then None else Some (a / b)

-- 内包集合
def Evens := {x in Nat | x mod 2 == 0}

-- forall + theorem
theorem evens_double : forall n in Nat, 2 * n in Evens := by induction
```

## 2.7 互換性ノート

seki は pre-1.0 なので将来の構文追加で衝突する可能性がある予約候補:

- `do` notation (今後 IO モナド強制で導入予定)
- `where` 句 (let の代替)
- `private` / `pub` 可視性
- `record` 構造

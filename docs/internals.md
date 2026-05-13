# 実装アーキテクチャ

このドキュメントは seki の Rust 実装の構造・データフロー・拡張ポイントを説明する。コードを読むときの地図として使うことを想定している。

## 目次

1. [モジュール一覧](#1-モジュール一覧)
2. [パイプライン](#2-パイプライン)
3. [AST](#3-ast)
4. [値とランタイム表現](#4-値とランタイム表現)
5. [評価器](#5-評価器)
6. [型チェッカ](#6-型チェッカ)
7. [Prover](#7-prover)
8. [プレリュードと組込関数](#8-プレリュードと組込関数)
9. [テストと例題の駆動](#9-テストと例題の駆動)
10. [型クラスの自動辞書解決](#10-型クラスの自動辞書解決)
11. [エラーと診断](#11-エラーと診断)
12. [今後の拡張](#12-今後の拡張)

---

## 1. モジュール一覧

```
src/
├── lib.rs        SekiError 型 + parse_program() 公開 API + モジュール公開
├── lexer.rs      tokenize(&str) -> Vec<Token> (data/match/with/import/as/?/class/instance/Real 対応)
├── ast.rs        Expr / Decl (Def/Theorem/Axiom/Expr/Import/ClassMeta/InstanceMeta) /
│                 Proof (9 戦術 + Seq combinator) / LocatedDecl /
│                 BinOp / UnOp / Param + subst (公開) + alpha_equiv
├── parser.rs     再帰下降 + Pratt 風 (parse_program / parse_expr_str) +
│                 パース段階 desugar:
│                   data Foo = A | B T  →  def A := ("A", ()), def B := \x -> ...
│                   match e with | pat -> body | ...  →  if/let チェーン
│                   let x = e ? in body              →  match e | Err -> Err | Ok x -> body
│                   import "path" [as M]             →  Decl::Import (実体は main で処理)
│                   M.name (compound identifier)     →  Var("M.name") 直接参照
│                   (x : A) -> B(x)                  →  Expr::DepArrow (依存関数型)
│                   class C A where m1:T1 ; m2:T2    →  data CDict A = MkCDict T1 T2
│                                                      + def m1 := \dict -> match ... | MkCDict f1 _ -> f1
│                   instance Inst : C T where m1=e1  →  def Inst := MkCDict e1 e2
│                 lookahead `peek_at(1)` で `<id> =` / `<id> :` の binding shape を判定し
│                 メソッドループの過剰消費を防ぐ
├── termination.rs 構造的減少 + 辞書順による再帰の終了性検査:
│                   check(name, params, body) -> TerminationStatus
│                   - n - C (C >= 1) / n / C (C >= 2)
│                   - e mod p (rem_euclid bound)
│                   - tail / snd / treeLeft / treeRight
│                   - fst/snd の任意チェイン (match パターン束縛変数)
│                   - 辞書順 (lex): パラメータ並び替えのいずれかで引数タプルが
│                     厳密に小さい場合受理 (gcd, ackermann)
│                   let-binding を substitution map として追跡し、
│                   match desugar 後の `let h = fst (snd xs) in ...` も処理。
│                   inner lambda での name shadow を考慮、相互再帰は未対応
├── value.rs      Value (Int/Real/Bool/Str/Set/Tuple/Closure/Builtin/Unit) /
│                 SetVal (Enum/Comp/Atomic/Arrow/DepArrow/Product/ListOf/TreeOf) /
│                 AtomicSet (Nat/Int/Real/Bool/Prop/StringS/Universe) / Env / Globals /
│                 render_as_list / render_as_tree / render_as_ctor
├── eval.rs       EvalCtx::eval / apply / member / make_builtin_prelude (真にミニマル: 
│                 print / error / card / fst / snd / pair / intToReal / floor / ceil /
│                 round / sqrt / pow / List / Tree / pi / e / atomic 集合) +
│                 install_stdlib (seki stdlib を起動時評価) +
│                 try_forall_from_definition / try_exists_from_definition (集合定義からの
│                 自明判定)
├── stdlib.seki   seki で書かれた標準ライブラリ:
│                 - リスト/木のコンストラクタ・デストラクタ (タグ付きペア符号化)
│                 - 有理数 (Rat = Int × Pos) と演算
│                 - Option / Result + map/bind/unwrapOr/okOr 等の Monad 風ヘルパ
│                 - 述語サブタイプ (Pos / Byte / Int8 / Even / Odd / ...)
│                 - 高階関数 (map / filter / foldr / foldl / range / sumList / ...)
│                 - 算術ヘルパ (succ / pred / abs / square / cube / powInt / maxOf / ...)
│                 include_str! で埋め込み、起動時に自動ロード
├── algebra.rs    Polynomial / div_const / mod_const / 多項式正規化 / 符号解析
│                 (polynomial_pos / nonneg / nonpos / neg) / quadratic_psd (Sylvester)
├── typecheck.rs  Shape / ShapeEnv / check_shape / check_value_in +
│                 軽量な型推論 (TypeEnv / infer_type / prelude_types) — Arrow 型まで再構築
├── prover.rs     Prover::verify (by eval / refl / by algebra / by induction (Nat/List/Tree) /
│                 by strong_induction / by simp / by unfold / by intros / 証明項 + Seq 合成
│                 の 9 戦術 + combinator) + run_step (TacOutcome) + unfold_calls +
│                 simplify_list_ops / simplify_tree_ops +
│                 SimpRule / collect_simp_rules / simp_rewrite / match_pattern
└── main.rs       CLI / REPL / ProgramState (decl 駆動ループ + import ローダ
                  + base_dirs スタック + loaded/loading セット + insert_tracker +
                  annotate_error: Decl の line/col を Type/Runtime/Proof エラーに付与)
```

### プレリュードの 2 層構造

`make_prelude()` は次の順で実行される:

1. **`make_builtin_prelude()`** — Rust 実装の atomic 集合 (`Nat`/`Int`/`Real`/`Bool`/…) と低レベルプリミティブ (`fst`/`snd`/`pair`/`print`/`error`/`card`/`List`/`Tree`/Real 機械演算) を `Globals` に登録。
2. **`install_stdlib()`** — `include_str!("stdlib.seki")` で埋め込んだ seki ソースを `parse_program` でパース、各 `def` を 1 件ずつ評価して `Globals::defs` に登録。途中の def は前のものを参照可能。

stdlib のパース失敗・評価失敗は **panic** で報告 (build-time bug として扱う)。これによりエンドユーザは常に整合の取れた prelude を手にする。

各モジュールは独立しており、依存方向は **lib < lexer < ast < parser, value < eval < (typecheck, prover) < main**。循環なし。

### Rust 層と seki 層の分離基準

「Rust で書くか seki で書くか」の判断は **次のチェックリスト** で行う。
**1 つでも `はい` に該当するものだけ Rust に置く** —— それ以外は `stdlib.seki` で書く。

| 条件 | Rust に置く理由 |
|---|---|
| (a) **副作用** が必要か (I/O / OS リソース / panic) | seki は純粋関数のみ。`print`/`error` のような I/O は Rust に必須。 |
| (b) **Value enum の variant** に直接アクセスする必要があるか | seki から `Tuple` や `Set` の内部表現は触れない。`fst`/`snd`/`pair`/`card` がこれ。 |
| (c) **新しい `SetVal` の variant** を生成する必要があるか | 例: `List T` は `SetVal::ListOf` を作る。これは seki では生成不可能。`List`/`Tree` 型コンストラクタが該当。 |
| (d) **無限集合の atomic 表現** が必要か | `Nat`/`Int`/`Real`/`String`/`Set` は列挙不可なので `SetVal::Atomic` として Rust 側で扱う。 |
| (e) **Rust の機械演算 (f64 ops 等)** が必要か | `floor`/`ceil`/`round`/`sqrt`/`pow`/`intToReal` は IEEE 754 演算を直接使う。 |

逆に **次のものはすべて seki 層 (`stdlib.seki`) に置く**:

- 値 (定数を含む) — `pi`, `e` は値であり計算ではないので seki でよい (`def pi := 3.141592653589793`).
- 既存プリミティブの組み合わせで定義できる関数 — `succ`/`pred`/`abs`/`maxOf`/`square`/...
- ADT の構築子・分解子 — `nil`/`cons`/`head`/`tail`/`leaf`/`node`/`isLeaf`/...  
  (タグ付きペアによる集合論的構築。`fst`/`snd` のみが Rust プリミティブ)
- 述語サブタイプ — `Pos`/`Neg`/`Even`/`Byte`/`Int8`/...  
  (内包集合 `{x in T | P}` で定義)
- 高階関数・コレクション操作 — `map`/`filter`/`foldr`/`range`/`length`/...
- エラー / 失敗の表現 — `Option`/`Result` + `mapOption`/`bindResult`/`okOr`/...
- `data` 宣言 — Rust 側に hard-code するのではなく、構文糖として処理して seki 側に登録。

#### 判断フロー

```
新しい関数 / 値 X を追加したい
        │
        ▼
(a) X は I/O や panic を伴うか? ──────────── Yes ──→ Rust (eval.rs)
        │ No
        ▼
(b) Value の variant を直接触る必要があるか? ── Yes ──→ Rust
        │ No
        ▼
(c) 新しい SetVal variant を作るか? ────────── Yes ──→ Rust
        │ No
        ▼
(d) 無限集合の atomic 表現が必要か? ───────── Yes ──→ Rust
        │ No
        ▼
(e) f64 機械演算が必要か? ──────────────── Yes ──→ Rust
        │ No
        ▼
seki 層 (stdlib.seki) に書く
```

#### 現状の Rust builtin 一覧 (基準で正当化されるもののみ)

| 名前 | 該当条件 |
|---|---|
| `print` / `error` | (a) I/O / panic |
| `card` | (b) `SetVal::Enum` の variant 検査 |
| `fst` / `snd` / `pair` | (b) `Value::Tuple` の生成・分解 |
| `List` / `Tree` | (c) `SetVal::ListOf` / `SetVal::TreeOf` の生成 |
| `Nat` / `Int` / `Real` / `String` / `Set` / `Bool` / `Prop` | (d) atomic 集合 |
| `intToReal` / `floor` / `ceil` / `round` / `sqrt` / `pow` | (e) f64 機械演算 |

これ以外のグローバルは全て `stdlib.seki` で seki 言語自身によって定義される。
**新機能を加えるときは「Rust に置く強い理由 (a)〜(e) の 1 つ」がない限り `stdlib.seki` に書く** のが本プロジェクトの方針。

---

## 2. パイプライン

```
   source string
        │
        ▼  lexer::tokenize
   Vec<Token>
        │
        ▼  parser::parse_program
   Vec<Decl>
        │
        ▼  main::ProgramState::run_decls (1 件ずつ処理)
        ├─→ Decl::Def     : shape→eval→(membership 検査)→globals 登録
        ├─→ Decl::Theorem : shape→Prover::verify→theorems 登録
        ├─→ Decl::Axiom   : shape→axioms 登録
        └─→ Decl::Expr    : shape→eval→print
```

各ステージは `SekiResult<T> = Result<T, SekiError>` を返し、エラーは即座に伝播する。

---

## 3. AST

`src/ast.rs`。中核は 2 つの enum。

### `Expr`

すべての式を統一表現する。**型レベルの式と値レベルの式は同じ Expr** で表現される (集合 = 型なので分離する必要がない)。

```rust
pub enum Expr {
    Int(i64), Bool(bool), Str(String),
    Var(String),
    Lambda { params: Vec<Param>, body: Box<Expr> },
    App { func: Box<Expr>, args: Vec<Expr> },
    Let { name, ty: Option<Box<Expr>>, value, body },
    If { cond, then_branch, else_branch },
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),
    SetEnum(Vec<Expr>),
    SetComp { var, domain, pred },
    Arrow(Box<Expr>, Box<Expr>),       -- 型矢印
    Forall { var, domain, body },
    Exists { var, domain, body },
}
```

`Param { name, ty: Option<Expr> }` で関数引数を表現。

### `Decl` / `Proof`

```rust
pub enum Decl {
    Def     { name, ty: Option<Expr>, value: Expr },
    Axiom   { name, prop: Expr },
    Theorem { name, prop: Expr, proof: Proof },
    Expr(Expr),
    Import  { path: String, alias: Option<String> },   // import "path" [as M]
}

pub enum Proof {
    ByEval,                  // :=  by eval
    Refl,                    // :=  refl
    ByAlgebra,               // :=  by algebra
    ByInduction,             // :=  by induction
    ByStrongInduction,       // :=  by strong_induction
    Term(Expr),              // :=  <expr>
}
```

`data` 宣言と `match` 式は **AST には乗らず**、パーサ段階で desugar 完了:
- `data Foo = A | B Int` → 構築子の `def` 群に展開
- `match e with | pat -> body | ...` → `if`/`let` チェーンに展開

`?` 演算子も同様に `parse_let` 内で `match ... with | Err -> Err | Ok x -> body` に desugar。

---

## 4. 値とランタイム表現

`src/value.rs`。

### `Value`

```rust
pub enum Value {
    Unit,
    Int(i64), Bool(bool), Str(String),
    Set(Rc<SetVal>),
    Tuple(Vec<Value>),                                  // (a, b, c)
    List(Vec<Value>),                                   // [1, 2, 3]
    Tree(Rc<TreeVal>),                                  // leaf / (node l v r)
    Closure { params: Vec<String>, body: Box<Expr>, env: Env },
    Builtin(BuiltinFn),
}

pub enum TreeVal {
    Leaf,
    Node { left: Rc<TreeVal>, value: Value, right: Rc<TreeVal> },
}
```

`Rc<SetVal>` / `Rc<TreeVal>` で大きなデータ構造を共有してクローンコストを抑える。Closure は **lexical scope** を保持するために `env` を捕獲する。

### `SetVal`

```rust
pub enum SetVal {
    Enum(Vec<Value>),
    Comp { var, domain: Rc<SetVal>, pred: Expr, env: Env },
    Atomic(AtomicSet),                                  // Nat/Int/Bool/String/Prop/Set
    Arrow { from: Rc<SetVal>, to: Rc<SetVal> },
    Product(Vec<Rc<SetVal>>),                           // A times B times C
    ListOf(Rc<SetVal>),                                 // List T
    TreeOf(Rc<SetVal>),                                 // Tree T
}
```

- **Comp は捕獲環境を持つ**。`{x in S | foo bar x}` のように述語が外側スコープの値を参照することを許す。
- `Product` / `ListOf` / `TreeOf` で複合データ型を集合論的に表現。`(a, b) in (A times B)` は要素ごとの所属で判定、`xs in (List T)` は各要素の `T` 所属で判定、`t in (Tree T)` は全ノード値の `T` 所属で判定 (再帰)。

### `Env`

イミュータブルな cons-list を `Rc` で共有:

```rust
pub struct Env { head: Option<Rc<EnvNode>> }
struct EnvNode { name: String, value: Value, parent: Option<Rc<EnvNode>> }
```

`extend` は O(1)、`lookup` は O(深さ)。多数のクロージャが部分的に環境を共有してもメモリ効率が良い。

### `Globals`

トップレベル定義のコンテナ:

```rust
pub struct Globals {
    pub defs:     HashMap<String, Value>,
    pub theorems: HashMap<String, Value>,
    pub axioms:   HashMap<String, Value>,
}
```

`lookup` は `defs → theorems → axioms` の順に探す。

### 等価性

- `value_eq`: 値の構造的等価。Int/Bool/Str/Unit は内容比較、Set は `set_eq`、Tuple/List は要素ごと再帰、Tree は `tree_eq`、Closure/Builtin は不等。
- `set_eq`: Enum 同士は集合的 (順序・重複無視)、Atomic は kind 比較、Arrow / Product / ListOf / TreeOf は構造的に再帰。Comp 絡みは保守的に false。
- `tree_eq`: Leaf 同士は等しい、Node 同士は left/value/right を再帰的に比較。

---

## 5. 評価器

`src/eval.rs` の `EvalCtx`。

### `eval(&Expr, &Env) -> SekiResult<Value>`

各 Expr バリアントを再帰的に評価。注目点:

- **`Var`**: env → globals の順に探す。グローバル参照のおかげで再帰関数が成立する (`def fact := \n -> ... fact ...`)。
- **`App`**: 関数値と引数列を `apply` に渡す。
- **`Lambda`**: 評価環境を捕獲してクロージャを返す。
- **`If`**: 条件を評価して分岐 (型: Bool 必須)。
- **`Let`**: 値を評価して env を拡張、本体を評価。
- **`SetComp`**: 述語と現在の env を捕獲した `SetVal::Comp` を返す (述語は遅延評価)。
- **`Forall` / `Exists`**: まず `try_forall_from_definition` / `try_exists_from_definition` で**集合の定義から自明判定**を試みる:
  - `forall x in {y in S | P(y)}, body` で body が α-同値で P と一致 → 即時 `true`
  - body が `lhs op rhs` で Nat/Int 上の多項式関係として代数判定可能 → 即時 `true`
  - 空集合上の forall (vacuous) → `true`、空集合上の exists → `false`
  - 上記で決まらなければ `enumerate_set` で要素列挙、各要素で本体を評価して累積 (atomic 無限集合は SAMPLE_BOUND までの標本検査; これは健全ではない)。

### `apply(Value, Vec<Value>) -> SekiResult<Value>`

カリー化ロジック:

- 引数が parameters と一致 → 直ちに body を評価
- 引数が少ない → 残りパラメータを持つクロージャを返す (部分適用)
- 引数が多い → body を評価してから残り引数を再帰的に適用

Builtin の場合は arity ぶん引数を取って Rust 関数を呼ぶ。

### 集合演算

- `member(v, s, env)` — `v in s`
- `subset(a, b, env)` — `a` を列挙して各要素が `b` に属するか
- `union / intersect / difference` — 列挙ベースで実装。`union` は両辺 Enum のみ対応 (片側無限の合理的なセマンティクスがないため意図的)。

### `enumerate_set`

集合の要素を `Vec<Value>` として返す。

| SetVal | 振る舞い |
|---|---|
| `Enum(xs)` | そのまま返す |
| `Comp { domain, pred, env }` | domain を再帰的に列挙し、pred で filter |
| `Atomic(Nat)` | `0..SAMPLE_BOUND` の Int 列 (デフォルト 200) |
| `Atomic(Int)` | `-SAMPLE_BOUND..SAMPLE_BOUND` |
| `Atomic(Bool/Prop)` | `[false, true]` |
| `Atomic(String/Universe)` | エラー (列挙不可) |
| `Arrow{...}` | エラー (関数空間は列挙不可) |

`SAMPLE_BOUND` は eval.rs の `pub const SAMPLE_BOUND: i64 = 200`。引き上げると検証は強くなるが、`forall x in Nat, ... forall y in Nat, ...` のようなネストは O(N²) に跳ね上がる。

### 評価戦略

- **eager**: すべての引数は呼び出し前に評価される
- **短絡評価**: `and` / `or` は左側で結果が決まれば右側を評価しない
- **コピーセマンティクス**: `Value` は `Clone`。Set は `Rc` で共有されるが、Int/Bool/Str はクローンされる

---

## 6. 型チェッカ

`src/typecheck.rs`。**2 段構成**で、shape 検査と membership 検査を分けている。

### Shape 検査 (`check_shape`)

各 Expr を粗い shape (`Int / Bool / Str / Set / Tuple / List / Tree / Fn / Unit / Unknown`) に推論し、明らかな不整合を検出する。例:

- `1 + true` → `arithmetic rhs: expected Int, got Bool`
- `if 5 then ...` → `if condition: expected Bool, got Int`
- 関数でない値の適用

`Unknown` は推論不能を示し、エラーにはしない (`Var` の参照、`App` の戻り値など)。

健全性のためではなく、エラーの早期発見が目的。

### Membership 検査 (`check_def_membership`)

`def name : T := value` の文脈で `value in T` を判定。

- 通常の値 → `EvalCtx::member` で判定
- Closure + Arrow → 標本検査:
  - `from` から数個の値を取り (Enum なら全要素、Bool なら両方、Nat なら 0..5、Int なら -2..3)
  - 関数を適用して結果が `to` に属するかチェック
  - すべて通れば accept

これは **健全ではない** (反例が標本外にある可能性) が、簡単なミスを捕まえるには有効。

### `ShapeEnv` の伝播

`main::ProgramState` が宣言ごとに `ShapeEnv` を更新する。`def x : Int := ...` を処理すると `x` の shape を `Int` で env に追加する。後続の宣言は `x` の shape を参照できる。

### 軽量な型推論 (`infer_type`)

`def name := body` で型注釈が省略された場合、`typecheck::infer_type(body, &TypeEnv) -> Option<Expr>` が呼ばれる。
推論ルール (簡略):

- `Lambda { params, body }`: 引数注釈付きパラメータの型と、`body` から推論した戻り値型を `Arrow` でカリー化して返す。注釈なしパラメータは `Set` (任意) として扱う。
- `Int(_) | Real(_) | Bool(_) | Str(_)`: それぞれ `Int` / `Real` / `Bool` / `String`。
- `BinOp(arith, l, r)`: 両辺の型から数値演算の結果型を推論 (Int + Real → Real, etc)。
- `If { cond, then_branch, else_branch }`: 両分岐の型が一致すれば返す。
- `App { func, args }`: `func` の Arrow 型から戻り値部を引き出す。
- `Var(n)`: `TypeEnv` または `Globals.inferred_types` から検索。

成功すれば `Globals.inserted_types: HashMap<String, Expr>` に記録され、`def name : T = value` の形で表示される。
REPL `:type EXPR` も同じ `infer_type` を呼ぶ。

`prelude_types()` は `make_builtin_prelude` で登録される組込関数の型 (`succ : Int -> Int` など) を `TypeEnv` の初期値として返す。

### 終了性検査 (`termination::check`)

各 `Decl::Def` 処理時に呼ばれる:

```rust
match termination::check(name, &params, &body) {
    TerminationStatus::Verified | NonRecursive => (),
    TerminationStatus::Unknown(reason) => eprintln!("warning: termination of `{}` not verified ({})", name, reason),
}
```

`collect_recursive_calls` が `body` を再帰的に走査し、`name` への `App { func: Var(name), args }` を集める。`Lambda { params: lp, .. }` 内で `lp` のいずれかが `name` と同名なら shadow とみなしてスキップ。
`is_structurally_smaller` がパラメータ位置ごとに減少を判定する。一つでも減少していれば call は OK。

健全性については **意図的に保守的**: 確認できなくても定義は受理 (warning のみ)。これは型なし言語として false positive 許容を優先するため。

---

## 7. Prover (9 戦術 + 合成)

`src/prover.rs` の `Prover::verify(prop, proof, env) -> SekiResult<Value>`。

戦術は **closer** (証明完了型: `eval`/`refl`/`algebra`/`induction`/`strong_induction`/証明項) と **transformer** (goal を書き換えて次戦術に渡すだけ: `unfold`/`intros`/`simp` の部分動作) に分かれる。

合成 `Proof::Seq(Vec<Proof>)` は各戦術を順に `run_step` で実行する:

- `TacOutcome::Closed`: 戦術が goal を閉じた → 終了 (最後の戦術でなくても可)
- `TacOutcome::NewGoal(g)`: 戦術が goal を書き換えた → 次の戦術に渡す
- 最後の戦術が `NewGoal` で終わると `tactic sequence ended with an unclosed goal` エラー

```seki
theorem t : forall a in Int, sq a + 0 == a*a := by intros then unfold sq then algebra
-- 1. intros: forall を剥がして `sq a + 0 == a*a` を返す (NewGoal)
-- 2. unfold sq: `sq a` を `a*a` に展開して `a*a + 0 == a*a` (NewGoal)
-- 3. algebra: 多項式恒等式として証明 (Closed)
```

### `by unfold f` — 関数の 1 段 β-展開

`unfold_calls(e, name, params, body)` が goal の AST を走査し、`App(Var(name), args)` を `body[params := args]` に置換する。bottom-up なので、同じ goal 内に複数の `f` 呼び出しがあれば全て同時に展開される。1 段のみ (置換結果に再帰しない) なので、再帰関数でも安全。

### `by intros`

`strip_foralls(prop)` で先頭の `Forall { var, domain, body }` を剥がす。残った free var は後続戦術 (algebra/simp/eval) が自動的に扱える。複数の foralls がネストしている場合、全て一度に剥がされる。

### `by algebra` — 多項式正規化 + 符号解析 + 定数 div/mod

`src/algebra.rs` の `Polynomial = Vec<Monomial>` (BTreeMap でソートされた変数指数を持つ単項式の列) を用いる。各 Monomial の係数は `i128`。

**等号 `==`**: `lhs - rhs` が 0 多項式 ⇔ 等しい。

**不等号** (`<`, `<=`, `>`, `>=`, `!=`): `polynomial_pos / nonneg / nonpos / neg` でドメイン依存の符号判定。
  - `Nat`: 全係数が ≥ 0 → ≥ 0、加えて定数項 > 0 → > 0
  - `Int`:
    1. すべての変数の指数が偶数 + 全係数 ≥ 0 → ≥ 0、または
    2. **二次形式の半正定値判定** (`quadratic_psd`): 単項式の最高次が 2 まで、対応する対称行列を構築し Sylvester 基準 (主小行列式すべて ≥ 0) で PSD を判定。最大 4 変数まで対応。
    - これにより Cauchy-Schwarz 系 `a²+b² ≥ 2ab` などが扱える

**定数 div / mod**:
  - `expr_to_poly` で `BinOp::Div(p, c)` を `p.div_const(c)` に、`BinOp::Mod(p, c)` を `p.mod_const(c)` に簡約
  - `div_const`: 全係数が `c` で割り切れれば結果を返し、そうでなければ不透明原子化
  - `mod_const`: 全係数を `c` で剰余を取り、合わせて normalize

**ドメイン推定**: `detect_domain` が forall 束縛子の domain 構文を見て、すべて `Nat` なら `PolyDomain::Nat`、それ以外は `PolyDomain::Int`。

### `by induction` — 構造帰納法 (Nat / List / Tree)

`induction_mode` で領域を見て分岐:

| 領域 | 基底 | ステップ |
|---|---|---|
| `Nat` | `n := 0` | `n := k+1` を unfold + simplify_ifs |
| `List T` | `xs := []` | `xs := cons x ys` を unfold + simplify_list_ops |
| `Tree T` | `t := leaf` | `t := node l v r` を unfold + simplify_tree_ops |

各モードでステップは `discharge_step(op, lhs_diff, rhs_diff, dom)` に落ちる:
  - `==`: `lp - rp == 0` (純多項式等価)
  - `>=`/`>`: `polynomial_nonneg(lp - rp)` — IH のスラックで `>` が `>=` で済む
  - `<=`/`<`: `polynomial_nonpos(lp - rp)`

`simplify_list_ops` / `simplify_tree_ops` は次の組込簡約則を実装:
  - `null (cons _ _) → false`、`null nil → true`
  - `head (cons x _) → x`、`tail (cons _ ys) → ys`
  - `isLeaf (node _ _ _) → false`、`isLeaf leaf → true`
  - `treeVal (node _ v _) → v`、`treeLeft (node l _ _) → l`、`treeRight (node _ _ r) → r`

これらにより、構造帰納法のステップで `length (cons x ys) → 1 + length ys` のような unfold 後の自然な簡約が成立する。

### `by strong_induction` — 深さ 2 強帰納法 (Nat)

Fibonacci 等の多段階漸化式向け。

1. **基底**: `P(0)`, `P(1)` を `by eval` で確認
2. **ステップ**: `n := k+2` を unfold。`f k`、`f (k+1)` は不透明な原子として現れるため、`PolyDomain::Nat` 上の符号判定 (Nat 域で原子 ≥ 0 とみなす) で直接 `lhs(k+2) op rhs(k+2)` を判定

健全性: 不等式の方向と一致する形で原子を扱うので、`>= 0` 系の不等式が中心。

### `by simp` — 等式書換え戦術

`Globals.theorem_props` および `Globals.axiom_props` に蓄積された等式 theorem / axiom を **方向付き書換え規則** (LHS → RHS) として収集し、目標 (goal) に対して反復的に適用する。

1. **規則収集** (`collect_simp_rules`): 各 prop から先頭の `forall` 束縛子をストリップしてその bound vars を **メタ変数** とし、本体が `lhs == rhs` 形であれば `SimpRule { metavars, lhs, rhs }` を作成。
2. **書換え** (`simp_rewrite`): goal を bottom-up に走査し、各サブ式に対して `match_pattern(rule.lhs, subexpr, rule.metavars)` で構造マッチを試みる。マッチすれば `apply_subst(rule.rhs, binding)` で置換。
3. **反復** (`verify_simp`): 不動点まで繰り返す (最大 64 反復)。途中の状態は `seen: Vec<Expr>` に蓄積する。
4. **成功条件**: 経由した任意の状態で
  - `Bool(true)` リテラルに reduce、または
  - `a == b` で `alpha_equiv(a, b)` が成立、または
  - `ctx.eval(state)` が `Bool(true)` を返す

`seen` 配列を使うのは、対称的規則 (`add_comm` など) が両方向に発火して oscillation を起こすケースで、1-step で `e == e` 形にたどり着く可能性を拾うため。

**マッチング** (`try_match`):
  - パターンに登場する Var が `metavars` に含まれていれば、初出時はバインディングを記録、再出時は `alpha_equiv` で一貫性チェック。
  - そうでない Var, Int/Real/Bool/Str リテラルは構造的に同一かを比較。
  - `App`, `BinOp`, `UnOp`, `Tuple`, `List`, `If` は再帰的に対応する子をマッチ。
  - `Lambda` は引数名が完全一致するときのみ受理 (alpha-renaming は未対応)。

**既知の限界**:
  - 対称規則 (e.g., `a + b == b + a`) は単独では oscillation するため、補助的な情報なしには `0 + x == x + 0` のような goal を `simp` のみで通せない。
  - 条件付き等式 (forall 述語に追加の仮定があるもの) は未対応。

### 戦術別ロジック (既存):

### `Proof::ByEval`

`ctx.eval(prop, env)` を呼び、`Value::Bool(true)` で受理。`false` なら `proof error: proposition reduced to false`。Bool 以外 (Int 等) なら `did not reduce to a Bool`。

### `Proof::Refl`

prop が `BinOp(Eq, a, b)` であることを期待。両辺を評価し `value_eq` で比較。等しければ受理、違えば `refl: lhs ≠ rhs`。

### `Proof::Term(term)`

prop の形に応じて分岐:

- **`Forall { var, domain, body }`**: term を評価してクロージャ/組込関数か確認。domain を列挙。各要素で
  - `apply(term, [e])` を呼ぶ (副作用検査)
  - `body[var := e]` を評価して `true` か確認
  失敗時は具体的な反例を報告 (`counterexample: with x = 3 ...`)。

- **`Exists { var, domain, body }`**: term を評価して値 `w` を得る。`w in domain` を確認、`body[var := w]` を評価して `true` か確認。

- **その他**: term は単に「タグ」として評価し (失敗するとエラー)、prop は通常評価して `true` を期待。

`Forall` では証明項の本体は実質使われない (構造制約: 関数であること、有限列挙が成立すること)。本格的な依存型での `\x -> proof_of_P(x)` のような扱いではない。

---

## 8. プレリュードと組込関数

`eval::make_prelude() -> Globals` がプログラム起動時のグローバル環境を作る。

| 名前 | 種類 | 内容 |
|---|---|---|
| `Nat`, `Int`, `Bool`, `String`, `Prop`, `Set` | `Set` 値 | `SetVal::Atomic(...)` |
| `print` / `card` / `id` / `succ` / `pred` | Builtin (1) | 標準出力 / 濃度 / 恒等 / 後者 / 前者 |
| `fst` / `snd` / `pair` | Builtin (1/1/2) | タプルアクセサ・コンストラクタ |
| `nil` | List 値 | 空リスト (関数ではない) |
| `cons` / `head` / `tail` / `null` | Builtin (2/1/1/1) | リスト構築/分解/空判定 |
| `length` / `append` / `reverse` / `toSet` | Builtin (1/2/1/1) | リスト操作 |
| `List` | Builtin (1) | `Set -> Set` — 要素集合を渡すとリスト型集合を返す |
| `leaf` | Tree 値 | 空木 (関数ではない) |
| `node` | Builtin (3) | `Tree -> A -> Tree -> Tree` — 内部ノード構築 |
| `isLeaf` / `treeVal` / `treeLeft` / `treeRight` | Builtin (1) | 木のテスト/アクセサ |
| `Tree` | Builtin (1) | `Set -> Set` — 要素集合から二分木型集合を作る |

組込関数を追加する例 (eval.rs `make_prelude` 内):

```rust
fn b_double(args: &[Value]) -> Result<Value, String> {
    match &args[0] {
        Value::Int(n) => Ok(Value::Int(n * 2)),
        v => Err(format!("double: expected Int, got {}", v.type_name())),
    }
}
g.defs.insert("double".into(), Value::Builtin(BuiltinFn {
    name: "double", arity: 1, func: b_double,
}));
```

---

## 9. テストと例題の駆動

### 統合テスト

`tests/integration.rs` が公開 API (`parse_program`, `EvalCtx`, `Prover`) を直接呼ぶ。`cargo test` で実行。**47 ケース** (タプル / リスト / Tree / by algebra / by induction / by strong_induction / data・match / Option・Result / `?` 演算子を含む全戦術と新機能をカバー)。

加えて `algebra` モジュールに **7 ユニットテスト** (多項式正規化・乗除・因数定数化・PSD 判定など)。

### 例題

`examples/*.seki` を `cargo run -- <file>` で実行。`run-all.sh` などはないが、ループで:

```sh
for f in examples/*.seki; do echo "== $f =="; cargo run -q -- "$f"; done
```

### main.rs `ProgramState`

REPL とファイル実行で共通に使う状態管理:

```rust
struct ProgramState {
    globals: Globals,
    shapes:  ShapeEnv,
}
```

`run_decl` が宣言を 1 件ずつ処理し、副作用でフィールドを更新する。**def の登録順序**に注意: 関数値の場合は型注釈チェックの **前** に globals に挿入し、チェックが失敗したらロールバックする。これにより自己参照する再帰関数が型注釈付きで定義できる (`5_number_theory.seki` の `fact` 等)。

---

## 10. 型クラスの自動辞書解決

`class`/`instance` は元来パース段階で desugar されて `def` の集合になる (`MkEqDict` 構築子 + 各メソッドの projection)。これに加えて、自動辞書解決のために次のメタデータが伝搬する:

### `Decl::ClassMeta` と `Decl::InstanceMeta`

パーサが `class Eq A where ...` を見ると、通常の `def` 群に加えて

```rust
Decl::ClassMeta {
    class_name: "Eq",
    ctor_name: "MkEqDict",
    methods: vec!["eq", "neq"],
}
```

を emit する。`instance EqInt : Eq Int where ...` を見ると

```rust
Decl::InstanceMeta {
    instance_name: "EqInt",
    class_name: "Eq",
    type_name: "Int",
}
```

を emit する (`type_name` は instance 宣言時の型引数を文字列化したもの)。

### `Globals` の登録

`main::run_decl` が上記メタを処理して、

- `Globals.class_methods: HashMap<String, String>` (method → class)
- `Globals.class_ctor: HashMap<String, String>` (class → 辞書 ctor 名)
- `Globals.instances: HashMap<(String, String), String>` ((class, type) → instance 名)

を埋める。

### `EvalCtx::eval` での割り込み

`Expr::App { func, args }` 評価時、`func` が `Var(method)` で `method` が登録済みクラスメソッドなら、`args[0]` をまず評価する。その値が:

- 既に `class_ctor[class]` をタグに持つ `Tuple` (＝辞書) → そのまま使用 (明示渡し)
- そうでない (Int/Bool/Str/...) → `argv[0].type_name()` をキーに `instances[(class, type)]` を引いて辞書を取得、`argv` の先頭に挿入

挿入後、通常の `apply` 経路で projection 関数 → 実方法本体の β-簡約が走る。インスタンスが見つからない場合は介入せず、projection 内の `match` が "non-exhaustive" エラーを出す (= 通常の class method 適用エラー)。

```seki
eq 3 5
-- 1. eq is class method of Eq
-- 2. args[0] = 3 :: Value::Int, not a dictionary
-- 3. lookup instances[("Eq", "Int")] = "EqInt"
-- 4. prepend g.defs["EqInt"] to args, then continue evaluation
-- 5. eq EqInt 3 5 → false
```

## 11. エラーと診断

### `SekiError` の構造

`src/lib.rs`:

```rust
pub enum SekiError {
    Lex(String),
    Parse(String),
    Type(String),
    Runtime(String),
    Proof(String),
}
```

各 variant には機械可読なアクセサがある:

- `error.code()`: `"E001"`〜`"E005"` の安定コード (Lex=E001, Parse=E002, Type=E003, Runtime=E004, Proof=E005)
- `error.category()`: `"lex"`/`"parse"`/`"type"`/`"runtime"`/`"proof"` (Display プレフィックスと一致)
- `error.message()`: カテゴリプレフィックスなしの本文
- `error.is_proof_error()`: テストで「proof tactic がこの命題を拒否した」を判定するための便利関数

LSP / 構造化テスト診断・将来の機械可読出力向けに用意してある。

### `LocatedDecl` と位置情報の付与

`src/ast.rs` に `LocatedDecl { decl: Decl, line: usize, col: usize }`。
`parser::parse_program` が各トップレベル宣言の **キーワード位置** (`def`/`theorem`/`axiom`/...) を `(line, col)` として記録する。`data` のように複数の `def` を生成する宣言は、すべての派生 `def` で同じ位置を共有する。

`main.rs::run_decl` は `run_decl_inner` の結果を `annotate_error(e, line, col)` でラップし、`Type`/`Runtime`/`Proof` カテゴリのエラー本文に `[line:col] ` プレフィックスを付ける (`Lex`/`Parse` は元から自前で位置情報を持つので素通し)。

```
type error: [12:1] value "purple" is not a member of declared type Color
```

### 将来の拡張: span を Expr に持たせる

現在は **decl 単位** の粒度の位置情報のみ。`forall x in Int, body` のようなネスト式の中で proof error が発生したとき、その forall や body の正確な位置は分からない。Expr 全 variant に `Span` を付ければ「式の何文字目で失敗した」まで指せるが、AST が肥大するためトレードオフ。LSP 統合時に再考。

---

## 12. 今後の拡張

直近の作業で実装済み (履歴):
**A1-A3** 終了性検査 (match パターン束縛変数 / 辞書順 lex / `mod`) + `by simp`。
**C1-C2** Decl 単位の位置情報 + `SekiError` のエラーコード/カテゴリ API。
**P1.1-P1.3** タクティク合成 `then` + `by unfold` + `by intros`。
**P2.1** 型クラスの自動辞書解決。
**P2.3** 群論 / 環・体 / 線形代数のミニライブラリ (sample 22-25)。

### 実装が比較的容易なもの

- **パターンマッチの網羅性検査**: 現在は `match` の最終 fallback が `error "non-exhaustive match"` のランタイムエラー。コンパイル時に検出できればより堅牢。
- **`forall x y in S` の糖衣**: 現在は `forall x in S, forall y in S, ...` と書く必要があるネストを、複数変数で 1 つの量化子にまとめる。
- **Expr 単位の位置情報 (span)**: 現状は Decl 単位の `[line:col]` のみ。Expr 全 variant に Span を持たせれば proof error が forall や式の正確な位置を指せる。LSP の前提。
- **`forall n in Nat, n >= k` の境界推論**: 現在 `by algebra` で扱える符号は polynomial-domain ベースだが、定数境界 (例: `forall n in Nat, n + 5 > 4`) は `polynomial_pos` の細粒度化で扱える余地あり。
- **任意深さの強帰納法**: 現在 `by strong_induction` は深さ 2 固定。`by strong_induction 3` 等で参照前段数を指定できるよう拡張。
- **`?` 演算子の拡張**: 現在は let-value 専用。任意の式コンテキストで使えるようにすると `f (g x?)` 等が書きやすくなる。
- **Option 用 `?o` 演算子**: 現在 `?` は Result 専用。Option 用も加えると一貫性が高まる。
- **`by simp` の対称規則ハンドリング**: `add_comm` のような対称規則は両側で発火し oscillate する。LHS/RHS の項順序付け (KBO 等) で書換え方向を決定すれば改善できる。
- **`Decidable` 型クラス + `by decide`**: 命題が Bool に落とせるとき自動証明する戦術。型クラスインフラの上に乗る。

### 中程度の労力

- **真にスコープ分離されたモジュール**: 現在の `import "x" as M` は名前空間を flat にしたまま prefix を付けるだけ (bare 名も leak)。完全に分離するには `Globals` を木構造にする必要がある。
- **より強い型推論**: 現状 `infer_type` はラムダ・算術・if など主要な構成子に限定されており、`match` パターン束縛・`forall`/`exists` の domain・依存型では `Set` (任意) で諦めている。単方向 (intro 型) と双方向 (check 型) を混ぜた本格的な bidirectional checking で改善余地あり。
- **3次以上の不等式判定**: 現在 PSD 判定は 2 次形式まで。3 次は一般に難しいが、奇数次の単項式正値性 (`x³ ≥ 0` 失敗、`x²y² ≥ 0` 成功) などの限定パターンは扱える。
- **可変除数の div / mod**: 現状定数除数のみ。`(a*n) / n` のような単項キャンセルは検出可能。
- **線形不等式の決定 (`by linarith`)**: Fourier-Motzkin で線形不等式を完全決定。`forall n in Nat, n + 5 > 4` のような定数境界が一発で通る。
- **依存パラメトリック ADT の専用構文**: `data Vec : Nat -> Set where ...` 構文を加え、`{xs | length xs == n}` を自動生成。
- **依存ペア型 `Σ (x : A), B(x)`**: refinement で書ける現状を first-class 構文に。
- **LSP サーバ最小実装**: hover で型表示、diagnostics をエディタに流す。`tower-lsp` クレートで土台。
- **REPL の強化**: `rustyline` で行編集・履歴・自動補完。

### 大きな労力 (本格的な定理証明への道)

- **依存型の完全検査**: 現状はサンプリングのみ。任意の `n` で member を保証するには別の証明手続きが要る (帰納法と組み合わせる等)。
- **本物の Curry-Howard**: `Proof : Prop` を first-class に。証明項自体に型を付け、検証は型検査として行う。これは現在の seki の「集合論で検証」哲学とは別の道。
- **相互再帰の unfold**: 現在の `unfold_one` は単一関数の 1 段展開のみ。相互再帰関数 (例: `even` / `odd`) はサポートしない。
- **タクティクモード**: ゴールスタックを持って対話的に証明を組み立てる UI。`then` 合成の上位互換で、`<;>` (all goals) や `;` (sequential) を持つ。Lean / Coq の主要機能。
- **ADT に対する構造帰納法**: 現在は組込 List/Tree のみ。`data` で定義された任意 ADT に対しても induction を効かせる。
- **WASM コンパイル**: ブラウザで seki を動かす。教育向け playground が可能。
- **CAS (記号計算)**: 微分・積分・式変形を組み込む。`derive (\x -> x*x*x) == \x -> 3*x*x` を proof で通せる。

### コード品質関連

- **ベンチマーク**: forall ネスト + by algebra のスケーリング測定。
- **REPL の改善**: `rustyline` を依存に入れて行編集・履歴をサポート (現状は素の `read_line`)。
- **算術オーバーフロー**: 多項式係数が `i128` だが、`saturating_*` で握りつぶしている。サウンドネスのためには checked 化と saturating 時のエラー報告が望ましい。
- **`SekiError` の構造化深化**: 現状はカテゴリ + メッセージ。`code: ErrorCode + loc: Option<Span> + hint: Option<String>` の rich diagnostic に拡張すれば LSP / カラー表示・修正候補提示が乗る。

---

## 関連

- 言語仕様: [language.md](language.md)
- 定理証明ガイド: [proofs.md](proofs.md)

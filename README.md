# seki

集合論ベースの定理証明言語 + プログラミング言語のプロトタイプ。Lean のような証明体験を、ZF 風の素朴集合論セマンティクスで実現することを目指している。Rust 実装、外部依存ゼロ。

```seki
-- 集合は2通りの定義
def Days     := {"Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"}     -- 列挙
def EvenNat  := {x in Nat | x mod 2 == 0}                             -- 内包(述語)

-- ラムダ計算 + 集合論ベースの型注釈
def double : Nat -> Nat := \(n : Nat) -> n * 2

-- タプル / リスト / 木 / 直積
def Pair := Nat times Bool
def xs   := [1, 2, 3, 4, 5]
def t    := node (node leaf 1 leaf) 2 (node leaf 3 leaf)

-- 無限ケースの「真の」証明
theorem distrib                                    -- ℤ 上の多項式恒等式
  : forall a in Int, forall b in Int, forall c in Int,
        a * (b + c) == a * b + a * c
  := by algebra

theorem cauchy                                     -- 不等式 (PSD 2次形式)
  : forall a in Int, forall b in Int,
        a*a + b*b >= 2 * a * b
  := by algebra

def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
theorem gauss                                      -- ℕ 上の数学的帰納法
  : forall n in Nat, 2 * sum n == n * (n + 1)
  := by induction

def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)
theorem ll_nn                                      -- リスト構造帰納法
  : forall xs in (List Int), listLen xs >= 0
  := by induction

def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)
theorem fib_nn                                     -- 強帰納法 (深さ2)
  : forall n in Nat, fib n >= 0
  := by strong_induction
```

## 特徴

- **集合 = 型** — 任意の集合 `T` は型として使える。`v : T` は本質的に `v in T` (set membership)。`Bool == {false, true}` は文字通りの集合等価で、`refl` で証明できる。
- **2 種類の集合定義** — 列挙 `{1, 2, 3}` と 述語による内包 `{x in S | P(x)}`。
- **数値型** — `Nat`、`Int`、`Real` (f64) を組込。`Int ⊂ Real` で算術は自動昇格 (`1 + 2.5 == 3.5`)。
- **seki 自身で書かれた標準ライブラリ** — `src/stdlib.seki` で **List / Tree のコンストラクタ・デストラクタ** (`nil`/`cons`/`head`/`tail`/`null`/`length`/`map`/...; `leaf`/`node`/`isLeaf`/`treeVal`/...)、`Pos`/`Neg`/`Even`/`Byte`/`Int8` 等の述語サブタイプ、`Rat = Int × Pos` の有理数、算術ヘルパ (`succ`/`pred`/`abs`/`square`/...) を構築。起動時に自動ロード。Rust 層は最小限のプリミティブ (タプル・算術演算子・I/O) のみ。
- **代数的データ型を集合から構築** — タプル `(a, b)` のみを Rust プリミティブとし、リスト `[1, 2, 3]` (= `(1, (1, ..., (0, ())))`) や二分木 `node l v r` (= `(3, (l, (v, r)))`) は **seki 言語自身でタグ付きペアとして集合論的に構築**。`data` 宣言と `match` 式で簡潔に書け (`data Maybe A = None | Some A`、`match m with | None -> ... | Some x -> ...`)、内部表現はやはりタグ付きペア (純粋な構文糖)。
- **エラーハンドリング** — stdlib に `Option`/`Result` + ヘルパ (`mapOption`/`bindResult`/`unwrapOr`/`okOr`)、`?` 演算子で `let x = expr ? in body` の形でエラー伝播 (Result の `Err` を自動再パック)。
- **モジュールシステム** — `import "path/file.seki"` で他ファイルを読込、`import ... as M` で `M.name` 形式の修飾アクセス、循環依存検出。**ライブラリパス自動探索**: `import "cas/calc.seki"` のように lib/ 相対パスでも書ける (検索順: 現ファイル相対 → `SEKI_LIB_PATH` → `<cwd>/lib` → `<binary>/../lib` → `~/.seki/lib` → `-I` 引数)。
- **依存型** — `(x : A) -> B(x)` で引数の値に応じて返り値の型 (集合) が変わる関数を表現。`Vec n` 型 (長さ n のリスト集合)、`{x : T \| P(x)}` の refinement 型を統一的に扱う。型注釈付き定義はサンプル検査で member 判定。
- **型推論** — `def double := \x -> x * 2` のように注釈なしで定義しても、本体や引数注釈から最も具体的な型を推論し `def double : (Set -> Int) = <fn:x>` のように表示する。REPL では `:type expr` で式の型を直接問い合わせ可能。
- **終了性検査** — 構造的減少 (`n - C`, `n / C` (`C ≥ 2`), `tail`, `snd`, `treeLeft`/`treeRight`) で見える再帰は静的に検証。確認できなければ `warning` を出すが定義は受理する (false positive を許容)。
- **型クラス** — `class Eq A where eq : A -> A -> Bool` と `instance EqInt : Eq Int where eq = ...` を提供。純粋な desugar で `data EqDict` (辞書 record) と projection 関数に変換し、`eq EqInt 3 3` のように **辞書を明示的に渡す** スタイル。Lean / Haskell のような自動解決はないが静的型なしでも安全。
- **記号は単語** — `forall`, `exists`, `in`, `notin`, `union`, `intersect`, `subset`, `times`, `lambda`/`\` 等。Unicode 記号は使わない。
- **9 種類の証明戦術 + 合成**:

  | 戦術 | 種別 | 用途 |
  |---|---|---|
  | `by eval` | closer | 命題を簡約 (有限のみ健全) |
  | `refl` | closer | 等式の構造的等価 |
  | `by algebra` | closer | 多項式正規化 + 符号解析 + 定数 div/mod + PSD 2次形式 (∞ ✓) |
  | `by induction` | closer | Nat / List / Tree 上の構造帰納法 (∞ ✓) |
  | `by strong_induction` | closer | 深さ 2 強帰納法 (Fibonacci 等、ℕ ∞ ✓) |
  | `by simp` / `by simp [l1, l2]` | both | 既存の等式 theorem を方向付き書換え規則として連鎖適用 |
  | `by unfold f` | transformer | 関数 f の定義を 1 段 β-展開 (closer と組合せる) |
  | `by intros` | transformer | 先頭の forall を剥がして free var 化 |
  | 証明項 | closer | Curry-Howard 風 (forall は関数, exists は witness) |
  | `tac1 then tac2 [then tac3 ...]` | combinator | タクティク合成: `by intros then unfold f then algebra` |

- **REPL とファイル実行** — 1 バイナリ、外部依存ゼロ。
- **システム開発機能 (汎用言語層)** — Phase 1 (基盤): 文字列演算 (`strLen` / `strSplit` / `strJoin` / `strReplace` / `substring` / `strToUpper` 等)、ファイル I/O (`readFile` / `writeFile` / `appendFile` / `fileExists` — すべて `Result E A` を返す)、CLI 引数 (`args : List String`)、環境変数 (`getEnv`)、可変参照 (`mkRef` / `readRef` / `writeRef` — `Ref A` は記憶セルの集合)、効率的辞書 (`Dict K V` ⊂ K × V、O(1) 操作)。Phase 2 (拡張): 時刻 (`nowSecs` / `nowMillis` / `monotonicMillis` / `sleep`)、乱数 (xorshift64* PRNG: `randomSeed` / `randomInt` / `randomRange`)、ビット演算 (`bitAnd` / `bitOr` / `bitXor` / `bitShl` / `bitShr` / `bitNot` / `popcount`)、プロセス実行 (`execShell` シェル経由、`runCommand` 直接 spawn)、JSON 完全サポート (`Json` ADT + `jsonParse` + `jsonEncode`、外部依存ゼロ)、TCP ネットワーキング (`tcpListen` / `tcpAccept` / `tcpConnect` / `tcpRead` / `tcpWrite` / `tcpClose` — `Handle` は I/O escape hatch)。Phase 3 (Web 層 + 並行性): URL parser (`urlParse`)、HTTP request/response codec (`httpParseRequest` / `httpFormatResponse`)、blocking HTTP client (`httpGet`)、stdlib の `httpServe` ハンドラ駆動サーバ (`HttpRequest` / `HttpResponse` ADT + `reqMethod` / `reqPath` / `reqHeaders` / `reqBody` + `httpOk` / `httpJson` / `httpNotFound`)、原子整数による真の並行性 (`atomicNew` / `atomicGet` / `atomicSet` / `atomicAdd` / `atomicCas` + `spawnAtomicAdd` で OS スレッド起動)、IO 型マーカ (`IO A == A`、将来の effect tracking のための予約)。 Phase 4 (クロージャ並行性 + FFI): **Rc → Arc 全面移行** で `Value : Send + Sync`、クロージャベース `spawn : (() -> A) -> Thread A` / `join : Thread A -> A`、mpsc channel (`chanNew` / `chanSend` / `chanRecv` / `chanClose`)、FFI via libc dlopen (`ffiLoad` / `ffiCallIntInt` / `ffiCallStrInt` / `ffiClose`、Linux/macOS、外部 Rust クレートなし)。すべて集合論的に解釈可能で `forall x in S, P x` がそのまま使える。

## クイックスタート

ビルド (Rust 1.70+):

```sh
cargo build --release
```

ファイル実行:

```sh
cargo run -- examples/06_boolean_algebra.seki
```

ワンライナー:

```sh
cargo run -- -e 'theorem t : 2 + 2 == 4 := by eval'
```

REPL:

```sh
cargo run
seki> def S := {1, 2, 3}
seki> 2 in S
true
seki> :defs
seki> :q
```

## ディレクトリ構成

```
seki/
├── src/             Rust 実装 (lexer・parser・eval・prover・termination・...)
├── stdlib.seki      自動ロードされる stdlib (Rat / List / Tree / Option / Result / ...)
├── lib/             再利用可能な seki モジュール群 (algebra / cas / numeric)
├── tests/
│   ├── integration.rs    Rust 統合テスト
│   └── seki/             lib/ に対応する seki テスト
├── examples/        walking-tour サンプル (01〜37)
├── sample/          実サービス志向のミニアプリ (calc/wordcount/ledger/todo_api)
└── docs/            ドキュメント
```

詳細:
- [lib/README.md](lib/README.md) — ライブラリ構成と使い方
- [tests/seki/README.md](tests/seki/README.md) — テスト一覧

## サンプル

| ファイル | 内容 |
|---|---|
| `examples/01_basic.seki` | 数値・関数・let・if |
| `examples/02_sets.seki` | 列挙集合 / 内包集合 / union, intersect, diff, subset |
| `examples/03_lambda.seki` | カリー化・高階関数・関数型による型検査 |
| `examples/04_proofs.seki` | forall/exists・theorem の3戦術 |
| `examples/05_number_theory.seki` | 階乗・素数集合・gcd の証明 |
| `examples/06_boolean_algebra.seki` | De Morgan・分配律・吸収律 (22 個) |
| `examples/07_modular.seki` | Z/12Z 加法群の公理検証 (10 個) |
| `examples/08_set_identities.seki` | 集合論恒等式 (18 個) |
| `examples/09_algorithms.seki` | Gauss 公式・パスカル・冪乗則 (9 個) |
| `examples/10_puzzles.seki` | ピタゴラス数・年齢パズル・鳩の巣 (7 個) |
| `examples/11_tuples_lists.seki` | タプル・直積・リスト・map/filter/foldr |
| `examples/12_infinite_proofs.seki` | by algebra / by induction で**無限域**を証明 (20 個) |
| `examples/13_advanced_tactics.seki` | 不等式・div/mod・list/tree 帰納法・強帰納法 (24 個) |
| `examples/14_types_and_real.seki` | 型の集合論的実装・実数型 (Real)・自動昇格 (13 個) |
| `examples/15_set_definition_proofs.seki` | 集合の定義から forall/exists を健全に判定 (17 個) |
| `examples/16_stdlib_constructions.seki` | stdlib (Rat / Pos / range / map / treeSize…) の活用 (13 個) |
| `examples/17_pair_encoded_adt.seki` | リスト/木のタグ付きペア符号化 (集合論的構築) (6 個) |
| `examples/18_data_match.seki` | 代数的データ型 (`data`) とパターンマッチ (`match`) |
| `examples/19_modules_and_errors.seki` | Option/Result/`?` 演算子/モジュール (`import`) |
| `examples/20_dependent_types.seki` | 依存関数型 `(x : A) -> B(x)` と Vec n |
| `examples/21_inference_termination_classes.seki` | 型推論 / 終了性検査 / 型クラス (`class`/`instance`) |
| `examples/22_group_theory.seki` | 群論 — `lib/algebra/axioms.seki` + `Z/nZ` で半群/モノイド/可換群を任意 n で検証 (17 個) |
| `examples/23_indexed_adts.seki` | 値添字付き ADT (Vec n / Fin n / Sigma 型) — refinement で構築 (3 個) |
| `examples/24_rings_fields.seki` | 環・可換環・有限体 GF(p) (p 素数) — 汎用述語 `isField`/`isCommutativeRing` (17 個) |
| `examples/25_linear_algebra.seki` | 汎用 n-次元ベクトル + n×m 行列 (`lib/algebra/vector.seki`, `matrix.seki`) — 2/3/5-D 同一関数で検証 (25 個) |
| `examples/26_cas.seki` | **計算機代数 (CAS)**: 記号微分・積分・FTC・Leibniz — 主に `parseSym` 記法、ADT/DSL との同値性も検証 (16 個) |
| `examples/27_cas_advanced.seki` | **高度な CAS**: 多項式正規化 (`parseSym "pow (x+1) 5"`)・GCD (PRS)・因数分解・solve・BigInt (22 個) |
| `examples/28_cas_linalg_ode.seki` | **線形代数 & ODE**: n×n 行列式・2x2 固有値・Euler/RK4・Newton 法・Gauss 消去 (17 個) |
| `examples/29_analysis.seki` | **解析学**: 数値微分・積分・Taylor 級数 (exp/sin/cos/ln)・Leibniz・固定点 (Babylonian, φ) (20 個) |
| `examples/30_system.seki` | **システム開発 (Phase 1)**: 文字列・ファイル I/O・CLI 引数・`Ref`・`Dict` (32 個) |
| `examples/31_system_advanced.seki` | **システム開発 (Phase 2)**: 時刻・乱数 (PRNG)・ビット演算・プロセス実行・JSON・TCP (26 個) |
| `examples/32_system_phase3.seki` | **システム開発 (Phase 3)**: HTTP codec/client/サーバ・原子整数 + 真の並行性・IO 型マーカ (24 個) |
| `examples/33_phase4_concurrency.seki` | **システム開発 (Phase 4)**: クロージャベース並行性 (`spawn`/`join`)・mpsc channel・FFI (10 個) |
| `examples/34_phase5.seki` | **システム開発 (Phase 5)**: Bytecode VM・parMap・IO 強制・SMT-lite (linarith)・LSP (26 個) |
| `examples/35_call_syntax.seki` | **関数呼出 (Phase 11)**: `f(a, b, c)` C 流と `f a b c` curried の共存 (16 個) |
| `examples/36_for_loops.seki` | Python の `for` 文の seki での書き方 11 通り |
| `examples/37_python_for.seki` | **for 構文 (Phase 12)**: `for x in xs do body` の Python 風 syntax |
| `examples/helpers_mod.seki` | (支援ファイル) 19 のモジュール例から `import` される補助関数 |

合計で **429 件** の theorem と 1 件の axiom が `examples/` に含まれている。

## sample/ — 実サービス志向ミニアプリ

`examples/` がチュートリアル的な単一ファイルなのに対し、`sample/` は
**実サービスを模した小さなアプリ集**:

| パス | 内容 | 強みの軸 |
|---|---|---|
| [`sample/calc/`](sample/calc/) | 多項式 f(x) を CAS で微分・積分し、結果を 14 個の定理で検証 | **CAS + 証明** の統合 (他言語にない) |
| [`sample/wordcount/`](sample/wordcount/) | テキストファイル → 単語頻度集計 → 上位 N 件表示 | 文字列処理 + Dict + 自前ソートの実用例 |
| [`sample/ledger/`](sample/ledger/) | JSON 取引履歴を読み、`by algebra` で総和保存を証明しつつ適用 | 不変条件 + 健全な検証 + JSON + ファイル I/O |
| [`sample/todo_api/`](sample/todo_api/) | TODO REST API (GET/POST/DELETE)。dry-run + 実サーバ起動の両モード | HTTP + JSON + Ref<Dict> + ルーティング |

詳細は [`sample/README.md`](sample/README.md) を参照。

## ドキュメント

**使用者向け** (まずはここから):

- [docs/tutorial.md](docs/tutorial.md) — 段階的なチュートリアル (30〜60 分で一周)
- [docs/cheatsheet.md](docs/cheatsheet.md) — 構文・演算子・組込関数・戦術の早見表
- [docs/cookbook.md](docs/cookbook.md) — 「~したい」「~を証明したい」レシピ集

**リファレンス**:

- [docs/language.md](docs/language.md) — 言語仕様 (構文・型・演算子・BNF)
- [docs/proofs.md](docs/proofs.md) — 定理証明ガイド (9 戦術 + 合成の詳細・パターン集・限界)

**実装者向け**:

- [docs/internals.md](docs/internals.md) — 実装アーキテクチャ (モジュール・データフロー・拡張ポイント)

## ステータス

動作するプロトタイプ。下記が動く:

- 集合論的セマンティクス (列挙集合・内包集合・所属/部分集合/和/積/差/直積)
- ラムダ計算 + カリー化 + 再帰 + 集合論ベースの型注釈検査
- タプル / リスト / 二分木 (タグ付きペア符号化、stdlib で seki 自身が実装)
- 代数的データ型 (`data`) + パターンマッチ (`match`)
- エラーハンドリング (`Option`/`Result` + `?` 演算子)
- モジュールシステム (`import "path"` / `import ... as M`)
- 多項式正規化による**無限域**等式・不等式の証明
- 整数除算 `/c`・剰余 `mod c` (定数除数) の代数判定
- 半正定値 2次形式の自動判定 (Sylvester 基準・最大 4 変数)
- Nat / List / Tree 上の構造帰納法 (`==`, `<=`, `>=`, `<`, `>` 全対応)
- 深さ 2 の強帰納法 (Fibonacci 等)
- 集合の定義 (内包の述語) からの forall/exists 自明判定
- 依存関数型 `(x : A) -> B(x)` (サンプル検査ベースの member 判定)
- 軽量な型推論 (Arrow 型まで再構築)・REPL `:type` 問い合わせ
- 構造帰納・辞書順 (lex)・`mod`・`fst`/`snd` チェイン・`match` パターン束縛変数を扱う終了性検査 (warning 報告)
- 型クラス (`class`/`instance`) — **辞書の自動解決** (`eq 3 3` で `Eq Int` インスタンスを自動補完) + 明示的辞書渡しもサポート
- `by simp` / `by unfold` / `by intros` 戦術 + `then` によるタクティク合成 (`by intros then unfold f then algebra`)
- **AC-canonicalization for `by simp`**: 可換和/可換積を正規形に変換、対称規則 (`a+b == b+a`) も oscillate せず使える
- **`by linarith`** (線形不等式戦術 — algebra のサブセットとして提供)
- **`by decide`** (Bool に落とせる命題を強制的に決定)
- **`let rec`**: ローカル再帰関数 (`let rec f := \x -> ... f (x-1) ... in body`)
- **enum-style `data` の自動セット化**: `data Color = Red | Green | Blue` で `def Color := {Red, Green, Blue}` が自動生成、`forall x in Color, ...` が動く
- **任意 `data` 型に対する `by induction`** (recursive ADT も含む): 各構築子について自動で case 分析。recursive ctor の引数は IH/opaque atom として扱う
- エラーの位置情報 (`[line:col]` プレフィックス) + **ソース行 + キャレット表示** + 機械可読なエラーコード (`E001`〜`E005`)
- **`forall (x y z) in S` 多変数 sugar**、**match の tuple パターン** (`Some (a, b)` 等)、**match 網羅性検査 (warning)**
- **命題 implication `P => Q`** (右結合、`not P or Q` への parse 時 desugar)

主要な未対応:

- 依存型の完全検査 (現状はサンプリングのみ — 任意の引数で必ず正しい保証はない)
- 依存パラメトリック ADT の専用構文 (`data Vec : Nat -> Set where ...`) — refinement + 既存 ADT で代用可
- 依存ペア型 `Σ (x : A), B(x)` の専用構文 (refinement で代用可)
- 3 次以上の不等式・可変除数の div/mod
- パターンマッチの網羅性検査
- 任意深さの強帰納法・整列性原理
- 相互再帰関数の unfold
- 真のスコープ分離されたモジュール (現状はフラットな名前空間に prefix 追加)
- `by simp` の対称規則 (`add_comm` 等) — oscillation で 1-step ぶんしか効かない
- AST span (Expr 単位の位置情報) — エラーは decl 単位の `[line:col]` まで
- LSP / インタラクティブなタクティクモード (goal-stack)

詳細は [docs/internals.md](docs/internals.md) の「今後の拡張」を参照。

## ライセンス

未設定 (個人プロジェクト)。

# Roadmap

これは **honest roadmap** です — 「いつかやりたいこと」ではなく
「現実的に何が必要で、なぜ難しいか」を記録します。
予定が確定しているものとそうでないものを明示します。

## 現在の位置 (2026-09)

- **バージョン**: 0.10.0 (Phase 6 進行中)
- **コード規模**: ~18,000 行 Rust + stdlib
- **builtin**: 120 個
- **テスト**: 192 統合 + 46 単体 + 12 property + 8 LSP、
  `.seki` テスト 31 ファイル (全て `cargo test` に配線済み)、
  `lib/` + `examples/` + `tests/seki/` 合計 955 定理
  (**kernel 検証済み 925 / `axiomatic` 3 / `unchecked` 23 / `sampled` 17**)
- **TCB**: 約 2,600 行 (`kernel.rs` + `unfold.rs` + `rewrite.rs` +
  多項式算術)。`prover.rs` の 4,134 行は TCB の外
- **依存クレート**: ゼロ
- **バイナリ**: `seki` + `seki-lsp`

---

## Phase 6 — Production-readiness 整備 (次に着手) 🎯

**目標**: プロジェクトを「外から使える」レベルに引き上げる。
コードの中身よりも周辺の信頼性整備が中心。

### 進行中
- [x] GitHub Actions CI (`.github/workflows/ci.yml`)
- [x] CHANGELOG / ROADMAP / CONTRIBUTING / SECURITY
- [x] `seki --version` + semver ポリシー
- [x] リリースビルドスクリプト

### 完了 (0.8.0)
- [x] **演繹 (`by apply` / `by have` / `by assumption`)** — 証明が初めて
      合成できるようになった。955 定理中 12 件しか他の定理を使っていなかった
      状態を解消する土台
- [x] **Farkas 証明書** — 仮定付き線形算術 (スケーリング・緩み・区間) が
      kernel 検証済みで通るようになった
- [x] **確からしい事実からの推論** (0.10.0) — `with confidence` + Fréchet
      下界。確率は kernel の外 (`src/confidence.rs`)
- [x] **仮定の逆算** (0.10.0) — 失敗したゴールについて「何を仮定すれば
      成り立つか」を検証済みで提案 (`src/abduce.rs`)
- [x] **型注釈が証明義務になった** (0.9.0) — `def f : A -> {y | Q y}` が
      生む `forall x in A, Q[y := f x]` を定理と同じ prover・同じ kernel で
      検証する。`docs/spec/06-soundness.md` が「残る最大の穴」と呼んでいた
      部分。落ちない義務は `--audit` で名前と内容が出る
- [x] **`by auto` が健全な証明を優先** (0.9.0)
- [x] **分出公理** (0.8.1) — 無制限内包をやめ、Russell の逆理を到達不能に
- [x] **評価ステップ予算と深さ上限** (0.8.1) — 非停止の定義がハングや
      プロセス abort ではなくエラーで止まるようになった
- [x] **証明項 (proof term) と kernel** — タクティクは信頼されなくなった。
      TCB が約 9,000 行から約 2,600 行へ。`--audit` / `--proof` で可視化。
      導入時に `by algebra` の実在する健全性バグを発見
- [x] **有界な内包を有限と認識** — `{x in Nat | x < 12}` 上の証明が
      標本検査ではなく網羅列挙になった
- [x] **信頼水準 (`TrustLevel`) + `--strict`** — 「証明された」の機械検査。
      `docs/spec/06-soundness.md` §6.0
- [x] **Int overflow を runtime error に** — `by eval` と `by algebra` が
      同一命題について矛盾する状態を解消
- [x] **`Session` をライブラリへ** — 統合テストが本物のドライバを通り、
      LSP が静的 shape 検査の診断を出せるようになった
- [x] **構造的エンコーディングの簡約を表駆動に** — データ型を足すのに
      Rust のコードを増やさない形へ
- [x] **`target/` を git 管理下から外した**
- [x] **未配線テストの検出** — `.seki` テストの配線忘れを `cargo test` が落とす

### 計画
- [ ] **`by induction` のステップの証明項** — 残る `unchecked` 29 件のうち
      19 件。基底ケースは既に kernel が検証している。ステップの正規化
      (後者側の展開 + `if` の簡約) に witness 形式を与える必要がある
- [ ] **`by algebra` の残り** — 符号解析・`!=`・有理関数の約分 (各 1 件)
- [ ] **引数位置の refinement** — `(amt : {a in Nat | a <= bal}) -> ...`。
      返り値位置は 0.9.0 で証明義務になった (`src/obligation.rs`)
- [ ] **エラー位置情報の精緻化** — 現在は decl 単位の `[line:col]`。Expr 単位
      の span を AST に持たせて、`x + true` のような場合に `true` 部分だけを
      指せるようにする。
- [ ] **didYouMean** — `stlrLen` を typo して `strLen` を提案。
- [ ] **REPL の改善** — 永続コマンド履歴、`:help`、`:builtins` リスト、
      `:doc <name>` で builtin の docstring 表示。
- [ ] **テストハーネス拡充** — parser fuzz harness、property-based tests
      for value_eq / set_eq / VM / linarith。
- [ ] **stdlib API ドキュメント** — 各 builtin に doc comment + 自動抽出。
- [ ] **配布バイナリ** — GitHub Releases に Linux x86_64 / macOS arm64 の
      static binary を upload。

---

## Phase 7 — 性能 ⚡

**目標**: production web service で使えるレベルの実行速度。

### 計画
- [ ] **Bytecode VM の完全化**
  - クロージャ / 関数適用
  - パターンマッチ (`match`)
  - List / Tuple / Set 操作
  - 全例題が VM で動く
- [ ] **JIT または AOT compile to native**
  - 最初は Cranelift 統合 (オプションで `--features=jit`)
  - 中期では LLVM bindings 経由のネイティブ生成
- [ ] **GC tuning** — 現状 Arc refcount のみ。世代別 GC を検討
  (ただし large refactor; trade-off は慎重に)。
- [ ] **ベンチマークスイート** — `bench/` 配下に標準ベンチ。SPECint 風の
      テストハーネス。

**honest 評価**: 完全 VM だけで 2-4 週間、ネイティブ codegen は 2-6 ヶ月。

---

## Phase 8 — 健全性 🛡

**目標**: 「証明された」が本当に意味するようにする。

### 計画
- [ ] **多変数線形整数算術** — 既存の単変数 Fourier-Motzkin を多変数に拡張。
- [ ] **Real (実数) の線形算術** — Q 上の線形 FM。
- [ ] **依存型の SMT 委譲** — Z3 オプション統合 (現状の zero-deps とは
      `--features=smt` で trade off)。
- [ ] **終了性検査の強制モード** — `#[total]` annotation で warning を error に。
- [ ] **言語仕様書** — `docs/spec/`  配下に BNF + 意味論 + 健全性議論。

**honest 評価**: 健全な依存型は深い topic。F* / Lean / Coq の蓄積に
追いつくには年単位の投資。

---

## Phase 9 — エコシステム 🌳

**目標**: サードパーティパッケージを書ける土台。

### 計画
- [ ] **パッケージマネージャ** (`seki-pkg` バイナリ)
  - `Seki.toml` manifest
  - semver 解決
  - github からの fetch
  - lockfile
  - キャッシュ in `~/.seki/cache/`
- [ ] **公式 registry** — GitHub Pages or 専用ホスト。
- [ ] **コア library 群**
  - `seki-http` — async HTTP server framework
  - `seki-sqlite` — SQLite bindings via FFI
  - `seki-json-schema` — JSON schema validation with type-level guarantees
  - `seki-tls` — TLS via rustls bindings (ここで zero-deps を一部譲歩)
  - `seki-async` — async/await on top of mio/io_uring
- [ ] **公式 web framework** — Phase 3 の `httpServe` を発展させる。

**honest 評価**: パッケージマネージャだけで 2-3 ヶ月。エコシステム全体は
コミュニティが必要。

---

## Phase 10 — 完全な開発体験 🛠

**目標**: VS Code / Neovim ユーザがストレスなく書ける。

### 計画
- [ ] **LSP の機能拡充**
  - hover (型 + docstring)
  - goto-definition
  - completion
  - rename refactor
  - code actions
- [ ] **デバッガ** — 段階実行、ブレークポイント、ウォッチ式。
- [ ] **フォーマッタ** (`seki-fmt`) — opinionated、設定ゼロ。
- [ ] **公式 VS Code 拡張** — Marketplace に publish。
- [ ] **オンライン playground** — wasm ビルドで browser 上で動く。

---

## やらない / Out of Scope

honest 評価: 以下は **意図的に実装しない** 予定です。

- **GUI ライブラリ** — 言語の競争力ではない。HTTP server を経由した web UI で十分。
- **メタプログラミング / マクロ** — `data` / `class` の desugar 以上は複雑性が高すぎる。
- **エフェクトハンドラ** — F\* の effect 階層は強力だが、現在の seki の規模では
  IO monad で十分。
- **HKT (higher-kinded types)** — 型クラスを強力にするが、設計が深い。
- **TLS の hand-roll** — セキュリティクリティカル。rustls などの mature な
  実装を FFI 経由で使う。

---

## 中止 / 取り下げ

なし (まだ若いプロジェクトなので)。

---

## バージョン体系

- **0.1〜0.5**: 初期実装期 (Phase 1-5)。**破壊的変更頻繁**
- **0.6〜0.9**: Production-readiness 整備期 (Phase 6-7)。重要な
  破壊的変更が出る場合は CHANGELOG に明示。
- **1.0**: 言語仕様書 + 健全な依存型 + 完全 VM + LSP がそろった時点でリリース。
  以降は semver に厳密に従う。

**目標時期**: 1.0 は **2027 後半〜2028 前半** を想定 (1 人開発の場合)。
チームが拡張すれば前倒し可能。

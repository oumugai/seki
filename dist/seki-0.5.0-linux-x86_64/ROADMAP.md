# Roadmap

これは **honest roadmap** です — 「いつかやりたいこと」ではなく
「現実的に何が必要で、なぜ難しいか」を記録します。
予定が確定しているものとそうでないものを明示します。

## 現在の位置 (2026-05)

- **バージョン**: 0.5.0 (Phase 5 完了)
- **コード規模**: ~12,000 行 Rust + 285 行 stdlib
- **builtin**: 120 個
- **テスト**: 107 統合 + 27 seki test + 429 example 定理
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

### 計画
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

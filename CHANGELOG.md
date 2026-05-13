# Changelog

このファイルは [Keep a Changelog](https://keepachangelog.com/ja/1.1.0/) フォーマットに従い、
バージョンは [Semantic Versioning](https://semver.org/spec/v2.0.0.html) に従います。

## 互換性ポリシー

seki は **pre-1.0** です。これは次を意味します:

- **マイナーバージョン (0.X.0)** で破壊的変更が起こり得ます。
- **パッチバージョン (0.X.Y)** はバグ修正のみで、ソース互換性は保たれます。
- **1.0** に到達するまでに **言語仕様書** と **健全性議論** を整備します。

---

## [Unreleased]

### Added

### Changed

### Deprecated

### Removed

### Fixed

### Security

---

## [0.5.0] — 2026-05-12 — "Phase 5: 性能 + 健全性の第一歩"

### Added

- **Bytecode VM** (`src/bytecode.rs`)
  新規 410 行の stack-based VM。算術 / 制御フロー / `let` / 短絡 and/or を
  コンパイルして実行。`vmEval` / `vmTime` / `vmCompiles` 経由でアクセス可能。
  100 万回 arithmetic eval を ~150ms (≒6.5M ops/sec)。
- **parMap** thread pool — `parMap : (A → B) → List A → List B`。
  リスト要素ごとに OS thread を spawn、結果順序を保持。I/O bound タスクで
  実用的な並列性。
- **IO モナド強制** — 型注釈 `A → IO B` が付いた関数は、サンプル検査時に
  呼び出されなくなった (副作用が型検査で走る問題を解消)。
- **SMT-lite** (`src/linarith.rs`、新規 261 行) — 一変数線形整数算術の
  健全な決定手続き。`linarithProve` / `linarithCounter` builtin。
  Refinement 型 `{x in Int | 線形式}` の健全な判定基盤を提供。
- **LSP サーバ** (`seki-lsp` バイナリ、新規 395 行) — JSON-RPC over stdio。
  `initialize` / `didOpen` / `didChange` / `didSave` / `didClose` /
  `publishDiagnostics` をサポート。Parse error をエディタに送る。
  外部 Rust クレートゼロ維持。
- 例題 `examples/34_phase5.seki` (26 定理)。

### Changed

- `Value` 型周辺の `Arc` / `Mutex` 化を完全化。
- builtin 総数: 114 → **120**。
- 例題定理数: 403 → **429**。

## [0.4.0] — 2026-05-12 — "Phase 4: クロージャ並行性 + FFI"

### Added

- **Rc → Arc + RefCell → Mutex 全面移行** — `Value: Send + Sync` を保証。
  クロージャがスレッド境界を越えられるように。
- **クロージャベース `spawn` / `join`** — 任意のクロージャを OS thread で実行。
  キャプチャした共有状態 (Atomic / Channel / Dict) はスレッド間で透過的に共有。
- **mpsc Channel** — `chanNew` / `chanSend` / `chanRecv` / `chanClose`。
  multi-producer / single-consumer モデル。
- **FFI via libc dlopen** — `ffiLoad` / `ffiCallIntInt` / `ffiCallStrInt` /
  `ffiClose`。Linux/macOS の `.so` を直接呼べる。libloading クレート不使用
  (`extern "C" { fn dlopen(...) }` を直接宣言)。

### Changed

- builtin 総数: 104 → 114。
- 例題定理数: 393 → 403。

## [0.3.0] — 2026-05-12 — "Phase 3: Web 層 + 真の並行性"

### Added

- **URL parser** — `urlParse : String → Result (String × Int × String) String`。
- **HTTP codec** — `httpParseRequest` / `httpFormatResponse`。
- **HTTP client** — `httpGet`、blocking。
- stdlib に `HttpRequest` / `HttpResponse` ADT、`httpServe`、便利レスポンス。
- **AtomicI64** + **`spawnAtomicAdd`** — 真の並列原子加算 (OS thread)。
- **IO 型マーカ** — `IO : Set → Set` を恒等関数として登録 (Phase 5 で
  サンプル検査スキップに利用される)。

## [0.2.0] — 2026-05-12 — "Phase 2: システム開発"

### Added

- **時刻 / Sleep** — `nowSecs` / `nowMillis` / `monotonicMillis` / `sleep`。
- **プロセス実行** — `execShell` / `runCommand`。
- **PRNG** (xorshift64*) — `randomSeed` / `randomInt` / `randomRange` /
  `randomFloat`。外部クレートなし。
- **ビット演算** — `bitAnd` / `bitOr` / `bitXor` / `bitShl` / `bitShr` /
  `bitNot` / `popcount`。
- **JSON** — `Json` ADT + `jsonParse` + `jsonEncode`。完全 hand-rolled
  パーサ、外部依存なし。
- **TCP ネットワーキング** — `tcpListen` / `tcpAccept` / `tcpConnect` /
  `tcpRead` / `tcpWrite` / `tcpClose`。`Value::Handle` バリアントで socket
  を opaque token として exposing。

## [0.1.0] — 2026-05-12 — "Phase 1: 汎用言語層の基盤"

### Added

- **文字列演算** — `strLen` / `strConcat` / `strContains` / `strStartsWith` /
  `strEndsWith` / `strIndexOf` / `strReplace` / `strSplit` / `strJoin` /
  `substring` / `strToUpper` / `strToLower` / `strTrim` / `strChars` /
  `intToStr` / `realToStr` / `strToInt` / `strToReal` / `toStr`。
- **ファイル I/O** — `readFile` / `writeFile` / `appendFile` / `fileExists` /
  `removeFile`。すべて `Result E A` を返して失敗を型に表現。
- **I/O ストリーム** — `println` / `eprint` / `eprintln` / `readLine`。
- **OS / プロセス** — `args : List String` / `getEnv` / `exit`。
- **可変参照** — `mkRef` / `readRef` / `writeRef`。`Value::Ref` バリアント。
- **辞書** — `Dict K V` (`Value::Dict`)、`dictInsert` / `dictGet` /
  `dictMember` / `dictRemove` / `dictSize` / `dictKeys` / `dictValues` /
  `emptyDict`。O(1) 操作、関数的更新。
- stdlib helpers: `when` / `unless` / `forEach` / `readLines` / `writeLines` /
  `newCounter` / `incr` / `decr` / `modifyRef` / `dictFromList` /
  `dictMap` / `unwrapOrExit` / `iterRange`。
- 例題 `examples/30_system.seki`。

## [0.0.x] — 2025〜2026 初期 — "プロトタイプ期"

集合論ベースの定理証明系 + プログラミング言語のコア:

- 集合論的セマンティクス (列挙集合・内包集合・union/intersect/subset/in)。
- ラムダ計算 + カリー化 + 再帰 + 型注釈。
- タプル / List / Tree (タグ付きペア符号化)。
- `data` 宣言 + `match` 式 (代数的データ型)。
- エラーハンドリング (`Option` / `Result` / `?` 演算子)。
- モジュール (`import`)、ライブラリパス自動探索。
- 9 種類の証明戦術 (`eval` / `refl` / `algebra` / `induction` /
  `strong_induction` / `simp` / `unfold` / `intros` / `decide` / `linarith`)。
- 型クラス (`class` / `instance`、自動辞書解決)。
- 依存型 (サンプル検査ベース)。
- 終了性検査 (warning)。
- AC-canonicalization for `by simp`。
- CAS (記号微分 / 積分 / 多項式 GCD / 因数分解 / 線形・2 次方程式求解 /
  BigInt / `parseSym` で数式直書き)。
- 解析学 (数値微分・積分・Taylor 級数・固定点反復)。
- 線形代数 (n×n 行列式 / 固有値 / Gauss 消去 / Newton 法 / ODE)。
- 群論・環論 (汎用述語 + 任意の Z/nZ)。
- ベクトル空間 (任意次元)。

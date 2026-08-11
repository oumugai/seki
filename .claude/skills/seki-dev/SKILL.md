---
name: seki-dev
description: seki 言語処理系自体 (このリポジトリ src/, lib/, tests/, docs/) に手を入れる際の開発規約 — ビルド/テストの回し方、テストファイルの置き方、ドキュメント同期のルール。コンパイラ/stdlib/ドキュメントを変更するときに読み込む。
---

# seki 本体の開発規約

このリポジトリは seki 言語処理系自体 (Rust 実装 + `.seki` 標準ライブラリ)。
利用者として `.seki` を書く場合は `seki-tactics` skill を、構文早見が
欲しい場合は `seki-reference` skill を使う。ここは **処理系側**
(`src/*.rs`, `lib/*.seki`, `tests/`, `docs/`) を変更する際の規約。

## ビルド・テスト

```sh
cargo build --bin seki --quiet   # デバッグビルド (target/debug/seki)
cargo build --release            # リリースビルド (遅いが速く動く)
cargo test                       # unit + tests/integration.rs + tests/property_tests.rs
```

`/seki-run` / `/seki-check` / `/seki-test` スラッシュコマンドがこれらを
ラップしている。

### スタックサイズの注意 (重要)

評価器に TCO が無いため、深い非末尾再帰 (`forall n in Nat` の `by eval` が
`SAMPLE_BOUND`=200 まで再帰関数を評価する等) で **ネイティブスタックを
溢れさせて SIGABRT で落ちる** バグが 2026-08 に見つかった。対処:

- `src/main.rs` の `main()` は `real_main()` を **256 MiB スタックの専用
  スレッド** で実行するだけの薄いラッパーになっている。ここを変更するときは
  この意図 (深い再帰対策) を壊さないこと。
- `.cargo/config.toml` に `[env] RUST_MIN_STACK = "67108864"` があり、
  `cargo test` がスレッドを spawn するテストにも同じ余裕を持たせている。
  この設定ファイルは削除しないこと。
- `src/lsp_main.rs` は現状 eval を呼ばない (診断はパースのみ) ので未対応の
  ままでも安全 — 将来 LSP に評価/型検査を足すなら同様のスレッド化が必要。

## テストファイルの配置規約

`lib/` 配下の `.seki` モジュールに対する自動テストは次の形:

1. `tests/seki/test_<name>.seki` — 対応する `lib/` モジュールを `import` し、
   theorem (できれば `docs/spec/09-testing.md` の階層1/2、つまり
   `forall ... := by algebra/induction/eval`) を並べる。
2. `tests/integration.rs` 末尾付近の `run_seki_test_file(path, min_theorems)`
   ヘルパを呼ぶ `#[test] fn seki_lib_test_<name>()` を追加して配線する。
   このヘルパは実際に `seki` バイナリをプロセスとして実行し、
   `"✓ proved"` の件数と `"proof error"` が 0 件であることを assert する。
3. `/seki-new-libtest` スラッシュコマンドがこの手順をラップしている。

`tests/seki/test_*.seki` を追加しただけでは **`cargo test` に含まれない**
(明示的な `#[test]` 配線が必要) — 過去に UI ライブラリ (`lib/ui/`) のテスト
ファイルがこの配線を忘れたまま未コミットで残っていたことがあった。新しい
`.seki` テストファイルを見つけたら、対応する `#[test]` が
`tests/integration.rs` にあるか必ず確認する。

## ドキュメントは実装より古くなりがち — 鵜呑みにしない

このリポジトリでは複数回、`README.md` の「主要な未対応」や
`docs/internals.md` の「今後の拡張」バックログ、`docs/spec/06-soundness.md`
の健全性表が **実装より古くなっている** ことが見つかっている
(例: `by simp` の対称規則 oscillation は既に解消済みだったのに「未対応」と
書かれていた、`by algebra` は Real を扱えないと書かれていたが実際は扱える、
逆に `by linarith` はドキュメントの例が実際には動かず `src/linarith.rs` の
専用ソルバに接続されていないことが分かった、等)。

**ドキュメントのバックログや健全性表を根拠に何かを実装/主張する前に、
必ず実際に `.seki` スクリプトを書いて `./target/debug/seki` で走らせて
現状を確認すること。** 動作例 (```seki ブロック) を含むドキュメントを
変更するときも同様に、変更前に一度実際に走らせて真偽を確かめる。

不整合を見つけたら、その場で該当ドキュメントを直す
(`README.md` / `docs/internals.md` / `docs/proofs.md` /
`docs/spec/05-tactics.md` / `docs/spec/06-soundness.md` あたりに
記述が分散しているので、1箇所直したら他に同じ主張が無いか
`grep` で確認する)。変更内容は `CHANGELOG.md` の `[Unreleased]` にも記録する。

## リポジトリの既知のクセ

- `target/` (Rust のビルド生成物) が誤って git 管理下にあり、ビルドするたびに
  差分が出る。**`git add` するときは `target/` を含めない** — 明示的にファイル名
  を指定して `git add` すること (`git add -A` / `git add .` は使わない)。
- リポジトリルート直下に `it_investment_*.seki` のような、処理系本体とは
  無関係なユーザのスクラッチファイルが置かれていることがある。処理系の
  変更作業では触らない。
- `.claude/` (このディレクトリ) 配下のスラッシュコマンド・skill は
  他の利用者と共有するため git 管理下にある。ローカル限定の設定は
  `.claude/settings.local.json` に置く。

## 関連

- `seki-tactics` skill — 証明戦術の選び方 (利用者向け)
- `seki-reference` skill — 構文・組込関数早見
- `docs/spec/08-rust-seki-split.md` — Rust 側とライブラリ側の分担方針
- `docs/spec/09-testing.md` — テスト哲学 (階層モデル)

---
description: seki ファイルをビルドして実行する
argument-hint: <file.seki> [-- program-args...]
---

seki (このリポジトリの言語処理系) のファイルをビルド・実行してください。

## 手順

1. `git rev-parse --show-toplevel` でリポジトリルートを特定し、そこの
   `Cargo.toml` に `name = "seki"` があることを確認する。違えば
   「このコマンドは seki リポジトリ専用です」と伝えて止める。
2. リポジトリルートで `cargo build --bin seki --quiet` を実行する
   (初回以降は増分ビルドなので速い)。エラーが出たら実行を止め、
   コンパイルエラーをそのまま見せる。
3. `$ARGUMENTS` が空なら: **REPL はここでは起動できない** (対話的な標準入力が
   必要なため)。代わりに次のいずれかを提案する:
   - `/seki-run -e '式'` 相当を使うか (下記)、
   - ユーザ自身が `! ./target/debug/seki` をプロンプトで手動起動する。
4. `$ARGUMENTS` の最初のトークンが `-e` なら、残りを式として
   `./target/debug/seki -e '<式>'` を実行する。
5. それ以外は最初のトークンをファイルパスとして
   `./target/debug/seki <file> [残りの引数]` を実行し、標準出力・標準エラーを
   そのまま提示する。
6. `proof error` / `type error` が出た場合は、行番号を読み、関連する
   `docs/spec/05-tactics.md` (タクティク) や `docs/language.md` (型) の節を
   参照して、原因の見立てを一言添える。`seki-tactics` skill が読み込まれて
   いなければ参照して良い。

## 例

```
/seki-run examples/13_advanced_tactics.seki
/seki-run -e 'theorem t : 2 + 2 == 4 := by eval'
/seki-run sample/todo_api/main.seki -- --dry-run
```

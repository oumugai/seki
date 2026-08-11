---
description: seki ファイル(群)を --check で副作用なしに型検証・証明検証する
argument-hint: [file.seki | directory]
---

seki の `--check` モード (各トップレベル式の値を出力せず、パース・型検査・
theorem 証明だけを行う) でファイルを検証してください。

## 手順

1. リポジトリルートを特定し (`git rev-parse --show-toplevel`、
   `Cargo.toml` の `name = "seki"` を確認)、`cargo build --bin seki --quiet`
   でビルドする。
2. `$ARGUMENTS` が単一の `.seki` ファイルなら:
   `./target/debug/seki --check <file>` を実行し、結果をそのまま見せる。
3. `$ARGUMENTS` がディレクトリ、または省略された場合は `examples/` と
   `tests/seki/` を対象にする: その下の `*.seki` を1つずつ `--check` し、
   - 通過数 / 失敗ファイル数を集計した表で報告する
   - 失敗したファイルは theorem 名・行番号・エラーメッセージを列挙する
4. `proof error` が出た theorem は、`docs/spec/05-tactics.md` の該当タクティク
   節や `docs/spec/06-soundness.md` の健全性表を参照し、「そもそも証明できる
   命題か (反例がないか)」も含めて一言で見立てを述べる。
5. 大量のファイルを流すときは1つずつ `timeout 10 ...` で実行し、
   ハングする場合 (無限ループの `by eval` など) を検出したら報告する。

## 例

```
/seki-check examples/14_types_and_real.seki
/seki-check lib/ui
/seki-check
```

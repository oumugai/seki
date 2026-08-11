---
description: cargo test (単体 + 統合 + property) を実行し、結果を要約する
argument-hint: [test name filter]
---

このリポジトリの Rust テストスイート (unit / `tests/integration.rs` /
`tests/property_tests.rs`、および `tests/integration.rs` 経由で走る
`tests/seki/test_*.seki`) を実行してください。

## 手順

1. リポジトリルートで、`$ARGUMENTS` が空なら `cargo test`、指定があれば
   `cargo test -- $ARGUMENTS` (または `cargo test --test integration --
   $ARGUMENTS` のようにフィルタを絞る) を実行する。
2. 実行時間がかかることがあるので十分なタイムアウトを取る。テストは
   デフォルトでスレッドを spawn するため `.cargo/config.toml` の
   `RUST_MIN_STACK` が効いている前提 (深い再帰の SIGABRT クラッシュ対策 —
   詳細は `seki-dev` skill 参照)。
3. 全部 pass なら「N 件 pass (unit/integration/property の内訳)」を簡潔に
   報告する。
4. 失敗があれば:
   - 失敗した test 名と assert / panic メッセージを抜き出す
   - `git status` / `git diff` で直近の変更点を確認し、関連しそうな行を指す
   - **SIGABRT / "stack overflow" が出た場合**は、深い非末尾再帰が原因の
     可能性が高い。`.cargo/config.toml` が存在し `RUST_MIN_STACK` を設定
     しているか、`src/main.rs` の `real_main` がスレッド経由で起動している
     かを確認する (誤って削除/変更されていないか)。
5. 新しい `tests/seki/test_*.seki` を追加した直後にこのコマンドを流す場合は
   `/seki-new-libtest` の手順が正しく `tests/integration.rs` へ配線したかも
   合わせて確認する。

## 例

```
/seki-test
/seki-test algebra_
/seki-test seki_lib_test_ui
```

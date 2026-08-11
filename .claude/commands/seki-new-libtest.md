---
description: 新しい tests/seki/test_<name>.seki を作り、tests/integration.rs に配線する
argument-hint: <対象の lib モジュール相対パス> <確認したい性質の概要>
---

このリポジトリの既存の規約に従って、`lib/` 配下のモジュールに対する
自動テストを追加してください。規約 (詳細は `seki-dev` skill 参照):

- `tests/seki/test_<name>.seki` が対応する `lib/` モジュールを `import` し、
  theorem を並べる
- `tests/integration.rs` に `run_seki_test_file("tests/seki/test_<name>.seki",
  min_theorems)` を呼ぶ `#[test] fn seki_lib_test_<name>()` を追加する
  (`min_theorems` はファイル内の実際の `theorem` 数)
- `run_seki_test_file` は `seki` バイナリを実際に実行し、
  「exit success」「"✓ proved" が min_theorems 件以上」
  「"proof error" が 0 件」を assert する

## 手順

1. `$ARGUMENTS` で示された `lib/` モジュールを読み、公開されている関数・
   性質を洗い出す。
2. `docs/spec/09-testing.md` の階層モデルに従い、可能な限り
   `forall ... := by algebra/induction` (階層1、完全証明) または
   `forall x in {...} := by eval` (階層2、有限完全) で書く。単一点の
   `assertEq` (階層0) は最小限にする。
3. `tests/seki/test_<name>.seki` を新規作成し、先頭で対象モジュールを
   `import` する。既存の `tests/seki/test_*.seki` (例: `test_ui_dom.seki`)
   のスタイル (`assertEq` + `TestCase` + `runMain` での集計) を真似ても良いし、
   単純に `theorem` を並べるだけでも良い。
4. `cargo build --bin seki --quiet && ./target/debug/seki
   tests/seki/test_<name>.seki` で単体に実行し、全 theorem が
   `✓ proved` になることを確認する。
5. `tests/integration.rs` の既存の `seki_lib_test_*` 群のすぐ後ろに、
   同じパターンで新しい `#[test]` を追記する。
6. `cargo test --test integration seki_lib_test_<name>` で新テストだけ実行し
   通ることを確認し、最後に `/seki-test` (または `cargo test`) で全体に
   回帰がないことも確認する。
7. `README.md` の examples 表や `CHANGELOG.md` の `[Unreleased]` に
   追記が必要かユーザに確認する (機能追加を伴う場合)。

## 例

```
/seki-new-libtest lib/numeric/linalg.seki 逆行列の性質をいくつか検証したい
/seki-new-libtest lib/ui/sse.seki SSEイベントのエンコードを検証したい
```

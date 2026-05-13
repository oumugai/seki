# Contributing to seki

seki への貢献を歓迎します。本ドキュメントは「最低限知っておいてほしいこと」を
コンパクトにまとめたものです。

## 開発環境

最小要件:

- Rust **1.70 以上** (Edition 2021、いくつかの安定 API を使用)
- Cargo
- POSIX 環境 (Linux / macOS) — FFI ビルトインは Windows では動きません
- Python 3 (LSP テストに使用)

```sh
git clone https://github.com/<your>/<seki-fork>.git
cd seki
cargo build --release
cargo test --release
```

例題と test suite を全実行:

```sh
for f in examples/*.seki; do
  [ "$f" = "examples/helpers_mod.seki" ] && continue
  ./target/release/seki "$f" >/dev/null || echo "FAIL: $f"
done
for f in tests/seki/test_*.seki; do
  ./target/release/seki "$f" >/dev/null || echo "FAIL: $f"
done
```

## ブランチ・PR 運用

- `main` が常にビルド成功 + 全テスト pass。
- 機能追加は `feat/<short-name>` ブランチで作業。
- バグ修正は `fix/<short-name>`。
- リファクタは `refactor/<short-name>`。
- **小さく分けて PR を出す**。1 PR = 1 トピック原則。

## コードスタイル

- `cargo fmt` を実行 (CI で check; 違反は warning 扱い、当面 fail させません)。
- `cargo clippy` の警告にはなるべく対処。すべて潰す必要はないが、明らかな
  問題はマージ前に直す。
- **コメントは「なぜ」を書く**。「何を」しているかは識別子と関数名で読める
  はずです。

## 新しい builtin を追加する場合

1. `src/eval.rs` に Rust 関数を書く (`fn b_xxx(args: &[Value]) -> Result<Value, String>`)。
2. `make_prelude` で `g.defs.insert("xxx".into(), bi("xxx", arity, b_xxx));` で登録。
3. 必要なら `src/typecheck.rs` の `prelude_shapes` にも追加 (関数の場合 `Shape::Fn`)。
4. **テスト** を `tests/seki/` に追加。
5. **example** に使い方の demo を追加 (適切な番号の `examples/NN_*.seki` 内)。
6. **README** の builtin 一覧 + 該当 example の theorem 数を更新。
7. **CHANGELOG.md** の `[Unreleased]` セクションに記述。

## テスト

- **Rust ユニット/統合テスト**: `tests/integration.rs` 内。`cargo test --release` で実行。
- **seki テスト**: `tests/seki/test_*.seki`。`cargo test` から自動実行されないので
  個別に走らせる必要があります (CI が一括実行)。
- **example**: `examples/*.seki`。すべて `exit 0` で完走することがリリース条件。

## ドキュメント

- ユーザ向け: `README.md`、`docs/tutorial.md`、`docs/cookbook.md`、
  `docs/cheatsheet.md`、`docs/language.md`、`docs/proofs.md`。
- 実装者向け: `docs/internals.md`。

新機能は最低 1 つはドキュメントに記述してください。

## バグ報告

GitHub Issues に下記の情報を:

1. seki のバージョン (`seki --version`)
2. OS (Linux distribution / macOS バージョン)
3. 再現可能な最小の seki コード
4. 期待した挙動 / 実際の挙動
5. error 出力全文

## 機能リクエスト

GitHub Issues に下記を:

1. **何ができるようになるか** (ユースケース)
2. **なぜそれが必要か** (現状で代替不可能か)
3. **集合論的な意味付け** (もしあれば — seki の哲学に沿うかの判断材料)
4. **複雑度の見積もり** (どれくらい大きな変更か)

「言語に何が欠けているか」より「**自分のユースケースに何が困っているか**」
の形で書いてもらえると、優先度判断がしやすいです。

## セキュリティ

脆弱性報告は `SECURITY.md` を参照。

## 行動規範

短く言うと: **他者を尊重して、技術的な議論にフォーカスしてください**。

- いかなる差別・嫌がらせも禁止。
- 技術的批判は OK だが、人格批判は不可。
- 「Code of Conduct」違反は管理者が対処。最終手段としてプロジェクトから
  除外することがあります。

詳しくは [Contributor Covenant](https://www.contributor-covenant.org/version/2/1/code_of_conduct/)
に準拠します。

## ライセンス

本プロジェクトに貢献することで、その貢献内容を seki のライセンス
(現在: 未設定 — 個人プロジェクト) に従って配布する許諾を与えたものと見なされます。
公式 OSS ライセンスを採用する際は CHANGELOG にて告知します。

# seki Language Specification

このディレクトリは seki の **言語仕様 (draft)** です。
seki 0.5.0 時点の挙動を記述しています。1.0 までは破壊的変更が入り得ます。

## 構成

| ファイル | 内容 |
|---|---|
| `01-lexical.md`       | 字句構造 (lexical syntax): トークン、コメント、リテラル |
| `02-grammar.md`       | 構文 (BNF + 操作子優先順位) |
| `03-semantics.md`     | 操作意味論 (evaluation rules、 set membership) |
| `04-type-system.md`   | 型 = 集合という考え方、依存型、refinement、型クラス |
| `05-tactics.md`       | 9 種類の証明戦術の意味論と健全性条件 |
| `06-soundness.md`     | 健全性に関する正直な議論 (sampling-based dep type, 終了性) |
| `07-stdlib.md`        | stdlib のデータ構造の集合論的解釈 |
| `08-rust-seki-split.md` | Rust 層と seki 層の分割原則 — 何が Rust に、何が seki に居るべきか |
| `09-testing.md` | テスト哲学 — 「点」ではなく「集合全体の振る舞い」で検証する |
| `10-builtin-metadata.md` | Rust builtin の集合論的・構造的メタデータと seki 側 API |

## 設計目標

1. **集合 = 型**: 任意の集合 `T` は型として使える。`v : T` は `v ∈ T`。
2. **English keywords, no Unicode**: `forall`, `union`, `subset`、`∀`/`∪`/`⊆` は使わない。
3. **証明と計算と CAS の統合**: 同じ言語で書ける。
4. **シンプルな実装**: ~3000 行 Rust + ~285 行 stdlib + 依存ゼロ。

## 健全性の honest な現状

- **依存型**: サンプル検査ベース → 健全ではない (Phase 6+ で SMT 委譲予定)
- **終了性**: warning のみ (Phase 7+ で `#[total]` annotation 予定)
- **`by algebra` / `by linarith`**: 整数 / 有理数の多項式 + 線形不等式に対して
  健全
- **`by induction`**: Nat / List / Tree / user `data` に対して構造帰納法、
  健全
- **`by eval`**: 有限ケースに対して健全 (列挙集合 + 内包 ∩ 有限ドメイン)
- **`by linarith` (新版 SMT-lite)**: 一変数線形整数算術、健全 (property test
  で検証)

## バージョン

このドキュメントは seki 0.5.0 に対応。前バージョンの記述は
`git log` で履歴を確認できます。

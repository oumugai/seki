# seki sample projects

`examples/` がチュートリアル的な単一ファイルのデモなのに対し、`sample/` は
**実サービスを模したミニアプリ** を集めたディレクトリです。それぞれの
プロジェクトは独立して動き、README に動作確認手順が書かれています。

| プロジェクト | 内容 | seki の強みを示す軸 |
|---|---|---|
| [`calc/`](calc/) | 検証付き電卓 — 式を CAS で微分・積分し、結果を `by eval` で証明 | **CAS + 証明** の統合 (他言語にはない unique 角度) |
| [`wordcount/`](wordcount/) | テキスト解析 CLI — ファイルから単語頻度を集計し上位 N 件を表示 | 文字列 + Dict + ソート (実用的データ処理) |
| [`todo_api/`](todo_api/) | TODO REST API — JSON 入出力 + in-memory ストア + ルーティング | HTTP + JSON + 並行性 (web 開発) |
| [`ledger/`](ledger/) | 取引帳簿 — 各 step で「総和保存」「残高 >= 0」の不変条件を検査 | refinement type + 健全な検証 |

## 共通の動作確認

```sh
# まずビルド
cargo build --release

# 各サンプルの README に従って実行
./target/release/seki sample/calc/main.seki
./target/release/seki sample/wordcount/main.seki sample/wordcount/sample.txt 5
./target/release/seki sample/ledger/main.seki sample/ledger/transactions.json
./target/release/seki sample/todo_api/main.seki    # 別 terminal で curl http://127.0.0.1:8088/todos
```

## テスト

各 sample に `tests.seki` があり、`lib/test/runner.seki` のテストフレームワークを使って
**静的 (theorem) + 動的 (assertion)** の二層検証を行います。

```sh
# 全 sample のテストを一括実行
./sample/run_tests.sh

# 個別実行
./target/release/seki sample/calc/tests.seki
./target/release/seki sample/wordcount/tests.seki
./target/release/seki sample/ledger/tests.seki
./target/release/seki sample/todo_api/tests.seki
```

### テストフレームワーク (`lib/test/runner.seki`)

集合論ベースのアサーション API を提供:

| 関数 | 集合論的役割 |
|---|---|
| `assertMember elem s`    | `elem ∈ s` (集合所属) |
| `assertNotMember elem s` | `elem ∉ s` |
| `assertSubset a b`       | `a ⊆ b` |
| `assertSetEq a b`        | `a ⊆ b ∧ b ⊆ a` (順序非依存等価) |
| `forAllInList xs f`      | `∀x ∈ xs, f(x) = Pass` (property test) |
| `assertEq` / `assertNeq` | 構造的等価 |
| `assertSome` / `assertNone` / `assertOk` / `assertErr` | ADT パターン照合 |
| `assertContains` | 文字列部分一致 |

### テスト集計 (現状)

| sample | 動的 assertion | 静的 theorem | 合計検証数 |
|---|---|---|---|
| `calc/`     |  5 | 14 | 19 |
| `wordcount/`| 13 |  1 | 14 |
| `ledger/`   | 14 |  3 | 17 |
| `todo_api/` | 21 |  1 | 22 |
| **計**      | **53** | **19** | **72** |

すべて pass で `exit 0`、いずれかが fail で `exit 1`。CI に組み込み可能。

## ディレクトリ構成 (Phase 9 後)

各 sample は **3 ファイル構成**:

- `lib.seki` — 純粋ロジック (テストから import 可能)
- `main.seki` — CLI driver (`lib.seki` を import)
- `tests.seki` — 検証 (`lib.seki` + `test/runner.seki` を import)

## なぜ examples/ ではなく sample/ ?

- `examples/` は **教育的・チュートリアル的** で言語機能の紹介に焦点。1 ファイル完結、定理証明中心。
- `sample/` は **アプリ志向** で実際のサービスを書く感覚を示す。複数ファイル可、副作用あり、CLI 引数を取る、ファイル I/O や HTTP を使う。

seki が「実行可能な数学・検証付きスクリプト言語」として **実用に耐える** こと
を示すための場所です。

## 設計原則

すべての sample は以下に従います:

1. **依存ゼロ** — seki + stdlib のみで完結
2. **証明と計算の混在** — 単なる計算ではなく、不変条件や恒等式を可能な
   範囲で証明する
3. **ドキュメント完備** — README に「何ができるか」「どう動かすか」「集合論的
   解釈は何か」を書く
4. **小さい** — 1 ファイルで読めるよう、各サンプルは < 200 行を目指す

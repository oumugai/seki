---
name: seki-dev
description: seki 言語処理系自体 (このリポジトリ src/, lib/, tests/, docs/) に手を入れる際の開発規約 — ビルド/テストの回し方、TCB を予算として扱う方針、Real=ℝ の設計不変条件、自分の体系を攻撃する習慣、ドキュメント同期のルール。コンパイラ/stdlib/ドキュメントを変更するときに読み込む。
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
(明示的な `#[test]` 配線が必要)。これは実害を出している: `sigma` が Σ 型の
キーワードになったとき `lib/probability/{continuous,montecarlo}.seki` が
パースできなくなったが、`test_probability.seki` が未配線だったため
数か月気づかれなかった (同時に 3 つの他のテストも未配線だった)。

現在は `every_seki_test_file_is_wired_into_cargo_test` が配線忘れを検出して
`cargo test` を落とすので、新しい `.seki` テストを置いたら必ず
`tests/integration.rs` に `run_seki_test_file` を呼ぶ `#[test]` を足すこと。

### Rust 側のテストは `Session` を使う

`tests/integration.rs` の `run()` はかつて宣言駆動ループの**再実装**だった
(`import` を `panic!` していた)。現在は `seki::session::Session` —
`seki file.seki` と同じコードパス — を呼ぶ。宣言処理を書き写さないこと。

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

- ~~`target/` が誤って git 管理下にある~~ → 0.8.0 で `.gitignore` に
  `/target` を追加し、`git rm -r --cached target` で追跡から外した
  (追跡ファイル 1295 → 274)。`dist/` は今も追跡下にある (リリース成果物
  76 ファイル、バイナリ 2 個を含む) ので、`git add -A` は依然として避ける。
- リポジトリルート直下に `it_investment_*.seki` のような、処理系本体とは
  無関係なユーザのスクラッチファイルが置かれていることがある。処理系の
  変更作業では触らない。
- `.claude/` (このディレクトリ) 配下のスラッシュコマンド・skill は
  他の利用者と共有するため git 管理下にある。ローカル限定の設定は
  `.claude/settings.local.json` に置く。

## グローバルインストール (このマシン限定、git 管理外)

seki を任意のディレクトリ/プロジェクトから使えるように、このマシンでは:

- `~/.local/bin/seki` — このリポジトリの release ビルドをコピーした
  グローバルバイナリ (PATH 上)。
- `~/.seki/lib` — このリポジトリの `lib/` への symlink。`seki` の
  import 解決の第4候補 (`SEKI_LIB_PATH` → cwd/`lib` → バイナリ相対 →
  `~/.seki/lib`) がここを見るので、どこからでも stdlib が引ける。
- `~/.claude/commands/{seki-run,seki-check,seki-new-theorem,seki-install}.md`
  と `~/.claude/skills/{seki-tactics,seki-reference}/` — グローバル版の
  コマンド/skill (このリポジトリの `.claude/` とは別物、こちらは
  git 管理されない個人環境)。

ソースを変更したら **`/seki-install`** でグローバル版に反映する
(release ビルド → テスト → `~/.local/bin/seki` へコピー)。反映を忘れると
グローバル版のコマンドが古い動作のままになる。

## 評価の上限 (0.8.0〜)

seki は停止性を強制しないので、評価器に 2 つの上限があります:

- `DEFAULT_EVAL_BUDGET` = 5,000 万ステップ (`SEKI_EVAL_BUDGET`)
  — `eval` と `apply` のループ両方で消費するので末尾再帰の暴走も捕まる
- `DEFAULT_EVAL_DEPTH` = 2,000 (`SEKI_EVAL_DEPTH`)
  — 非末尾再帰がネイティブスタックを尽くす前に止める

どちらも宣言ごとに補充されます。コーパス全体は 500 万ステップ・深さ 1,000 の
内側なので余裕はありますが、**重い計算を stdlib に足すときはこの上限に
当たっていないか確認すること** (当たっていれば上限を上げるより、
その計算を見直す方がたいてい正しい)。

テストで上限を変えるときは **`std::env::set_var` を使わないこと** —
env はプロセス全体なので並行実行中の他のテストに漏れます。
`tests/integration.rs` の `run_binary_with_env` のように子プロセスに
限定してください。

## TCB (信頼計算基盤) は「予算」

TCB は `src/kernel.rs` / `src/rewrite.rs` / `src/unfold.rs` /
`src/interval.rs` と `algebra.rs` の多項式算術
(`Polynomial::{add,sub,mul,scale}`, `expr_to_poly`, `decimal_to_rat`)。
**約 4,900 行で、処理系全体 28,000 行あまりの 17%**。

これは「小さいほうがいい」ではなく**予算**として扱う。機能を足すときは
必ず「信頼すべきものが増えるか」を先に判断すること。実際の判断例:

- 微分を差商 `(f(x+h)-f(x))/h` でなく `|f(x+h)-f(x)-L·h| <= ε|h|` で
  定義した — 有理式の約分を TCB に入れないため
- 区間モードの組込関数は**明示的な表**で、載っていないものは失敗する
  (fail-closed)。`tan` などは剰余の評価を書いていないので拒否される
- 超越関数の囲いは**剰余項の評価だけが信頼対象**になるよう書いてある
  (級数は既存の区間演算で評価する)。区間 Newton 法まで足すとその性質が
  失われるので、意図的に止めてある
- 使われていない TCB のコードは削除する (`nonneg_form`、`detect_domain`)

ここを触るときは:

- 新しい原始規則を足したら、`src/kernel.rs` の `forgery_tests` に
  「その規則を偽造したらどうなるか」のテストを必ず足す
- kernel は `EvalCtx::finite_only` でしか動かない (サンプリング禁止)。
  この不変条件を壊さないこと
- タクティク側 (`prover.rs`) はいくらでも探索してよい。健全性の責任は
  kernel にある。タクティクのバグは証明を**失敗**させるだけであるべき
- **`certify` はタクティクが失敗したら失敗しなければならない**。証明書を
  組み立ててカーネルに拒否させるのでは不十分 — 拒否された*評価*ステップは
  エラーではなく sampled として報告されるため、偽のゴールが
  「proved [sampled]」として登録される (`by witness` で実際に起きた)

## `Real` は ℝ、`f64` はその近似 (設計不変条件)

小数リテラルは書いたとおりの 10 進数として読む (`decimal_to_rat`)。
評価器は `f64` で計算するので、両者は丸めるところで食い違う。

**この食い違いを隠さないこと。** 一度、`by algebra` が `0.1 + 0.2 == 0.3` を、
`by eval` がその否定を証明し、カーネルが**両方を承認する**状態になった。
現在の解決:

1. カーネルは実数の比較を有理数の範囲内では厳密に決める
2. 範囲外では**保証された囲い** (`src/interval.rs`) を試す
3. それも決まらなければ評価器の答えを信頼するが `Approximate` と記録する

判定は構文 (リテラルがあるか) ではなく**評価器が実数に触れたか**
(`EvalCtx::touched_real`) で行う — `def a := 0.1` のように定義に隠すと
構文的な検査は抜けられるため。

新しい組込関数や評価経路を足すときは、区間モードでどう振る舞うかを
必ず決めること。決めなければ fail-closed で拒否されるので安全側に倒れる。

## 自分の体系を攻撃する

5 段の信頼水準は**正直さの上にしか成り立たない**。各段の境界は過大主張が
隠れうる場所で、実際に見つかった例:

| バグ | 症状 |
|---|---|
| `Real` の二重の読み | カーネルが `P` と `¬P` を両方承認 |
| `certify` が検証しない | 偽のゴールが `proved [sampled]` になる |
| 整数の離散性が証明書側に無い | `if i < r` の else 枝から出る等式に証明書が付かない |
| 証明書の向きの取り違え | `<=` で書くと未検証、`>=` なら通る |
| 率の飽和演算 | `0.1 * 0.2 * 0.3 == 1.0` が「kernel 検証済み」 |

**偽の命題を並べて拒否されることを確かめるテストを書くこと。**
`tests/integration.rs` には「false ... claims are refused」系のテストが
入っている。タクティクやカーネルを強くしたら、対応する偽の主張も足す。

## 証明を変更するときは信頼水準を見る

theorem の出力に `[sampled — NOT a proof]` や `[axiomatic]` が付いていたら、
その証明は無限ドメインの標本検査か未証明の公理に依存している
(`docs/spec/06-soundness.md` §6.0)。`seki --strict` で `Sound` 以外を拒否できる。

**タクティクや評価器に手を入れたら、コーパス全体の分布が変わっていないか
確認する**:

```sh
for f in $(find examples tests/seki lib -name '*.seki'); do
  ./target/release/seki --audit "$f" 2>/dev/null | grep -oE '^  [a-z]+: +[0-9]+'
done | awk -F'[: ]+' '{t[$2]+=$3} END {for (k in t) print k, t[k]}' | sort
```

2026-09 時点の実測 (**変更したら必ず取り直すこと**):

```
approximate     8      ← 反復アルゴリズムの区間依存性 (wrapping effect)
axiomatic      16
sampled        20      ← 無限ドメインの標本検査。証明ではない
sound        1148
unchecked      22      ← 大半は by induction のステップ
```

悪化していたら、健全だった証明を壊したか、証明項の生成が保守的に
倒れすぎている。`seki --proof <file> <名前>` で証明項を読める。

ディレクトリを渡すと 1 枚にまとまる: `seki --audit examples/services`。
弱い主張が残っていれば exit 1 なので、CI のゲートに使える。

## 関連

- `seki-tactics` skill — 証明戦術の選び方 (利用者向け)
- `seki-reference` skill — 構文・組込関数早見
- `docs/spec/08-rust-seki-split.md` — Rust 側とライブラリ側の分担方針
- `docs/spec/09-testing.md` — テスト哲学 (階層モデル)

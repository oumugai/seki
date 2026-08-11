---
description: 新しい theorem を対話的に設計・証明し、実行して動作確認するまで行う
argument-hint: <証明したい性質の自然言語での説明>
---

`$ARGUMENTS` で説明された性質を、実際に検証が通る seki の `theorem` として
書き上げてください。**推測で「証明できたはず」と報告しない** — 必ず
`seki` バイナリで実行して確認すること。`seki-tactics` skill (証明戦術の
選び方) を読み込んでいなければ先に読み込む。

## 手順

1. 性質を `forall x1 in T1, ..., xn in Tn, <relation>` の形に定式化する。
   ドメイン (Nat/Int/Real/List/Tree/data/列挙集合) と関係 (`==`, `<=`, `>`, ...)
   をはっきりさせる。曖昧な点があればユーザに確認する。
2. タクティクは `seki-tactics` skill の決定手順に従って選ぶ
   (大まかには: 多項式恒等式/不等式 → `by algebra`(`by linarith` は別名) →
   再帰関数の構造帰納 → `by induction` / `by strong_induction` →
   決め手がなければ小さな有限集合で `by eval`、最後の手段が `by auto`)。
3. スクラッチファイル (session のスクラッチディレクトリ、または
   `/tmp` 配下) に theorem 案を書き、
   `cargo build --bin seki --quiet && ./target/debug/seki <file>` で
   **実際に通ることを確認する**。
4. 失敗したら:
   - エラーメッセージ (`cannot prove ... over ...` 等) からタクティクの
     選び直しを検討する
   - 命題自体が偽である可能性 (手で反例を作れないか) も検討する。偽なら
     ユーザに「その命題は成り立ちません、反例は...」と報告して終える。
5. 通ったら、配置先をユーザに確認する:
   - 単発のデモ/学習用なら `examples/` に新規ファイルとして追加するか
     既存ファイルに追記
   - 再利用可能な補題なら `lib/` の該当モジュールに追記し、
     `/seki-new-libtest` で対応するテストも用意することを提案する
6. 配置後、`/seki-check` 相当 (`--check` での再検証) を一度走らせて
   最終確認する。

## 例

```
/seki-new-theorem 二分木の高さは常に0以上である
/seki-new-theorem リストを2回reverseすると元に戻る
/seki-new-theorem 正の実数 x, y について x/(x+y) + y/(x+y) == 1
```

---
name: seki-tactics
description: seki の theorem 証明で使うタクティク (by eval/algebra/induction/strong_induction/simp/unfold/intros/decide/linarith/auto) の選び方・健全性・既知の落とし穴をまとめる。theorem を書く/直す/レビューするときに読み込む。
---

# seki 証明戦術ガイド

seki は `theorem name : <命題> := <証明>` の形で命題を機械検証する。
**推測で「これで証明できるはず」と言わない** — 必ず実際にビルドして実行し、
`✓ proved` を確認すること (`/seki-run` または `/seki-check` コマンド、
あるいは `cargo build --bin seki --quiet && ./target/debug/seki <file>`)。

このドキュメントの記述はビルド済みの `seki` バイナリで **実際に動かして
検証済み** (2026-08 時点)。ただし `docs/` 配下の記述は実装より古くなっている
ことがあるので、この skill と食い違う場合は実際に動かして確かめること
(このリポジトリではそれが何度も起きている — 詳細は `seki-dev` skill)。

## タクティク選択の決定手順

`docs/spec/09-testing.md` の「階層モデル」がそのまま証明戦術選びの指針になる。
上から順に試し、**通る最強のものを使う** (階層が上がるほど健全性が強い):

1. **完全証明 (階層1、✅ 無限域で健全)**
   - 多項式の恒等式・不等式 (Int/Nat/**Real**) → `by algebra`
     (`by linarith` は完全に同じ実装への別名 — 名前で意図を示すだけ)
   - 再帰関数の構造帰納で閉じる → `by induction` (Nat: 0→k+1 / List: nil→cons /
     Tree / `data` ADT)
   - 2段以上先まで参照する再帰 (Fibonacci は `by strong_induction`、tribonacci 型など3段以上は `by strong_induction 3` のように depth を指定)
   - 既存の証明済み等式の連鎖で書き換えられる → `by simp` /
     `by simp [lemma1, lemma2]`
   - 前提を剥がしてから閉じたい → `by intros then <closer>` /
     `by unfold f then <closer>`
   - 決め手がなければ **`by auto`** — 上記の組合せを総当たりで試すポートフォリオ
     探索。「型は合っているはずだが戦術が分からない」ときの最初の一手として良い。
2. **有限完全 (階層2、✅ 列挙集合上で健全)**: `forall x in {a,b,c,...}, P x`
   の形にして `by eval`。無限ドメイン (`Nat`/`Int`) に `by eval` を使うと
   `SAMPLE_BOUND` (200) までのサンプル検査に **格下げされる** (健全ではない)。
3. **性質列挙 (階層3、🟡 列挙ケースのみ)**: 副作用や `Ref` を含むなら
   `forAllInList xs (\x -> assertMember ... / assertEq ...)`。
4. **点での例示 (階層0、❌ 避ける)**: `assertEq expected (f specific_input)`。
   ドキュメント目的や、他の階層で書けない一点リグレッションの最終手段のみ。

新しい theorem / test を書くときは、まず1を試し、無理なら2、3、4と降りる。
既存の点assertionの集まりを見つけたら、forall + 階層1/2 に**まとめ直せないか**
を検討する (行数が減り、カバレッジが増える — `docs/spec/09-testing.md` の
`sample/calc/` 移行例を参照)。

## 各タクティクの健全性と落とし穴

| タクティク | 健全性 | 注意点 |
|---|---|---|
| `refl` | ✅ | 構文的に完全一致する場合のみ。alpha-renaming なし |
| `by eval` | ✅ 有限ドメインのみ / 🟡 `Nat`・`Int` は `SAMPLE_BOUND`=200 まで | 無限ドメインで「通った」は健全性の証明ではない |
| `by algebra` | ✅ Int/Rat/**Real** (Real は `f64_to_rat` で厳密な有理数化) | `if` の場合分け対応済み。仮定の連言 (`a>0 and b>0 => ...`) は個別の仮定に分解され、**複数仮定の等重み1の和** がゴールと一致すれば閉じる (`hyps_sum_proves`) — 例: `x>0, y>0 ⊢ x+y>0` は通るが `x>0, y>0 ⊢ x-y>0` は通らない (健全)。可変除数は `==` かつ単項キャンセルで閉じる場合のみ (`(a*n)/n == a`、`(a*n) mod n == 0`) — 可変除数の不等式や剰余非零の一般ケースは未対応 |
| `by linarith` | ✅ `by algebra` と全く同じ実装への別名 | **専用の単変数 Fourier-Motzkin ソルバ (`linarithProve` builtin, `src/linarith.rs`) にはタクティクとして未接続**。多変数の線形不等式が欲しい場合、`by algebra`/`by linarith` が通らなければ現状これ以上強い一般解はない |
| `by induction` | ✅ 構造帰納 (Nat/List/Tree/data) | 真の**相互帰納法** (2つの関数の性質を互いを IH として同時に証明) は未対応 |
| `by strong_induction <N>` | ✅ well-founded on Nat (`N` 省略時2) | `N` は「関数が実際に何段前を参照するか」であり探索深さではない — 小さすぎる `N` は証明失敗になる (基底境界を跨ぐ未解決の `if` を検出するガードあり。2026-08、これが無いと偽の命題が通ってしまうバグがあった)。大きすぎる `N` は余分な基底を検査するだけで安全 |
| `by simp` | ✅ 各書換えステップが健全 | 対称規則 (`add_comm` 等) も AC-canonicalization で oscillation せず扱える。**条件付き等式** (`a > 0 => lhs == rhs` のような、規則自体に前提があるもの) は未対応 — `forall ..., lhs == rhs` の直接形のみ登録できる |
| `by decide` | ✅ Bool に reduce できる場合のみ | 型クラス無しの直接評価。`Decidable` 型クラスへの一般化はまだ無い |
| `by unfold f` | ✅ 1段展開 + 非再帰の呼び出し先を推移的に展開 | 再帰関数 `f` 自身は1段だけ展開されて止まる (無限展開しない安全策)。相互再帰の組 (`isEven`/`isOdd` 等) も呼び出しグラフのサイクル検出で正しく「再帰」と判定され、同様に1段で止まる (2026-08 修正 — 以前は誤って「非再帰」判定され32回まで交互展開が暴走した) |
| `by intros` | ✅ 全称除去 | transformer なので単体では閉じない。`then` で closer と組む |
| `by auto` | ✅ (個々の候補の健全性に従う) | 固定順のポートフォリオ探索。`theorem t : P` (`:=` 省略形) はこれに desugar される |

## 既知のクラッシュ・性能上の注意

- 評価器に **TCO (末尾呼出最適化) が無い**。非末尾再帰の深さが数百に達すると
  ネイティブスタックを消費する。以前はこれが `seki` バイナリのクラッシュ
  (SIGABRT) を引き起こしていたが、`main()` を大きいスタックの専用スレッドで
  実行するよう修正済み (2026-08、`seki-dev` skill 参照)。それでも**極端に深い
  再帰は避ける**べき — 例えば `forall n in Nat` の `by eval` サンプル検査は
  `n` を `SAMPLE_BOUND`=200 まで評価するので、非末尾再帰な関数を絡めると重い。

## クイックリファレンス

```seki
-- 完全証明 (Real 含む)
theorem t1 : forall x in Real, x + 0.0 == x := by algebra
theorem t2 : forall (x y) in Int, x > 0 and y > 0 => x + y > 0 := by linarith

-- 構造帰納
theorem len_nonneg : forall xs in List Int, length xs >= 0 := by induction

-- ポートフォリオ (戦術が分からないときの最初の一手)
def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
theorem gauss : forall n in Nat, 2 * sum n == n * (n + 1) := by auto

-- 有限完全 (無限ドメインより先にこちらで小さく確認するのも良い)
theorem small_check : forall x in {0, 1, 2, 3}, x * x >= x := by eval
```

詳細な仕様は `docs/spec/05-tactics.md` (各タクティクの正式な意味論) と
`docs/spec/06-soundness.md` (健全性の honest な議論) を参照。ただし食い違いを
見つけたら実装 (`src/prover.rs`) と実行結果を優先する。

# 6. 健全性 (Soundness) — Honest Discussion

このページは seki の **健全でない部分** を honest に列挙します。
production 採用や数学的厳密性を求める場合の参考にしてください。

## 6.1 何が健全か

### ✅ 健全な部分

| 機能 | 健全性の根拠 |
|---|---|
| `refl`、構造的等価 | 純粋な構文的判定 |
| `by eval` (有限ドメイン) | 全列挙の閉じた決定 |
| `by algebra` (Int/Rat/**Real**) | 多項式正規化 + Sylvester 基準。Real は `f64_to_rat` で厳密な有理数に変換して判定 (浮動小数の丸め誤差はそのまま — `0.1 + 0.2 == 0.3` は正しく false と出る) |
| `by induction` (Nat/List/Tree/data) | 構造帰納法、ADT の有限構築可能性 |
| `by strong_induction` / `by strong_induction <N>` (Nat, 深さ可変) | well-founded relation on ℕ。展開後に基底境界を跨ぐ未解決の `if` が残る場合は証明を失敗させる (`contains_var_conditioned_if` ガード, 2026-08 追加 — §6.6 参照) |
| `by simp` chain | 各 step が健全な書換え、対称規則 (`add_comm` 等) も AC-canonicalization で oscillation なく扱える |
| `by linarith` | `by algebra` の別名 (同じ多項式判定 + 仮定の加算結合 `hyps_sum_proves` + 多変数 Fourier-Motzkin 消去 `fm_is_unsat`)。**FM は「証明できる」方向のみ健全** — 有理数緩和が unsat なら整数/Nat 系も unsat だが、逆に有理数 SAT が整数解の存在を保証しないので反証には使わない。単変数専用の Fourier-Motzkin ソルバ (`linarithProve` builtin, Phase 5, property test 検証済) は別実装で、タクティクにはまだ接続されていない |
| 列挙集合 / 直積 / ADT membership | 完全に構造的 |
| 型クラス辞書化 | 静的に解決、実行時に明示渡し可能 |

## 6.2 何が健全でないか

### 🟡 sample-based: 完全保証なし、しかし実用上多くを catch

| 機能 | 限界 | 影響 |
|---|---|---|
| 依存型 `(x : A) -> B(x)` のチェック | `from` を 5-200 個 sample してチェック | 大きい `Int` での反例を取りこぼす |
| `forall x in Int, P(x)` の `by eval` | `[-200, 200)` のみ列挙 | 同上 |
| Refinement type のチェック | predicate を sample で評価 | 線形以外は弱い |
| 関数型 `A -> B` の member check | sample 適用で返り値を確認 | 同上 |

**影響を受けるパターン例**:
```seki
-- これは現状コンパイルが通るが、x = 201 で破綻する
def f : Int -> Pos := \x -> x  -- Pos = {x | x > 0}, but x = -50 violates
```

サンプル `x = -50` は `[-200, 200)` 内なので、これは現在検出される。
しかし以下は検出されない:
```seki
-- 関数が "ほぼ常に" Pos を返すが x = 10^9 で破綻するケース
def g : Int -> Pos := \x -> if x == 1000000001 then 0 - 1 else x + 1
```

### 🔴 検証されない部分

| 機能 | 状況 |
|---|---|
| 終了性 (termination) | warning のみ、無限ループ証明が通る可能性 |
| メモリ安全性 | Rust が保証する範囲内 (FFI で逸脱可能) |
| 例外的でない振る舞い | Int overflow は wrapping、Real は NaN/Inf あり |
| パターンマッチの網羅性 | warning のみ |
| データ競合 | `Arc<Mutex>` で sync 化されているが、deadlock 検出はない |
| FFI 経由のコード | 完全 unsafe (`SECURITY.md` 参照) |

### 例: 終了性の穴

```seki
def evil := \(_ : Unit) -> evil ()    -- 無限再帰
-- 終了性 warning が出るが、定義は受理される
theorem absurd : forall x in Unit, evil x == 1 := refl  -- これは絶対通らない
                                                          -- (refl が構造マッチ
                                                          -- しないため)
-- しかし `by eval` を使うと無限ループに陥る可能性
```

実装ノート: `by eval` は明示的な fuel (10000 ステップ) で abort するため、
無限ループ証明が成立することは現状ない。ただし、これは健全性の証明ではなく
**実装上の fuel** に依存している。

## 6.3 sample-based check の改善計画

Phase 6+ の優先項目:

### 線形整数 refinement の SMT 委譲 (進行中)

Phase 5 で `linarithProve` builtin を導入。これを型システムに統合して
`{x in Int | linear predicate}` の member check を symbolic 化する:

```rust
fn check_value_in(v, refinement) {
    if is_linear_refinement(refinement) {
        match decide_membership_via_linarith(v, refinement) {
            Proven => Ok(true),
            Refuted(cex) => Err(format!("refuted at {}", cex)),
            Unknown => sample_check(v, refinement),  // fallback
        }
    } else {
        sample_check(...)
    }
}
```

### 多変数線形算術 (Phase 7 候補)

一般的な Fourier-Motzkin elimination を多変数化。

### 非線形 SMT 委譲 (Phase 8+)

Z3 / cvc5 統合をオプション機能として (`--features=smt`)。
trade-off: zero-deps の哲学と衝突。

### 終了性検査の強制モード

```seki
#[total]
def factorial := \n -> if n == 0 then 1 else n * factorial (n - 1)
-- 終了性が構造減少で示せないと **error** に
```

## 6.4 健全性の落とし穴: 具体例

### Pattern A: 大きい数での反例

```seki
def myInverse : Pos -> Pos := \x ->
    if x > 1000 then 0 - 1 else 1 / x
```

サンプル検査が `[1, 200]` だけ見るならパス。実際は `x = 1001` で 0 を超えた値
を返す。これが現状の最大の不健全性。

### Pattern B: 終了しない関数による spurious proof

```seki
def loop := \(n : Nat) -> loop (n + 1)
theorem fake : forall n in Nat, loop n == 0 := by eval
-- by eval は loop の評価で fuel exhausted エラーになるが、
-- 場合によっては成立するように見える可能性
```

### Pattern C: 浮動小数点の不正確性

```seki
theorem t : 0.1 + 0.2 == 0.3 := by eval     -- 失敗する (f64 の丸め誤差)
theorem t2 : 0.1 + 0.2 == 0.3 := by algebra -- こちらも失敗する
-- どちらも正しい挙動: 0.1/0.2/0.3 は f64 として厳密に表現できず、
-- `by algebra` は各リテラルを厳密な有理数に変換した上で判定するので
-- 「本当に等しくない」ことを健全に検出している (誤って通すことはない)。
```

### Pattern D (発見・修正済み): `by strong_induction` の基底境界すり抜け

`by strong_induction` に depth パラメータを追加した際 (2026-08)、実際に
**偽の命題が証明できてしまうケース**が見つかった:

```seki
def f := \n ->
    if n == 0 then 0
    else if n == 1 then 0
    else if n == 2 then 0 - 1              -- ここが負!
    else f (n - 1) + f (n - 2) + f (n - 3)  -- 実際は depth 3 が必要

theorem bad : forall n in Nat, f n >= 0 := by strong_induction 2  -- 修正前: ✓ 証明できてしまった
-- f 2 == -1 が直接の反例なのに、P(0), P(1) しか基底として検査せず、
-- step 側では `if (k+2) == 2 then -1 else ...` という `k` に依存する
-- 未解決の if が「非負と仮定した不透明項」に丸め込まれてしまっていた。
```

原因: 与えた depth (ここでは 2) が関数の実際の参照深さ (3) より小さいと、
`k+depth` を展開した式に **`k` に依存する未解決の `if`** が残る。これを
`expr_to_poly` の「非該当項はすべて不透明な非負変数」というフォールバックが
無条件に飲み込んでしまい、境界のすぐ内側に潜む負のリテラルを一度も
チェックしないまま「非負の和だから非負」と誤って結論していた。

修正: 展開結果に `k` に依存する未解決の `if` が残っていないかを明示的に
検査するガード (`contains_var_conditioned_if`) を追加し、見つかった場合は
証明を **失敗** させるようにした (`by strong_induction: could not resolve
every base-case boundary ...`)。`tests/integration.rs` の
`strong_induction_rejects_insufficient_depth_instead_of_a_false_proof` に
回帰テストとして固定済み。

## 6.5 production 利用に当たって

「絶対に必要な性質」は **`by algebra` / `by induction` / `by linarith` /
`refl` でのみ証明された theorem** に限定するのが honest。
sample-based でしか証明されていない命題は invariant 維持に頼ってはいけない。

監査の指針:
1. `by eval` を使った theorem は **有限ドメイン上のみ** に限る
2. 依存型注釈は **ドキュメント** 扱いし、unsafe な前提条件には頼らない
3. `Real` 上の証明は `by algebra` (厳密な有理数変換) では健全。ただし
   `f64` リテラル自体の丸め誤差は解消されない — 厳密性が必須なら
   `Rat = Int × Pos` を使う
4. FFI と `execShell` は信頼できる入力に対してのみ使う

## 6.6 まとめ

- **健全な部分** は明確に存在し、それだけで実用的な検証が可能
- **健全でない部分** も明確で、線形整数 refinement は Phase 5 で改善開始
- 1.0 までに sample-based を SMT 委譲ベースに置き換える計画 (Phase 6-8)
- それまでは **「証明された」は健全な戦術で取得したものか確認すべき**

# 6. 健全性 (Soundness) — Honest Discussion

このページは seki の **健全でない部分** を honest に列挙します。
production 採用や数学的厳密性を求める場合の参考にしてください。

> **0.8.0 での最大の変更**: 各 theorem は **証明項 (proof term)** を持ち、
> タクティクとは独立した **kernel** がそれを原始推論規則から再構成します。
> タクティクは信頼されなくなりました — 探索してよいが、出したものは
> kernel の検査を通らなければなりません。§6.0 を参照。
>
> これは机上の話ではありません。導入した当日に `by algebra` の実在する
> 健全性バグ (`forall n in Nat, f n >= 0` を `f n = -5` に対して証明して
> しまう) を kernel が発見しました (§6.0.4)。

## 6.0 証明項 (proof term) と kernel

### 6.0.1 なぜ必要だったか

0.8.0 まで、`Prover::verify` が `Ok(Bool(true))` を返すこと**そのもの**が
証明でした。後から別のプログラムが再検査できる成果物は何も残らず、
タクティクが実行しうるコードすべて — `prover.rs` のパターンマッチ的
ヒューリスティック、`algebra.rs` の決定手続き、評価器全体 — が
**信頼計算基盤 (TCB)** に入っていました。約 9,000 行のどこかにバグが
あれば定理が黙って生成されます。実際に 2 回起きています
(Pattern D と `by eval` のサンプリング)。

### 6.0.2 何が変わったか

タクティクは証明項 (`crate::kernel::Cert`) を**生成**します。これは
ゴールをどう閉じたかを原始推論規則の木として記録したものです。
`kernel::check` がその木を命題に対して歩き、各ステップをゼロから
再確立します。

**タクティクはもはや信頼されていません。** 探索手続きであり、その出力は
独立した検査を通らなければなりません。これが標準的な LCF 分割です —
**探索は難しくバグりうる。検査は易しく、正しくなければならないのは
そこだけ。**

```
$ seki --proof examples/13_advanced_tactics.seki abs_int_nonneg
theorem abs_int_nonneg : (forall x in Int, ((if (x >= 0) then x else (- x)) >= 0))
case split on the goal's first `if`:
  when the condition holds:
    the hypotheses [(x >= 0)] add up to `x` - `0` (over Int)
  when it does not:
    the hypotheses [(x < 0)] add up to `(- x)` - `0` (over Int)

kernel verdict: every step re-established from primitives
```

### 6.0.3 何がまだ信頼されているか

正直に、依存度の高い順に:

1. **`src/kernel.rs`** (約 1,300 行)。
2. **評価器 — ただし基底項に限る。** seki の意味論は `eval` そのものなので、
   「`2 + 2` は本当に `4` か」は走らせる以外に決着しません。これは
   計算による反射 (computational reflection) で、Coq の `vm_compute` や
   Lean の `Decidable.decide` と同じ仮定です。kernel はこれを 1 点だけ
   狭めています: **`EvalCtx::finite_only` を通して評価するため、無限集合を
   列挙しようとすると標本を取る代わりにエラーになります。**
   サンプリングの穴は構造的に塞がれました — タクティクが 200 点の検査を
   差し出しても、kernel は `forall n in Nat, P n` を受理できません。
3. **多項式算術** (`Polynomial::{add,sub,mul,scale}` と `expr_to_poly`、
   `algebra.rs` の約 200 行)。その上に載る**決定手続き** (符号解析・PSD 判定・
   Fourier-Motzkin・仮定の部分集合探索) は信頼されていません — それらは
   witness を提案するだけで、kernel は加算と比較だけで検査します。
4. **`src/unfold.rs`** (286 行) — 定義の展開。置換が本物の定義を使っている
   ことだけが健全性に効きます。どこまで展開するかの戦略が間違っていても
   証明が**失敗**するだけで、偽の証明は通りません。
5. **`src/rewrite.rs`** (722 行) — 等式による書換え (Leibniz 則) と
   AC 正規化、`if` の場合分け。kernel は証明項が主張する書換え結果を
   **実際に再実行して**到達するか確かめます。

TCB は約 2,600 行。それ以外 — `prover.rs` 全体 (4,134 行)、`algebra.rs` の
残り、`termination.rs`、`linarith.rs` — は **TCB の外**です。

### 6.0.4 kernel が実際に見つけたバグ

証明項を導入した直後、次が kernel に拒否されました:

```seki
def neg : Nat -> Int := \(n : Nat) -> 0 - 5
theorem bad : forall n in Nat, neg n >= 0 := by algebra   -- 0.8.0: ✓ 通っていた
def actual := neg 3                                        -- = -5
```

原因: `expr_to_poly` は多項式に変換できない部分式を**不透明原子**という
変数に写します。`polynomial_nonneg` は `Nat` 上で「全係数が非負なら非負」と
判定しますが、これは**変数が非負である**ことに依存します。
`forall n in Nat` で束縛された `n` には成り立ちますが、任意の式を表す
不透明原子には成り立ちません。kernel は原子ごとに束縛を確認するため
この混同を拒否し、`polynomial_nonneg` を修正しました
(`algebra::is_opaque_atom`)。

帰納法のステップでは事情が逆で、`__atom_(f k)` は「より小さい引数での命題」
すなわち**帰納法の仮定**そのものなので非負と仮定してよい。この用途だけを
`polynomial_nonneg_under_ih` に分離しました。この残る仮定こそが、
帰納法のステップが kernel 検証済みにならない理由です (§6.0.6)。

### 6.0.5 信頼水準は証明項から導出される

`TrustLevel` は kernel の判定 (`Verdict`) から**導出**されます。独立した
第 2 の解析ではないので、両者が食い違うことはありません。

| 水準 | 意味 | 表示 |
|---|---|---|
| `Sound` | 全ステップが原始規則から再確立された | (印なし) |
| `Axiomatic` | 再確立されたが `axiom` に依存する | `[axiomatic]` |
| `Unchecked` | witness を出さないタクティクを通った | `[unchecked — no proof term]` |
| `Sampled` | 無限ドメインの有限標本 — **証明ではない** | `[sampled — NOT a proof]` |

定理を引用すると**その判定を引き継ぎます** — 未検証の証明を、それを
引用するだけの第 2 の定理が洗浄することはできません。

```sh
seki --audit FILE     # 各定理がどう検証されたかを一覧
seki --proof FILE 名  # 証明項そのものを表示
seki --strict FILE    # Sound 以外を拒否 (SEKI_STRICT=1 でも可)
```

### 6.0.6 実際の分布と残る穴

`lib/` + `examples/` + `tests/seki/` の全 **968 定理**:

- **kernel 検証済み — 925** (95.6%)
- `axiomatic` — 3 (IVT 公理から厳密に導出されたもの)
- `unchecked` — 23
- `sampled` — 17

`unchecked` の内訳 (すべて名前と件数が出ます):

| タクティク | 件数 | 何が足りないか |
|---|---|---|
| `by induction` | 20 | ステップを「後者側を展開して多項式の差を比べる」形で落としており、その正規化 (`unfold_one` + `simplify_ifs`) に witness 形式がない。**基底ケースは kernel が obligation を導出して検査している** |
| `by eval` | 16 | 無限ドメインの標本検査 (= `sampled` と同じ命題) |
| `by algebra` | 3 | 符号解析・`!=`・有理関数の約分 |
| `by strong_induction` | 1 | 固定深さまでの展開に witness がない |

**これらは「見えない穴」ではなく「名前の付いた、数えられる穴」です。**
`--strict` で拒否でき、`--audit` で一覧できます。

### 6.0.7 Farkas 証明書 — 探索と検査の分離の実例

仮定付きの線形算術は、この設計が一番はっきり効く場所です。

```seki
theorem npv_positive_on_range
  : forall r in Real, (0.05 <= r) and (r <= 0.15) => (100.0 - 200.0 * r) > 0.0
  := by algebra
```

`by algebra` は Fourier-Motzkin 消去で乗数を**探し**、証明項には

```
`(100 - (200 * r))` - `0` = 200·((r <= 0.15)) + ~70
```

という Farkas 証明書が載ります。kernel は仮定を 200 倍して緩み 70 を足し、
目標の差と一致するかを見るだけ — 消去アルゴリズムは一切信頼しません。
乗数が負なら (不等号が逆転するので) 拒否し、引用された仮定がゴールの
仮定に無ければ拒否します。

等式の仮定は符号の制約が要らない (`p = 0` なら任意の λ で `λp = 0`) ので
別の規則 `EqCombination` になっており、これが `by obtain` で取り出した
witness の定義性質 (`w³ - w - 2 = 0`) をゴールの形 (`w³ = w + 2`) に
並べ替える経路です。

### 6.0.9 型注釈も証明義務になる (0.9.0)

`def f : A -> {y in B | Q y}` は「**どんな引数でも**結果が `Q` を満たす」と
主張します。seki はその主張を、関数を定義域の標本に適用して結果を見ることで
検査していました。証明項を入れても、定理側が 95% kernel 検証済みになる一方で
型側は点検査のままで、このページはそれを「残る最大の穴」と呼び続けて
いました。

しかしその主張は普通の命題です:

```
def f : A -> {y in B | Q y}      ⟹      forall x in A, Q[y := f x]
```

0.9.0 からは `src/obligation.rs` がこの義務を生成し、**定理と同じ prover が
証明を探し、同じ kernel が検証します**。新しく信頼するものはありません。

```seki
def NonNeg := {x in Int | x >= 0}

-- 帳簿の不変条件 (sample/ledger の overdraft チェックと同じ形):
-- ガードがあるので「残高は負にならない」が型として証明される
def safeWithdraw : Nat -> Nat -> NonNeg := \bal amt ->
    if amt <= bal then bal - amt else bal          -- 証明される

-- ガードを外すと成り立たない (bal=0, amt=1 で -1)
def unsafeWithdraw : Nat -> Nat -> NonNeg := \bal amt -> bal - amt
--                                              [sampled — NOT a proof]
```

証明の中身は場合分けと Farkas 証明書です:

```
$ seki --audit examples/41_refinement_types.seki
safeWithdraw     the obligation was proved and kernel-checked
unsafeWithdraw   only sampled — the obligation
                 `(forall __arg1 in Nat, (forall __arg2 in Nat,
                   ((unsafeWithdraw __arg1 __arg2) >= 0)))` was not proved
```

落とせなかった義務は **標本検査に戻りますが、そう記録されます** —
`[sampled — NOT a proof]` と表示され、`--strict` が拒否し、`--audit` が
義務そのものを見せます。これで seki のすべての主張 (定理・型注釈) が
同じ土俵に載りました。

**生成されるのは refinement の部分だけです。** `f x` が refinement の
基底ドメイン (上の `Int`) に入ることは型の形の問題で、従来どおり
標本検査が担当します。引数位置の refinement
(`(amt : {a in Nat | a <= bal}) -> ...`) もまだ対象外です。

### 6.0.10 確からしい事実からの推論 (0.10.0)

LLM が抽出した事実のように「100% 確実ではないが確率的に正しそう」な前提から
推論したい場合があります。seki の分担は:

| 層 | 担当 | 変更 |
|---|---|---|
| kernel | 演繹が正しいか (二値) | **一切変更していない** |
| `Verdict.assumptions` | どの仮定に推移的に依存するか | 既存 |
| `crate::confidence` | その仮定群が結論をどこまで保証するか | 追加 (kernel の外) |

**確率を kernel に入れません。** 入れると `Sound` が連続量になり、
「kernel 検証済み」が意味を失います。一方、確率計算が必要とする構造 —
依存の推移的追跡 — は証明項が既に持っているので、その上に載せるだけです。

確信度付きの仮定はあくまで `axiom` であり、それを使った定理は
`TrustLevel::Axiomatic` のままです。確信度は**直交する第二の報告**です。

```seki
axiom gold_implies_discount
  : forall spend in Nat, spend >= 100 => spend / 10 >= 10
  with confidence 0.9
  from "LLM extraction 2026-09, opus-5, 200 件で precision 0.90"
```

```
$ seki --audit file.seki
single   axiom `gold_implies_discount`
         confidence >= 9/10 (from `gold_implies_discount` 9/10)
both     axiom `customer_spend`; axiom `gold_implies_discount`
         confidence >= 7/10 (from `customer_spend` 4/5, `gold_implies_discount` 9/10)

$ seki --min-confidence 0.85 file.seki
proof error: --min-confidence 17/20: `both` is only warranted to 7/10
```

#### 掛け算ではなく Fréchet 下界

`0.9 × 0.8 = 0.72` は**独立性を仮定した数字**で、同じ抽出パス由来の事実は
独立ではありません。結論はすべての仮定が成り立って初めて成り立つので、
保証できるのは Fréchet 下界です:

```
P(A₁ ∧ … ∧ Aₙ) ≥ max(0, Σ P(Aᵢ) − (n−1))
```

これは保守的なだけではなく、**含意に付けた確信度に対しては厳密**です。
`axiom r : A => B with confidence q` は `P(A→B) ≥ q` を意味し、
`P(A) ≥ p` から:

```
P(B) ≥ P(A∧B) = P(A) − P(A∧¬B) ≥ p − (1−q) = p + q − 1
```

つまり上の境界そのものです。**確からしいルールの連鎖は、独立性を一切
仮定せずに正しく合成します。**

⚠️ **LLM の confidence は較正された確率ではありません。** 0.9 という数字に
意味があるかは別問題なので、seki は常に**下界**として扱い、`from` による
由来の記録を推奨します。有理数は厳密に保持されます (`0.9` は `9/10` と
読まれ、f64 の丸めは入りません)。

⚠️ **`[sampled]` と混同しないこと。** サンプリングは*検査の穴*であって
認識論的主張ではありません。「無限ドメインを 200 点しか見ていない」は
「90% 確からしい」ではなく、別の軸として別に表示されます。

⚠️ **`lib/probability/` とは別物です。** あちらは確率分布を*対象として*
モデル化します (`bernoulli 0.7`)。こちらは*証明の信頼度*です。

### 6.0.12 小数リテラルと厳密有理数の桁あふれ (0.10.1 で修正)

`by algebra` は `f64` リテラルを**厳密な有理数**に変換して判定します。
`0.1` は 1/10 ではなく `3602879701896397 / 36028797018963968` です。
分母が 2^55 程度あるので、**3 つ掛けると i128 をあふれます**。

飽和演算 (`saturating_mul`) を使っていたため、あふれると*もっともらしい
誤った値*が黙って返り、`0.1 * 0.2 * 0.3` が厳密有理数として **1** に
なっていました。結果:

```seki
theorem exploit : (0.1 * 0.2 * 0.3) == 1.0 := by algebra   -- 0.10.0: ✓ 通った
def actual := 0.1 * 0.2 * 0.3                              -- = 0.006
```

`--audit` は `kernel-checked from primitives` と報告していました。
**多項式算術は kernel が信頼する部分なので、これは TCB の中の健全性バグ**
です (確率推論のデモを作っている最中に発見)。

修正: 有理数演算はすべて checked になり、あふれると
**poison 値**を返します。poison は:

- どの演算にも伝播する
- `is_zero()` は常に false (等式証明が誤って通らないように)
- `sign()` は常に負 (`sign() >= 0` の検査がすべて失敗するように)
- `expr_to_poly` が `None` を返す (タクティクは「多項式の範囲外」と報告)
- kernel は明示的に拒否する

**実用上の注意**: 率や割合を扱うときは `0.1` ではなく `1.0/10.0` と
書いてください。前者は f64 由来の巨大な分母を持ち、3 つ以上掛けると
「多項式の範囲外」になって証明できなくなります。後者は厳密に 1/10 です。

```seki
theorem ok : ((1.0/10.0) * (2.0/10.0) * (3.0/10.0)) == (6.0/1000.0) := by algebra
```

### 6.0.11 仮定の逆算 (0.10.0)

証明が失敗するのは、たいてい主張が誤っているからではなく**仮定が
足りない**からです。`cannot prove (100 - 200r) > 0` は正しいが役に立たず、
著者が知りたいのは「`r < 1/2` なら成り立つ」です。

```
$ seki file.seki
proof error: by algebra: cannot prove (100 - (200 * r)) > 0 over Real
  it would hold given `(r < (1 / 2))` — add it as a hypothesis
  (`... => <goal>`) or tighten an existing one
```

パラメータが推定値であるモデルでは、この「どこまでなら成り立つか」は
証明そのものより有用なことがあります (感度解析)。

`crate::abduce` は**探索**なので何も信頼されません。提案は必ず
「仮定として足して実際に通るか」を確認してから出るので、**出た提案は
必ず効きます**。ゴールの言い換えにしかならない提案 (`n >= 5` は
`n >= 5` があれば成り立つ) は黙って捨てられ、線形の断片の外では
何も言いません。

### 6.0.8 kernel は偽造された証明項を拒否する

kernel に価値があるのは**間違った**証明項を拒否するときだけなので、
`src/kernel.rs` の `forgery_tests` が手で組み立てた 16 種類の偽造を
すべて拒否することを固定しています:

- 無限ドメインでの `Ground` 評価
- ドメインの要素を取りこぼす `ForallFinite`
- ドメイン外の witness
- `Int` 上での非負係数規則 / 不透明原子を変数扱いする規則
- ゼロでない差に対する `Zero` 主張
- ゴールと別の不等式についての witness
- ゴールが仮定していない仮定を使う `HypSum`
- 文が一致しない `Cite`、未検証の定理の引用 (判定を引き継ぐことを確認)
- 到達しない書換え結果、実際の定義と違う `Unfold`
- 汎化した変数を評価で片付ける `Generalize`
- `if` が無いゴールでの `CaseSplit`
- サンプリング可能な文脈で kernel を動かそうとすること
- **負の Farkas 乗数** (不等号を逆転させる)、足し合わせが合わない証明書
- **前提を落とさずに補題を適用する**、補題が到達しない結論を主張する
- 仮定にないものを `Assumption` で閉じる、証明できない事実を `have` する

## 6.1 何が健全か

### ✅ 健全な部分

| 機能 | 健全性の根拠 |
|---|---|
| `refl`、構造的等価 | 純粋な構文的判定 |
| `by eval` (有限ドメイン) | 全列挙の閉じた決定。証明項は要素ごとの部分証明を持ち、**kernel が自分でドメインを列挙し直して**要素数の一致を確認する。有界な内包 (`{x in Nat | x < 12}`) も有限と認識される |
| `by eval` (無限ドメインだが定義から決定できる場合) | `try_forall_from_definition` — 内包の述語そのもの / その連言肢のひとつ / `Nat`・`Int`・`Real` 上の多項式判定 (多変数の入れ子 `forall` も剥がす)。列挙を一切行わないので `Sound` |
| `exists` の witness (無限ドメインでも) | 列挙で `true` になったということは実際の witness が存在する (§6.0 polarity) |
| `by algebra` (Int/Rat/**Real**) | 多項式正規化 + Sylvester 基準。Real は `f64_to_rat` で厳密な有理数に変換して判定 (浮動小数の丸め誤差はそのまま — `0.1 + 0.2 == 0.3` は正しく false と出る)。**証明項は witness を持つ**: 差がゼロ多項式 / 全係数非負 / 全指数偶数 / 平方の非負結合 / **Farkas 係数** (仮定を有理数倍して足す) / **等式仮定の線形結合**。kernel は掛けて足して比較するだけ |
| `by apply` / `by have` / `by assumption` (0.8.0) | modus ponens・カット規則・仮定参照。証明項は `Cert::Apply` / `Cert::Have` / `Cert::Assumption` で、kernel が補題の具体化をやり直し、前提をひとつ残らず検査する (§5.1b) |
| `by induction` (Nat/List/Tree/data) | 構造帰納法、ADT の有限構築可能性。**基底ケースは kernel が obligation を導出して検査する**が、ステップにはまだ witness 形式がない (§6.0.6) |
| `by strong_induction` / `by strong_induction <N>` (Nat, 深さ可変) | well-founded relation on ℕ。展開後に基底境界を跨ぐ未解決の `if` が残る場合は証明を失敗させる (`contains_var_conditioned_if` ガード, 2026-08 追加 — §6.6 参照) |
| `by simp` chain | 各 step が健全な書換え、対称規則 (`add_comm` 等) も AC-canonicalization で oscillation なく扱える |
| `by linarith` | `by algebra` の別名 (同じ多項式判定 + 仮定の加算結合 `hyps_sum_proves` + 多変数 Fourier-Motzkin 消去 `fm_is_unsat`)。**FM は「証明できる」方向のみ健全** — 有理数緩和が unsat なら整数/Nat 系も unsat だが、逆に有理数 SAT が整数解の存在を保証しないので反証には使わない。単変数専用の Fourier-Motzkin ソルバ (`linarithProve` builtin, Phase 5, property test 検証済) は別実装で、タクティクにはまだ接続されていない |
| 列挙集合 / 直積 / ADT membership | 完全に構造的 |
| 型クラス辞書化 | 静的に解決、実行時に明示渡し可能 |
| `by obtain` (existential elimination, 2026-08 追加) | 標準的な存在除去則。前提の discharge に失敗すればエラー、witness は評価不能なシンボルとしてのみ使える (§6.5) |

## 6.2 何が健全でないか

### 🟡 sample-based: 完全保証なし、しかし実用上多くを catch

| 機能 | 限界 | 影響 |
|---|---|---|
| 依存型 `(x : A) -> B(x)` のチェック | `from` を 5-200 個 sample してチェック | 大きい `Int` での反例を取りこぼす。**返り値の refinement については 0.9.0 から証明を試みる** (§6.0.9) |
| `forall x in Int, P(x)` の `by eval` | `[-200, 200)` のみ列挙 | 同上。**ただし `[sampled]` と記録・表示され、`--strict` で拒否される** (§6.0) |
| Refinement type のチェック | **0.9.0 から証明義務として prover + kernel に流す** — 落とせなければ sample に戻り、`[sampled]` と記録される (§6.0.9) | 落ちなかったものは名前が出る |
| 関数型 `A -> B` の member check | sample 適用で返り値を確認 | 返り値が refinement なら上と同じ経路。引数位置の refinement はまだ sample のみ |

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
| 終了性 (termination) | warning のみ。0.8.0 から評価ステップ予算と深さ上限で暴走は**エラーとして**止まる (以前はハングまたは abort — 下記) |
| メモリ安全性 | Rust が保証する範囲内 (FFI で逸脱可能) |
| 例外的でない振る舞い | ~~Int overflow は wrapping~~ → **0.8.0 で runtime error に変更** (下記)。Real は NaN/Inf あり |
| パターンマッチの網羅性 | warning のみ |
| データ競合 | `Arc<Mutex>` で sync 化されているが、deadlock 検出はない |
| FFI 経由のコード | 完全 unsafe (`SECURITY.md` 参照) |

### 修正済み: Int overflow による戦術間の矛盾

`Int` は論理の上では ℤ ですが実行時は `i64` です。0.5.0 まで算術は
wrapping していたため、次が通っていました:

```seki
theorem ov : 9223372036854775807 + 1 < 0 := by eval   -- 0.5.0: ✓ 通った
```

`by algebra` は同じ命題を ℤ の多項式として扱うので偽と判定します。
**同一命題について 2 つの信頼された戦術が矛盾する**状態でした。

0.8.0 から `+` `-` `*` `/` `mod` 単項 `-` `pow` はすべて checked 演算になり、
`i64` の範囲を出ると runtime error になります (bytecode VM 側も同じ方針に
統一 — `vmRun` は `eval` の最適化であって別の意味論ではないため)。

```
runtime error: Int overflow in `9223372036854775807 + 1`: the result leaves
the range of a 64-bit integer. seki's Int is the mathematical integers in
the logic but i64 at runtime; wrapping would make `by eval` disagree with
`by algebra`, so it is refused. Use lib/cas/bigint.seki for
arbitrary-precision arithmetic.
```

任意精度が必要なら `lib/cas/bigint.seki` を使ってください。

### 終了性の穴 — と、そこで実際に起きること

```seki
def evil := \(_ : Unit) -> evil ()    -- 無限再帰
-- 終了性 warning が出るが、定義は受理される
```

seki は停止性を **warning** にとどめます (Lean のように停止性の証明を
義務づけると、この言語が狙う書き味が失われるため)。したがって
非停止の定義が評価器に渡ることは起こりえます。

**訂正 (0.8.0)**: このページは以前「`by eval` は明示的な fuel (10000
ステップ) で abort するため、無限ループ証明が成立することは現状ない」と
書いていました。**これは誤りでした。** `COMP_FUEL = 10_000` は
「内包が定義域の要素を何個まで絞り込むか」の上限で、1 要素の評価に
どれだけかかるかについては何も言いません。実測すると:

| 形 | 0.8.0 以前の挙動 |
|---|---|
| 末尾再帰 (`\n -> loop (n+1)`) | **永久にハングする** (TCO ループは `eval` に再入しないので fuel を消費しない) |
| 非末尾再帰 (`\n -> 1 + loop (n+1)`) | **`fatal runtime error: stack overflow` でプロセスが abort** |

どちらも「偽の定理が証明される」わけではありませんが、プログラムとして
報告できるエラーですらありませんでした。

0.8.0 で 2 つの上限を入れました。どちらも**時間ではなく回数**なので、
同じプログラムはどの計算機でも同じように失敗します:

- **評価ステップ予算** (`DEFAULT_EVAL_BUDGET` = 5,000 万、
  `SEKI_EVAL_BUDGET` で変更可) — `eval` と `apply` のループの両方で消費
  するので、末尾再帰の暴走も捕まります。宣言ごとに補充されるので、
  長いファイルが長さで不利になることはありません。
- **評価の深さ上限** (`DEFAULT_EVAL_DEPTH` = 2,000、`SEKI_EVAL_DEPTH`)
  — 非末尾再帰は予算よりずっと速くネイティブスタックを食うので、
  スタックが尽きる前に止めます。

```
runtime error: evaluation budget of 50000000 steps exhausted — the
computation does not appear to terminate. ...
runtime error: evaluation nested 2000 levels deep — ...
```

`lib/` + `examples/` + `tests/seki/` 全体は 500 万ステップ・深さ 1,000 の
内側で評価されるので、いずれも実用上の余裕は十分あります。

**これは健全性の証明ではありません。** 停止性を強制していない以上、
「非停止の定義は証明に使えない」ことは*上限に依存*しています。
違いは、その依存が明示的で、再現可能で、プロセスの abort ではなく
エラーとして報告される点です。

### 基礎づけ: 無制限内包ではなく分出

seki は「集合論ベース」を名乗りますが、0.8.0 以前は公理系が
**無制限内包**でした。実測すると:

```seki
def selfmem := Set in Set          -- 0.8.0 以前: true
def R := {x in Set | x notin x}    -- 0.8.0 以前: 受理される
def paradox := R in R              -- 0.8.0 以前: スタックオーバーフローで abort
```

Russell の逆理が (偽の定理としてではなく、無限後退として) 到達可能な
状態でした。0.8.0 で ZF の**分出公理**に相当する制限を入れました:

- **`Set` は自分自身の元ではない** — `Set` は全集合のクラスであり、
  真のクラスは集合ではないので `Set in Set` は `false` です。
- **`Set` を定義域とする内包は拒否されます** — 新しい集合は*既に存在する
  集合*から切り出す以外に作れません。これが naive な内包と ZF を分ける
  制限そのもので、これにより `R` は構成できなくなります。

```
runtime error: cannot build a set by comprehension over `Set`: `Set` is the
class of all sets, not a set itself, so `{x in Set | ...}` is not a
legitimate construction ...
```

既存集合からの切り出し (`{x in {1,2,3,4} | x mod 2 == 0}`) と、
`forall A in Set, ...` のような**量化**は従来どおり動きます
(`lib/settheory/axioms.seki` の ZF 公理の記述はこの形です)。

**残る限界**: 宇宙階層はまだありません。`Set` が自分自身を含まないことと
`Set` からの内包を禁じることで既知の逆理は塞がれていますが、
「seki の集合論は ZF である」と主張できるところまでは形式化されて
いません。

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

### Pattern B (対処済み): 終了しない関数による spurious proof

```seki
def loop := \(n : Nat) -> loop (n + 1)
theorem fake : forall n in Nat, loop n == 0 := by eval
```

0.8.0 では評価ステップ予算で止まります (実測):

```
runtime error: evaluation budget of 50000000 steps exhausted — the
computation does not appear to terminate. ...
```

以前は「fuel exhausted エラーになる」と書いてありましたが、実際には
この形 (末尾再帰) は**永久にハング**していました。§6.2 の訂正を参照。

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

## 6.5 `axiom` と `exists` — 何が証明で何が宣言か

`axiom name : P` は **P を証明なしに真だと宣言するだけ** — `Decl::Axiom`の
処理は shape check のみ行い、実際に `globals.axioms[name] = Value::Bool(true)`
という真偽タグを登録する (`main.rs`)。つまり `axiom` はいかなる意味でも
「証明」ではなく、**ユーザが正しいと保証する古典的な仮定**にすぎない。

以前 (2026-08 前半) はこれが実質「宣言しただけで使い道が無い」機構だった:
`exists x, P(x)` を主張する axiom を宣言しても、そこから `P` を満たす `x`
の性質を取り出して**他の定理の証明に使う**手段が無かった (`axiom` の識別子
を式中で参照すると常に `Bool(true)` として評価されるだけで、witness を
計算に持ち込む経路が存在しなかった)。

2026-08 に `by obtain w from L [with x:=e,...] then <closer>` (§5.12) を
追加し、これを解消した。これは標準的な**存在除去則** (existential
elimination) の実装であり、以下の点で健全:

- `L` (axiom または theorem) の前提を実際に discharge できない限り
  witness を取り出せない (偽の前提から任意の結論を「証明」できる抜け道は
  無い)。
- 取り出した `w` は**計算可能な値を一切持たない** — 純粋にシンボリックな
  名前であり、`by algebra` のような自由変数をシンボリックに扱うタクティク
  でのみ使える。`by eval` で `w` を評価しようとすると unbound identifier
  エラーになる (これは意図的 — `w` に対応する実際の値を計算する手段は
  一般には存在しない、というのが `axiom` を使う理由そのものだから)。

**残る限界**: `by obtain` は「axiom として宣言された exists 命題を使う」
ことしかできない。**exists 命題を axiom によらず構成的に証明する**手段
(実数の完備性から `sup S` のような witness を導出する、Skolem 関数を
`def` レベルで計算可能にする、等) はまだ無い。したがって「中間値の定理
そのもの」(`lib/analysis/ivt.seki` の `ivt_general`) は今も証明されて
おらず、古典的な公理として認めた上で `by obtain` により**そこから先を
厳密に導出する**という形でしか使えない。これは多くの形式化ライブラリが
実数解析の基礎を扱う標準的なやり方 (完備性や選択公理などを公理として
認め、そこから演繹する) でもある。

## 6.6 production 利用に当たって

「絶対に必要な性質」は **kernel 検証済み (`Sound`) の theorem** に限定するのが
honest。以前この節にあった監査の指針は、**人間の規約から機械検査を経て、
独立した検査器による再構成に変わりました**:

```sh
seki --strict file.seki     # Sound でない theorem があればエラー終了
seki --audit  file.seki     # 各定理がどう検証されたかを一覧
seki --proof  file.seki 名  # 証明項そのものを読む
```

CI に `--strict` を入れておけば、サンプリングにも未検証のタクティクにも
依存した命題が invariant の前提に紛れ込むことはありません。

残る監査の指針 (まだ機械検査になっていないもの):

1. ~~`by eval` を使った theorem は有限ドメイン上のみに限る~~ → kernel が
   構造的に保証する (サンプリングできる文脈では動かない)
2. 依存型注釈は **ドキュメント** 扱いする — **型注釈の member check は
   まだ sample-based で、証明項の対象外** (§6.2)。これが残る最大の穴
3. `Real` 上の証明は `by algebra` では健全。ただし `f64` リテラル自体の
   丸め誤差は解消されない — 厳密性が必須なら `Rat = Int × Pos` を使う
4. FFI と `execShell` は信頼できる入力に対してのみ使う
5. `[unchecked]` の theorem は、その命題が偽だと言っているわけではない —
   「タクティクを信じるしかない」という意味。`--audit` でどのタクティクか
   分かるので、そのタクティクを信じるかは利用者の判断

## 6.7 まとめ

- **証明項と kernel** (0.8.0): タクティクは信頼されなくなった。TCB は
  約 9,000 行から約 2,600 行 (+ 基底項での評価) に縮んだ
- 全 955 定理のうち **909 (95.2%) が kernel により原始規則から再構成**された
- 残る 46 件は **名前と件数が出る**: `unchecked` 29 / `sampled` 17。
  `--audit` で一覧、`--strict` で拒否できる
- 導入時に `by algebra` の**実在する健全性バグ**を kernel が発見した (§6.0.4)
- **型注釈も証明義務になった** (0.9.0、§6.0.9) — 定理と型が同じ prover と
  同じ kernel を通るようになり、seki のすべての主張が同じ土俵に載った。
  落ちない義務は名前と内容が出る
- 基礎づけは 0.8.0 で**無制限内包から分出へ**移り、Russell の逆理が
  到達不能になった (§6.2)。非停止の定義もハング/abort ではなく
  エラーとして止まるようになった
- 次の目標は `by induction` のステップ (残り 23 件中 20 件) に witness 形式を
  与えること、および refinement 型の義務を証明器に流すこと

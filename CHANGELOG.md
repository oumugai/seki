# Changelog

このファイルは [Keep a Changelog](https://keepachangelog.com/ja/1.1.0/) フォーマットに従い、
バージョンは [Semantic Versioning](https://semver.org/spec/v2.0.0.html) に従います。

## 互換性ポリシー

seki は **pre-1.0** です。これは次を意味します:

- **マイナーバージョン (0.X.0)** で破壊的変更が起こり得ます。
- **パッチバージョン (0.X.Y)** はバグ修正のみで、ソース互換性は保たれます。
- **1.0** に到達するまでに **言語仕様書** と **健全性議論** を整備します。

---

## [Unreleased]

## [0.10.2] — 2026-09-20

追加のみ。応用例を書こうとして当たった4点の修正です。

### 区間 refinement 型が証明できるようになった

```seki
def Unit01 := {x in Real | (0.0 <= x) and (x <= 1.0)}
def halve      : Unit01 -> Unit01 := \x -> x / 2.0      -- 証明される
def complement : Unit01 -> Unit01 := \x -> 1.0 - x      -- 証明される
def escapes    : Unit01 -> Unit01 := \x -> x + 0.5      -- [sampled]
```

「この関数は単位区間を単位区間に写す」が**型として**機械検証されます。
これを塞いでいたのは次の3つでした。

- **連言の結論が扱えなかった** — `{x | a <= x and x <= b}` という
  **最も普通の refinement 型**の証明義務は連言なので、`by algebra` が
  「関係式ではない」と言って終わっていました。連言肢ごとに証明し、
  kernel が分割を自分で導出して突き合わせる `Cert::AndIntro` を追加。
- **内包をドメインに持つ束縛の述語が仮定として使われていなかった** —
  `forall x in {y in Real | 0 <= y and y <= 1}` は `0 <= x and x <= 1` を
  自由に使えるはず (集合の定義から全ての元が満たす) ですが、その制約は
  どのタクティクも読まない場所にありました。`kernel::domain_hypotheses`
  が prover と kernel の両方に供給します。
- **集合の名前が元のドメインとして認識されなかった** — `forall x in Unit01`
  が `Int` 上と報告され (綴りしか見ていなかった)、`Real` について何も
  証明できませんでした。

### 形状推論が割り算で `Int` を決め打ちしていた

```seki
def f := \a b -> if a <= b then a / b else 1.0
-- type error: if branches have different shapes: Int vs Real
```

型注釈のない引数は shape が `Unknown` ですが、`a / b` を `Int` と
決め打ちしていたため、正しく型の付く関数が**型エラー**になっていました。
両辺が `Int` と分かっているときだけ `Int`、それ以外は `Unknown` に。


## [0.10.1] — 2026-09-19

### 健全性の修正: 厳密有理数演算の桁あふれ (TCB 内)

確率推論のデモを作っている最中に発見しました。

```seki
theorem exploit : (0.1 * 0.2 * 0.3) == 1.0 := by algebra   -- 0.10.0: ✓ 通った
def actual := 0.1 * 0.2 * 0.3                              -- = 0.006
```

`--audit` は `kernel-checked from primitives` と報告していました。

原因: `Rat` の演算が `saturating_mul` を使っていました。`f64` の `0.1` は
1/10 ではなく分母 2^55 程度の有理数なので、**3 つ掛けると i128 をあふれ**、
飽和して*もっともらしい誤った値*が黙って返ります (`0.1*0.2*0.3` が
厳密有理数として `1` になる)。**多項式算術は kernel が信頼する部分**なので、
これは TCB の中の健全性バグでした。

修正: 有理数演算をすべて checked にし、あふれたら **poison 値**を返します。
poison はどの演算にも伝播し、`is_zero()` は常に false、`sign()` は常に負
(= `sign() >= 0` の検査がすべて失敗する)、`expr_to_poly` は `None` を返し、
kernel は明示的に拒否します。「あふれた数に正しい符号は無いので、
必ず負ける方を返す」という方針です。

**実用上の注意**: 率や割合は `0.1` ではなく `1.0/10.0` と書いてください。

### 仮定の逆算の改善

- 逆算した境界が f64 由来の巨大な有理数
  (`3602879701896397 / 17834254524387164`) になり、読めない上に i64 変換で
  壊れていました。**強い側に丸めた読める候補**を順に試し、検証を通った
  最初のものを出すようにしました (`p < 1/5` のような形)。
- 検証済みの提案のみを出すという方針は不変です。

### 例

- `examples/43_medical_diagnosis.seki` — ベイズ算術 (kernel 検証済み) と
  有病率推定の不確実性 (`with confidence`) を**分けて**扱うデモ。
  偶然的な確率と認識的な確率を混ぜないことを示します。
- `examples/44_business_decision.seki` — 不確実な前提からの投資判断。
  前提が 2 つなら confidence >= 13/20、弱い前提 (0.6) を 1 つ足すと
  **1/4 まで落ちる** — 掛け算 (0.405) では見えない事実。


## [0.10.0] — 2026-09-19

> 追加のみです。既存のプログラムはそのまま動きます。

### 確からしい事実からの推論

LLM が抽出した事実のように「100% 確実ではないが確率的に正しそう」な前提
から推論したい場合があります。

```seki
axiom gold_implies_discount
  : forall spend in Nat, spend >= 100 => spend / 10 >= 10
  with confidence 0.9
  from "LLM extraction 2026-09, opus-5, 200 件で precision 0.90"
```

**核心の設計判断: 確率を kernel に入れません。** 入れると `Sound` が
連続量になり、この対話で積み上げた「kernel 検証済み」の意味が失われます。
一方、確率計算が必要とする構造 — 「この結論はどの仮定に推移的に依存して
いるか」— は**証明項が既に持っています**。だから `src/confidence.rs` は
その上に載るだけで、kernel も `Cert` も `TrustLevel` も変更していません。
確信度付きの仮定はあくまで `axiom` (= `Axiomatic`) で、確信度は
**直交する第二の報告**です。

- **合成は掛け算ではなく Fréchet 下界** `max(0, Σpᵢ − (n−1))`。
  `0.9 × 0.8 = 0.72` は独立性を仮定した数字で、同じ抽出パス由来の事実は
  独立ではありません。しかもこの境界は**含意に付けた確信度に対して厳密**
  です (`P(A) ≥ p`, `P(A→B) ≥ q` ⟹ `P(B) ≥ p+q−1`) — 確からしいルールの
  連鎖は独立性を一切仮定せずに正しく合成します。
- 有理数は厳密に保持されます。`0.9` は `9/10` と読まれ、f64 の丸めが
  レポートに漏れません (`rational_from_decimal`)。
- `--audit` が confidence 行を出し、`--min-confidence R` が下限を切ります。
- `from "..."` で由来を記録。**LLM の confidence は較正された確率では
  ない**ので、数字だけでなく出所を残すことを推奨します。
- `examples/42_uncertain_facts.seki`。

### 仮定の逆算 (abduction)

証明が失敗するのはたいてい主張が誤っているからではなく**仮定が足りない**
からです。`cannot prove (100 - 200r) > 0` は正しいが役に立ちません。

```
proof error: by algebra: cannot prove (100 - (200 * r)) > 0 over Real
  it would hold given `(r < (1 / 2))` — add it as a hypothesis
  (`... => <goal>`) or tighten an existing one
```

- `src/abduce.rs` — 線形なゴールについて、それを成り立たせる変数の境界を
  求めます。パラメータが推定値のモデルでは、この「どこまでなら成り立つか」
  が証明そのものより有用なことがあります (感度解析)。
- **探索なので何も信頼されません。** 提案は「仮定として足して実際に通るか」
  を確認してから出るので、出た提案は必ず効きます。ゴールの言い換えにしか
  ならない提案は黙って捨て、線形の断片の外では何も言いません。

### 足りないものを名指しするエラーメッセージ

- `by apply` の前提が落ちないとき、**どの前提か・今スコープに何があるか・
  どう供給するか**を出します:

  ```
  by apply mono: premise `(a <= b)` is neither assumed nor provable outright
  (nothing is assumed here).
    supply it with `by have h : (a <= b) := <proof> then apply mono`,
    or add it to the theorem's hypotheses
  ```

- 補題名の綴り違いに候補を出します (`did you mean `mono`?`)。


## [0.9.0] — 2026-09-19

> 型注釈が証明義務になりました。既存のプログラムはそのまま動きます
> (落ちない義務は従来どおり標本検査に戻ります) が、`by auto` が選ぶ証明が
> 変わることがあります — 常に「より健全な方」に変わります。

### 型注釈も証明義務になった (残る最大の穴を塞いだ)

`def f : A -> {y in B | Q y}` は「**どんな引数でも**結果が `Q` を満たす」と
主張します。seki はこれを関数を定義域の標本に適用して検査しており、
`docs/spec/06-soundness.md` §6.2 が「残る最大の穴」と呼び続けていました。
証明項を入れても、定理側が 95% kernel 検証済みになる一方、型側は点検査の
ままでした。

その主張は普通の命題です:

```
def f : A -> {y in B | Q y}      ⟹      forall x in A, Q[y := f x]
```

- **`src/obligation.rs`** — 型注釈から証明義務を生成。カリー化された
  arrow 鎖を剥がし、返り値位置の refinement の述語に `f x1 x2 ...` を
  代入します。
- 生成された義務は **定理と同じ prover が探し、同じ kernel が検証**します。
  新しく信頼するものはありません。
- 落とせなければ従来どおり標本検査に戻りますが、**そう記録されます** —
  `[sampled — NOT a proof]` と表示され、`--strict` が拒否し、`--audit` が
  義務そのものを見せます。
- `examples/41_refinement_types.seki` — 帳簿の overdraft 不変条件を含む
  動く例 (証明される 4 件 / 標本のみ 2 件)。

```seki
def NonNeg := {x in Int | x >= 0}
def safeWithdraw : Nat -> Nat -> NonNeg := \bal amt ->
    if amt <= bal then bal - amt else bal     -- 証明される (場合分け + Farkas)
def unsafeWithdraw : Nat -> Nat -> NonNeg := \bal amt -> bal - amt
--                                            [sampled — NOT a proof]
```

生成されるのは refinement の部分だけです。基底ドメインへの所属と、
引数位置の refinement はまだ標本検査です。

### 健全性の修正 (kernel の穴)

- **ストリクト不等式が係数だけで通っていた** — `NonnegCoeffs` witness の
  strict 判定が「差が恒等的にゼロでない」ことしか要求しておらず、
  `forall n in Nat, n > 0` (n=0 で偽) の偽造証明項を kernel が受理して
  いました。`by algebra` はこの目標を拒否するので既存の定理に影響は
  ありませんが、**kernel はタクティクが何を出すかに関係なく正しくなければ
  なりません**。

  正しい条件は「**定数項が正**」です — 変数はすべて 0 になりうるので、
  非負係数の和が strict に正になるのは定数のおかげです。`EvenPowers` にも
  strict 版を追加し (`x² + 1 > 0` が通るようになりました)、偽造テストを
  2 件追加しました。

### `by auto` が健全な証明を優先するようになった

`try_portfolio` は最初に goal を閉じた候補を返し、安い closer が先に
並んでいるため、`by unfold f then algebra` で証明できる目標でも
`by eval` が標本検査で勝っていました。**証明を探す探索として逆**です。

`try_portfolio_sound` を追加し、各候補を certify して kernel に通し、
最初に完全に健全だったものを採用します。健全なものが無ければ従来どおり
最初に通ったものを返すので、見つかる範囲が狭まることはありません。

### `by algebra` の修正

- **仮定があると単純な witness を試していなかった** — `hyps.is_empty()` で
  分岐していたため、場合分けの「どうでもいい方の枝」
  (`amt > bal ⊢ bal >= 0`) が Farkas に回され、無関係な仮定から導けずに
  未検証になっていました。単純な witness は仮定の有無に関係なく有効です。
- 多項式化に失敗した時点で場合分けに進むようになりました (0.8.0 で入れた
  修正の続き)。


## [0.8.1] — 2026-09-19

> 破壊的変更: `{x in Set | ...}` はエラーになり、`Set in Set` は `false`
> になりました。コーパスに該当箇所はありませんが、無制限内包に依存した
> コードは動かなくなります。

### 基礎づけ — 無制限内包から分出へ

seki は「集合論ベース」を名乗りながら、公理系は**無制限内包**でした。

```seki
def selfmem := Set in Set          -- 0.8.0 以前: true
def R := {x in Set | x notin x}    -- 0.8.0 以前: 受理される
def paradox := R in R              -- 0.8.0 以前: スタックオーバーフローで abort
```

Russell の逆理が (偽の定理としてではなく無限後退として) 到達可能でした。
ZF の**分出公理**に相当する制限を入れました:

- **`Set` は自分自身の元ではない** — 全集合のクラスは真のクラスであり
  集合ではないので `Set in Set` は `false`。
- **`Set` を定義域とする内包は拒否** — 新しい集合は*既に存在する集合*から
  しか切り出せない。これが naive な内包と ZF を分ける制限そのもので、
  `R` は構成できなくなります。エラーは理由と対処を述べます。

既存集合からの切り出しと `forall A in Set, ...` のような量化は従来どおり
動きます (`lib/settheory/axioms.seki` の ZF 公理記述はこの形)。
宇宙階層はまだ無いので「seki の集合論は ZF である」とまでは言えません。

### 非停止の定義がハング/abort ではなくエラーになった

`docs/spec/06-soundness.md` は「`by eval` は明示的な fuel (10000 ステップ)
で abort する」と書いていましたが、**これは誤りでした**。`COMP_FUEL` は
「内包が定義域の要素を何個まで絞り込むか」の上限で、1 要素の評価時間に
ついては何も言いません。実測:

| 形 | 0.8.0 以前 |
|---|---|
| 末尾再帰 | **永久にハング** (TCO ループは `eval` に再入せず fuel を消費しない) |
| 非末尾再帰 | **`fatal runtime error: stack overflow` で abort** |

時間ではなく**回数**による上限を 2 つ入れました (同じプログラムはどの
計算機でも同じように失敗します):

- **評価ステップ予算** `DEFAULT_EVAL_BUDGET` = 5,000 万
  (`SEKI_EVAL_BUDGET`) — `eval` と `apply` のループ**両方**で消費するので
  末尾再帰の暴走も捕まる。宣言ごとに補充。
- **評価の深さ上限** `DEFAULT_EVAL_DEPTH` = 2,000 (`SEKI_EVAL_DEPTH`)
  — 非末尾再帰は予算よりずっと速くネイティブスタックを食うので、
  尽きる前に止める。

`lib/` + `examples/` + `tests/seki/` 全体は 500 万ステップ・深さ 1,000 の
内側で評価されるので余裕は十分あります。これは健全性の**証明ではなく**、
停止性を強制していない以上「非停止の定義は証明に使えない」ことが上限に
依存している点は変わりません。違いは、その依存が明示的で、再現可能で、
プロセスの abort ではなくエラーとして報告されることです。


## [0.8.0] — 2026-09-19

> 演繹の導入。証明が初めて**合成**できるようになりました。
> 既存のプログラムはそのまま動きます (`by algebra` は以前より多くを
> 証明するようになりましたが、少なくなってはいません)。

### 演繹 — 証明が合成できるようになった

計測から始めました。全 955 定理のうち、**既存の定理を使っていたのは
12 件 (1.3%)** でした。原因は具体的で、証明済みの事実を再利用する手段が
`by simp` (等式のみ) と `by obtain` (存在命題のみ) しかなく、
**含意と不等式 — 数学的事実の大半 — は再利用できなかった**ためです。
`lib/` は数学ライブラリではなく、955 個の独立した判定結果の集積でした。

- **`by apply L [with x := e, ...]`** — modus ponens。補題を具体化し、
  前提を落とし、結論をゴールとして読みます。束縛変数は補題の結論と
  目標を照合して推論されるので、`with` が要るのは**結論に現れない変数**
  だけです (推移律の `y` など)。与え忘れると何が決まらなかったかを
  名指しで教えます。前提は「すでに仮定にある」か「`by algebra` で落ちる」
  必要があり、飛ばして適用することはできません。

- **`by have <name> : <prop> := <proof> then <closer>`** — カット規則。
  中間の事実を現在の仮定の下で証明してから使います。入れ子の証明は
  1 タクティクで、続く `then` は外側の鎖に属します。

- **`by assumption`** — ゴールの結論がすでに仮定にあるとき閉じます。

証明の文脈 (Γ) は**ゴールそのもの**が持ちます — `h1 and h2 => C` は
2 つの仮定を持つゴールで、`by have` が鎖を伸ばし `by apply` /
`by assumption` が読みます。別の文脈オブジェクトはありません。

kernel 側は `Cert::Apply` / `Cert::Have` / `Cert::Assumption` を追加。
補題の具体化をやり直し、結論がゴールと一致するか確かめ、**前提を
ひとつ残らず検査**します。

- `examples/40_deduction.seki` — 演繹の動く例 13 件、すべて kernel 検証済み。

### 仮定付き線形算術が証明項を持つようになった

- **Farkas 証明書** — 仮定を非負の有理数倍して足し、非負の緩みを加えた
  ものが目標の差と一致する、という witness。`by algebra` は
  Fourier-Motzkin で乗数を**探し**、kernel は掛けて足すだけで**検査**します。
  以前の「係数 1 の部分集合の和」を厳密に包含し、次が新たに通ります:

  | 形 | 必要だったもの |
  |---|---|
  | `x <= 3 ⊢ 2x <= 6` | 乗数 2 |
  | `2a <= 10 ⊢ 2a <= 12` | 緩み 2 |
  | `0.05 <= r <= 0.15 ⊢ 100 - 200r > 0` | 乗数 200 + 緩み 70 |
  | 2 パラメータの区間 | 複数の乗数 |

  乗数は単項式ごとの係数比較を線形システムとして立て、有理数上の
  Gauss 消去で厳密に解きます。部分集合を小さい順に試すので、証明書は
  最小の形になります。

- **等式仮定の線形結合** (`Cert::Poly` の `EqCombination`) — 等式は
  任意の (負でもよい) 係数で足せるので Farkas とは別規則。
  `w³ - w - 2 = 0 ⊢ w³ = w + 2` のような、`by obtain` で取り出した
  witness の定義性質をゴールの形に並べ替える経路です。

- `by algebra` が**多項式化に失敗した時点で場合分けに進む**ようになり、
  `(if x >= y then x else y) >= y` のような直接 `if` を含むゴールが
  kernel 検証済みで通るようになりました。差がゼロの非strict不等式
  (`y >= y`) も `Zero` witness で閉じます。

- `by obtain` が `then` チェーンの途中でも証明項を落とさなくなりました。
  `tests/seki/test_analysis_ivt.seki` の IVT 由来の 3 定理が
  `[unchecked]` から `[axiomatic]` になった — つまり
  **「検証していない」から「IVT 公理から厳密に導出済み」に変わりました**。

### 測定

全 968 定理のうち **925 (95.6%) が kernel 検証済み**
(`axiomatic` 3 / `unchecked` 23 / `sampled` 17)。
残る `unchecked` は `by induction` のステップ 20 件が大半です。


## [0.7.0] — 2026-09-19

> 破壊的変更を含みます。`by algebra` が不透明部分式を無条件に非負と仮定
> しなくなったため、**その仮定に依存していた証明は通らなくなります**
> (コーパスでは 2 件。どちらも実際に偽を証明できる経路でした)。
> `theorem` の出力に kernel の判定が印として付きます。

### 証明項 (proof term) と kernel

- **`src/kernel.rs`** — 証明項 (`Cert`) と、タクティクを一切呼ばない
  独立した検査器を追加。タクティクは `Prover::certify` で証明項を
  **生成**し、`kernel::check` がそれを原始推論規則から再構成する。
  **タクティクはもはや信頼されていない** — 探索してよいが、出したものは
  検査を通らなければならない (LCF 分割)。

  原始規則: `Refl` / `SyntacticRefl` / `Ground` / `ForallFinite` /
  `ExistsWitness` / `ForallFromComprehension` / `Generalize` /
  `CaseSplit` / `Poly` (5 種の witness) / `Induction` / `Rewrite` /
  `Unfold` / `Cite` / `Obtain`、および明示的な逃げ道 `Trusted`。

- **kernel はサンプリングできる文脈では動かない** — `EvalCtx::finite_only`
  を通して評価するため、無限集合を列挙しようとするとエラーになる。
  `docs/spec/06-soundness.md` §6.2 のサンプリングの穴が**構造的に**
  塞がれた。タクティクが 200 点の検査を差し出しても受理されない。

- **TCB が約 9,000 行から約 2,600 行に縮んだ** — `kernel.rs` (1,294) +
  `unfold.rs` (286) + `rewrite.rs` (722) + 多項式算術 (約 200) + 基底項での
  評価。`prover.rs` 全体 (4,134 行) と `algebra.rs` の決定手続きは TCB の外。

- **`seki --audit FILE`** — 各定理がどう検証されたかの一覧。
  **`seki --proof FILE NAME`** — 証明項そのものを読める形で表示。

- **信頼水準は kernel の判定から導出されるようになった** — 独立した第 2 の
  解析ではなくなったので、両者が食い違うことがない。新しい水準
  `Unchecked` (witness を出さないタクティクを通った) を追加。
  定理を引用するとその判定を引き継ぐ。

- 全 955 定理のうち **909 (95.2%) が kernel 検証済み**。残る 46 件は
  `--audit` で名前と理由が出る (`unchecked` 29 / `sampled` 17)。

- `src/kernel.rs` の `forgery_tests` — 手で組み立てた 16 種類の**偽造された
  証明項**をすべて拒否することを固定。

### 健全性の修正 (kernel が発見)

- **`by algebra` が不透明部分式を非負と仮定していた** — `expr_to_poly` は
  多項式に変換できない部分式を不透明原子という*変数*に写す。
  `polynomial_nonneg` は `Nat` 上で「全係数が非負なら非負」と判定するが、
  これは変数が非負であることに依存する。`forall n in Nat` で束縛された
  `n` には成り立つが、任意の式を表す不透明原子には成り立たない。結果:

  ```seki
  def neg : Nat -> Int := \(n : Nat) -> 0 - 5
  theorem bad : forall n in Nat, neg n >= 0 := by algebra   -- 0.6.0: ✓ 通った
  def actual := neg 3                                        -- = -5
  ```

  `algebra::is_opaque_atom` で区別するよう修正。帰納法のステップでは
  不透明原子は「より小さい引数での命題」= 帰納法の仮定なので非負と
  仮定してよく、その用途だけを `polynomial_nonneg_under_ih` に分離した。
  この残る仮定が、帰納法のステップが kernel 検証済みにならない理由。

  影響を受けた定理 2 件 (`tests/seki/test_ui_app.seki` の `dec_nn` と
  `examples/38_ui_counter.seki` の `dec_keeps_nn`) を `by eval` に変更し、
  経緯をソース中にコメントした。

- **`canonicalize` の定数畳み込みが `saturating_add` だった** — i64 の境界で
  黙ってクランプし、偽の等式が正規化で真になりうる。`checked_add` にした。

### 健全に判定できる範囲の拡大

- **有界な内包が有限として認識されるようになった** — `Zn 12 = {x in Nat | x < 12}`
  は明らかに有限だが、`is_definitely_finite` は基底ドメインしか見ずに
  無限と判定していた。述語の連言肢が変数を整数リテラル (または内包の
  クロージャが束縛する整数) で上から抑えていて、その値が `SAMPLE_BOUND` の
  内側なら、列挙は網羅的である。この 1 点でコーパスの `sampled` が
  75 件から 17 件に減った。
- **2 変数二次形式の平方完成** — `a² + b² >= 2ab` のような PSD 判定に、
  `p = (1/4c₁)(2c₁a + c₃b)² + ((4c₁c₂ - c₃²)/4c₁)b²` という witness を出す
  ようになった。kernel は展開して比較するだけでよい。

### 構造

- **`src/unfold.rs` / `src/rewrite.rs`** — 定義の展開と等式書換えを
  `prover.rs` から切り出した。どちらも原始推論規則 (定義による置換と
  Leibniz 則) であり、「どの等式を試すか」を決めるタクティクとは層が違う。
  kernel が証明項を検証するのに再実行する必要もある。
  `by simp` が closer と transformer で持っていた不動点ループの重複も
  これに伴い解消。
- `EvalCtx::finite_only` — サンプリングを拒否する評価文脈。


## [0.6.0] — 2026-09-19

> 破壊的変更を含むため、互換性ポリシー通りマイナーバージョンを上げています。
> `Int` の算術が overflow で wrapping せずエラーになる点と、`theorem` の
> 出力に信頼水準の印が付く点が既存のプログラム/スクリプトに影響します。

### 健全性 (breaking な意味論変更を含む)

- **信頼水準 (`TrustLevel`) の導入** — `Prover::verify` がゴールを閉じたことと
  命題が真であることは別だという区別を、人間の監査指針
  (`docs/spec/06-soundness.md` §6.6) から**機械検査**に変えた。
  各 theorem は証明の最も弱い材料の水準を `globals.theorem_trust` に記録し、
  それを引用した定理に伝播させる:

  | 水準 | 意味 | 表示 |
  |---|---|---|
  | `Sound` | サンプリングにも未証明の仮定にも依存しない | (印なし) |
  | `Axiomatic` | `axiom` に依存する | `[axiomatic]` |
  | `Sampled` | 無限ドメインの有限標本のみ — **証明ではない** | `[sampled — NOT a proof]` |

  判定は精密で、保守側にしか倒れない: 実際に発火した `by simp` の規則だけを
  数え、`then` チェーンでは**実際に閉じたステップ**を見る (`by unfold` /
  `by intros` / `by obtain` は評価しないので `by unfold absR then algebra` は
  Real 上でも `Sound`)、`by simp` が書換えだけで閉じたのか評価で閉じたのかを
  区別する、量化子の polarity を追う (正の `exists` は witness を実際に
  見つけているので `Sound`、負の `forall` も同様)。判断できない位置は
  必ず `Sampled` とする。`docs/spec/06-soundness.md` §6.0 を参照。

- **`--strict` / `SEKI_STRICT=1`** — `Sound` でない theorem を拒否する。
  CI に入れておけば、サンプリングに頼った命題が invariant の前提に
  紛れ込むことはない。

- **Int overflow が runtime error に** (意味論変更)。`Int` は論理上は ℤ だが
  実行時は `i64` で、算術が wrapping していたため
  `theorem ov : 9223372036854775807 + 1 < 0 := by eval` が通っていた
  (`by algebra` は同じ命題を偽と判定する — **同一命題について 2 つの信頼された
  戦術が矛盾していた**)。`+` `-` `*` `/` `mod` 単項 `-` `pow` をすべて checked
  演算にし、範囲を出たらエラーにした。bytecode VM (`vmRun`) も同じ方針に統一
  (明示的に `wrapping_*` を使っていた)。任意精度が必要なら
  `lib/cas/bigint.seki`。

- **無限ドメイン上でも健全に判定できる範囲を拡大** (`try_forall_from_definition`):
  - `Real` を多項式判定の対象に追加 — `forall x in Real, x * x >= 0.0` が
    列挙ではなく `by algebra` と同じ判定で決まるようになった。
  - 内包の述語の**連言肢ひとつ**でも可 — `{x in Int | -3 <= x and x <= 3}` の
    元が `x <= 3` を満たすことが定義から従うようになった。
  - **同じドメインの入れ子 `forall` を剥がす** — `forall a in Int, forall b in
    Int, forall c in Int, a * (b + c) == a * b + a * c` が
    200×400×400 の総当たりではなく記号的に決まる。

  この 3 つで、コーパス中の `Sampled` が 23 件から 7 件に減った。

### 修正

- **`lib/probability/{continuous,montecarlo}.seki` が壊れていた** — Σ 型の
  導入で `sigma` がキーワードになったとき、これらが `sigma` をラムダの
  仮引数名に使っていたためパースできなくなっていた。対応する
  `tests/seki/test_probability.seki` が `cargo test` に**配線されていなかった**
  ため気づかれていなかった。仮引数を `sd` に改名。
- 未配線だった 4 つの `.seki` テストファイル
  (`test_analysis_advanced` / `test_numeric_linalg` / `test_numeric_matrix_eq` /
  `test_probability`) を `tests/integration.rs` に配線。さらに
  `every_seki_test_file_is_wired_into_cargo_test` を追加し、配線忘れが
  次の `cargo test` で落ちるようにした。
- キーワードを仮引数位置に書いたときのエラーが
  `expected Arrow but got LParen` という無関係なものだったのを、
  ``` `sigma` is a keyword and cannot be used as a lambda parameter name ```
  に変更。
- `docs/spec/01-lexical.md` のキーワード一覧が `src/lexer.rs` と
  ずれていた (`sigma`/`where`/`fn`/`for`/`do`/`diff` などが欠落) のを修正し、
  両者の一致を `the_documented_keyword_list_matches_the_lexer` で固定した。

### 構造

- **`Session` をライブラリへ** (`src/session.rs`) — 宣言駆動ループ・import
  ローダ・エラー注釈が `src/main.rs` の中にあったため、バイナリを起動する
  以外に到達手段が無かった。結果として `tests/integration.rs` は
  `run_decl_inner` を**再実装したコピー**を検証しており (そのコピーは
  `import` を `panic!` していた)、`src/lsp_main.rs` はパースだけの診断に
  留まり、`src/lib.rs` が謳っていた `run` API は存在しなかった。
  - `tests/integration.rs` の 84 箇所が本物のドライバを通るようになった。
  - LSP が**静的 shape 検査**の診断を出すようになった (宣言ごとに継続するので
    複数のエラーを同時に報告)。評価を伴う検証は LSP では行わない — キー入力
    ごとに書きかけのバッファを評価すると `execShell` が実際に走るため。
  - `main.rs` 1468 行 → 881 行。
- **`by auto` と REPL の再検査が信頼水準を記録するようになった** —
  この 2 経路は `Session` を通らずに theorem を登録していたため、
  記録漏れが `Sound` として読まれてしまう穴があった。`verify_and_register`
  に統一。
- **構造的エンコーディングの簡約を表駆動に** — `simplify_list_ops` と
  `simplify_tree_ops` というほぼ同一の 80 行の走査が 2 つあり、それぞれ
  専用の shape 認識器を伴っていた (3 つめのエンコーディングには 3 つめの
  コピーが必要という形)。走査を 1 回だけ書き、`Encoding` 表 (構成子・射影・
  判別子・再帰測度) で駆動するようにした。副産物として、構成子の単射性・
  排他性による等式分解が list 専用だったのが tree にも効くようになった
  (`node leaf 5 leaf == node leaf (2 + 3) leaf` が `by algebra` で通る)。
  詳細は `docs/spec/08-rust-seki-split.md` §8.1.1。
- `ast::children` — Expr の直下の部分式を列挙する汎用ヘルパ。variant を
  足したときに走査側が静かに取りこぼさないようにするため。
- `by simp` の 2 つの実装 (closer としての `verify_simp` と `then` チェーンの
  transformer としての `run_step`) が持っていた不動点ループの重複を
  `simp_fixpoint` に統合。両者の唯一の実質的な違い (closer は AC 正規化する、
  transformer はしない) は `SimpMode` として明示した。

### リポジトリ

- **`target/` を git の管理下から外した** — ビルド生成物 1021 ファイルが
  追跡されており (追跡ファイル全 1295 個中)、`.git` が 354 MB になっていた。
  `.gitignore` に `/target` を追加。ファイル自体はディスク上に残る。


### Added

- `by obtain w from L [with x := e, ...] then <closer>` — 存在除去則
  (existential elimination) タクティクを追加。`axiom`/`theorem` の
  `exists x, P(x)` を具体化し、witness の性質を後続タクティクの仮定として
  使えるようにする。`axiom` が計算内容を一切持たない (真偽タグに退化する)
  ため、宣言しただけで使い道が無かった問題への対処 (`docs/spec/06-soundness.md`
  §6.5)。
- `lib/analysis/ivt.seki`: 中間値の定理を `axiom ivt_general` として宣言し、
  `by obtain` で具体的な関数・区間に特殊化して使う例を追加。二分法
  (`bisect`) と、1ステップで区間幅が厳密に半分になるという一般定理
  (`bisect_width_halves`、∀a,b∈Real で健全) も追加。
- `lib/analysis/elementary.seki`: sin/cos/exp/ln の代数的性質 (ピタゴラスの
  恒等式・奇関数性/偶関数性・指数法則・対数の逆関数性) を axiom として追加。
  `by algebra` はこれらの関数呼び出しを常に不透明アトム扱いするため、
  `by simp` で使える形での提供。
- `lib/analysis/limit.seki`: `isContinuousAt`/`isLimit` の教科書通りの
  ε-δ 定義を追加。線形関数の連続性は `by algebra` で完全に健全に証明。
- `lib/cas/poly.seki`: `polyIntegrate` (不定積分) を追加し、微積分学の
  基本定理を次数非依存の一般形で証明 (`ftc_poly_general`、`by induction`
  の汎化サポートが必要だった)。
- `lib/algebra/structures.seki`: `isNormalSubgroupOf`・`groupOrderOf`・
  `cosetOf`/`quotientGroup`・`unitsOf`・`charOf` を追加。Lagrangeの定理・
  商群構成・単元群・体の標数を具体的な有限インスタンスで証明。
- `lib/cas/multipoly.seki`: `def buchberger` を実装 (これまではヘッダに
  記載だけあり未定義だった)。生成元の全ペアの S-多項式を計算し、既存生成元で
  簡約した非ゼロ剰余を新規生成元として追加する不動点反復。
  `tests/seki/test_cas_multipoly.seki` に `<x²+y²-1, x-y>` (Cox-Little-O'Shea
  の定番例) の Gröbner 基底を計算し、ideal 保存・非自明性・Buchberger 判定条件
  (全ペアの S-多項式が 0 に簡約されること) を `by eval` で検証するテストを追加。
- `lib/cas/poly.seki`: `def factorFull` — Kronecker 補間法による 2 次因子探索を
  `factor` (有理根定理のみ) に追加。3 点 (0,1,2) での値の約数の組み合わせから
  2 次補間多項式を構成し、実際に整除するか確認する。`x⁴+3x²+2 = (x²+1)(x²+2)`
  (有理根なし・2 次因子に分解できる) と `x⁴+1` (Q 上既約、円分多項式) を
  `tests/seki/test_cas_poly.seki` で検証。既存の `factor`/`factorRec` は不変。
- `lib/cas/calc.seki`: `integ` に**部分分数分解**によるケースを追加。分母が
  異なる整数根を持つ 1 次式の積に完全分解でき、かつ部分分数の係数
  (`A_i = N(rᵢ)/D'(rᵢ)`) が整数になる有理関数を `Σ Aᵢ·ln(x-rᵢ)` として積分する
  (`tryPartialFractionInteg`)。`1/((x-1)(x-2))` の積分を追加し、
  `cas/rational.seki` の `RatFn` 演算による独立検証 (再構成した部分分数が
  元の有理関数と等しいこと) も併記。適用できない場合 (仮分数・重根・既約2次分母
  など) は既存のフォールバック (`SMul other (SVar v)`、不正確) を維持。
- `by algebra` (および別名 `by linarith`) が仮定の**加算結合**を扱えるようになった:
  `x > 0 and y > 0 => x + y > 0` のように、連言の前提を複数の仮定へ分解した上で
  正の重み 1 での和がゴールと一致すれば閉じる (`hyps_sum_proves`)。
- `tests/seki/test_ui_{dom,app,models}.seki` を `cargo test` に接続
  (`lib/ui/` — サーバ駆動 UI ライブラリの自動テスト)。
- `by strong_induction <N>`: 深さ可変の強帰納法 (`N` 省略時は 2、後方互換)。
  Fibonacci (`N=2`) 以外の多段階漸化式 (tribonacci 型は `N=3`) にも対応。
- `by algebra`/`by linarith` が可変除数の **mod 単項キャンセル**に対応:
  `<expr> mod v == 0` (`v` は変数) を、`v` が分子の全項の factor であれば
  健全に証明する (`Polynomial::exact_div_by_var`)。符号に関係なく成立。
- `--strict-match` CLI フラグ / `SEKI_STRICT_MATCH` 環境変数: パターンマッチ
  網羅性チェックを警告からコンパイル時エラーへオプトインで昇格。既存の
  `lib/`/`examples/`/`tests/`/`sample/` は非網羅 match が0件なため
  デフォルト動作は変更なし。
- `seki-lsp` に `textDocument/hover` / `textDocument/definition` を追加:
  カーソル位置の識別子をテキストベースで抜き出し、組込関数カタログか
  ドキュメントのトップレベル `def`/`theorem`/`axiom` 名と照合して表示/ジャンプ
  する (非スコープ対応の最小実装)。`tests/lsp.rs` に実プロセスを JSON-RPC で
  駆動する統合テストを8件追加。
- 依存ペア型 (Σ) `sigma (x : A), B(x)`: `DepArrow` (Π) と対をなす新しい
  `Expr::DepPair` / `SetVal::DepPair`。`(a, b)` のメンバーシップ判定は
  `a in A and b in B[x:=a]` で、`DepArrow` と異なりサンプリング不要 (候補の
  pair を直接持っている) — 完全に健全。`B` が `x` を参照しなければ
  `A times B` と同義。
- `by algebra`/`by linarith` に**多変数 Fourier-Motzkin 消去**を追加
  (`algebra::fm_is_unsat` / `LinConstraint` / `relation_to_constraints`、
  `prover::try_fm_prove`)。仮定+否定ゴールを線形制約に変換し変数を1つずつ
  消去。既存の `hyps_sum_proves` (等重み1の和のみ) では届かない、
  ヒポthesis のスケーリングが必要なケース (`x <= 3 ⊢ 2x <= 6`) やゴールに
  現れない変数の消去 (`x <= y and y <= 10 ⊢ x <= 10`) に対応。健全性は
  「証明できる」方向のみ (有理数緩和が unsat なら整数系も unsat だが、
  逆は成り立たないので反証には使わない)。

### Changed

- `closure_is_recursive` を直接自己参照のみのチェックから、呼び出しグラフを
  辿る**推移的**なサイクル検出に変更。相互再帰の組 (`isEven`/`isOdd` 等) が
  「非再帰」と誤判定され `by unfold f then ...` の推移展開で32回の反復上限
  まで交互に展開し続けていた問題を修正 (不健全ではなかったが、無駄に深く
  展開されて `by unfold` の「1段展開して先はオペーク項」という意図した
  挙動から外れていた)。

- `docs/internals.md` / `docs/proofs.md` / `docs/spec/05-tactics.md` / `README.md`
  の「未対応」リストを実装状況に合わせて更新
  (`forall (x y) in S` 糖衣・match 網羅性警告・`by simp` の対称規則 oscillation
  解消・`by decide` は既に実装済みだった一方、`by linarith` タクティクが実際には
  `by algebra` の別名にすぎず専用ソルバ `linarith.rs` に未接続だった点を明記、
  `by strong_induction` の深さ可変化・相互再帰 unfold 境界検出を追記)。
  `docs/spec/05-tactics.md` §5.3 (`by algebra`) にも同じ「Real は扱わない」
  という古い記述が残っていたのを発見・修正 (他の箇所は既に修正済みだった)。
- `by auto` (ポートフォリオ探索タクティク) と `lib/ui/` を仕様書に追記。

### Deprecated

### Removed

### Fixed

- **健全性バグ修正**: `by algebra` の仮定リストが、単一の仮定が定数として
  自己矛盾する場合 (例: `unfold` で `if n==0` を具体化した結果生じる
  `1==0`) を検出できず、到達不能な `if` 分岐を無駄に証明しようとして
  失敗していた。`hyps_contradict` に定数多項式の符号チェックを追加。
- **健全性バグ修正**: 整数の離散性 (`n > 0 (Nat) ⊢ n >= 1`) が実装されて
  おらず、既存テスト `dec_nn` が実は `let`/タプルの不透明アトム化バグに
  隠れてどの仮定にも基づかず「証明」されていたことが発覚。`expr_to_poly`
  に非再帰 `let`・リテラルタプルの `fst`/`snd`・`intToReal` の透過処理を
  追加したところ真の (未証明の) ゴールが露出したため、`integer_strengthen`
  (`poly>0 (Nat/Int) ⊢ poly>=1`) を追加して正しい根拠で証明が通るようにした。
- **健全性バグ修正**: `by algebra` の `if` 場合分けがゴール側にしか適用
  されず、仮定側に埋め込まれた `if` (`absR` 等を unfold した結果生じる)
  は場合分けされずに実質使い物にならなかった。ε-δ論法や絶対値を含む
  不等式の証明に広く影響する基礎的な穴だった。
- `by algebra` にリストの構造的等価性分解 (`cons h1 t1 == cons h2 t2` ⟺
  `h1==h2 and t1==t2`) を追加。
- **クラッシュ修正**: 非末尾再帰なユーザ定義関数を深く評価すると (例:
  `forall n in Nat` のサンプル検査が `SAMPLE_BOUND` = 200 まで再帰する場合)
  デフォルトのメインスレッドスタック (Linux で通常 8 MiB) を溢れて
  `seki` バイナリごと SIGABRT で落ちていた。`main()` の実処理を
  256 MiB スタックの専用スレッドで実行するよう変更 (`src/main.rs`)。
  テスト実行時の同種のクラッシュも `.cargo/config.toml` の
  `RUST_MIN_STACK` で解消。
- **健全性バグ修正**: `by strong_induction` に depth パラメータを追加する
  過程で、指定した depth が実際の再帰参照深さより小さいと**偽の命題を
  証明できてしまう**バグを発見。基底境界を跨ぐ場合分けが未解決の `if` の
  まま「非負と仮定した不透明項」に丸め込まれていたことが原因
  (`docs/spec/06-soundness.md` Pattern D 参照)。展開後に `k` に依存する
  未解決の `if` が残っていないかを検査するガード (`contains_var_conditioned_if`)
  を追加し、該当する場合は証明を失敗させるよう修正。回帰テスト
  `strong_induction_rejects_insufficient_depth_instead_of_a_false_proof` を追加。

### Security

---

## [0.5.0] — 2026-05-12 — "Phase 5: 性能 + 健全性の第一歩"

### Added

- **Bytecode VM** (`src/bytecode.rs`)
  新規 410 行の stack-based VM。算術 / 制御フロー / `let` / 短絡 and/or を
  コンパイルして実行。`vmEval` / `vmTime` / `vmCompiles` 経由でアクセス可能。
  100 万回 arithmetic eval を ~150ms (≒6.5M ops/sec)。
- **parMap** thread pool — `parMap : (A → B) → List A → List B`。
  リスト要素ごとに OS thread を spawn、結果順序を保持。I/O bound タスクで
  実用的な並列性。
- **IO モナド強制** — 型注釈 `A → IO B` が付いた関数は、サンプル検査時に
  呼び出されなくなった (副作用が型検査で走る問題を解消)。
- **SMT-lite** (`src/linarith.rs`、新規 261 行) — 一変数線形整数算術の
  健全な決定手続き。`linarithProve` / `linarithCounter` builtin。
  Refinement 型 `{x in Int | 線形式}` の健全な判定基盤を提供。
- **LSP サーバ** (`seki-lsp` バイナリ、新規 395 行) — JSON-RPC over stdio。
  `initialize` / `didOpen` / `didChange` / `didSave` / `didClose` /
  `publishDiagnostics` をサポート。Parse error をエディタに送る。
  外部 Rust クレートゼロ維持。
- 例題 `examples/34_phase5.seki` (26 定理)。

### Changed

- `Value` 型周辺の `Arc` / `Mutex` 化を完全化。
- builtin 総数: 114 → **120**。
- 例題定理数: 403 → **429**。

## [0.4.0] — 2026-05-12 — "Phase 4: クロージャ並行性 + FFI"

### Added

- **Rc → Arc + RefCell → Mutex 全面移行** — `Value: Send + Sync` を保証。
  クロージャがスレッド境界を越えられるように。
- **クロージャベース `spawn` / `join`** — 任意のクロージャを OS thread で実行。
  キャプチャした共有状態 (Atomic / Channel / Dict) はスレッド間で透過的に共有。
- **mpsc Channel** — `chanNew` / `chanSend` / `chanRecv` / `chanClose`。
  multi-producer / single-consumer モデル。
- **FFI via libc dlopen** — `ffiLoad` / `ffiCallIntInt` / `ffiCallStrInt` /
  `ffiClose`。Linux/macOS の `.so` を直接呼べる。libloading クレート不使用
  (`extern "C" { fn dlopen(...) }` を直接宣言)。

### Changed

- builtin 総数: 104 → 114。
- 例題定理数: 393 → 403。

## [0.3.0] — 2026-05-12 — "Phase 3: Web 層 + 真の並行性"

### Added

- **URL parser** — `urlParse : String → Result (String × Int × String) String`。
- **HTTP codec** — `httpParseRequest` / `httpFormatResponse`。
- **HTTP client** — `httpGet`、blocking。
- stdlib に `HttpRequest` / `HttpResponse` ADT、`httpServe`、便利レスポンス。
- **AtomicI64** + **`spawnAtomicAdd`** — 真の並列原子加算 (OS thread)。
- **IO 型マーカ** — `IO : Set → Set` を恒等関数として登録 (Phase 5 で
  サンプル検査スキップに利用される)。

## [0.2.0] — 2026-05-12 — "Phase 2: システム開発"

### Added

- **時刻 / Sleep** — `nowSecs` / `nowMillis` / `monotonicMillis` / `sleep`。
- **プロセス実行** — `execShell` / `runCommand`。
- **PRNG** (xorshift64*) — `randomSeed` / `randomInt` / `randomRange` /
  `randomFloat`。外部クレートなし。
- **ビット演算** — `bitAnd` / `bitOr` / `bitXor` / `bitShl` / `bitShr` /
  `bitNot` / `popcount`。
- **JSON** — `Json` ADT + `jsonParse` + `jsonEncode`。完全 hand-rolled
  パーサ、外部依存なし。
- **TCP ネットワーキング** — `tcpListen` / `tcpAccept` / `tcpConnect` /
  `tcpRead` / `tcpWrite` / `tcpClose`。`Value::Handle` バリアントで socket
  を opaque token として exposing。

## [0.1.0] — 2026-05-12 — "Phase 1: 汎用言語層の基盤"

### Added

- **文字列演算** — `strLen` / `strConcat` / `strContains` / `strStartsWith` /
  `strEndsWith` / `strIndexOf` / `strReplace` / `strSplit` / `strJoin` /
  `substring` / `strToUpper` / `strToLower` / `strTrim` / `strChars` /
  `intToStr` / `realToStr` / `strToInt` / `strToReal` / `toStr`。
- **ファイル I/O** — `readFile` / `writeFile` / `appendFile` / `fileExists` /
  `removeFile`。すべて `Result E A` を返して失敗を型に表現。
- **I/O ストリーム** — `println` / `eprint` / `eprintln` / `readLine`。
- **OS / プロセス** — `args : List String` / `getEnv` / `exit`。
- **可変参照** — `mkRef` / `readRef` / `writeRef`。`Value::Ref` バリアント。
- **辞書** — `Dict K V` (`Value::Dict`)、`dictInsert` / `dictGet` /
  `dictMember` / `dictRemove` / `dictSize` / `dictKeys` / `dictValues` /
  `emptyDict`。O(1) 操作、関数的更新。
- stdlib helpers: `when` / `unless` / `forEach` / `readLines` / `writeLines` /
  `newCounter` / `incr` / `decr` / `modifyRef` / `dictFromList` /
  `dictMap` / `unwrapOrExit` / `iterRange`。
- 例題 `examples/30_system.seki`。

## [0.0.x] — 2025〜2026 初期 — "プロトタイプ期"

集合論ベースの定理証明系 + プログラミング言語のコア:

- 集合論的セマンティクス (列挙集合・内包集合・union/intersect/subset/in)。
- ラムダ計算 + カリー化 + 再帰 + 型注釈。
- タプル / List / Tree (タグ付きペア符号化)。
- `data` 宣言 + `match` 式 (代数的データ型)。
- エラーハンドリング (`Option` / `Result` / `?` 演算子)。
- モジュール (`import`)、ライブラリパス自動探索。
- 9 種類の証明戦術 (`eval` / `refl` / `algebra` / `induction` /
  `strong_induction` / `simp` / `unfold` / `intros` / `decide` / `linarith`)。
- 型クラス (`class` / `instance`、自動辞書解決)。
- 依存型 (サンプル検査ベース)。
- 終了性検査 (warning)。
- AC-canonicalization for `by simp`。
- CAS (記号微分 / 積分 / 多項式 GCD / 因数分解 / 線形・2 次方程式求解 /
  BigInt / `parseSym` で数式直書き)。
- 解析学 (数値微分・積分・Taylor 級数・固定点反復)。
- 線形代数 (n×n 行列式 / 固有値 / Gauss 消去 / Newton 法 / ODE)。
- 群論・環論 (汎用述語 + 任意の Z/nZ)。
- ベクトル空間 (任意次元)。

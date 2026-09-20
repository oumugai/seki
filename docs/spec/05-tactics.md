# 5. 証明戦術

seki は **15 種類のタクティク + コンビネータ** を持ちます。それぞれの
意味論と健全性条件をまとめます。

タクティクは `theorem` の `:=` の後に `by <tactic>` 形式で書きます。
複数を `then` で合成できます。

```
theorem t : P := by tac1 then tac2 then tac3
```

> **証明項**: タクティクは証明項 (`crate::kernel::Cert`) を生成し、
> タクティクを一切呼ばない kernel がそれを原始推論規則から再構成します。
> **タクティクは信頼されていません** — 探索してよいが、出したものは検査を
> 通らなければなりません。各定理には kernel の判定から導かれた水準
> (`Sound` / `Axiomatic` / `Unchecked` / `Sampled`) が付き、引用先に
> 伝播します。`seki --proof FILE NAME` で証明項そのものを読めます。
> 詳細は `docs/spec/06-soundness.md` §6.0。以下の各節の「健全性」は
> この水準のことです。

## 5.1 `by eval`

**意味**: 命題を完全簡約して `Bool::true` になるか確認する。

**健全性**: 列挙集合 / 内包の有限ドメインに対して健全 (`Sound`)。
無限ドメイン上の正の位置の `forall` は `SAMPLE_BOUND` (200) でのサンプル
検査になり **健全ではない** (`Sampled`)。

ただし次の 2 つは無限ドメインでも `Sound` です:

- **定義から決まる場合** — 内包の述語そのもの (またはその連言肢)、および
  `Nat` / `Int` / `Real` 上の多項式関係は `try_forall_from_definition` が
  列挙せずに判定します。多変数の入れ子 `forall` も剥がして判定します。
- **`exists` の witness** — 列挙で `true` になったということは実際に
  witness を見つけたということなので、ドメインの残りを見ていなくても証明です。

```seki
theorem t1 : 1 + 1 == 2 := by eval                    -- ✅ Sound
theorem t2 : forall x in {1,2,3}, x > 0 := by eval     -- ✅ Sound (有限)
theorem t3 : forall n in Nat, n + 1 > 0 := by eval     -- ✅ Sound (多項式判定)
theorem t4 : exists n in Nat, n > 100 := by eval       -- ✅ Sound (witness)

def f := \n -> if n < 300 then 0 else 1
theorem t5 : forall n in Nat, f n == 0 := by eval      -- 🔴 Sampled (実際に偽)
```

## 5.1b 演繹 — `by apply` / `by have` / `by assumption`

0.8.0 まで、証明された事実を再利用する手段は `by simp` (等式のみ) と
`by obtain` (存在命題のみ) しかありませんでした。含意や不等式 —
数学的事実の大半 — は再利用できず、全 955 定理のうち他の定理を使って
いたのは **12 件**だけで、残りはすべて決定手続きでゼロから証明されて
いました。`lib/` は数学ライブラリではなく、独立した判定結果の集積でした。

この 3 つがその穴を埋めます。

### 証明の文脈 (Γ)

seki は証明の文脈を **ゴールそのものの中**に持ちます。`h1 and h2 => C`
は「2 つの仮定を持つゴール」です。`by have` がその鎖を伸ばし、
`by apply` と `by assumption` がそれを読みます。別の文脈オブジェクトは
ありません。

### `by apply L [with x := e, ...]` — modus ponens

`L` (定理または公理) を具体化し、その前提を落とし、結論をゴールとして
読み取ります。

```seki
theorem double_mono
  : forall x in Real, forall y in Real, x <= y => (2.0*x) <= (2.0*y)
  := by algebra

-- 束縛変数は結論と目標の照合で推論されるので `with` は要らない
theorem concrete : (2.0 * 1.0) <= (2.0 * 3.0) := by apply double_mono
```

前提は **仮定にあればそれで、無ければ `by algebra` で**落とします。
落とせなければエラーです — 前提を飛ばして適用することはできません。

`with` が要るのは**結論に現れない変数**だけです。推移律がその例で、
`y` は結論 `x <= z` のどこにも出てきません:

```seki
theorem le_trans : forall x in Real, forall y in Real, forall z in Real,
    (x <= y) and (y <= z) => x <= z := by algebra

theorem chained : forall a in Real, forall c in Real,
    (a <= 5.0) and (5.0 <= c) => a <= c
  := by apply le_trans with y := 5.0
```

与え忘れると、何が決まらなかったかを名指しで教えます。

**健全性**: ✅ 証明項は `Cert::Apply` で、kernel が補題の文から具体化を
やり直し、結論がゴールと一致するか確かめ、**前提をひとつ残らず検査**します。
公理に依存していればそれも引き継ぎます。

### `by have <name> : <prop> := <proof> then <closer>` — カット規則

中間の事実を立ててから使います。`prop` は**現在の仮定の下で**証明されます。

```seki
theorem forward : forall a in Real, a <= 5.0 => (2.0 * a) <= 12.0
  := by have h : (2.0 * a) <= (2.0 * 5.0) := by apply double_mono
     then algebra
```

⚠️ 入れ子の証明は **1 タクティク**です。上の `then algebra` は外側の鎖に
属します (そう読めるように、そう構文解析されます)。複数手順が要る中間
事実は独立した `theorem` にしてください。

**健全性**: ✅ `Cert::Have`。kernel は `fact` を現在の仮定の下で検査し、
その後ゴールを `fact` 付きで検査します。

### `by assumption`

ゴールの結論がすでに仮定にあるとき閉じます。場合分けが残す枝の多くが
この形です。

**健全性**: ✅ `Cert::Assumption`。kernel が仮定の鎖を見て一致を確認します。

### `by witness v := <項>`

存在命題の **導入**。`by obtain` の双対で、`exists v in D, P(v)` を
`P(<項>)` に置き換えて次のタクティクに渡します。

```seki
theorem lin_cont : forall eps in Real, eps > 0.0 =>
  (exists d in Real, forall x in Real,
     absR (x - 1.0) < d => absR ((2.0*x + 1.0) - 3.0) < eps)
  := by witness d := eps / 2.0 then unfold absR then algebra
```

これが無いと ε-δ が書けても **証明できません** — 連続性の主張はすべて
`forall eps, eps > 0 => exists delta, ...` の形で、証明するとは δ を ε の
関数として **差し出す** ことだからです。`lib/analysis/limit.seki` の定義に
「theorem の証明には使わないこと」という注意書きが付いていたのは、
まさにこの導入規則が無かったためです。

⚠️ 項は `forall` で束縛された変数とリテラルから `+ - * /` で組んだもの
に限ります。割り算の**分母は非零リテラル**でなければなりません
(`eps / 2.0` は可、`1.0 / eps` は不可) — `eps != 0` という仮定が
文脈にあっても、それを読むのは推論であって所属判定ではないからです。

**健全性**: ✅ `Cert::Witness`。kernel は (a) 項が領域の元であることを
構文的に確かめ (`witness_is_total`)、(b) 代入後の義務を**自分で導出して**
から検査します。証明書が選べるのは項だけで、それが何を証明する義務を
生むかは選べません。

## 5.1c 区間 — 「この範囲のすべての値について」

`lo .. hi` と `中心 +- 許容差` は、その間の**すべての実数**を表す値を作ります
(どちらも `interval lo hi` への糖衣で、パーサで展開されるので、カーネルも
型検査もタクティクも今までどおりのものしか見ません)。

```seki
def rBand := 8000.0 .. 12000.0
def startup := 22.5 +- 7.5        -- 仕様書の書き方に合わせる

theorem in_spec : (rToTemp rBand >= 270.0) and (rToTemp rBand <= 310.0) := by eval
```

演算は範囲を丸ごと運び、比較は**範囲全体が決めたときだけ**答えます。
したがってここで証明されることは範囲内のどの値についても成り立ちます —
再帰・条件分岐・`exp`/`ln`/`sin`/`cos` を含む任意の計算を通して。

結合は算術より緩く比較より強いので、`1.0 + 2.0 .. 5.0` は 3 から 5 の帯です。

### `lo` / `hi` / `width` / `mid`

囲いがどう出たかを読む関数。ただの数は幅ゼロの帯なので、そちらにも使えます。

```seki
theorem contracts : width (run 20 x0) < 0.25 := by eval
```

`width` が重要なのは、**囲いが広がっていないことを主張できる**からです。
区間演算は同じ値が式に複数回現れると広がります (依存性)。Newton 法の
`x - (x³-8)/(3x²)` は `x` が 3 回出るので、実数の反復が縮む場面で囲いは
広がります。そうなったとき失敗は

```
interval arithmetic does not settle this claim (... — the left enclosure is 2 wide).
An enclosure widens wherever a value appears more than once, so this shows
neither that the claim holds nor that it fails
```

と出ます — 「偽である」ではなく「この方法では決まらない」です。

## 5.2 `refl`

**意味**: 命題が `Refl: x == x` 形に構造一致するか。**型項としても使える** (Curry-Howard)。

**健全性**: ✅ 完全に健全 (構造的等価のみ)。証明項は `Refl` (両辺を評価して
比較) または `SyntacticRefl` (両辺が同じ項) の 1 ステップ。

```seki
theorem t : 42 == 42 := refl
```

## 5.3 `by algebra`

**意味**: 多項式正規化 + 符号解析 + PSD 2 次形式判定 + 有理関数の交差乗算。
無限ドメインの多項式恒等式 / 不等式を扱える。

- **div/mod**: 定数除数は直接畳み込む。可変除数は `==` かつ結果が単項キャンセル
  で閉じる場合のみ対応 — `/` は `ratpoly_equal` (`(a*n)/n == a` を有理関数の
  交差乗算で判定)、`mod` は `Polynomial::exact_div_by_var` (`(a*n) mod n == 0`
  — 分子の全項が除数の変数を factor に持てば健全、符号無関係)。可変除数の
  不等式や、剰余が非零の一般ケースは未対応。
- **`if` の場合分け**: ゴール側だけでなく**仮定 (hypothesis) 側**に埋め込まれた
  `if` も場合分けする (2026-08 修正 — `absR := \r -> if r<0.0 then -r else r`
  を unfold した結果生じる仮定側の `if` が場合分けされず、`n>0 ⊢ n-1>=0`
  のような ε-δ 論法の核心的な推論すら通らなかった)。
- **仮定の積 (Positivstellensatz)**: 仮定を非負の重みで足すだけでなく、
  仮定どうしの**積**も生成子に使う。生成子の個数 (掛け合わせる仮定の数)
  はゴールの次数から決まり、最大 4 まで。どの生成子を使うかは**厳密有理数の
  phase-1 単体法** (`solve_nonneg_optimal`) が決める — 部分集合探索では
  3 個が限界で `a³ <= 1` に届かなかった。
- **反対称性**: `<=` と `>=` の両方が示せれば `==` を結論する
  (`Cert::Antisymmetry`)。極限や上限の一意性はこの形。
- **正の量で割る**: `c > 0` と `c·l OP c·r` から `l OP r` を結論する
  (`Cert::CancelPositive`)。Positivstellensatz は非負量を**足す**ことしか
  できないので `(1-k)·A <= 0` までは行けても `A <= 0` に移れない。
  縮小写像の議論はすべてここで止まる。線形のゴールかつ非線形の仮定が
  あるときだけ試す (線形どうしなら Farkas が完全なので、試すだけ無駄)。
- **等式の仮定**: `p == 50.0` のような等式は 2 本の不等式を含意するので、
  生成子として両方向を使う。カーネルが等式から自分で導出する
  (`add_equality_consequences`)。
- **足りない仮定の逆算**: 閉じられなかったとき、変数の bound を名指しで
  返す (`src/abduce.rs`)。Farkas を逆向きに走らせ、足りない仮定を表す列を
  1 本足して同じ実行可能性問題を解く。**最弱の** bound を選ぶには
  Charnes–Cooper 変換が要る (bound は 2 つの未知数の比なので、線形目的
  では取れない)。矛盾する仮定は ex falso で何でも「証明」できてしまうため
  候補から外す。

  bound が**積の中**に要るときは線形の読みでは見えない —
  `x >= 0 ⊢ x² <= 4` は `x <= 2` で成り立つが、証明書は `(2-x)(2+x)` で、
  未知数が生成子に掛かる。そういうゴールでは**証明器に直接訊く**:
  「`var <= c` でゴールが閉じるか」は `c` について単調なので、倍々の
  はしごで境界を挟んでから二分する。1 回 1 回が本物の証明試行なので、
  線形の読みが原理的に無力な**非線形のゴールに限って**走らせる。
- **ドメインの推定**: `forall x in Real` のような束縛子が無いゴール
  (自由なグローバルについての主張 — モデルがパラメータを述べる形) は、
  実数リテラルを含むなら `Real` として読む。以前は `Int` に落ちていて、
  整数の離散性が実数に誤適用されていた。
- **整数の離散性**: `Nat`/`Int` では厳密不等式 `poly > 0` から `poly >= 1` を
  仮定強化として自動導出する (2026-08 追加、`integer_strengthen`)。有理数緩和
  だけに頼る Fourier-Motzkin では `n > 0 (Nat) ⊢ n - 1 >= 0` は証明できない
  (実数では偽) ため、これが無いと通らない。
- **`let` / タプル / `intToReal`**: 非再帰 `let x = v in body` はインライン展開、
  リテラルタプルへの `fst`/`snd` はその場で射影、`intToReal e` は値保存の型変換
  として `e` の多項式をそのまま使う (2026-08 追加) — 以前はいずれも不透明アトム
  だった。
- **リスト構造等価性**: `xs == ys` のゴールで両辺が (`cons`/`nil`/リテラル
  タプル形いずれかで) 構造的に判別できる場合、`cons h1 t1 == cons h2 t2`
  は `h1==h2 and t1==t2` に、`nil==nil` は自明に真に、`nil` vs `cons` は
  矛盾 (証明失敗ではなく偽) に分解する (2026-08 追加)。
- **超越関数**: `sin`/`cos`/`exp`/`ln` などの呼び出しは常に不透明アトム。
  代数的性質 (ピタゴラスの恒等式など) が必要な場合は
  `lib/analysis/elementary.seki` の `axiom` を `by simp` で使う。

**健全性**: ✅ `Int` / `Rat` / **`Real`** 上の多項式について健全 (`Real` は
`f64_to_rat` で厳密な有理数に変換して判定)。

```seki
theorem distrib : forall (a b c) in Int, a * (b + c) == a * b + a * c
    := by algebra
theorem cauchy : forall (a b) in Int, a*a + b*b >= 2 * a * b
    := by algebra
theorem mod_cancel : forall a in Int, forall n in Int, n != 0 -> (a * n) mod n == 0
    := by algebra
```

## 5.4 `by induction`

**意味**: 構造帰納法。`Nat` / `List` / `Tree` / user `data` ADT に対応。
recursive constructor の引数は IH (帰納仮説) として扱う。

**健全性**: ✅ 構造帰納法は健全 (整列性原理 + ADT の有限構築可能性に依存)。

```seki
def listLen := \xs -> if null xs then 0 else 1 + listLen (tail xs)
theorem nn : forall xs in (List Int), listLen xs >= 0 := by induction
```

**汎化された帰納法仮説 (List、2026-08 追加)**: 帰納変数の直後にさらに
`forall`が続く形 (`forall p in List T, forall k in Nat, forall c in Real,
LHS(p,k,c) == RHS(p,k,c)`、`==` ゴールのみ) は `verify_list_induction_generalized`
にディスパッチされる。単純な構造帰納では IH が「同じ k, c での性質」しか
使えないが、再帰呼び出しが `k+1` のような**異なる値**での性質を必要とする
関数 (積分の分母インデックスのような、呼び出しごとに変わる補助引数を持つ
もの) には対応できない。汎化版は IH を「`forall k c, LHS(k,c,ys)==RHS(k,c,ys)`」
という `by simp` 同様の書き換え規則として保持し、ステップケースの (1段
unfold した) ゴールにパターンマッチで適用する — 必要な `k+1` 等への
インスタンス化を自動的に発見する。`Nat` 帰納法はまだこの汎化に非対応。

```seki
-- 積分の分母インデックス k・微分側の先頭ジャンク係数 c を汎化した例
-- (lib/cas/poly.seki の ftc_poly_general と同じ形)
theorem ftc_general
  : forall p in List Real, forall m in Nat, forall c in Real,
      polyDerivRec (cons c (polyIntegrateRec p (m + 1))) (m + 1) == p
  := by induction
```

## 5.5 `by strong_induction` / `by strong_induction <N>`

**意味**: 深さ `N` (省略時 2) の強帰納法。`P(0), ..., P(N-1)` を基底とし、
`P(k+N)` を「展開で現れる再帰呼出しは (Nat 上の) 非負な不透明項」として
多項式符号判定する。`N` は **タクティクが探索する深さではなく、対象の
再帰定義が実際に何段前を参照するか** — Fibonacci (`fib(n-1)+fib(n-2)`) は
`N=2`、tribonacci 型 (`f(n-1)+f(n-2)+f(n-3)`) は `N=3` が必要。

```seki
def fib := \n -> if n < 2 then n else fib (n - 1) + fib (n - 2)
theorem fib_nn : forall n in Nat, fib n >= 0 := by strong_induction

def trib := \n ->
    if n == 0 then 0 else if n == 1 then 1 else if n == 2 then 1
    else trib (n - 1) + trib (n - 2) + trib (n - 3)
theorem trib_nn : forall n in Nat, trib n >= 0 := by strong_induction 3
```

**健全性**: ✅ Nat 上で健全 — `N` を関数の実際の参照深さより**小さく**指定すると、
展開後にまだ `k` に依存する未解決の `if` (基底境界を跨ぐ場合分け) が残るが、
これを検出して **証明を失敗させる** (`by strong_induction N: could not resolve
every base-case boundary ...`)。この検出が無いと、未解決の `if` が
「非負と仮定した不透明項」に丸め込まれ、境界のすぐ内側に潜む負のリテラルを
一度も検査せずに偽の命題を通してしまう実際のバグがあった (2026-08 に発見・
修正 — `docs/spec/06-soundness.md` 参照)。`N` を関数の参照深さより**大きく**
指定した場合は単に余分な基底を検査するだけで安全。

## 5.6 `by simp` / `by simp [theorem1, theorem2]`

**意味**: 既存の theorem を方向付き書換え規則として連鎖適用。
AC-canonicalization により可換和 / 可換積に対応 (対称規則も oscillate しない)。

**健全性**: ✅ 各 rewrite 規則自体が健全な theorem なので chain も健全。

```seki
theorem t : x + 0 == x := by simp [add_zero]
```

## 5.7 `by unfold f`

**意味**: 関数 `f` の定義を 1 段 β-展開する transformer。展開結果に現れる
**非再帰**のユーザ定義呼び出しはさらに推移的に展開される
(`unfold_nonrec_transitive`) — `f` が非再帰の `g` を呼ぶなら `g` も見える。
通常は closer (`eval`, `algebra`, ...) と組み合わせる。

**健全性**: ✅ 定義の展開は意味保存。

**相互再帰**: `f` と `g` が互いを呼び合う組 (`isEven`/`isOdd` 等) の場合、
呼び出しグラフのサイクル検出 (`closure_is_recursive`, 2026-08 修正) により
両方とも「再帰的」と判定され、推移展開の対象から除外される — `f` 自身は
1 段展開されるが、その中で呼ばれる `g (...)` はそこでオペークな項として
止まる (直接の自己再帰と同じ扱い)。**2026-08 以前**は直接の自己参照しか
検出できず、相互再帰の組を「非再帰」と誤判定して交互に展開し続け、
32 回の反復上限まで暴走していた。

```seki
def square := \x -> x * x
theorem t : square 3 == 9 := by unfold square then eval

def f := \n -> if n == 0 then 0 else g (n - 1) + 1
def g := \n -> if n == 0 then 0 else f (n - 1) + 1
-- 1段展開後、`g (n - 1)` はそのままオペークな項として残る
theorem f_step : forall n in Nat, n > 0 -> f n == g (n - 1) + 1
    := by unfold f then algebra
```

**未対応**: 真の**相互帰納法** (2つの関数の性質を互いを IH として同時に
証明する) はまだ無い。上の例のように「一方をもう一方の1段先のオペーク項
として扱う」だけで閉じる範囲でしか使えない。

## 5.8 `by intros`

**意味**: 先頭の `forall x in S, P(x)` を剥がして `x` を free var として
証明文脈に入れる transformer。

**健全性**: ✅ 全称除去は健全。

```seki
theorem t : forall n in Nat, n + 0 == n
    := by intros then algebra
```

## 5.9 `by decide`

**意味**: 命題を強制的に `Bool` に落として真偽を判定。
古典論理を仮定 (排中律と LEM 系)。

**健全性**: ✅ Bool に reduce できるならば健全。それ以外はエラー。

## 5.10 `by linarith`

**意味**: `by algebra` の別名 (実装上は同じ `verify_algebra` に dispatch する) —
「線形不等式を証明したいときの意図を示す」ための名前として使う。
前提の連言 (`P1 and P2 and ... => Q`) は個別の仮定に分解され、以下の順で
ゴールを閉じる:

1. 単一の仮定からの直接含意 (`hypothesis_proves`)
2. 複数仮定を **等重み 1 で加算した結果がゴールの多項式と一致する** 場合
   (`hyps_sum_proves`) — 例えば `x > 0`, `y > 0` から `x + y > 0` を導ける
3. **多変数 Fourier-Motzkin 消去** (`algebra::fm_is_unsat`, 2026-08 追加):
   仮定と否定したゴールを線形制約 (`poly <=/< 0` の集合) に変換し、
   変数を1つずつ「下界と上界のペアから新しい制約を作る」ことで消去、
   最終的に矛盾する定数制約が出れば「証明できる」と判定する。
   2 の等重み1の和では届かない **スケーリングが必要なケース**
   (`x <= 3 ⊢ 2x <= 6`) や **ゴールに現れない変数の消去**
   (`x <= y and y <= 10 ⊢ x <= 10`) もこれで通る。

単変数専用の Fourier-Motzkin ソルバ (整数区間による厳密決定) は
`src/linarith.rs` に**別実装**として存在し、`linarithProve` builtin として
式ベースで呼べる (Phase 5)。`by linarith` タクティクは (3) の多変数版を
使うが、これは `src/linarith.rs` とは別のコード (`src/algebra.rs` /
`src/prover.rs`) — 2つのソルバの統合は今後の課題。

**健全性**: ✅ 1・2 は前述の通り健全。3 (多変数 FM) は
**「証明できる」方向のみ健全** — 仮定+否定ゴールの有理数緩和が
充足不能なら元の (整数/Nat の) 系も充足不能なので健全だが、逆に
有理数として充足可能でも整数解が存在しない場合があるため、
3 を「反証」(偽の判定) には使わない設計。`linarithProve` builtin 自体も
線形整数 / 有理数算術に対して健全 (property test
`linarith_never_proves_a_falsehood` で 400 例検証)。

```seki
theorem t : forall (x y) in Int, x > 0 and y > 0 => x + y > 0
    := by linarith

-- 多変数消去が必要な例 (等重み1の和では届かない)
theorem t2 : forall x in Int, x <= 3 -> 2 * x <= 6 := by linarith
theorem t3 : forall (x y) in Int, x <= y and y <= 10 -> x <= 10 := by linarith
```

## 5.11 `by auto`

**意味**: ポートフォリオ探索。固定順序のタクティク列
(`refl` → `by eval` → `by decide` → `by algebra` → `by induction` →
`by strong_induction` → `by intros then algebra`) と、命題に現れる
ユーザ定義関数ごとの `unfold f then algebra` / `unfold f then induction`、
既存 theorem との記号重なりでランク付けした `by simp [lemma]` の組合せを
順に試し、**最初にゴールを閉じたもの**を採用する。

`theorem t : P` (`:=` を省略した形) は REPL / ファイルの両方でこれに
desugar される。REPL の `:why` コマンドは補題を優先する変種
(`try_portfolio_lemma_first`) を使う — どの既存定理を使って閉じたかを
知りたい場面のため。

**健全性**: ✅ 各候補タクティク自身の健全性に従う (portfolio は
「どれを最初に試すか」の探索順だけで、証明自体の正しさには関与しない)。

```seki
def sum := \n -> if n == 0 then 0 else n + sum (n - 1)
theorem gauss : forall n in Nat, 2 * sum n == n * (n + 1) := by auto
    -- portfolio が unfold + induction の組合せを発見して閉じる
```

## 5.12 `by obtain w from L [with x := e, ...] then <closer>`

**意味**: 存在命題の除去 (existential elimination)。`L` は既存の `axiom`
または `theorem` の名前。`with` の束縛で `L` の命題中の名前 (`forall`
束縛変数、および `forall` で束縛されていない自由変数 — 関数のように
`Set` で自然に表現しにくいドメインを持つものはしばしば自由変数のまま
残される) を具体的な式に置き換える。置換後、残る前提 (`=>` の左辺) を
現在のゴール自身の前提と照合するか `by algebra` で discharge し、
結論が `exists v in D, P(v)` であることを要求して、`v` を `w` という
**シンボリックな名前**に置き換えた `P(w)` を後続の `<closer>` の
仮定として使えるようにする (transformer)。

`w` は計算可能な値を持たない — 「論理的にはこの性質を満たす値が存在する」
ことしか表さないので、`by eval` 等で `w` を評価しようとするとエラーになる。
`by algebra` のように自由変数をシンボリックに扱うタクティクでのみ使える。

**用途**: `axiom` は宣言されただけでは真偽タグに退化し計算内容
(witness 抽出手続き) を一切持たない (`06-soundness.md` 参照)。
`by obtain` はこれに対する対処で、たとえば中間値の定理のような
「構成的に証明できないが古典的に真だと認める」事実を `axiom` として
宣言した上で、**その先の定理を厳密に導出する**ことを可能にする。

**健全性**: ✅ 標準的な自然演繹の存在除去則そのもの — `exists x, P(x)` と
「任意の `x` が `P(x)` を満たすなら `Q`」から `Q` を導いてよい、という
規則を、`w` という具体的だが不透明な名前を使って実現している。前提の
discharge に失敗すれば (= `L` を正当に呼び出せる根拠が無ければ) proof
error になるので、偽の前提から任意の結論を「証明」できてしまうことはない。

```seki
-- 中間値の定理を axiom として宣言 (f, a, b は自由変数のまま)
axiom ivt_general
  : (f a) * (f b) <= 0.0
    => (exists c in Real, (a <= c) and (c <= b) and ((f c) == 0.0))

def f_cubic := \x -> x * x * x - x - 2.0

-- f_cubic(1)*f_cubic(2) <= 0 なので [1,2] に根がある。
-- その根 w について w³ = w + 2 が成り立つことを厳密に導出する。
theorem cubic_root_relation
  : (f_cubic 1.0) * (f_cubic 2.0) <= 0.0 => (w * w * w) == (w + 2.0)
  := by obtain w from ivt_general with f := f_cubic, a := 1.0, b := 2.0
     then unfold f_cubic then algebra
```

## 5.13 証明項 (Curry-Howard)

タクティクなしで Curry-Howard 風に書ける場合:
- `forall x in S, P(x)` は関数 `\x -> ...` として与える。適用結果は捨てられ、
  `P(x)` を `enumerate_set` でサンプルした各 `x` について直接 eval して
  判定する — つまり `\x -> refl` のような「証明」を関数の中身に書く仕組みは
  無く、関数はほぼ何でもよい (型が合ってさえいれば)。無限ドメイン (Real/
  Nat/Int) では `06-soundness.md` の `by eval` と同じサンプル検査に
  過ぎないので、無限ドメインの等式・不等式は素直に `by algebra` を使う方が
  健全性が強い。
- `exists x in S, P(x)` は witness 式そのもの (タプルではない)。

```seki
-- 動くが、無限ドメインでは by eval 同様サンプル検査でしかない (非推奨) —
-- 実際にはこの命題は by algebra で完全に健全に証明できる
theorem t : forall x in Nat, x == x := \x -> x
theorem e : exists x in Nat, x > 5 := 6
```

## 5.14 タクティク合成 (`then`)

```
proof := tac1 then tac2 then tac3
```

`tac1` で命題を変形し、`tac2` でさらに変形し、最後の `tacN` (closer) で
閉じる。慣用例:

```seki
theorem mul_add : forall (x y z) in Int, x * (y + z) == x * y + x * z
    := by intros then algebra
```

## 5.15 健全性の総まとめ

| 戦術 | 種別 | 健全性 |
|---|---|---|
| `eval` | closer | ✅ 有限のみ / 🟡 無限ドメインはサンプル |
| `refl` | closer / 項 | ✅ |
| `algebra` | closer | ✅ Int / Rat / Real 上の多項式 + 仮定の加算結合・多変数 Fourier-Motzkin (仮定側 if の場合分け、整数離散性、let/タプル/intToReal透過、リスト構造等価性を含む) |
| `linarith` | closer | ✅ `algebra` の別名 (同じ健全性) |
| `decide` | closer | ✅ Bool に reduce できる場合のみ |
| `induction` | closer | ✅ 構造帰納 (List は補助パラメータの汎化にも対応) |
| `strong_induction <N>` | closer | ✅ Nat、深さ可変 (`N` 省略時2) |
| `simp` | both | ✅ 既存定理の連鎖 |
| `unfold` | transformer | ✅ 定義展開、相互再帰も1段で正しく止まる |
| `intros` | transformer | ✅ 全称除去 |
| `auto` | closer (portfolio) | ✅ 各候補タクティクの健全性に従う |
| `obtain` | transformer | ✅ 存在除去則そのもの (前提discharge失敗時はエラー) |
| Curry-Howard 項 | closer | ✅ (ただし forall 側は無限ドメインで `by eval` 同様サンプル検査 — 非推奨) |

タクティク 12 種 (auto, obtain を含む) すべて、想定範囲内では健全。
**全体としての健全性の弱点** は型システムの sample-based dep type check
であり、タクティクではない。`06-soundness.md` 参照。

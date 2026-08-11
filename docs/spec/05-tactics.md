# 5. 証明戦術

seki は **11 種類のタクティク + コンビネータ** を持ちます。それぞれの
意味論と健全性条件をまとめます。

タクティクは `theorem` の `:=` の後に `by <tactic>` 形式で書きます。
複数を `then` で合成できます。

```
theorem t : P := by tac1 then tac2 then tac3
```

## 5.1 `by eval`

**意味**: 命題を完全簡約して `Bool::true` になるか確認する。

**健全性**: 列挙集合 / 内包の有限ドメインに対して健全。
無限ドメイン上の `forall` は `SAMPLE_BOUND` (200) でのサンプル検査になり
**健全ではない**。

```seki
theorem t1 : 1 + 1 == 2 := by eval                    -- ✅
theorem t2 : forall x in {1,2,3}, x > 0 := by eval     -- ✅
theorem t3 : forall n in Nat, n + 1 > 0 := by eval     -- 🟡 sampled
```

## 5.2 `refl`

**意味**: 命題が `Refl: x == x` 形に構造一致するか。**型項としても使える** (Curry-Howard)。

**健全性**: ✅ 完全に健全 (構造的等価のみ)。

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

## 5.12 証明項 (Curry-Howard)

タクティクなしで Curry-Howard 風に書ける場合:
- `forall x in S, P(x)` は関数として、適用すると証明を返す
- `exists x in S, P(x)` は witness + 証明のタプル

```seki
theorem t : forall x in Nat, x == x := \x -> refl
theorem e : exists x in Nat, x > 5 := (6, refl)  -- 略式
```

## 5.13 タクティク合成 (`then`)

```
proof := tac1 then tac2 then tac3
```

`tac1` で命題を変形し、`tac2` でさらに変形し、最後の `tacN` (closer) で
閉じる。慣用例:

```seki
theorem mul_add : forall (x y z) in Int, x * (y + z) == x * y + x * z
    := by intros then algebra
```

## 5.14 健全性の総まとめ

| 戦術 | 種別 | 健全性 |
|---|---|---|
| `eval` | closer | ✅ 有限のみ / 🟡 無限ドメインはサンプル |
| `refl` | closer / 項 | ✅ |
| `algebra` | closer | ✅ Int / Rat / Real 上の多項式 + 仮定の加算結合・多変数 Fourier-Motzkin |
| `linarith` | closer | ✅ `algebra` の別名 (同じ健全性) |
| `decide` | closer | ✅ Bool に reduce できる場合のみ |
| `induction` | closer | ✅ 構造帰納 |
| `strong_induction <N>` | closer | ✅ Nat、深さ可変 (`N` 省略時2) |
| `simp` | both | ✅ 既存定理の連鎖 |
| `unfold` | transformer | ✅ 定義展開、相互再帰も1段で正しく止まる |
| `intros` | transformer | ✅ 全称除去 |
| `auto` | closer (portfolio) | ✅ 各候補タクティクの健全性に従う |
| Curry-Howard 項 | closer | ✅ |

タクティク 11 種 (auto を含む) すべて、想定範囲内では健全。
**全体としての健全性の弱点** は型システムの sample-based dep type check
であり、タクティクではない。`06-soundness.md` 参照。

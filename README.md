# seki

集合論ベースの証明言語 + プログラミング言語。Rust 実装、外部依存ゼロ、単一バイナリ。

**seki の単位は「証明」ではなく「主張とその根拠の等級」です。**

計算を走らせることと、その計算について何かを主張することが同じ行為になっていて、
処理系は主張ごとに**どの種類の根拠が得られたか**を報告します。成果物は
`seki --audit` が出す表であって、`theorem` はその行を生む手段です。

```seki
def consume := \tokens cost -> if tokens >= cost then tokens - cost else tokens

theorem consume_never_goes_negative
  : forall tokens in Real, forall cost in Real,
      (tokens >= 0.0) and (cost >= 0.0) => consume tokens cost >= 0.0
  := by unfold consume then algebra
```

`consume` は普通の実装です。足したのは `theorem` だけ。境界を書き間違えると
(`tokens >= cost` を `tokens > 0.0` に)、代表的なテストケースは**全部通ったまま**
この定理が落ちます。

```
proof error: by algebra (then-branch of `if (tokens > 0)`):
  cannot prove (tokens - cost) >= 0 over Real
```

テストは「この入力で動いた」を言い、定理は「**この範囲のすべての入力で**成り立つ」
を言います。

## `--audit` — 何が証明で、何が計算で、何が仮定か

```
$ seki --audit examples/assurance/system.seki

theorem                                       how it was verified
------------------------------------------------------------------------------
calibration_stays_in_spec                     kernel-checked from primitives
control_effort_within_rating                  axiom `disturbance_bounded`
                                              confidence >= 9/10 (from `disturbance_bounded` 9/10)
displayed_temperature_is_trustworthy          axiom `sensor_drift_bounded`
                                              confidence >= 4/5 (from `sensor_drift_bounded` 4/5)
gain_envelope                                 kernel-checked from primitives
```

信頼水準は 5 段の格子です。低いほうの 2 つは**偽を通しうる**と明記されています —
seki は不健全なタクティクを排除せず、**等級をつけて管理する**ことを選んでいます。
これが純粋な証明系と違うところで、実用言語でもあることを可能にしています。

| 水準 | 意味 | 表示 |
|---|---|---|
| `sound` | カーネルが原始推論規則から再構成した | (印なし) |
| `axiomatic` | 証明は正しいが `axiom` に乗っている | `[axiomatic]` |
| `unchecked` | タクティクは閉じたが証明項が無い | `[unchecked — no proof term]` |
| `approximate` | 浮動小数点で決めた — **偽を通しうる** | `[approximate — floating point]` |
| `sampled` | 無限ドメインの有限標本 — **証明ではない** | `[sampled — NOT a proof]` |

`--strict` は `sound` 以外を拒否し、`--min-confidence 0.8` は仮定の確度に下限を
切ります。ディレクトリを渡すとシステム全体で 1 枚の報告になり、証明以外に立って
いる主張から始まります (審査で実際に見るのはそのリストなので、良い知らせの下に
埋めません)。弱い主張が残っていれば exit code が非ゼロなので、ビルドのゲートに
なります。

```
$ seki --audit examples/services

claims resting on something other than a kernel proof
------------------------------------------------------------------------------
  axiomatic   serial_availability_meets_slo  (sla.seki)
              axiom `auth_availability`; axiom `cdn_availability`; axiom `db_availability`
              confidence >= 13/20 (from `auth_availability` 9/10, ...)

assumed without proof
------------------------------------------------------------------------------
  auth_availability     9/10 — ベンダー SLA + 12か月の実測 (2025-09〜2026-08)
  db_availability       4/5 — 自社運用、計画停止を除外した集計

==============================================================================
18 claims across 5 file(s), 3 assumption(s)
  sound:       17
  axiomatic:   1
```

## 「この集合のすべての値について」を言う 3 つの方法

seki は同じことを 3 通りで担い、`--audit` が**どれが担ったか**を記録します。

| 方法 | 書き方 | 届く範囲 | 代償 |
|---|---|---|---|
| 記号的 | `forall x in Real, 仮定 => 結論` + `by algebra` | 多項式関係、次数 4 まで。**厳密** | 多項式の外に出られない |
| 数値的 | `lo .. hi` / `中心 +- 許容差` + `by eval` | 再帰・分岐・`exp`/`ln`/`sin`/`cos` を含む**任意の計算** | 囲いが広がる (依存性) |
| 列挙 | 有限集合 + `by eval` | 有限ドメイン | 無限では標本になる |

```seki
-- 記号的: 多項式なので厳密に決まる
theorem gain_box : forall a in Real, forall b in Real,
  (a >= 0.0) and (a <= 1.0) and (b >= 0.0) and (b <= 1.0) => a * b <= 1.0 := by algebra

-- 数値的: 対数が入るので多項式では書けない。範囲を丸ごと運んで証明する
def rToTemp := \r -> 1.0 / (0.00335 + 0.000257 * (ln (r / 10000.0)))
theorem temp_in_spec
  : (rToTemp (8000.0 .. 12000.0) >= 270.0) and (rToTemp (8000.0 .. 12000.0) <= 310.0)
  := by eval

-- 解析が結論を出せるだけ精密かも主張できる
theorem enclosure_is_tight : width (evolve 50 (22.5 +- 7.5)) < 0.2 := by eval
```

数値的な方法は**保証された囲い** (`src/interval.rs`) で計算します。演算は外側に
丸めるので囲いは広がることしかなく、比較は範囲全体が決めたときだけ答えます。
`exp`/`ln`/`sin`/`cos` は Lagrange の剰余で抑えた級数で、境界が保証されている
範囲の外は**推定せず拒否**します。

`width` が重要なのは、**囲いが広がっていないことを主張できる**ことです。
これが無いと「仕様を守った」が「たまたま囲いが収まった」のか区別がつきません。

## 探索と検査の分離

タクティクが「証明できた」と言っても、それは証明ではありません。タクティクは
証明項を**生成**し、タクティクを一切呼ばない小さな **kernel** がそれを原始推論
規則から再構成します。探索は難しくバグりうるが、検査は易しく、正しくなければ
ならないのはそこだけです ([docs/spec/06-soundness.md](docs/spec/06-soundness.md))。

```
$ seki --proof examples/13_advanced_tactics.seki abs_int_nonneg
theorem abs_int_nonneg : (forall x in Int, ((if (x >= 0) then x else (- x)) >= 0))
case split on the goal's first `if`:
  when the condition holds:
    this is one of the hypotheses in scope
  when it does not:
    `(- x)` - `0` = ((x < 0)) (over Int)

kernel verdict: every step re-established from primitives
```

kernel は `EvalCtx::finite_only` を通して評価するので、**無限ドメインのサンプリング
を構造的に受理できません**。TCB (kernel + rewrite + unfold + interval) は **4,896 行**、
処理系全体 28,000 行あまりの 17% です。TCB は「小さいほうがいい」ではなく
**予算**として扱われていて、機能を足すたびに「信頼すべきものが増えるか」で判断
しています。

導入した日に、kernel は `by algebra` の**実在する健全性バグ**を見つけました —
`f n = -5` に対して `forall n in Nat, f n >= 0` が証明できていました。

## 仮定は消さずに追跡する

「全部証明しろ」ではなく「仮定してよい、ただし結論まで運ぶ」。

```seki
axiom db_availability : dbA >= 0.9990
  with confidence 0.8 from "自社運用、計画停止を除外した集計"
```

合成は**掛け算ではなく Fréchet 下界** `max(0, Σpᵢ − (n−1))`。`0.9 × 0.8 = 0.72` は
独立性を仮定した数字で、同じ抽出パス由来の事実は独立ではありません。確率は
kernel に入れません — 入れると `sound` が連続量になり「kernel 検証済み」が意味を
失います。

## 失敗が情報を返す

証明が失敗するのはたいてい主張が誤っているからではなく仮定が足りないからです。

```
$ seki capacity.seki
proof error: by algebra: cannot prove (perNode * nodes) >= rps over Real
  it would hold given `(perNode >= 625)` — add it as a hypothesis ...
```

5000 rps ÷ 8 台 = 625。Farkas を逆向きに走らせて境界を求め、**最弱の**ものを
選びます (境界は 2 つの未知数の比なので Charnes–Cooper 変換が要ります)。非線形
なら証明器に直接訊きます。矛盾する提案は ex falso で何でも「証明」できてしまう
ので候補から外します。

囲いが決まらなかったときも、**幅と理由**を返します。

```
interval arithmetic does not settle this claim
  ([-1, 1] and [1/2, 1/2] overlap — the left enclosure is 2 wide).
  An enclosure widens wherever a value appears more than once, so this
  shows neither that the claim holds nor that it fails
```

「偽である」ではなく「**この方法では決まらない**」と読めることが要点です。

## 限界 — 名前と理由がついている

```
$ for f in $(find examples tests/seki lib -name '*.seki'); do
    seki --audit "$f" | grep -oE '^  [a-z]+: +[0-9]+'
  done | awk -F'[: ]+' '{t[$2]+=$3} END {for (k in t) print k, t[k]}'

sound        1148
unchecked      22
sampled        20
axiomatic      16
approximate     8
```

- **`approximate` 8 件**はすべて**反復アルゴリズムの区間依存性** (wrapping effect)。
  Newton 法の `x - (x³-8)/(3x²)` は `x` が 3 回出るので、実数の反復が縮む場面で
  囲いは広がります。埋めるには区間 Newton 法が要り、TCB がさらに増えます。
- **`unchecked` 22 件**の大半は `by induction` のステップ (基底ケースは kernel が
  検証しますが、ステップの正規化に witness 形式がまだありません)。
- **`sampled` 20 件**は無限ドメインの標本検査で、**証明ではありません**。
  `--strict` が拒否します。
- 初期条件が集合のとき、`by algebra` は多項式の外に出られず、区間は依存性で
  広がります。その中間 (区間 Newton、平均値形式) は未実装です。

## クイックスタート

```sh
cargo build --release                                # Rust 1.70+、依存ゼロ
cargo run -- examples/04_proofs.seki                 # ファイル実行
cargo run -- --audit examples/services               # プロジェクト監査
cargo run -- -e 'theorem t : 2 + 2 == 4 := by eval'  # ワンライナー
cargo run                                            # REPL
```

## 証明戦術

| 戦術 | 種別 | 用途 |
|---|---|---|
| `by eval` | closer | 命題を簡約 (有限ドメイン / 厳密有理数 / 区間のときだけ `sound`) |
| `refl` | closer | 等式の構造的等価 |
| `by algebra` / `by linarith` | closer | 多項式正規化 + Positivstellensatz (仮定の積、次数 4)・反対称性・正の量で割る |
| `by induction` | closer | Nat / List / Tree / 任意の `data` 上の構造帰納法 |
| `by strong_induction <N>` | closer | 深さ可変の強帰納法 |
| `by decide` | closer | Bool に落とせる命題を強制的に決定 |
| `by auto` | closer | 戦術のポートフォリオ探索 |
| `by apply L [with x := e]` | closer | modus ponens — 定理/公理の引用 |
| `by assumption` | closer | 結論がすでに仮定にある |
| `by have h : P := <proof>` | transformer | カット規則 (前向きの積み上げ) |
| `by witness v := <項>` | transformer | 存在導入 — ε-δ はこれが無いと書けても証明できない |
| `by obtain c from L` | transformer | 存在除去 |
| `by unfold f` | transformer | 定義を 1 段 β-展開 |
| `by intros` | transformer | 先頭の forall を剥がす |
| `by simp [l1, l2]` | both | 等式 theorem を書換え規則として連鎖適用 |
| `tac1 then tac2 ...` | combinator | 合成 |

## 言語としての seki

証明の話ばかりしましたが、seki は**普通に動くプログラミング言語**です。
`lib/` の `def` は 653 個に対し `theorem` は 52 個で、数学ライブラリではありません。

- **集合 = 型** — 任意の集合 `T` は型。`v : T` は本質的に `v in T`。
  `Bool == {false, true}` は文字通りの集合等価で `refl` で証明できる。
- **stdlib は seki 自身で書かれている** — List / Tree / Option / Result / Rat を
  タグ付きペアとして構築。Rust 層は最小限のプリミティブのみ。
- **ADT と `match`**、`data` 宣言、`?` によるエラー伝播、モジュール (`import`)、
  依存型 `(x : A) -> B(x)`、Σ型、型クラス、型推論、終了性検査。
- **システム開発の機能** — 文字列、ファイル I/O、`Ref`、`Dict`、時刻、乱数、
  ビット演算、プロセス実行、JSON、TCP、HTTP (codec / client / `httpServe`)、
  原子整数と真の並行性 (`spawn` / `join` / channel)、FFI (dlopen)、
  Bytecode VM、LSP。
- **記号は単語** — `forall`, `exists`, `in`, `union`, `subset`, `times` 等。
  Unicode 記号は使わない。

型注釈も証明されます。`def f : A -> {y in B | Q y}` は「どんな引数でも結果が `Q` を
満たす」という主張で、定理と同じ prover・同じ kernel に流れます。

## 何に向くか

(a) 証明・計算・仮定の混在が避けられず、(b) その違いで誰かが行動を変える領域。

- **運用包絡線の検証** — 入力・パラメータ・初期状態がこの範囲のどこであっても
  仕様を守る、を普通に書いたコードのまま証明する
- **アシュアランスケース** — `--audit DIR` の出力が安全性論証の断片になる
  ([`examples/assurance/`](examples/assurance/))
- **システム開発の不変条件** — 金額の保存、資源の上限、締切の予算、容量計画、
  SLA の合成 ([`examples/services/`](examples/services/))
- **LLM 出力の検証層** — 確度つきの事実から推論し、結論の確度の下界と
  足りない仮定を返す

向かないもの: **数学** (答えが二値であるべきで、等級は役に立たない — Lean の
設計が正しい)。**普通のテスト** (誰も等級を読まないなら遅い assert)。

## ディレクトリ構成

```
seki/
├── src/             Rust 実装
│   ├── kernel.rs      証明項の検査 (TCB)
│   ├── interval.rs    保証された囲い (TCB)
│   ├── rewrite.rs     書換えと場合分け (TCB)
│   ├── unfold.rs      定義展開 (TCB)
│   ├── prover.rs      タクティク (探索 — 信頼しない)
│   ├── abduce.rs      足りない仮定の逆算
│   ├── confidence.rs  Fréchet 下界
│   └── stdlib.seki    自動ロードされる stdlib
├── lib/             再利用可能な seki モジュール (analysis / control / algebra / cas / numeric / ui)
├── examples/        walking-tour (01〜46) + assurance/ + services/
├── sample/          実サービス志向のミニアプリ (calc / wordcount / ledger / todo_api)
├── tests/           Rust 統合テスト + lib/ に対応する seki テスト
└── docs/            ドキュメント
```

## ドキュメント

**使用者向け**: [docs/tutorial.md](docs/tutorial.md) · [docs/cheatsheet.md](docs/cheatsheet.md) · [docs/cookbook.md](docs/cookbook.md)

**リファレンス**: [docs/language.md](docs/language.md) · [docs/proofs.md](docs/proofs.md) · [docs/spec/](docs/spec/)

**健全性の議論**: [docs/spec/06-soundness.md](docs/spec/06-soundness.md) — 何が健全で、
何がそうでなく、なぜそう設計したか。kernel が見つけた実在のバグも記録してある。

**実装者向け**: [docs/internals.md](docs/internals.md)

## この設計の弱点

5 段の格子は**正直さの上にしか成り立ちません**。各段の境界は過大主張が隠れうる
場所です。実際、開発中に見つかった例:

- `Real` に ℝ と `f64` の 2 つの読みがあり、kernel が `0.1 + 0.2 == 0.3` と
  その否定を**両方**承認していた
- `by witness` の `certify` がタクティクを実行しておらず、偽のゴールが
  「proved [sampled]」になっていた
- 整数の離散性が証明書側に無く、`if i < r` の else 枝から出る等式に証明書が
  付かなかった

防御は `--strict` と、**自分の体系を攻撃し続けること**の 2 つしかありません。
偽の命題を並べて拒否されることを確かめるテストが `tests/integration.rs` に
入っているのはそのためです。

## ライセンス

未設定 (個人プロジェクト)。

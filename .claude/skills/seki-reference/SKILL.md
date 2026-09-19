---
name: seki-reference
description: seki の構文・演算子・組込関数・タクティクの早見表と、正確な情報の探し方。.seki コードを書く/読む、または組込関数の正確なシグネチャを知りたいときに読み込む。
---

# seki 構文・組込関数リファレンス

網羅的なチートシートは既に `docs/cheatsheet.md` にある。ここでは
**最頻出の型と、組込関数の正確な情報を得る方法** をまとめる — 手で書いた
関数一覧は更新が追いつかず古くなるので、正確なシグネチャは常に
下記の「組込関数の探し方」を使うこと。

## 最頻出構文

```seki
def name := expr                          -- 値
def name : Type := expr                   -- 型注釈
def name p1 p2 := expr                    -- 関数糖衣
def name (x : Nat) (y : Nat) : Bool := …  -- 完全注釈
data Foo A = Bar | Baz Int A              -- ADT
theorem name : Prop := proof              -- 機械検証 (proof は by タクティクか証明項)
axiom name : Prop                         -- 検証なし公理

\x y -> body                -- ラムダ
let x = e in body           -- let (let x = e ? in body で Result 伝播)
if c then a else b
match e with | Some x -> ... | None -> ... | _ -> ...
forall x in S, body         -- forall (x y) in S, body で多変数 (共通ドメイン)
exists x in S, body
sigma (x : A), B            -- 依存ペア型 Σ (B は x を参照可能; 非依存なら A times B と同義)
{x in S | P}                 -- 内包集合
```

主なドメイン: `Nat` `Int` `Real` `Bool` `Str` `Unit`、`List T`、`Tree T`、
`data` で定義した ADT、列挙集合 `{1,2,3}`。

### 予約語 (識別子・仮引数名に使えない)

```
def let in where if then else
lambda fn
forall exists sigma
theorem axiom type by
data match with
import as class instance
true false
and or not notin subset union intersect diff times mod
for do
```

正本は `src/lexer.rs` の `keyword_spelling`
(`docs/spec/01-lexical.md` との一致はテストで固定されている)。
`sigma` `where` `fn` `for` `do` `diff` あたりは変数名に使いがちなので注意
— 実際 `lib/probability/` が `sigma` を仮引数に使っていて壊れていたことがある。
キーワードを仮引数位置に書くと専用のエラーが出る。

### `Set` は集合ではない (0.8.0〜)

`Set` は全集合のクラスです。**真のクラスは集合ではない**ので:

- `Set in Set` は `false`
- `{x in Set | P}` は**エラー** — 新しい集合は既存の集合からしか切り出せない
  (ZF の分出公理に相当。これが Russell の逆理を塞いでいる)

`forall A in Set, ...` のような**量化**と、型注釈としての `Set` は従来どおり。

### 評価の上限 (0.8.0〜)

停止性は warning なので、評価器に上限があります:
`SEKI_EVAL_BUDGET` (既定 5,000 万ステップ) と `SEKI_EVAL_DEPTH` (既定 2,000)。
暴走はハングや abort ではなくエラーになります。

### Int は i64 (0.8.0〜 overflow はエラー)

`Int` は論理上は ℤ だが実行時は `i64`。範囲を出る演算は
wrapping せず **runtime error** になる (`by eval` と `by algebra` が
矛盾しないようにするため)。任意精度が必要なら `lib/cas/bigint.seki`。

## CLI フラグ

```sh
seki <file>                 # 実行 (各宣言の結果を表示)
seki --check <file>         # 検証のみ (値を表示しない)
seki --audit <file>         # 各 theorem がどう検証されたかを一覧
seki --proof <file> <名前>  # その theorem の証明項を表示
seki --strict <file>        # Sound でない theorem を拒否 (SEKI_STRICT=1 でも可)
seki --strict-match <file>  # 非網羅的な match をパースエラーに
seki -e '<expr>'            # 式を1つ評価
seki -I <dir>               # lib の探索パスを追加 (繰り返し可)
```

`--strict` は「`[sampled]` / `[axiomatic]` が付く theorem をエラーにする」
— 詳細は `seki-tactics` skill と `docs/spec/06-soundness.md` §6.0。

## 組込関数の正確な情報の探し方

`docs/builtins.md` は概要だが、**確実に最新なのはビルド済みバイナリからの
直接問い合わせ**:

```sh
./target/debug/seki --list-builtins          # 全組込関数名を列挙
./target/debug/seki --builtin <name>         # 1つの詳細 (シグネチャ/副作用/性質)
./target/debug/seki --list-builtins-doc      # ドキュメント済み全件を1行ずつ
```

名前が分からず探索したいときは `--list-builtins-doc | grep <キーワード>`
が速い。個々の関数の型・副作用区分・性質 (交換法則等) を確認したいときは
`--builtin` を使う — これは `src/builtin_meta.rs` から生成されるので
ドキュメント (`docs/builtins.md`) より正確なことがある。

## タクティク一覧 (詳細は `seki-tactics` skill)

`refl` / `by eval` / `by algebra` (= `by linarith`) / `by induction` /
`by strong_induction` / `by simp [lemmas...]` / `by unfold f` / `by intros` /
`by decide` / `by auto` / `by obtain w from L [with x:=e,...]` (existential
elimination, 2026-08 追加) / `then` での合成。証明戦術の選び方や健全性の注意は
`seki-tactics` skill を読み込むこと。

## その他のドキュメント

- `docs/cheatsheet.md` — 1ページの完全な早見表 (このファイルの元ネタ)
- `docs/language.md` — 言語仕様の説明的な文章
- `docs/spec/01-lexical.md` 〜 `07-stdlib.md` — 正式な仕様書 (字句/文法/意味論/
  型システム/タクティク/健全性/stdlib)
- `docs/tutorial.md` / `docs/cookbook.md` — 学習用・「〜したい」レシピ集

これらもドキュメントである以上、実装より古くなっている可能性がある
(`seki-dev` skill 参照) — 動作を保証する主張をする前には実際に動かして
確かめること。

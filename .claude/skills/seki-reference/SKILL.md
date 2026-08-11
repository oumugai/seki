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
{x in S | P}                 -- 内包集合
```

主なドメイン: `Nat` `Int` `Real` `Bool` `Str` `Unit`、`List T`、`Tree T`、
`data` で定義した ADT、列挙集合 `{1,2,3}`。

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
`by decide` / `by auto` / `then` での合成。証明戦術の選び方や健全性の注意は
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

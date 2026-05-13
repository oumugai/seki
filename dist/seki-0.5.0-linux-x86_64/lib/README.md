# seki ライブラリ

`lib/` 以下は **再利用可能な seki モジュール群**。各サブディレクトリは
領域別に整理されている。

## 構成

```
lib/
├── algebra/                  代数構造
│   ├── axioms.seki           isAssoc / isCommutative / isMonoid / isGroup /
│   │                         isAbelianGroup / isRing / isField の汎用述語
│   ├── structures.seki       Group/Monoid/Ring/Field を data として bundle
│   │                         + アクセサ + is*On + 準同型 / 部分群 / 同型
│   ├── modular.seki          Z/nZ (Zn / addMod / mulMod / negMod / powMod / invMod)
│   ├── complex.seki          複素数 (Complex / cAdd / cMul / cConj / cDiv / cAbs)
│   ├── vector.seki           n-次元ベクトル (vadd / smul / vdot / vzero / evec)
│   └── matrix.seki           n×m 行列 (matAdd / matMul / matTranspose /
│                             matIdentity / det / nth / removeIdx / minorM)
├── analysis/                 解析学
│   ├── diff.seki             数値微分 (diffForward / diffCentral / gradient)
│   ├── integ.seki            数値積分 (台形 / Simpson / 中点)
│   ├── series.seki           Taylor 級数 (exp / sin / cos / ln) + Leibniz
│   └── limit.seki            極限・固定点・Cauchy 列・goldenRatio
├── cas/                      計算機代数 (記号計算)
│   ├── sym.seki              Sym ADT + 代数簡約 (simp1 / simplify)
│   ├── sym_dsl.seki          smart constructors (num/var/add/mul/pow/sq/...)
│   ├── calc.seki             微分・積分・代入・数値評価
│   ├── poly.seki             1 変数多項式 (演算 / GCD / 因数分解 / 判別式)
│   ├── multipoly.seki        多変数多項式 (S-多項式・モノミアル順序)
│   ├── rational.seki         有理関数 (自動約分付き)
│   ├── solve.seki            線形 / 2 次方程式
│   └── bigint.seki           任意精度整数 (デモ)
├── numeric/                  数値計算
│   ├── newton.seki           Newton 法 (根の数値解)
│   ├── gauss.seki            Gauss 消去 (連立線形方程式)
│   ├── ode.seki              Euler / RK4 / 2 変数連立 ODE
│   └── eigen.seki            2x2 / 3x3 固有値 (特性多項式 + Newton)
├── numth/                    数論
│   ├── gcd.seki              gcd / lcm / extGcd  (= numth の最も基本層)
│   └── primes.seki           素数判定 / Eratosthenes / fermatLittle
├── combinatorics/            組合せ論
│   └── basic.seki            階乗 / 二項係数 / Catalan / Fibonacci / Stirling
└── settheory/                公理的集合論
    └── axioms.seki           ZF + 選択公理・整列性・Zorn・正則性
```

## CAS の記法 (3 通り選べる)

```seki
import "cas/calc.seki"
import "cas/sym_dsl.seki"

-- 1. ADT 直接 (冗長だが構造が明確)
def e1 := SAdd (SMul (SNum 2) (SPow (SVar "x") 2)) (SNum 3)

-- 2. smart constructor DSL (短くて読みやすい)
def e2 := add (mul (num 2) (sq sx)) (num 3)

-- 3. parseSym で math notation 直書き (Rust builtin)
def e3 := parseSym "2 * pow x 2 + 3"

-- いずれも同じ Sym 値
differ "x" e3                  -- 4x (どの構築法でも同じ動作)
```

**parseSym がサポートする記法**: 整数リテラル, 変数, `+`/`-`/`*`/`/`, 単項 `-`,
`sin x` / `cos x` / `exp x` / `ln x`, `pow b n`, 括弧.

## 使い方

```seki
-- lib/ からの相対パスで自動探索される (推奨)
import "cas/sym.seki"
import "cas/calc.seki"

def x_ := SVar "x"
def f := SPow x_ 3
differ "x" f                  -- 3x^2
integS "x" f                  -- x^4 / 4
evalAt "x" 2 (differ "x" f)   -- Some 12
```

`as M` で名前空間を分けることもできる:

```seki
import "cas/sym.seki" as Sym
Sym.SNum 42                   -- 修飾アクセス
```

## ライブラリ検索パス

`import "path"` で path がローカルになければ、以下の順で探す:

1. 現ファイルのディレクトリ (従来通り)
2. `SEKI_LIB_PATH` 環境変数 (`:` 区切り)
3. `<cwd>/lib`
4. seki binary の親 `parent/lib`, `../lib`, `../../lib`
5. `~/.seki/lib`
6. CLI で渡した `-I <dir>` (複数可)

REPL では `:libpath` で現在のパスを表示、`:libpath add <dir>` で追加できる。

## 依存関係

```
numth/gcd ← algebra/modular, cas/poly
algebra/modular ← numth/primes (fermatLittle で powMod を使用)
algebra/vector ← algebra/matrix
algebra/matrix ← numeric/eigen, numeric/gauss
algebra/axioms ← algebra/structures
cas/sym ← cas/sym_dsl, cas/calc, cas/poly, cas/rational
cas/poly ← cas/multipoly, cas/rational, cas/solve (経由)
```

循環なし。各 lib は単一責務に絞ってある。

## 命名規約

- ファイル名: 小文字 + アンダースコアなし (例外: `sym_dsl.seki` は明示的 DSL を意味)
- 関数名: camelCase (`addMod`, `extGcd`, `invMod`, `powMod`, `polyGCD`)
- ADT 名: PascalCase (`Group`, `Sym`, `Eigvals`)
- 整数 GCD は **canonical `gcd`** (numth/gcd.seki に一本化、旧 `gcdInt` / `intGCD` は廃止)
- 拡張 Euclid は **`extGcd`** (旧 `extGCD` は廃止)
- 乗法逆元は **`invMod`** (旧 `modInverse` は廃止)
- modular べき乗は **`powMod`** (旧 `modPow` は廃止)

## テスト

各ライブラリの動作確認は `tests/seki/test_<name>.seki` にある。Rust 統合
テスト (`tests/integration.rs`) からも `cargo test` で実行される。

```sh
# 単独実行
cargo run --release -- tests/seki/test_cas_poly.seki

# 全テスト一括 (Rust + seki)
cargo test --release
```

## 設計指針

- **Rust への変更は最小限**: 全機能は seki 層の `data` + `match` + 再帰のみで実装。
  唯一の Rust builtin 拡張は `parseSym` (math notation → Sym 変換)。
- **examples とは独立**: `examples/01〜29` は walking-tour の demo。lib は
  本格的な再利用用。
- **theorem は test 側**: ライブラリ本体は `data` + `def` のみ。検証用
  theorem は `tests/seki/test_*.seki` に集約。

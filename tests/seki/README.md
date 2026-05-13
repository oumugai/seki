# tests/seki/ — seki ライブラリの検証

`lib/` 以下の各モジュールに対応するテストファイルが `test_<モジュール名>.seki` として格納されている。各テストは:

1. 対応する `lib/.../*.seki` を `import` で読み込む
2. `theorem ... := by eval / by algebra / ...` で性質を検証
3. 失敗があれば proof error として seki ランタイムが終了コード非 0 で報告

## ファイル一覧

| テストファイル | 対応ライブラリ | 主な検証内容 |
|---|---|---|
| `test_cas_sym.seki` | `lib/cas/sym.seki` | 簡約規則 (0/1 同一律・定数畳み込み・二重否定除去) |
| `test_cas_calc.seki` | `lib/cas/calc.seki` | 微分 (多項式・ライプニッツ・高階)・積分・FTC・線形性 |
| `test_cas_poly.seki` | `lib/cas/poly.seki` | 二項展開・多項式 GCD・有理根因数分解 |
| `test_cas_solve.seki` | `lib/cas/solve.seki` | 線形・2 次方程式・判別式 |
| `test_cas_bigint.seki` | `lib/cas/bigint.seki` | 往復 (fromInt/toInt)・加算 (基本/桁繰り上がり/i64 超え) |
| `test_algebra_axioms.seki` | `lib/algebra/axioms.seki` | 汎用公理述語 (isAssoc/isGroup/isField) + Z/nZ で各 n を一括検証 |
| `test_algebra_modular.seki` | `lib/algebra/modular.seki` | Z/nZ 演算 (addMod/mulMod/negMod/powMod/invMod) |
| `test_algebra_vector.seki` | `lib/algebra/vector.seki` | n-次元ベクトル (2-D/3-D/5-D を同じ関数で検証) |
| `test_algebra_matrix.seki` | `lib/algebra/matrix.seki` | n×m 行列 (2x2/3x3/2x3 矩形を同じ関数で検証) |
| `test_algebra_structures.seki` | `lib/algebra/structures.seki` | Group/Ring/Field 構造体 + isAbelianGroupOn / isFieldOn + 準同型 |
| `test_analysis_diff.seki` | `lib/analysis/diff.seki` | 前進/中心差分・2 階差分・多変数勾配 |
| `test_analysis_integ.seki` | `lib/analysis/integ.seki` | 台形/Simpson/中点則 + sin/exp の積分 |
| `test_analysis_series.seki` | `lib/analysis/series.seki` | exp/sin/cos/ln の Taylor + Leibniz + 調和数 |
| `test_analysis_limit.seki` | `lib/analysis/limit.seki` | 微分の極限定義・固定点反復 (Babylonian/φ)・Cauchy 列 |
| `test_algebra_complex.seki` | `lib/algebra/complex.seki` | 複素数の加減乗除・共役・絶対値・環公理 (21 個) |
| `test_cas_rational.seki` | `lib/cas/rational.seki` | 有理関数の正規化・約分・加減乗除・逆数 (12 個) |
| `test_3x3_eigenvalues.seki` | `lib/numeric/eigen.seki` | 3x3 特性多項式・Newton 法による数値固有値 (10 個) |
| `test_cas_dsl.seki` | `lib/cas/sym_dsl.seki` + `parseSym` | smart constructor DSL と parseSym で同じ Sym 値が作れること + 微分の数値検証 (10 個) |
| `test_numeric_matrix.seki` | `lib/numeric/eigen.seki` | n×n 行列式 (単位/上三角/反対称)・2x2 固有値の分類 |
| `test_numeric_ode.seki` | `lib/numeric/ode.seki` | RK4 で y'=y の y(1)≈e (誤差 1e-5)・単振動 |
| `test_numeric_newton.seki` | `lib/numeric/newton.seki` | √2・φ・∛8 の高精度近似 |
| `test_numeric_gauss.seki` | `lib/numeric/gauss.seki` | 2 元・3 元連立の解 |
| `test_numth_gcd.seki` | `lib/numth/gcd.seki` | gcd / lcm / 拡張 Euclid / mod inverse |
| `test_numth_primes.seki` | `lib/numth/primes.seki` | 素数判定 / Eratosthenes / k 番目の素数 |
| `test_numth_modular.seki` | `lib/algebra/modular.seki` + `lib/numth/primes.seki` | powMod (繰り返し二乗) / フェルマー小テスト |
| `test_combinatorics.seki` | `lib/combinatorics/basic.seki` | 階乗 / 二項係数 / Catalan / Fibonacci / Stirling |
| `test_cas_multipoly.seki` | `lib/cas/multipoly.seki` | 多変数多項式: 加算/乗算/主項/除算/S-多項式 |

## 実行方法

```sh
# 単体テスト
cargo run --release -- tests/seki/test_cas_poly.seki

# 全テスト + Rust 統合テスト (cargo test 経由)
cargo test --release

# 全 seki テストだけ走らせる
for f in tests/seki/test_*.seki; do
  echo "=== $f ==="
  cargo run --release --quiet -- "$f" 2>&1 | grep -E "proved|error" | head
done
```

## Rust integration test との関係

`tests/integration.rs` 内の `seki_lib_test_*` 関数が各 `test_*.seki` を seki binary 経由で実行し、`✓ proved` の数と `proof error` の不在を確認する。これにより `cargo test` 一発で全 seki テストも回せる。

## テスト総計

12 ファイル / **105 件** の theorem が `tests/seki/` に集約されている (検証時点)。

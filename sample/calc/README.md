# sample/calc — 検証付き電卓

多項式 `f(x) = x^3 - 2x + 5` に対して **CAS で記号微分・積分を計算** し、
結果を **`by eval` で証明 (テスト) する** 統合デモ。

## 動作確認

```sh
cargo build --release
./target/release/seki sample/calc/main.seki
```

## 出力例

```
theorem fp_at_neg2 ✓ proved
theorem fp_at_neg1 ✓ proved
...
theorem leibniz_at_5 ✓ proved

=== 検証付き電卓 ===

対象多項式 f(x) = x^3 - 2x + 5

f'(x) (記号計算):
SSub (SMul (SNum 3) (SPow (SVar "x") 2)) (SNum 2)
                          ^^^^^^^^^^^^
                          3 * x^2 - 2 を表す Sym ADT

値テーブル (x = -2 .. 2):
  x=-2:  f=1  f'=10  f''=-12
  x=-1:  f=6  f'=1   f''=-6
  x=0:   f=5  f'=-2  f''=0
  x=1:   f=4  f'=1   f''=6
  x=2:   f=9  f'=10  f''=12
```

## 何が検証されているか

| 定理 | 内容 |
|---|---|
| `fp_at_*` (5 個) | `f'(x) = 3x^2 - 2` を 5 点 (-2, -1, 0, 1, 2) で確認 |
| `fpp_at_*` (3 個) | `f''(x) = 6x` を 3 点で確認 |
| `ftc_at_*` (3 個) | 微積分の基本定理: `d/dx (∫f dx) == f` を 3 点で確認 |
| `leibniz_at_*` (3 個) | ライプニッツ規則: `(g·h)' == g'·h + g·h'` を 3 点で確認 |

合計 **14 個の定理** が `by eval` で証明されます。すべて pass しなければ
`seki` は exit 1 で終了するので、これは **テストランナー** としても機能
します。

## 他言語との比較

| 機能 | seki | Python+SymPy | Lean+Mathlib | Mathematica |
|---|---|---|---|---|
| 記号微分 | ✅ | ✅ | 🟡 | ✅ |
| 値での検証 | ✅ `by eval` | テストフレームワーク要 | ✅ | テスト要 |
| 数値評価 | ✅ | ✅ | 🟡 | ✅ |
| 同一ファイルで完結 | ✅ | ✅ (テスト含めると微妙) | ❌ | ✅ |
| 失敗時に CI で fail | ✅ exit 1 | ✅ | ✅ | 🟡 |
| 依存ゼロ | ✅ | ❌ (SymPy + pytest) | ❌ | ❌ |

seki の差別化点: **言語そのもの** に CAS と証明が組み込まれており、
単一バイナリで動く。

## 集合論的解釈

- `Sym` は ZF 風 disjoint union: `Sym = Num ∪ Var ∪ Sym×Sym×Tag ∪ ...`
- `parseSym "..."` はパース後のタグ付きペア (順序対) を生成
- `evalAt "x" v f` は `f` を `x := v` で置換評価 → `Option Int`
- 各 theorem は `forall x in {ある集合}, P x` を `by eval` で
  決定 (有限列挙)

## コードの位置

- `main.seki` — エントリポイント (約 100 行)

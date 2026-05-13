# sample/ledger — 不変条件付き帳簿

取引履歴 (JSON) を読み込み、各取引を適用しながら **集合論的不変条件** を
検証する帳簿システム。seki の **証明 + JSON + Dict + ファイル I/O** の
統合例。

## 動作確認

```sh
cargo build --release
./target/release/seki sample/ledger/main.seki sample/ledger/transactions.json
```

## 入力フォーマット

`transactions.json`:
```json
[
  {"from": "alice", "to": "bob",   "amount": 100},
  {"from": "bob",   "to": "carol", "amount": 30},
  ...
]
```

各アカウントの初期残高は `seedBalance = 1000` (コード内で定数)。

## 出力例

```
theorem transfer_preserves_total ✓ proved
theorem transfer_preserves_nonneg ✓ proved
theorem transfer_concrete_bal_100 ✓ proved

ledger: sample/ledger/transactions.json
  accounts: 3   initial total: 3000
  transactions: 5

final balances:
  carol : 1060
  bob : 1030
  alice : 910

initial total: 3000
final   total: 3000
✓ 総和保存の不変条件 OK (transfer_preserves_total で証明済)
```

## 何が証明 / 検証されているか

### 静的 (定理証明 — 全ての Int 値で成立)

```seki
theorem transfer_preserves_total
  : forall (a b amt) in Int,
      (a - amt) + (b + amt) == a + b
  := by algebra
```

`by algebra` は無限の Int に対する **多項式恒等式** を健全に証明するので、
これは「すべての可能な取引で総和が保存される」ことの **完全な証明** です。

```seki
-- 単変数の Phase 5 SMT-lite で具体例を検証
theorem transfer_concrete_bal_100
  : linarithProve "amt" ["100 >= amt", "amt > 0"] "100 - amt >= 0"
      == Some true
  := by eval
```

線形整数 SMT で「残高 100 のとき amt ≤ 100 かつ amt > 0 なら出金後も
非負」を証明。

### 動的 (実行時不変条件チェック)

- `applyTx` は `amt > 0` を実行時に検査 → `Err` を返す
- `applyTx` は `fbal >= amt` を実行時に検査 → 不足時は `Err`
- 最終的に `initialTotal == finalTotal` を確認 → 成立しなければ exit 3

## 集合論的解釈

各概念は集合として表現可能:

| 概念 | 集合論的型 |
|---|---|
| アカウント名 | `String` |
| 残高 | `{x in Int \| x >= 0}` (refinement) |
| 取引 | `String × String × Pos` |
| 帳簿状態 | `Dict String Int ⊂ String × Int` (関数的) |
| 取引履歴 | `List Tx` |

**不変条件**:
- 関数的: 各 (account, balance) ペアで account がユニーク (Dict が保証)
- 総和保存: `forall ledger states l₀, l₁: total(l₀) = total(l₁)` (定理証明済)
- 非負: `forall a in accounts l: balance(a, l) >= 0` (実行時検査)

## 失敗ケースのデモ

`transactions.json` を以下のように書き換えると失敗ケースを確認できます:

```json
[
  {"from": "alice", "to": "bob", "amount": 99999}
]
```

→ `TRANSACTION FAILED: overdraft: alice has 1000, needs 99999`

```json
[
  {"from": "alice", "to": "bob", "amount": -10}
]
```

→ `TRANSACTION FAILED: non-positive amount: -10`

両方ともプログラムは exit 2 で終わり、不変条件違反を入力データのレベルで
報告します。

## このサンプルが示す seki の強み

| 軸 | 内容 |
|---|---|
| **証明** | 総和保存を **無限の Int 領域で** `by algebra` 証明 |
| **健全な refinement** | `linarithProve` で残高関連の線形不等式を symbolic に決定 |
| **データ処理** | JSON parse → ADT → Dict → 集約 |
| **エラー型** | `Result E A` で失敗を型に表現、`?` の代替パターン |
| **CLI** | `args` で入力パス可変 |
| **同一ファイル** | 証明・実装・I/O が一体 |

> *Lean だと証明はできても JSON I/O が面倒。Python だと JSON I/O は楽だが*
> *総和保存の証明は手書きコメント止まり。seki はどちらも自然にできる。*

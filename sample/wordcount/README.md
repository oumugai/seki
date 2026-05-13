# sample/wordcount — テキスト解析 CLI

ファイルから単語頻度を集計し、上位 N 件を出力する実用ツール。
seki の **文字列操作 + Dict + ソート + 並列でない実用パイプライン** を示します。

## 動作確認

```sh
cargo build --release

# デフォルト (sample.txt, top 10)
./target/release/seki sample/wordcount/main.seki

# パスと top N を指定
./target/release/seki sample/wordcount/main.seki sample/wordcount/sample.txt 5

# 任意のテキストファイルに対して
./target/release/seki sample/wordcount/main.seki README.md 20
```

## 出力例

```
wordcount: sample/wordcount/sample.txt
  total tokens: 58  unique: 32

top 5:
  8  is
  8  the
  4  seki
  3  dog
  3  fox
```

## 処理パイプライン

```
readFile path
  └─> strSplit "\n"        -- 行
       └─> map (strSplit " ")  -- 単語
            └─> foldr append nil    -- flatten
                 └─> map strToLower
                      └─> filter (非空)
                           └─> foldl addWord (emptyDict ())  -- Dict 集計
                                └─> dictKeys → map kvOf      -- (word, count) リスト
                                     └─> insertion sort by count desc
                                          └─> takeN
                                               └─> forEach println
```

各 step が **集合論的に解釈可能** です:
- 各単語: 集合 `String` の元
- 頻度マップ: `Dict String Int ⊂ String × Int` の関数的部分集合
- ソート済リスト: 元の集合の **置換** (要素は同じ、順序が異なる)

## 引数の扱い

| 第 1 引数 | 入力ファイルパス | デフォルト `sample/wordcount/sample.txt` |
| 第 2 引数 | top N の数値 | デフォルト 10 (パース失敗時も 10) |

CLI 引数は seki の `args : List String` から取得。失敗時は `Err` を `Result`
で返し、`exit 1` で終了。

## このサンプルが示すこと

| 機能 | 用途 |
|---|---|
| `readFile` | 入力ファイル読込 (Result 型でエラー表現) |
| `strSplit` / `strTrim` / `strToLower` | テキスト前処理 |
| `Dict` | O(1) 頻度集計 |
| `foldl` / `foldr` / `map` / `filter` | 関数型データ処理 |
| 自前 `insertDesc` / `sortByCountDesc` / `takeN` | seki 内ですべて記述 |
| `args` | CLI 引数 |
| `exit` | エラーで終了 |

seki だけで **依存ゼロ** にテキスト解析パイプラインが書けることを実演。

## 他言語との比較

```python
# Python 同等
from collections import Counter
import sys
path = sys.argv[1] if len(sys.argv) > 1 else "sample.txt"
n = int(sys.argv[2]) if len(sys.argv) > 2 else 10
with open(path) as f:
    words = [w.lower() for w in f.read().split() if w]
c = Counter(words)
for word, count in c.most_common(n):
    print(f"  {count}  {word}")
```

行数比: seki ~80 行 vs Python ~10 行。違いの主因:
- seki には `Counter` / `most_common` がない (Dict + 自前 sort を書く)
- 改行 + 空白の二段分割を明示

性能比: seki tree-walking → Python `Counter` (C 実装) には桁違いに負ける。
このサンプルは「実用的に書けるか」のデモであって性能ベンチではない。

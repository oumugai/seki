# seki Builtin API Reference

このドキュメントは **Rust 層で実装された全 builtin** をカテゴリ別にまとめた
リファレンスです。seki 自身で書かれた stdlib (List/Tree/Option/Result 等) は
含みません — それらは `src/stdlib.seki` を直接読んでください。

凡例: 関数シグネチャ中の `IO X` は「X を返すが副作用を持つ」マーカ
(現状 `IO A == A`、Phase 5 以降は型検査時のサンプル評価をスキップ)。

各カテゴリは集合論的解釈 + 実装ノートを含みます。

---

## 1. 型 (Atomic Sets / Type Constructors)

集合論的に: いずれも「その要素のすべて」を表す集合。

| 名前 | 種類 | 意味 |
|---|---|---|
| `Nat`     | Set    | 自然数の集合 ℕ |
| `Int`     | Set    | 整数の集合 ℤ |
| `Real`    | Set    | IEEE-754 f64 |
| `Bool`    | Set    | `{false, true}` (列挙集合として実装) |
| `String`  | Set    | 有限文字列の集合 |
| `Prop`    | Set    | 命題 = `Bool` のエイリアス |
| `Set`     | Set    | universe (集合の集合) |
| `IO : Set -> Set`    | Function (恒等) | `IO A == A` のマーカ |
| `List : Set -> Set`  | Function | `List T` = T 上の有限リストの集合 |
| `Tree : Set -> Set`  | Function | `Tree T` = T 上の二分木の集合 |

---

## 2. 基礎操作 (Primitives)

### タプル

```
fst        : (A × B) -> A
snd        : (A × B) -> B
pair       : A -> B -> (A × B)
__tupproj  : Int -> Tuple -> Any         -- 内部用 (match 脱糖)
```

### コレクション

```
card       : Set -> Int                  -- 列挙集合の濃度
```

### エラー

```
error      : String -> Never              -- 例外を発生
```

---

## 3. 文字列演算

集合論的に: `String = ⋃ₙ Char^n`、操作はすべて pure。

| 名前 | シグネチャ | 例 |
|---|---|---|
| `strLen` | `String -> Nat` | `strLen "abc" = 3` |
| `strConcat` | `String -> String -> String` | `strConcat "a" "b" = "ab"` |
| `strContains` | `String -> String -> Bool` | `strContains "ll" "hello" = true` |
| `strStartsWith` | `String -> String -> Bool` | |
| `strEndsWith` | `String -> String -> Bool` | |
| `strIndexOf` | `String -> String -> Int` | not found returns `-1` |
| `strReplace` | `String -> String -> String -> String` | (old, new, src) |
| `strSplit` | `String -> String -> List String` | (delim, src) |
| `strJoin` | `String -> List String -> String` | (sep, parts) |
| `substring` | `Int -> Int -> String -> String` | (start, len, src) |
| `strToUpper` / `strToLower` / `strTrim` | `String -> String` | |
| `strChars` | `String -> List String` | UTF-8 文字ごとに分解 |
| `intToStr` / `realToStr` | `Numeric -> String` | |
| `strToInt` / `strToReal` | `String -> Option Numeric` | パース失敗で `None` |
| `toStr` | `Any -> String` | 任意の Value を表示文字列に |

---

## 4. 数値演算

```
intToReal  : Int -> Real
floor      : Real -> Int                  -- Int 入力はそのまま
ceil       : Real -> Int
round      : Real -> Int
sqrt       : Real -> Real                 -- 負数は実行時エラー
pow        : Numeric -> Numeric -> Numeric
```

### ビット演算 (Int = i64 上)

```
bitAnd / bitOr / bitXor  : Int -> Int -> Int
bitNot                   : Int -> Int
bitShl / bitShr          : Int -> Int -> Int   -- shift 0..63
popcount                 : Int -> Int          -- 立っているビット数
```

### 乱数 (xorshift64* PRNG, シード可)

```
randomSeed   : Int -> IO Unit              -- シード固定で再現性
randomInt    : Unit -> IO Int
randomRange  : Int -> Int -> IO Int        -- [lo, hi)
randomFloat  : Unit -> IO Real             -- [0, 1)
```

---

## 5. I/O

### 標準入出力

```
print     : Any -> IO Unit                 -- 改行なし
println   : Any -> IO Unit
eprint    : Any -> IO Unit                 -- stderr
eprintln  : Any -> IO Unit
readLine  : Unit -> IO (Option String)     -- EOF で None
```

### ファイル

すべて `Result E A` を返してエラーを型に表現:

```
readFile    : String -> IO (Result String String)
writeFile   : String -> String -> IO (Result Unit String)
appendFile  : String -> String -> IO (Result Unit String)
fileExists  : String -> IO Bool
removeFile  : String -> IO (Result Unit String)
```

### プロセス / 環境

```
args        : List String                  -- CLI 引数
getEnv      : String -> IO (Option String)
exit        : Int -> Never                  -- 戻らない
execShell   : String -> IO (Result String String)
runCommand  : String -> List String -> IO (Int × String × String)
                                            -- (exit_code, stdout, stderr)
```

### 時刻

```
nowSecs / nowMillis / nowMicros  : Unit -> IO Int  -- UNIX epoch
monotonicMillis                  : Unit -> IO Int  -- プログラム開始からの ms
sleep                            : Int -> IO Unit  -- ms ブロッキング
```

---

## 6. 可変参照 (Ref)

集合論的に: `Ref A` = 「A 値を保持する記憶セルの集合」。
等価性は cell identity (内容ではない)。

```
mkRef      : A -> IO (Ref A)
readRef    : Ref A -> IO A
writeRef   : Ref A -> A -> IO Unit
```

---

## 7. 辞書 (Dict)

集合論的に: `Dict K V` ⊂ `K × V`、関数的部分集合 (各 K は高々一度)。
**関数的更新** (insert / remove は新しい Dict を返す)。

```
emptyDict   : Unit -> Dict K V
dictInsert  : K -> V -> Dict K V -> Dict K V
dictGet     : K -> Dict K V -> Option V
dictMember  : K -> Dict K V -> Bool
dictRemove  : K -> Dict K V -> Dict K V
dictSize    : Dict K V -> Int
dictKeys    : Dict K V -> List K
dictValues  : Dict K V -> List V
```

キーは `Int` / `Bool` / `String` / `Tuple` of those に限る。

---

## 8. 並行性

### Atomic Int (Arc-backed, Send + Sync)

```
atomicNew   : Int -> IO Atomic
atomicGet   : Atomic -> IO Int
atomicSet   : Atomic -> Int -> IO Unit
atomicAdd   : Atomic -> Int -> IO Int      -- 返り値は old value
atomicCas   : Atomic -> Int -> Int -> IO Bool  -- (atomic, old, new), 成否
spawnAtomicAdd : Atomic -> Int -> Int -> IO Unit  -- (atomic, delta, delay_ms)
threadId    : Unit -> IO String
```

### クロージャベーススレッド

```
spawn  : (() -> A) -> IO (Thread A)
join   : Thread A -> IO A                  -- 結果を取得、ブロック
parMap : (A -> B) -> List A -> IO (List B) -- 並列写像、順序保持
```

### mpsc Channel

```
chanNew   : Unit -> IO (Channel A)
chanSend  : Channel A -> A -> IO (Result Unit String)
chanRecv  : Channel A -> IO (Result A String)
chanClose : Channel A -> IO Unit
```

---

## 9. ネットワーキング

### TCP (blocking)

```
tcpListen  : String -> Int -> IO (Result Listener String)
tcpAccept  : Listener -> IO (Result Socket String)
tcpConnect : String -> Int -> IO (Result Socket String)
tcpRead    : Socket -> Int -> IO (Result String String)  -- 最大 N bytes
tcpWrite   : Socket -> String -> IO (Result Unit String)
tcpClose   : Socket | Listener -> IO Unit
```

### HTTP

```
urlParse           : String -> Result (String × Int × String) String
                     -- (host, port, path)
httpParseRequest   : String -> Result HttpRequest String
httpFormatResponse : HttpResponse -> String
httpGet            : String -> IO (Result String String)  -- HTTPS 非対応
```

`HttpRequest` / `HttpResponse` は `src/stdlib.seki` の ADT 定義。
`httpServe : Int -> (HttpRequest -> HttpResponse) -> IO (Result Unit String)`
は stdlib のヘルパとして提供。

---

## 10. FFI (Linux / macOS のみ)

`dlopen` を `extern "C"` で直接呼ぶ。外部 Rust クレートには依存しない。

```
ffiLoad        : String -> IO (Result FfiLib String)     -- .so / .dylib をロード
ffiCallIntInt  : FfiLib -> String -> Int    -> IO (Result Int String)
                                                          -- C: int (int)
ffiCallStrInt  : FfiLib -> String -> String -> IO (Result Int String)
                                                          -- C: int (const char *)
ffiClose       : FfiLib -> IO Unit
```

**注意**: FFI は安全性検査をすり抜けます。信頼できないコードでは使用しないこと
(`SECURITY.md` 参照)。

---

## 11. JSON

```
jsonParse   : String -> Result Json String
jsonEncode  : Json -> String
```

`Json` ADT (`src/stdlib.seki`):
```
data Json
  = JNull
  | JBool Bool
  | JNum Real
  | JStr String
  | JArr (List Json)
  | JObj (List (String × Json))
```

stdlib ヘルパ: `jsonField`、`jsonAsString` / `jsonAsNumber` / `jsonAsBool` /
`jsonAsArr`、`jInt` / `jStr` / `jBool` / `jArr` / `jObj` / `jNull`。

---

## 12. 計算機代数 (CAS)

```
parseSym  : String -> Sym
            -- math 記法を Sym ADT (タグ付きペア) にパース
            -- サポート: 数値、変数、+ - * /、unary -、sin/cos/exp/ln/pow
```

`Sym` ADT と `differ` / `integ` / `evalAt` 等は `lib/cas/` 配下に seki で実装。

---

## 13. Bytecode VM

```
vmEval     : String -> Result Value String   -- パース + コンパイル + 実行
vmTime     : Int -> String -> Int            -- N 回実行の所要 ms
vmCompiles : String -> Bool                  -- コンパイル可能か判定
```

VM の対応範囲: 算術 + 比較 + 論理 (短絡) + `let` + `if`。
ラムダ / 関数適用 / 集合 / match は AST eval にフォールバック。

---

## 14. SMT-lite (線形整数算術)

一変数線形整数の決定手続き (Fourier-Motzkin の縮退版)。

```
linarithProve   : String -> List String -> String -> Option Bool
linarithCounter : String -> List String -> String -> Option Int
```

`linarithProve "x" ["x > 0", "x < 100"] "x + 1 > 0"` → `Some true`

仮説と目標は線形整数不等式の文字列。範囲外 (非線形 / 多変数) は `None`。

---

## カテゴリ別 builtin 数

| カテゴリ | 個数 |
|---|---|
| 型 / 型コンストラクタ | 10 |
| 基礎操作 | 5 |
| 文字列演算 | 19 |
| 数値演算 + ビット演算 + 乱数 | 13 |
| I/O (file + std + process + time) | 18 |
| Ref + Dict | 11 |
| 並行性 + Atomic + Channel + parMap + spawn | 16 |
| TCP + HTTP | 10 |
| FFI | 4 |
| JSON | 2 |
| CAS | 1 |
| Bytecode VM | 3 |
| SMT-lite | 2 |
| その他 (parseSym, mkRef, etc.) | 余り |
| **合計** | **120** |

---

## 関連ドキュメント

- `src/stdlib.seki` — seki 自身で書かれた追加 stdlib (List, Tree, Json,
  HttpRequest, helpers)
- `lib/` — オプショナルライブラリ (algebra, analysis, cas, numeric, numth,
  combinatorics, settheory)
- `docs/language.md` — 言語仕様
- `docs/cheatsheet.md` — 構文早見表
- `docs/cookbook.md` — ユースケース別レシピ

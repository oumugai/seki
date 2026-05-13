# 8. Rust 層と seki 層の分割原則

seki は **コンパイラとランタイムが Rust で書かれた言語** ですが、**標準
ライブラリと再利用ライブラリは seki 自身で書かれている** ハイブリッドです。
このページは「何が Rust に、何が seki に居るべきか」の原則を記録します。

## 8.1 原則 (decision rule)

ある機能 `F` を実装するとき、以下のいずれかに **該当しない** なら **seki**
に書く:

1. `F` は seki の **言語コアの定義** に関わる (集合論的演算、`forall`、
   `match` の脱糖、型推論など)
2. `F` には **OS との直接対話が必要** (file I/O、ネットワーク、time、
   random、process、FFI、stdin/stdout)
3. `F` は **interior mutability** を必要とする (`Ref`、`Dict`、`Atomic`、
   `Channel`)
4. `F` は **メタレベル** (parser/VM/SMT) で seki 自身を扱う
5. `F` を seki で書くと **桁違いに遅く / 不正確になる** (UTF-8 文字
   操作、大規模 JSON パース、暗号、ベクトル化された数値)

それ以外はすべて **seki に書く**。

## 8.2 Rust 層の builtin 分類 (Phase 5 時点、120 個)

### A. 集合論カーネル (10 個)
| 名前 | 理由 |
|---|---|
| `+`, `-`, `*`, `/`, `mod`, `==`, `<`, ... | 算術・比較 (組込) |
| `and`, `or`, `not` | Bool 演算 (組込) |
| `union`, `intersect`, `in`, `subset`, ... | 集合演算 (組込) |
| `pair`, `fst`, `snd` | タプル原始 |
| `card` | 列挙集合の濃度 |
| `error` | 制御フロー (例外的) |
| `__tupproj` | 内部: match の脱糖 |
| `IO`, `List`, `Tree` | 型レベルセット構築子 |

### B. システム I/O (~32 個)
| カテゴリ | 名前 |
|---|---|
| ファイル | `readFile`, `writeFile`, `appendFile`, `fileExists`, `removeFile` |
| stdio | `print`, `println`, `eprint`, `eprintln`, `readLine` |
| OS | `getEnv`, `exit`, `args`, `threadId` |
| プロセス | `execShell`, `runCommand` |
| 時刻 | `nowSecs`, `nowMillis`, `nowMicros`, `monotonicMillis`, `sleep` |
| 乱数 | `randomSeed`, `randomInt`, `randomRange`, `randomFloat` |
| ネット | `tcpListen`, `tcpAccept`, `tcpConnect`, `tcpRead`, `tcpWrite`, `tcpClose`, `httpGet` |
| FFI | `ffiLoad`, `ffiCallIntInt`, `ffiCallStrInt`, `ffiClose` |

注: `urlParse` / `httpParseRequest` / `httpFormatResponse` は Phase 8 で
**seki 側に移動** (`src/stdlib.seki`)。OS と直接やりとりしないので Rust
にいる必要がない — 文字列原子操作の上に純粋な seki で構築できる。

### C. 並行性プリミティブ (~13 個)
| カテゴリ | 名前 |
|---|---|
| Ref | `mkRef`, `readRef`, `writeRef` |
| Dict | `emptyDict`, `dictInsert`, `dictGet`, `dictMember`, `dictRemove`, `dictSize`, `dictKeys`, `dictValues` |
| Atomic | `atomicNew`, `atomicGet`, `atomicSet`, `atomicAdd`, `atomicCas`, `spawnAtomicAdd` |
| Channel | `chanNew`, `chanSend`, `chanRecv`, `chanClose` |
| Thread | `spawn`, `join`, `parMap` |

### D. メタレベル (8 個)
| 名前 | 役割 |
|---|---|
| `parseSym` | seki 自身のパーサで Sym ADT を構築 |
| `vmEval`, `vmTime`, `vmCompiles` | Bytecode VM access |
| `linarithProve`, `linarithCounter` | SMT-lite 決定手続き |

### E. 性能クリティカル (2 個)
| 名前 | 理由 |
|---|---|
| `jsonParse`, `jsonEncode` | hand-rolled パーサ、~300 行 Rust。seki で書くと遅い + デバッグが大変 |

### F. 文字列の原子操作 (12 個)
| 名前 | 理由 |
|---|---|
| `strLen` | UTF-8 文字数のカウントは Rust の native iter |
| `strConcat` | String 内部 buffer の効率的合成 |
| `strChars` | UTF-8 → List String (文字単位) |
| `substring` | UTF-8 boundary の正しい切り出し |
| `strSplit` | UTF-8 aware な delimiter 検索 |
| `strReplace` | 大量置換の効率 |
| `strIndexOf` | UTF-8 char index を返すため Rust native |
| `strToUpper` / `strToLower` / `strTrim` | Unicode case folding は Rust の `char::to_uppercase` 等に委譲 |
| `intToStr` / `realToStr` / `strToInt` / `strToReal` / `toStr` | 数値フォーマット / パース |

### G. 数値プリミティブ (~13 個)
| 名前 | 理由 |
|---|---|
| `intToReal`, `floor`, `ceil`, `round`, `sqrt`, `pow` | Real 機械演算 |
| `bitAnd`, `bitOr`, `bitXor`, `bitNot`, `bitShl`, `bitShr`, `popcount` | ビット操作 (i64 native) |

## 8.3 seki 層に「降りた」もの

Phase 1-5 で一度 Rust に置かれたが、Phase 7-8 で seki に降ろしたもの:

### 文字列の合成 (Phase 7、4 個)

- `strContains needle hay` ← `strIndexOf needle hay >= 0`
- `strStartsWith pre s` ← `substring 0 (strLen pre) s == pre`
- `strEndsWith suf s` ← `substring (strLen s - strLen suf) (strLen suf) s == suf`
- `strJoin sep xs` ← `foldr` over `xs` with `strConcat`

### URL / HTTP コーデック (Phase 8、3 個)

- `urlParse` — `strStartsWith` + `strIndexOf` + `strSplit ":"` + `strToInt` で
  scheme/host/port/path に分解。
- `httpParseRequest` — `strIndexOf "\r\n\r\n"` で header / body 分離、
  `strSplit "\n"` で line、各 line を `strIndexOf ":"` で name/value に分解。
- `httpFormatResponse` — `match` で `HttpResponse` を分解、`foldr` で
  header 行を整形、Content-Length は `any` + `append` で自動挿入。
- `httpStatusReason` (新規ヘルパ) — status → reason phrase のマッピング。

合計 **7 個** の builtin を seki に降ろした。Rust 側 LoC: 約 250 行削減。
性能影響: HTTP 系は I/O 律速、文字列合成系はマイクロベンチで誤差程度。

## 8.4 seki 層に居るデータ構造 (再掲)

| 型 | 集合論的解釈 | 場所 |
|---|---|---|
| `List(A)` | `{nil} ∪ A × List(A)` | `src/stdlib.seki` |
| `Tree(A)` | `{leaf} ∪ Tree(A) × A × Tree(A)` | `src/stdlib.seki` |
| `Option(A)` | `{nothing} ⊔ A` | `src/stdlib.seki` |
| `Result(E, A)` | `E ⊔ A` | `src/stdlib.seki` |
| `Rat` | `ℤ × ℤ⁺` | `src/stdlib.seki` |
| `Json` | `disjoint union` | `src/stdlib.seki` |
| `HttpRequest` / `HttpResponse` | tuple型 | `src/stdlib.seki` |
| `Sym` | 記号式 AST | `lib/cas/sym.seki` |
| `BigInt` | ℤ (canonical) | `lib/cas/bigint.seki` |
| `Polynomial` | 係数リスト | `lib/cas/poly.seki` |
| 群 / 環 / 体 | 代数構造 bundle | `lib/algebra/structures.seki` |
| `Vec(T)` / `Mat(T)` | ベクトル / 行列 | `lib/algebra/vector.seki` 等 |

## 8.5 「Rust に置きたくなる衝動」のチェックリスト

新機能を Rust に書くべきか迷ったら以下を確認:

- [ ] seki だけでは技術的に書けないか? (OS 呼出が必要 / interior mutability が必要)
- [ ] seki で書いたらユーザビリティが本当に下がる?  (10x 以上の差?)
- [ ] 既存の Rust builtin の合成では実現できない?
- [ ] 性能テスト (`vmTime` 等) で問題が確認できた?

すべて "yes" の場合のみ Rust 候補。それ以外は **デフォルト seki**。

## 8.6 例: HTTP の seki 移動 (Phase 8 で完了)

`httpParseRequest` / `httpFormatResponse` / `urlParse` は Phase 5 まで
Rust 実装でしたが、Phase 8 で seki に移動しました。

- **移動前**: Rust ~250 行 (`b_url_parse`, `b_http_parse_request`,
  `b_http_format_response`)
- **移動後**: seki ~130 行 (`src/stdlib.seki` の HTTP セクション)
- **性能**: HTTP 系は I/O 律速のため誤差程度
- **可読性**: 集合論セマンティクスで HttpRequest の構造が seki から見える

実例 (`urlParse`):

```seki
def urlParse := \url ->
    let parseRest = \scheme rest ->
        let default_port = if scheme == "https" then 443 else 80 in
        let slash = strIndexOf "/" rest in
        ...
    in
    if strStartsWith "http://" url then parseRest "http" ...
    else if strStartsWith "https://" url then parseRest "https" ...
    else Err ...
```

これは Rust 版より読みやすく、`strContains` / `strIndexOf` /
`substring` などの確立されたプリミティブの上で構築できることを示しています。

## 8.7 例: vmEval は Rust にあるが seki に移せるか?

`vmEval` は内部で bytecode compiler + VM を実行する。これらは seki 自身を
評価するメタレベルなので、seki で書こうとすると bootstrap 問題が発生する
(seki で seki の VM を書いて、その VM で seki を実行するには…)。

**判断**: Rust に残すべき。「seki で seki」は学術的興味はあるが、現実的
には循環。

## 8.8 まとめ

原則: **seki で書けるなら seki に書く。例外は OS access, 並行性, メタ,
本物の性能要件のみ**。

この原則を Phase 5 まで一部破っていた (`strContains` 等)。
Phase 7 で 4 個を seki 側に移動し、残りも適宜整理予定。

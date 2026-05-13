# 10. Builtin Metadata — Rust → seki への構造情報

> *seki でテストが「点ではなく振る舞い全体」で書けるためには、その「振る舞い」を*
> *誰かが宣言する必要がある。Phase 9 では Rust 側の builtin にそれを書いた。*

## 10.1 動機

`docs/spec/09-testing.md` で seki のテストは **集合論的に書くべき** と論じた。
「全 x について P が成り立つ」を主張するためには、`P` が何かを知っている必要が
ある。たとえば `strConcat` についての property test を書きたければ:

- それは **どんな集合からどんな集合への関数** なのか?
- **commutative か? associative か? identity element はあるか?**
- **副作用は? 全 (total) か?**

これらの情報を Phase 9 で各 Rust 実装に **メタデータ** として付与した。
テストは Rust の主張をクエリし、実装と照合できる。

## 10.2 メタデータの形

`src/builtin_meta.rs` の `BuiltinMeta` 構造体:

```rust
pub struct BuiltinMeta {
    pub name:        &'static str,
    pub signature:   &'static str,         // "strLen : String -> Nat"
    pub domain:      &'static str,         // "String"
    pub codomain:    &'static str,         // "Nat"
    pub effect:      Effect,
    pub properties:  &'static [&'static str],
    pub doc:         &'static str,
}

pub enum Effect {
    Pure,         // 副作用なし、決定的
    PartialPure,  // 純関数だが panic 可能 (sqrt 負数等)
    Read,         // OS から読む (file/env/clock/RNG)
    Write,        // OS に書く (file/stdout/exit/socket send)
    Mutate,       // seki の可変状態 (Ref/Dict/Atomic)
    Concurrent,   // 並行性 (spawn/channel/TCP)
    Unsafe,       // FFI / 信頼境界外
    Meta,         // コンパイラ/VM/SMT メタ
}
```

すべて `'static` で compile-time data — runtime cost ゼロ。

## 10.3 seki 側からの照会 API

8 個の builtin が `eval.rs` に追加された:

| 関数 | シグネチャ |
|---|---|
| `builtinDoc`        | `String -> Option String` |
| `builtinSig`        | `String -> Option String` |
| `builtinEffect`     | `String -> Option String` |
| `builtinDomain`     | `String -> Option String` |
| `builtinCodomain`   | `String -> Option String` |
| `builtinProperties` | `String -> List String` |
| `builtinHasProperty`| `String -> String -> Bool` |
| `builtinNames`      | `Unit -> List String` (全 documented builtin) |

すべて `Option` 経由なので、メタデータが無い builtin (低優先) は `None` を返し、
テストでは「**全てのコア builtin が metadata を持つ**」を property として書ける。

## 10.4 構造的性質の語彙

`properties` フィールドに使う string は **自由形式** だが、よく使う規約:

### 代数構造

| 性質 | 意味 |
|---|---|
| `total` | 入力ドメインで失敗しない |
| `commutative` | `f(a,b) == f(b,a)` |
| `associative` | `f(f(a,b),c) == f(a,f(b,c))` |
| `idempotent` | `f(x,x) == x` または `f(f(x)) == f(x)` |
| `involutive` | `f(f(x)) == x` |
| `self-inverse` | `op(a, a) == identity` |
| `monotonic` | `x <= y => f(x) <= f(y)` |
| `injective` | `f(x) == f(y) => x == y` |
| `left-identity-X` / `right-identity-X` | 単位元 |
| `absorbs-with-X` | `f(x, X) == X` (零元) |

### List/String 関連

| 性質 | 意味 |
|---|---|
| `length-additive` | `len (f a b) == len a + len b` |
| `length-preserving` | `len (f x) == len x` |
| `length-equals-strLen` | `length (strChars s) == strLen s` |

### 逆関数 / 関係

| 性質 | 意味 |
|---|---|
| `right-inverse-of-X` | `f (X y) == y` |
| `roundtrip-with-X` | 双方向: `f (X y) == y` かつ `X (f y) == y` |

### 効果

| 性質 | 意味 |
|---|---|
| `functional-update` | 入力を変更せず新しい値を返す (Dict 操作等) |
| `destructive` | OS リソースを破壊する (removeFile 等) |
| `never-returns` | 関数は戻らない (`exit`, `error`) |
| `partial` | 失敗可能性あり |

## 10.5 CLI

```sh
$ seki --list-builtins-doc
[Pure       ] fst : (A × B) -> A
[Pure       ] snd : (A × B) -> B
[Pure       ] strLen : String -> Nat
[Pure       ] strConcat : String -> String -> String
[Read       ] readFile : String -> IO (Result String String)
[Write      ] writeFile : String -> String -> IO (Result Unit String)
[Concurrent ] spawn : (() -> A) -> IO (Thread A)
[Unsafe     ] ffiLoad : String -> IO (Result FfiLib String)
[Meta       ] parseSym : String -> Sym
...

$ seki --builtin strConcat
strConcat : String -> String -> String
  Effect:     Pure
  Domain:     String, String
  Codomain:   String
  Properties: total, associative, left-identity-empty, right-identity-empty, length-additive
  Doc:        Concatenation. (String, strConcat, "") is a monoid.
```

LSP / IDE 統合は将来課題だが、CLI レベルで既にドキュメント検索が可能。

## 10.6 Property test の書き方

宣言と実装を **両方** 検査する。

```seki
import "test/runner.seki"

-- Rust が "self-inverse" と宣言していることを確認
def test_xor_self_inverse_declared :=
    assertTrue (builtinHasProperty "bitXor" "self-inverse")
        "bitXor must declare self-inverse"

-- そして実装が本当に self-inverse である
def xor_self := \x -> bitXor x x
def test_xor_self_inverse_holds :=
    forAllInList [0 - 100, 0 - 7, 0, 1, 7, 42, 9999]
        (\x -> assertEq 0 (xor_self x))
```

ドキュメンタリと実装が **食い違ったらテストが落ちる**。これにより:

1. **ドキュメント-実装の同期** が CI で担保される
2. リファクタで性質が壊れたら気づける
3. メタデータが「飾り」ではなく「実行される仕様」になる

実例 `sample/calc/tests_metadata.seki` — **33 個のメタデータ駆動 test** が:
- 全 core builtin が signature/doc/effect を持つことを確認
- bitXor / bitAnd / bitNot / strConcat / strLen / intToReal の宣言された性質
  を実装がすべて満たすことを確認
- effect 分類 (Pure / Read / Write / Concurrent / Unsafe / Meta) が
  正しいことを確認
- 全 documented builtin に signature/effect があることを確認 (網羅性)

## 10.7 集合論的解釈

`BuiltinMeta` 自体を集合として見ると:

```
BuiltinMeta = Names × Sig × Domain × Codomain × Effect × P(Properties) × Doc
```

各 builtin は `BuiltinMeta` 集合の元として **catalog** される。
seki のテストは:

```
∀ b ∈ catalog,
   "self-inverse" ∈ b.properties
   ⟹ ∀ x ∈ b.domain, b(x, x) == identity_of(b)
```

のような meta-level な claim を formalize できる(本記事末の `tests_metadata.seki`
の各 case はこの形)。

## 10.8 今後の方向

- **TypeDescriptor enum** を Domain / Codomain に与えて精緻化 (現状は string)
- **Refinement の properties → linarith の自動生成** — `properties: ["pos"]`
  と書いたら、その builtin が `Pos` 集合を尊重することを自動で linarith で
  証明させる
- **LSP hover で `--builtin <name>` の出力を表示** — IDE 統合
- **新しい builtin を追加する PR ガイドライン**: catalog entry を要求

## 10.9 まとめ

- Phase 9 で Rust 側 builtin に **集合論的・構造的メタデータ** を付与
- seki 側 8 個の照会 API でテストから利用可能
- CLI `--builtin <name>` / `--list-builtins-doc` で確認可能
- `sample/calc/tests_metadata.seki` で **33 個の metadata-driven property test** を実装
- メタデータが「**実行される仕様**」になり、ドキュメントが嘘をつかなくなった

これで seki は「ある関数の振る舞い全体を、Rust 側の宣言と seki 側の実装の
両方で **集合論的に** 記述・検証できる」言語になった。

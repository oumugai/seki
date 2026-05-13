# 3. 操作意味論

seki は **集合論的セマンティクス** を基盤とする。型 = 集合、命題 = 集合の
要素ではなく Bool 値、forall/exists は集合上の量化。

このページは seki 0.5.0 の実装に対応する **non-formal な操作意味論** を
記述します。完全に形式化された言語意味論 (Wright-Felleisen 型 progress &
preservation のような) は Phase 8 で `docs/spec/formal/` 配下に整備予定。

## 3.1 値の領域

```
Value := Unit
       | Int(i64)             -- 64-bit 符号付き整数
       | Real(f64)             -- IEEE-754 double
       | Bool(true | false)
       | Str(UTF-8 String)
       | Set(SetVal)           -- 後述
       | Tuple([Value, ...])
       | Closure(params, body, env)
       | Builtin(name, arity)
       | Ref(Arc<Mutex<Value>>)
       | Dict(Arc<Mutex<Map>>)
       | Handle(Socket | Listener | Atomic | Thread | Channel | FfiLib)
```

`Closure` と `Builtin` は callable な値。`Handle` は I/O escape hatch
(OS リソースへの opaque token)。

## 3.2 集合の領域

```
SetVal := Enum([Value, ...])                   -- 列挙
       | Comp(var, domain, predicate, env)     -- 内包
       | Atomic(Nat | Int | Real | Bool | String | Universe)
       | Arrow(from, to)                       -- 関数型
       | DepArrow(binder, from, to_expr, env)  -- 依存型
       | Product([SetVal, ...])                -- 直積
       | ListOf(SetVal)                        -- リスト集合
       | TreeOf(SetVal)                        -- 木集合
```

## 3.3 評価規則 (informal)

```
EVAL[Int(n)]        = Int(n)
EVAL[Real(r)]       = Real(r)
EVAL[Bool(b)]       = Bool(b)
EVAL[Str(s)]        = Str(s)
EVAL[Var(x)]        = env(x)  (else globals(x))

EVAL[\(p1, p2, ...) -> body] = Closure(params, body, env)

EVAL[f arg]         = apply(EVAL[f], EVAL[arg])

EVAL[a + b]         = numericPlus(EVAL[a], EVAL[b])
                     -- Int / Real 自動昇格
EVAL[a * b]         = numericMul(...)
EVAL[a == b]        = Bool(valueEq(EVAL[a], EVAL[b]))
EVAL[a in S]        = Bool(member(EVAL[a], EVAL[S]))

EVAL[if c then t else e] =
    case EVAL[c] of
      Bool(true)  -> EVAL[t]
      Bool(false) -> EVAL[e]
      _           -> RuntimeError

EVAL[let x = v in body] = EVAL[body with env extended by x = EVAL[v]]

EVAL[forall x in S, P] =
    let xs = enumerate(S) in
    Bool(every x in xs: EVAL[P with env[x ↦ x]] == true)

EVAL[exists x in S, P] = similar but with `any`

EVAL[match v with patterns] = match-first that pattern
```

## 3.4 関数適用 (apply)

```
apply(Closure(params, body, env), arg) =
    if len(params) >= 1:
        let env' = env extended by params[0] = arg
        if len(params) == 1: EVAL[body in env']
        else: Closure(params[1..], body, env')   -- partial app
    else: RuntimeError

apply(Builtin(name, arity, func), arg) =
    accumulate args; when full, call func(args)
```

`spawn` と `parMap` は apply で特殊ディスパッチされ、`EvalCtx` を新スレッド
にクローンして渡す。

## 3.5 集合要素判定 (member)

```
member(v, Enum([e1, ..., en]))     = any i: valueEq(v, ei)
member(v, Comp(x, dom, pred, env)) = member(v, dom) AND
                                     EVAL[pred in env[x ↦ v]] == true
member(v, Atomic(Nat))             = isNat(v) AND v >= 0
member(v, Atomic(Int))             = isInt(v)
member(v, Atomic(Real))            = isReal(v) OR isInt(v)  -- Int ⊂ Real
member(v, Atomic(Bool))            = isBool(v)
member(v, Arrow(from, to))         = isCallable(v)
                                      AND (sample-check) for many a in from:
                                          member(apply(v, a), to)
member(v, DepArrow(x, from, to_expr, env)) =
    if to_expr 形が `IO X`: return true (Phase 5 IO 強制)
    else: similar to Arrow with substitution to_expr[x := a]
member(v, Product([T1, ..., Tn]))  = isTuple(v) AND len(v) == n
                                     AND for each i: member(v[i], Ti)
member(v, ListOf(T))               = isList(v) AND for each x in v: member(x, T)
member(v, TreeOf(T))               = isTree(v) AND for each value in v: member(value, T)
```

**注**: `Arrow` と `DepArrow` の member 判定は sample-based。
これが現状の依存型が「健全でない」最大の理由。

## 3.6 列挙 (enumerate)

```
enumerate(Enum(xs))               = xs
enumerate(Comp(x, dom, pred, env)) = filter (\v -> EVAL[pred[x:=v]] == true) (enumerate dom)
                                     up to COMP_FUEL (= 10000)
enumerate(Atomic(Bool))           = [false, true]
enumerate(Atomic(Nat))            = [0, 1, ..., SAMPLE_BOUND-1]
enumerate(Atomic(Int))            = [-SAMPLE_BOUND, ..., SAMPLE_BOUND-1]
enumerate(Atomic(Real))           = error (不可能)
enumerate(Arrow / DepArrow)       = error
enumerate(ListOf / TreeOf)        = error (有限性が保証されない)
```

`SAMPLE_BOUND` のデフォルトは `200`。これが `forall n in Nat, P(n)` のような
無限ドメインに対する `by eval` の射程を決める (Phase 8 で SMT 委譲 + induction
を組み合わせて伸ばす予定)。

## 3.7 副作用と参照透明性

seki の **コア** は参照透明 (純粋関数型) だが、以下の **escape hatch** を持つ:

1. `IO` 系 builtins (println, readFile, writeFile, ...) — 順序評価
2. `Ref A` 経由の可変状態
3. `Dict K V` — 関数的更新だが、内部は `Arc<Mutex>` で同期可能
4. `Atomic` / `Channel` / `spawn` / `parMap` — 並行性
5. `Handle` (Socket / Listener / FfiLib) — OS リソース
6. `ffiCall*` — 任意 C 関数呼出 (完全 unsafe、`SECURITY.md` 参照)

これらが現れる関数は **`IO`** マーカ (Phase 5+) で型注釈可能。

## 3.8 評価戦略

**eager** (call-by-value, strict)。lazy 評価のサポートはない (Phase 8+ で
`lazy` キーワードを検討)。

例外: `and` / `or` / `=>` は短絡評価される。

## 3.9 末尾呼び出し / 再帰

seki は **末尾呼出最適化 (TCO) を行わない** ため、深い再帰はスタックを使う。

例: `length` を 5000 要素のリストに適用するとデフォルトスレッドのスタック
オーバーフローする (Phase 7 で iterative `length` 提供予定)。

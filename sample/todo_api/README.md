# sample/todo_api — JSON REST API

シンプルな TODO サービスの HTTP REST API。**HTTP + JSON + Ref<Dict> +
ルーティング** を統合したミニアプリ。

## エンドポイント

| メソッド | パス | 内容 | レスポンス |
|---|---|---|---|
| `GET`    | `/`            | ホームページ (HTML) | 200 |
| `GET`    | `/healthz`     | ヘルスチェック     | 200 JSON `{"status":"ok"}` |
| `GET`    | `/todos`       | 全件取得           | 200 JSON `[{...}, ...]` |
| `GET`    | `/todos/{id}`  | 1 件取得           | 200 JSON / 404 |
| `POST`   | `/todos`       | 作成 (body: `{"title":"..."}`) | 201 JSON / 400 |
| `DELETE` | `/todos/{id}`  | 削除               | 204 / 404 |

## 動作確認

### Dry-run (推奨 — ネットワーク不要)

```sh
cargo build --release
./target/release/seki sample/todo_api/main.seki
```

引数なしで実行すると **fake HttpRequest を 6 件** ハンドラに通して結果を
表示する dry-run モードになります。CI でロジック検証に使えます。
出力例:

```
todo_api: dry-run (pass --serve to start the HTTP server)

POST /todos {title:buy milk}:
HTTP/1.0 201 Created
Content-Type: application/json
Content-Length: 27

{"id":1,"title":"buy milk"}

...
```

### 実サーバ起動

```sh
./target/release/seki sample/todo_api/main.seki --serve 8088
# 別 terminal で:
curl http://127.0.0.1:8088/todos
curl -X POST -d '{"title":"buy milk"}' http://127.0.0.1:8088/todos
curl http://127.0.0.1:8088/todos/1
curl -X DELETE http://127.0.0.1:8088/todos/1
```

`--serve` がなければ dry-run、あれば実サーバとして listen します。
ポート番号は `--serve` の後ろに任意で指定 (デフォルト 8088)。

## アーキテクチャ

```
                                ┌─────────────────┐
                                │ store : Ref(Dict│
                                │  Int → String)  │
                                └────────▲────────┘
                                         │
                  ┌──────────────────────┼──────────────┐
                  │ handler              │              │
                  │ HttpRequest          │   readRef    │
                  │   → HttpResponse     │   writeRef   │
                  │                      │              │
TCP socket ──→ httpParseRequest ──→ handler ──→ httpFormatResponse ──→ TCP socket
   │                  ▲                                       │
   │                  │                                       │
   └── httpServe loop (stdlib): tcpAccept → read → handle → write → close
```

## コードの要点

### 状態管理

```seki
def store := mkRef (emptyDict ())
def nextId := mkRef 1
```

`Ref<Dict Int String>` で in-memory store。シングルスレッドなので Mutex
は不要 (内部的に `Arc<Mutex>` で守られているが、HTTP リクエストごとに
順次処理されるため race condition なし)。

### ルーティング

```seki
def handler := \req ->
    let m = reqMethod req in
    let p = reqPath req in
    if m == "GET" and p == "/todos" then handleList req
    else if m == "GET" and strStartsWith "/todos/" p then handleGet req
    else if m == "POST" and p == "/todos" then handleCreate req
    else if m == "DELETE" and strStartsWith "/todos/" p then handleDelete req
    else httpNotFound ()
```

method × path のパターンマッチで if 連鎖。

### JSON 入出力

```seki
-- 出力: TODO → Json ADT → エンコード文字列
def todoToJson := \id title ->
    JObj [("id", JNum (intToReal id)), ("title", JStr title)]

-- 入力: JSON ボディ → Result String String (title 抽出)
def parseCreateBody := \body ->
    match jsonParse body with
    | Err e -> Err (strConcat "bad JSON: " e)
    | Ok doc ->
        match jsonField doc "title" with
        | Some (JStr t) -> Ok t
        | _ -> Err "missing 'title' field"
```

stdlib の `Json` ADT を使い、エラーを `Result` で表現する典型パターン。

### URL パスからの ID 抽出

```seki
def parsePathId := \prefix path ->
    let plen = strLen prefix in
    if strLen path < plen + 1 then Err "missing id"
    else if substring 0 plen path == prefix then
        let rest = substring plen (strLen path - plen) path in
        match strToInt rest with
        | Some n -> Ok n
        | None   -> Err (strConcat "bad id: " rest)
    else
        Err "path does not match"
```

完全に seki だけ — URL routing library なし。

## このサンプルが示す seki の強み

| 軸 | 内容 |
|---|---|
| **HTTP I/O** | `httpServe` + `tcpListen/Accept/...` を stdlib で組み合わせ |
| **JSON 入出力** | `jsonParse` + `jsonEncode` + `Json` ADT が seki 自身で構築済み |
| **状態管理** | `Ref<Dict>` で in-memory store (Phase 4 後は thread-safe) |
| **エラーハンドリング** | 全 endpoint が `Result` 経由でエラーを 400/404 にマップ |
| **テスト容易性** | dry-run モードで実サーバなしにロジック検証可能 |
| **依存ゼロ** | 単一バイナリ + stdlib のみ。フレームワーク不要 |

> *Python+Flask だと依存が増え、Lean だと HTTP server は書けず、Rust だと*
> *最初の API までボイラープレートが多い。seki は ~120 行で動く REST サーバ。*

## 制限事項 (現状)

- **シングルスレッド** — 1 リクエストずつ処理。複数同時接続は捌けない。
  Phase 8+ で worker pool / `parMap` ベースの並行サーバを検討。
- **HTTP/1.0** — Connection: keep-alive 非対応。1 リクエスト 1 接続。
- **TLS なし** — HTTPS が必要なら nginx/Caddy などの reverse proxy 経由。
- **タイムアウト/再試行なし** — 信頼できる内部用途向け。

production には Phase 8 以降の改善が必要ですが、コンセプト実証 + 学習目的に
は十分です。

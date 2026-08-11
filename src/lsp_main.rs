//! seki-lsp: a minimal Language Server Protocol implementation.
//!
//! Phase 5 deliverable: editor integration via diagnostics, plus a minimal
//! Phase 6 `textDocument/hover`. Specifically:
//!
//!   * Listens on stdio for LSP JSON-RPC framed messages.
//!   * Responds to `initialize` with our capabilities (text sync + hover).
//!   * Tracks open documents via `textDocument/didOpen` / `didChange` /
//!     `didSave` notifications.
//!   * On every change, parses the document and publishes
//!     `textDocument/publishDiagnostics` with any parse error.
//!   * On `textDocument/hover`, looks up the identifier under the cursor —
//!     by raw text, not scope-aware AST resolution (see `handle_hover`) —
//!     against the Rust builtin catalog and the document's own top-level
//!     `def`/`theorem`/`axiom` names.
//!
//! Out of scope (Phase 6+ goals):
//!   * completion, goto-definition, code actions
//!   * scope-aware hover (a lambda param that shadows a same-named
//!     top-level `def` currently shows the top-level one — see below)
//!   * incremental parsing
//!   * full evaluation / type-check based diagnostics
//!   * multi-file projects
//!
//! Implementation notes:
//!   * JSON-RPC framing: `Content-Length: N\r\n\r\n<N bytes JSON>`
//!   * JSON: hand-rolled minimal parser/encoder for the small message
//!     subset we need.  Keeps the zero-dependency promise.

use std::collections::HashMap;
use std::io::{Read, Write, BufRead, BufReader};

fn main() {
    let mut server = Server::new();
    server.run();
}

/// One open document indexed by its LSP URI.
struct Document {
    text: String,
    /// Monotonic version counter from the client.
    version: i64,
}

struct Server {
    documents: HashMap<String, Document>,
    shutdown_requested: bool,
}

impl Server {
    fn new() -> Self {
        Server { documents: HashMap::new(), shutdown_requested: false }
    }

    fn run(&mut self) {
        let stdin = std::io::stdin();
        let mut reader = BufReader::new(stdin.lock());
        loop {
            match read_message(&mut reader) {
                Ok(Some(msg)) => self.handle_message(&msg),
                Ok(None) => break,  // EOF
                Err(_) => break,    // protocol error — just exit
            }
            if self.shutdown_requested {
                // After 'shutdown', the next 'exit' notification stops us.
                // We've already replied to shutdown; just keep reading for exit.
            }
        }
    }

    fn handle_message(&mut self, msg: &str) {
        // Parse the JSON envelope just enough to dispatch.  Look for `id`
        // (request) and `method`.  Notifications have no `id`.
        let method = extract_string(msg, "method").unwrap_or_default();
        let id = extract_id(msg);
        match method.as_str() {
            "initialize" => self.handle_initialize(id),
            "initialized" => { /* notification, no reply */ }
            "shutdown" => {
                self.shutdown_requested = true;
                send_response(id, "null");
            }
            "exit" => std::process::exit(0),
            "textDocument/didOpen" => self.handle_did_open(msg),
            "textDocument/didChange" => self.handle_did_change(msg),
            "textDocument/didSave" => self.handle_did_save(msg),
            "textDocument/didClose" => self.handle_did_close(msg),
            "textDocument/hover" => self.handle_hover(msg, id),
            other => {
                // Unknown request: reply with a minimal error so the client
                // doesn't hang waiting for a response.
                if let Some(id) = id {
                    let body = format!(
                        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"error\":{{\"code\":-32601,\"message\":\"method not found: {}\"}}}}",
                        id, other
                    );
                    write_raw(&body);
                }
            }
        }
    }

    fn handle_initialize(&self, id: Option<i64>) {
        // Declare capabilities: full text sync + publish diagnostics.
        let result = "{\
\"capabilities\":{\
\"textDocumentSync\":1,\
\"hoverProvider\":true\
},\
\"serverInfo\":{\"name\":\"seki-lsp\",\"version\":\"0.1.0\"}\
}";
        send_response(id, result);
    }

    fn handle_did_open(&mut self, msg: &str) {
        let uri = match extract_nested_string(msg, "textDocument", "uri") {
            Some(u) => u,
            None => return,
        };
        let text = extract_nested_string(msg, "textDocument", "text").unwrap_or_default();
        let version = extract_nested_int(msg, "textDocument", "version").unwrap_or(0);
        self.documents.insert(uri.clone(), Document { text: text.clone(), version });
        self.publish_diagnostics(&uri, &text);
    }

    fn handle_did_change(&mut self, msg: &str) {
        let uri = match extract_nested_string(msg, "textDocument", "uri") {
            Some(u) => u,
            None => return,
        };
        // Full text sync (capability 1): the message contains a single
        // ContentChange with the new full text in `.text`.
        let text = match extract_content_change_text(msg) {
            Some(t) => t,
            None => return,
        };
        let version = extract_nested_int(msg, "textDocument", "version").unwrap_or(0);
        self.documents.insert(uri.clone(), Document { text: text.clone(), version });
        self.publish_diagnostics(&uri, &text);
    }

    fn handle_did_save(&mut self, msg: &str) {
        // Some clients include the saved text; we recompute diagnostics if so.
        if let Some(uri) = extract_nested_string(msg, "textDocument", "uri") {
            if let Some(doc) = self.documents.get(&uri) {
                let text = doc.text.clone();
                self.publish_diagnostics(&uri, &text);
            }
        }
    }

    fn handle_did_close(&mut self, msg: &str) {
        if let Some(uri) = extract_nested_string(msg, "textDocument", "uri") {
            self.documents.remove(&uri);
            // Clear diagnostics for the closed file.
            self.publish_diagnostics(&uri, "");
        }
    }

    /// `textDocument/hover`: look up the identifier under the cursor.
    ///
    /// This is deliberately **not scope-aware** — it's a textual lookup,
    /// not an AST-resolved one. It checks, in order: (1) the Rust builtin
    /// catalog (`builtin_meta`), (2) the document's own top-level
    /// `def`/`theorem`/`axiom` names. A lambda parameter or `let`-bound
    /// name that happens to share text with a top-level `def` will show
    /// that `def`'s info instead of "no info" — an accepted limitation for
    /// a hand-rolled, zero-dependency server (real scope resolution would
    /// need a bound-variable-aware walk of the whole AST). Replies with a
    /// `null` result (no hover) when nothing matches, which LSP clients
    /// render as "nothing to show" rather than an error.
    fn handle_hover(&self, msg: &str, id: Option<i64>) {
        let respond_none = || send_response(id, "null");
        let Some(uri) = extract_nested_string(msg, "textDocument", "uri") else {
            return respond_none();
        };
        let Some(doc) = self.documents.get(&uri) else {
            return respond_none();
        };
        let Some(line0) = extract_nested_int(msg, "position", "line") else {
            return respond_none();
        };
        let Some(char0) = extract_nested_int(msg, "position", "character") else {
            return respond_none();
        };
        let Some((word, start, end)) = word_at(&doc.text, line0 as usize, char0 as usize) else {
            return respond_none();
        };
        let Some(markdown) = hover_markdown(&word, &doc.text) else {
            return respond_none();
        };
        let result = format!(
            "{{\"contents\":{{\"kind\":\"markdown\",\"value\":{}}},\
              \"range\":{{\"start\":{{\"line\":{},\"character\":{}}},\
              \"end\":{{\"line\":{},\"character\":{}}}}}}}",
            encode_string(&markdown),
            line0, start, line0, end
        );
        send_response(id, &result);
    }

    /// Parse `source` and publish any error as a single diagnostic.
    fn publish_diagnostics(&self, uri: &str, source: &str) {
        let diags = compute_diagnostics(source);
        let mut json = String::from("[");
        for (i, d) in diags.iter().enumerate() {
            if i > 0 { json.push(','); }
            json.push_str(&format!(
                "{{\"range\":{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}},\"severity\":1,\"source\":\"seki\",\"message\":{}}}",
                d.line, d.col, d.line, d.col + d.length, encode_string(&d.message)
            ));
        }
        json.push(']');
        let body = format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":{}}}}}",
            encode_string(uri), json
        );
        write_raw(&body);
    }
}

#[derive(Debug)]
struct Diagnostic {
    /// LSP coordinates are 0-based.
    line: usize,
    col: usize,
    length: usize,
    message: String,
}

/// Run seki's parser and turn any error into LSP-style diagnostics.
/// Currently emits at most one diagnostic per parse pass — the parser
/// fails fast.  Phase 6 could split into multiple by parsing decl-by-decl.
fn compute_diagnostics(source: &str) -> Vec<Diagnostic> {
    match seki::parse_program(source) {
        Ok(_) => Vec::new(),
        Err(seki::SekiError::Parse(msg)) => {
            // Try to extract line/col from the error message.  seki errors
            // start with "[line:col] " when they have location info.
            let (line, col) = parse_loc_prefix(&msg).unwrap_or((0, 0));
            vec![Diagnostic { line, col, length: 1, message: msg }]
        }
        Err(e) => {
            vec![Diagnostic { line: 0, col: 0, length: 1, message: format!("{}", e) }]
        }
    }
}

fn parse_loc_prefix(msg: &str) -> Option<(usize, usize)> {
    // Pattern: "[L:C] rest"   or   "[line N:M] rest"
    let s = msg.trim_start();
    let s = s.strip_prefix('[')?;
    let close = s.find(']')?;
    let inner = &s[..close];
    let mut parts = inner.split(':');
    let l: usize = parts.next()?.trim().parse().ok()?;
    let c: usize = parts.next()?.trim().parse().ok()?;
    // LSP uses 0-based positions; seki reports 1-based.
    Some((l.saturating_sub(1), c.saturating_sub(1)))
}

/// True for characters that continue an identifier once started (matches
/// `src/lexer.rs`'s rule: start with alpha/`_`, continue with
/// alphanumeric/`_`/`'`).
fn is_ident_continue(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Extract the identifier under (or immediately left of) `(line0, char0)`
/// — both 0-based, as LSP positions are. Returns `(word, start_char,
/// end_char)` on the same line so the caller can echo back a hover range.
/// Purely textual (character classes only, no lexer/AST involved) — good
/// enough for "what identifier is the cursor on", which is all hover needs.
fn word_at(text: &str, line0: usize, char0: usize) -> Option<(String, usize, usize)> {
    let line = text.split('\n').nth(line0)?;
    let line = line.strip_suffix('\r').unwrap_or(line);
    let chars: Vec<char> = line.chars().collect();
    if chars.is_empty() {
        return None;
    }
    // A cursor sitting right after the last character of a token (the
    // common case: LSP reports the position *after* where you last
    // clicked/typed) should still resolve to that token.
    let mut i = char0.min(chars.len() - 1);
    if !is_ident_continue(chars[i]) {
        if i > 0 && is_ident_continue(chars[i - 1]) {
            i -= 1;
        } else {
            return None;
        }
    }
    let mut start = i;
    while start > 0 && is_ident_continue(chars[start - 1]) {
        start -= 1;
    }
    let mut end = i + 1;
    while end < chars.len() && is_ident_continue(chars[end]) {
        end += 1;
    }
    if !(chars[start].is_alphabetic() || chars[start] == '_') {
        return None; // starts with a digit (or similar) — not an identifier
    }
    Some((chars[start..end].iter().collect(), start, end))
}

/// Render markdown hover content for `word`, or `None` if it's neither a
/// known builtin nor a top-level name declared in `source`.
fn hover_markdown(word: &str, source: &str) -> Option<String> {
    if let Some(m) = seki::builtin_meta::builtin_meta(word) {
        let props = if m.properties.is_empty() {
            String::new()
        } else {
            format!("\n\n**Properties:** {}", m.properties.join(", "))
        };
        return Some(format!(
            "```seki\n{}\n```\n**Effect:** {} · **Domain:** {} · **Codomain:** {}\n\n{}{}",
            m.signature, m.effect.name(), m.domain, m.codomain, m.doc, props
        ));
    }
    // Fall back to the document's own top-level `def`/`theorem`/`axiom`
    // names — not scope-aware, see `handle_hover`'s doc comment.
    let decls = seki::parse_program(source).ok()?;
    for d in &decls {
        match &d.decl {
            seki::ast::Decl::Def { name, ty, value } if name == word => {
                return Some(match ty {
                    Some(t) => format!("```seki\ndef {} : {}\n```", name, t),
                    None => format!("```seki\ndef {} := {}\n```", name, value),
                });
            }
            seki::ast::Decl::Theorem { name, prop, proof } if name == word => {
                return Some(format!(
                    "```seki\ntheorem {} : {}\n    := {}\n```",
                    name, prop, proof
                ));
            }
            seki::ast::Decl::Axiom { name, prop } if name == word => {
                return Some(format!("```seki\naxiom {} : {}\n```", name, prop));
            }
            _ => {}
        }
    }
    None
}

// ---------- minimal JSON-RPC framing -----------------------------------

fn read_message<R: BufRead>(reader: &mut R) -> std::io::Result<Option<String>> {
    let mut content_length: Option<usize> = None;
    loop {
        let mut header = String::new();
        let n = reader.read_line(&mut header)?;
        if n == 0 {
            return Ok(None);  // EOF
        }
        let trimmed = header.trim_end_matches(|c| c == '\r' || c == '\n');
        if trimmed.is_empty() {
            break;  // End of headers
        }
        if let Some(rest) = trimmed.strip_prefix("Content-Length:") {
            content_length = rest.trim().parse().ok();
        }
        // Other headers (Content-Type) are ignored.
    }
    let n = match content_length {
        Some(n) => n,
        None => return Ok(None),
    };
    let mut buf = vec![0u8; n];
    reader.read_exact(&mut buf)?;
    Ok(Some(String::from_utf8_lossy(&buf).into_owned()))
}

fn write_raw(body: &str) {
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let _ = write!(out, "Content-Length: {}\r\n\r\n{}", body.as_bytes().len(), body);
    let _ = out.flush();
}

fn send_response(id: Option<i64>, result_json: &str) {
    if let Some(id) = id {
        let body = format!(
            "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{}}}",
            id, result_json
        );
        write_raw(&body);
    }
}

// ---------- shallow JSON extraction (good enough for fixed shapes) -----
//
// We don't pull in a JSON crate (zero-deps).  These extractors work on
// the *known* LSP message shapes we handle.  They are *not* general
// JSON parsers — only the fields we need, with limited escape handling.

fn extract_string(msg: &str, key: &str) -> Option<String> {
    let needle = format!("\"{}\":", key);
    let pos = msg.find(&needle)?;
    let after = &msg[pos + needle.len()..].trim_start();
    if !after.starts_with('"') { return None; }
    extract_string_value(after)
}

fn extract_string_value(s: &str) -> Option<String> {
    let bytes = s.as_bytes();
    if !s.starts_with('"') { return None; }
    let mut out = String::new();
    let mut i = 1;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'"' {
            return Some(out);
        } else if c == b'\\' && i + 1 < bytes.len() {
            match bytes[i + 1] {
                b'"' => out.push('"'),
                b'\\' => out.push('\\'),
                b'/' => out.push('/'),
                b'n' => out.push('\n'),
                b'r' => out.push('\r'),
                b't' => out.push('\t'),
                b'u' => {
                    if i + 6 > bytes.len() { return None; }
                    let hex = std::str::from_utf8(&bytes[i + 2..i + 6]).ok()?;
                    let cp = u32::from_str_radix(hex, 16).ok()?;
                    if let Some(c) = char::from_u32(cp) { out.push(c); }
                    i += 6;
                    continue;
                }
                other => out.push(other as char),
            }
            i += 2;
        } else {
            out.push(c as char);
            i += 1;
        }
    }
    None
}

fn extract_id(msg: &str) -> Option<i64> {
    let pos = msg.find("\"id\":")?;
    let rest = msg[pos + 5..].trim_start();
    // Accept either an integer or a string ID (we always reply with int).
    let end = rest.find(|c: char| c == ',' || c == '}')?;
    let chunk = rest[..end].trim().trim_matches('"');
    chunk.parse::<i64>().ok()
}

/// Find `outer` key, then `inner` key inside its object value.
fn extract_nested_string(msg: &str, outer: &str, inner: &str) -> Option<String> {
    let needle = format!("\"{}\":", outer);
    let pos = msg.find(&needle)?;
    let after = &msg[pos + needle.len()..];
    // Scope the search to the balanced object that follows.
    let scope_end = match_balanced(after, '{', '}')?;
    extract_string(&after[..scope_end + 1], inner)
}

fn extract_nested_int(msg: &str, outer: &str, inner: &str) -> Option<i64> {
    let needle = format!("\"{}\":", outer);
    let pos = msg.find(&needle)?;
    let after = &msg[pos + needle.len()..];
    let scope_end = match_balanced(after, '{', '}')?;
    let scoped = &after[..scope_end + 1];
    let key_pat = format!("\"{}\":", inner);
    let kp = scoped.find(&key_pat)?;
    let rest = scoped[kp + key_pat.len()..].trim_start();
    let end = rest.find(|c: char| c == ',' || c == '}')?;
    rest[..end].trim().parse::<i64>().ok()
}

/// For `didChange`: the message has `"contentChanges":[{"text":"..."}]`.
fn extract_content_change_text(msg: &str) -> Option<String> {
    let cc = msg.find("\"contentChanges\":")?;
    let after = &msg[cc..];
    // First "text":"..." after the contentChanges key
    extract_string(after, "text")
}

/// Walk balanced delimiters starting at the first occurrence in `s`.
/// Returns the index of the matching close char (relative to s), or None.
fn match_balanced(s: &str, open: char, close: char) -> Option<usize> {
    let bytes = s.as_bytes();
    let open = open as u8;
    let close = close as u8;
    let mut i = 0;
    while i < bytes.len() && bytes[i] != open { i += 1; }
    if i >= bytes.len() { return None; }
    let mut depth = 0i32;
    let mut in_str = false;
    while i < bytes.len() {
        let c = bytes[i];
        if in_str {
            if c == b'\\' && i + 1 < bytes.len() { i += 2; continue; }
            if c == b'"' { in_str = false; }
        } else {
            match c {
                b'"' => in_str = true,
                x if x == open => depth += 1,
                x if x == close => {
                    depth -= 1;
                    if depth == 0 { return Some(i); }
                }
                _ => {}
            }
        }
        i += 1;
    }
    None
}

fn encode_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

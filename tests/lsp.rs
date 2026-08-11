//! Integration tests for `seki-lsp` (src/lsp_main.rs), driven as a real
//! subprocess over its actual stdio JSON-RPC framing — the same protocol a
//! real editor speaks. No JSON crate (project is zero-dependency): we frame
//! messages by hand and assert on substrings of the raw response body,
//! which is enough since we control exactly what each request should
//! produce.

use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Child, ChildStdin, Command, Stdio};

struct Lsp {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
}

impl Lsp {
    fn start() -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_seki-lsp"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn seki-lsp");
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Lsp { child, stdin, stdout }
    }

    fn send(&mut self, body: &str) {
        write!(self.stdin, "Content-Length: {}\r\n\r\n{}", body.len(), body).unwrap();
        self.stdin.flush().unwrap();
    }

    /// Read one framed message and return its raw JSON body.
    fn recv(&mut self) -> String {
        let mut content_length = None;
        loop {
            let mut header = String::new();
            let n = self.stdout.read_line(&mut header).expect("read header");
            assert!(n > 0, "seki-lsp closed stdout unexpectedly");
            let trimmed = header.trim_end_matches(['\r', '\n']);
            if trimmed.is_empty() {
                break;
            }
            if let Some(rest) = trimmed.strip_prefix("Content-Length:") {
                content_length = rest.trim().parse::<usize>().ok();
            }
        }
        let n = content_length.expect("no Content-Length header");
        let mut buf = vec![0u8; n];
        self.stdout.read_exact(&mut buf).expect("read body");
        String::from_utf8(buf).expect("utf8 body")
    }

    fn initialize(&mut self) {
        self.send(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#);
        let resp = self.recv();
        assert!(resp.contains("\"hoverProvider\":true"), "got: {}", resp);
    }

    fn did_open(&mut self, uri: &str, text: &str) {
        let escaped = text.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n");
        let msg = format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"{}","text":"{}","version":1}}}}}}"#,
            uri, escaped
        );
        self.send(&msg);
        let _diagnostics = self.recv(); // publishDiagnostics notification
    }

    fn hover(&mut self, uri: &str, line: usize, character: usize) -> String {
        let msg = format!(
            r#"{{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":{{"textDocument":{{"uri":"{}"}},"position":{{"line":{},"character":{}}}}}}}"#,
            uri, line, character
        );
        self.send(&msg);
        self.recv()
    }

    fn finish(mut self) {
        let _ = self.stdin.write_all(b""); // drop stdin to let it see EOF
        drop(self.stdin);
        let status = self.child.wait().unwrap_or_else(|_| {
            let _ = self.child.kill();
            self.child.wait().unwrap()
        });
        // A clean EOF exit is fine either way; we only care that it didn't
        // panic/crash while handling our requests (checked via responses).
        let _ = status;
    }
}

#[test]
fn hover_shows_builtin_metadata() {
    let mut lsp = Lsp::start();
    lsp.initialize();
    let uri = "file:///t_builtin.seki";
    lsp.did_open(uri, "theorem t : strLen \"abc\" == 3 := by eval\n");
    // "strLen" starts at column 12 on line 0.
    let resp = lsp.hover(uri, 0, 14);
    assert!(resp.contains("strLen : String -> Nat"), "got: {}", resp);
    assert!(resp.contains("Number of UTF-8 characters"), "got: {}", resp);
    lsp.finish();
}

#[test]
fn hover_shows_top_level_def_body() {
    let mut lsp = Lsp::start();
    lsp.initialize();
    let uri = "file:///t_def.seki";
    lsp.did_open(
        uri,
        "def square := \\x -> x * x\ntheorem t : square 3 == 9 := by unfold square then eval\n",
    );
    // "square" (the usage inside the theorem, line 1) starts at column 12.
    let resp = lsp.hover(uri, 1, 14);
    assert!(resp.contains("def square"), "got: {}", resp);
    lsp.finish();
}

#[test]
fn hover_shows_theorem_statement_at_its_own_name() {
    let mut lsp = Lsp::start();
    lsp.initialize();
    let uri = "file:///t_thm.seki";
    lsp.did_open(
        uri,
        "def square := \\x -> x * x\ntheorem myTheorem : square 3 == 9 := by unfold square then eval\n",
    );
    // "myTheorem" (the declaration's own name) starts at column 8 on line 1.
    let resp = lsp.hover(uri, 1, 12);
    assert!(resp.contains("theorem myTheorem"), "got: {}", resp);
    assert!(resp.contains("square"), "got: {}", resp);
    lsp.finish();
}

#[test]
fn hover_returns_null_for_unknown_or_out_of_range_position() {
    let mut lsp = Lsp::start();
    lsp.initialize();
    let uri = "file:///t_none.seki";
    lsp.did_open(uri, "theorem t : 1 + 1 == 2 := by eval\n");
    let resp = lsp.hover(uri, 0, 999);
    assert!(
        resp.contains("\"result\":null"),
        "expected a null hover result, got: {}",
        resp
    );
    lsp.finish();
}

#[test]
fn diagnostics_still_work_alongside_hover() {
    // Regression: adding hover must not disturb the existing diagnostics
    // path (parse errors still get published on didOpen).
    let mut lsp = Lsp::start();
    lsp.initialize();
    let uri = "file:///t_bad.seki";
    let msg = format!(
        r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"{}","text":"def x := (","version":1}}}}}}"#,
        uri
    );
    lsp.send(&msg);
    let diag = lsp.recv();
    assert!(
        diag.contains("publishDiagnostics") && diag.contains("\"severity\":1"),
        "got: {}",
        diag
    );
    lsp.finish();
}

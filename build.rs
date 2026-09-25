// Build script: capture a short git SHA into SEKI_GIT_SHA at compile time.
//
// Falls back silently when git isn't available or the build is outside a
// repo — `seki --version` then prints just the cargo version.  We don't
// pull in any external crates here; everything is std + a few git
// invocations via std::process::Command.

use std::path::Path;
use std::process::Command;

fn git(args: &[&str]) -> Option<String> {
    Command::new("git")
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

/// Ask cargo to re-run this script when `path` changes.  Only for paths that
/// exist: cargo treats a missing path as always changed, which would rebuild
/// on every `cargo build`.
fn watch(path: &str) {
    if Path::new(path).exists() {
        println!("cargo:rerun-if-changed={}", path);
    }
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    // A commit does not touch `HEAD` — it rewrites the branch ref `HEAD`
    // points at — so watching `HEAD` alone left the SHA stale after every
    // commit.  Watch HEAD (branch switches, detached checkouts), the ref it
    // names (commits), and `packed-refs` (where the ref lives after `git gc`).
    // `--git-path` resolves each for worktrees too.
    if let Some(head) = git(&["rev-parse", "--git-path", "HEAD"]) {
        watch(&head);
        if let Some(branch) = git(&["symbolic-ref", "-q", "HEAD"]) {
            if let Some(r) = git(&["rev-parse", "--git-path", &branch]) {
                watch(&r);
            }
        }
        if let Some(packed) = git(&["rev-parse", "--git-path", "packed-refs"]) {
            watch(&packed);
        }
    }

    let sha = git(&["rev-parse", "--short=10", "HEAD"]).unwrap_or_default();
    println!("cargo:rustc-env=SEKI_GIT_SHA={}", sha);
}

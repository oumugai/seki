// Build script: capture a short git SHA into SEKI_GIT_SHA at compile time.
//
// Falls back silently when git isn't available or the build is outside a
// repo — `seki --version` then prints just the cargo version.  We don't
// pull in any external crates here; everything is std + a single git
// invocation via std::process::Command.

use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    // If `.git/HEAD` changes, re-run.  This is a heuristic; covers branch
    // switches and most commits.
    println!("cargo:rerun-if-changed=.git/HEAD");

    let sha = Command::new("git")
        .args(["rev-parse", "--short=10", "HEAD"])
        .output()
        .ok()
        .and_then(|o| if o.status.success() { Some(o.stdout) } else { None })
        .and_then(|bytes| String::from_utf8(bytes).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_default();

    println!("cargo:rustc-env=SEKI_GIT_SHA={}", sha);
}

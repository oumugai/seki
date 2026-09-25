//! seki — set-theory based theorem prover / programming language.
//!
//! Usage:
//!     seki              start REPL
//!     seki <file.seki>  run a source file
//!     seki --check FILE check a file without printing the value of each expr
//!     seki -e <expr>    evaluate one expression and print its value

use seki::ast::{Decl, Expr, LocatedDecl, Proof};
use seki::eval::{set_program_args, EvalCtx};
use seki::prover::Prover;
use seki::session::Session;
use seki::typecheck::check_shape;
use seki::value::{Env, Globals, SetVal, Value};
use seki::{parse_program, parser, SekiError};
use seki::trust::TrustLevel;
use std::collections::BTreeMap;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::Instant;

/// Non-tail-recursive seki evaluation (e.g. a user-defined recursive
/// function sampled up to `SAMPLE_BOUND` for a `forall n in Nat` proof) can
/// use several hundred native stack frames. The OS-provided main-thread
/// stack (commonly 8 MiB on Linux, controlled by `ulimit -s`) is too small
/// for that, so the real entry point runs on a spawned thread with an
/// explicit larger stack instead.
const MAIN_STACK_SIZE: usize = 256 * 1024 * 1024;

fn main() -> ExitCode {
    thread::Builder::new()
        .stack_size(MAIN_STACK_SIZE)
        .spawn(real_main)
        .expect("failed to spawn main worker thread")
        .join()
        .expect("main worker thread panicked")
}

fn real_main() -> ExitCode {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    // Strip out `-I <path>` flags (library search-path additions) before
    // dispatching to the subcommand handler.  A bare `--` token is treated
    // as a separator: everything after it is forwarded verbatim to the seki
    // program as `args` and never re-interpreted by the driver.
    let mut extra_libs: Vec<PathBuf> = Vec::new();
    let mut args: Vec<String> = Vec::new();
    let mut user_args: Vec<String> = Vec::new();
    let mut iter = raw_args.into_iter();
    let mut seen_sep = false;
    while let Some(a) = iter.next() {
        if seen_sep {
            user_args.push(a);
            continue;
        }
        if a == "--" {
            seen_sep = true;
            continue;
        }
        if a == "-I" {
            if let Some(p) = iter.next() {
                extra_libs.push(PathBuf::from(p));
            } else {
                eprintln!("-I requires a directory argument");
                return ExitCode::from(2);
            }
        } else if let Some(rest) = a.strip_prefix("-I") {
            extra_libs.push(PathBuf::from(rest));
        } else if a == "--min-confidence" {
            // Reject any conclusion the assumptions warrant less than this.
            // Read by `Session::new`; also settable as SEKI_MIN_CONFIDENCE.
            match iter.next() {
                Some(v) => std::env::set_var("SEKI_MIN_CONFIDENCE", v),
                None => {
                    eprintln!("--min-confidence requires a number in [0, 1]");
                    return ExitCode::from(2);
                }
            }
        } else if a == "--strict" {
            // Refuse any theorem that is not fully `TrustLevel::Sound`:
            // no sampling of an infinite domain, no dependence on an
            // `axiom`.  Read by `Session::new`; also settable directly as
            // the `SEKI_STRICT` env var.
            std::env::set_var("SEKI_STRICT", "1");
        } else if a == "--strict-match" {
            // Promote non-exhaustive `match` from a warning to a parse
            // error. Read by `check_exhaustiveness` in src/parser.rs; also
            // settable directly as the `SEKI_STRICT_MATCH` env var.
            std::env::set_var("SEKI_STRICT_MATCH", "1");
        } else {
            args.push(a);
        }
    }
    if args.is_empty() {
        return repl_with(extra_libs);
    }
    match args[0].as_str() {
        "-e" | "--eval" => {
            if args.len() < 2 {
                eprintln!("--eval requires an expression");
                return ExitCode::from(2);
            }
            run_inline_with(&args[1..].join(" "), extra_libs, user_args)
        }
        "--check" => {
            if args.len() < 2 {
                eprintln!("--check requires a file");
                return ExitCode::from(2);
            }
            run_file_with(&args[1], true, extra_libs, user_args)
        }
        "--audit" => {
            if args.len() < 2 {
                eprintln!("--audit requires a file or directory");
                return ExitCode::from(2);
            }
            if Path::new(&args[1]).is_dir() {
                return audit_project(&args[1], extra_libs);
            }
            audit_file(&args[1], extra_libs, user_args)
        }
        "--proof" => {
            if args.len() < 3 {
                eprintln!("--proof requires a file and a theorem name");
                return ExitCode::from(2);
            }
            print_proof_term(&args[1], &args[2], extra_libs, user_args)
        }
        "-h" | "--help" => {
            print_help();
            ExitCode::SUCCESS
        }
        "-V" | "--version" => {
            print_version();
            ExitCode::SUCCESS
        }
        "--list-builtins" => {
            // Dump every Rust-side builtin name (sorted) to stdout.  Useful
            // for tooling (LSP completion, doc generation) and for users
            // who want to know "what's available?" without grepping source.
            let state = Session::new();
            let mut names: Vec<&String> = state.globals.defs.iter()
                .filter_map(|(k, v)| matches!(v, Value::Builtin(_)).then_some(k))
                .collect();
            names.sort();
            for n in names { println!("{}", n); }
            ExitCode::SUCCESS
        }
        "--builtin" => {
            // Print detailed metadata about a single builtin.  Useful for
            // LSP hover responses, doc generation, and quick lookup.
            if args.len() < 2 {
                eprintln!("--builtin requires a builtin name");
                return ExitCode::from(2);
            }
            let name = &args[1];
            match seki::builtin_meta::builtin_meta(name) {
                Some(m) => {
                    println!("{}", m.signature);
                    println!("  Effect:     {}", m.effect.name());
                    println!("  Domain:     {}", m.domain);
                    println!("  Codomain:   {}", m.codomain);
                    if !m.properties.is_empty() {
                        println!("  Properties: {}", m.properties.join(", "));
                    }
                    println!("  Doc:        {}", m.doc);
                    ExitCode::SUCCESS
                }
                None => {
                    eprintln!("builtin '{}' has no catalog entry (it may exist but lack metadata)", name);
                    ExitCode::from(3)
                }
            }
        }
        "--list-builtins-doc" => {
            // For every documented builtin, print one summary line.
            for n in seki::builtin_meta::all_documented_names() {
                if let Some(m) = seki::builtin_meta::builtin_meta(n) {
                    println!("[{:11}] {}", m.effect.name(), m.signature);
                }
            }
            ExitCode::SUCCESS
        }
        // File mode: any positional args beyond the file are treated as the
        // program's `args` even without `--` (matching shebang scripts).
        path => {
            let trailing: Vec<String> =
                args[1..].iter().cloned().chain(user_args.into_iter()).collect();
            run_file_with(path, false, extra_libs, trailing)
        }
    }
}

fn print_version() {
    // Build metadata embedded at compile time via Cargo's env vars + an
    // optional git short SHA picked up via build.rs (`SEKI_GIT_SHA`).  When
    // build.rs isn't running (e.g. building without git), we fall back to
    // the version only.
    let v = env!("CARGO_PKG_VERSION");
    match option_env!("SEKI_GIT_SHA") {
        Some(sha) if !sha.is_empty() => println!("seki {} ({})", v, sha),
        _ => println!("seki {}", v),
    }
}

fn print_help() {
    println!(
        "seki — set-theoretic theorem prover & programming language\n\n\
         Usage:\n  \
            seki                          start the REPL\n  \
            seki <file.seki> [args...]    run a source file with args\n  \
            seki <file.seki> -- [args...] same, but unambiguous\n  \
            seki --check FILE             verify a file (suppresses echoing)\n  \
            seki -e <expr> [-- args...]   evaluate one expression\n  \
            seki -I <dir>                 add <dir> to the lib path (repeatable)\n  \
            seki --audit FILE             run FILE and report how each theorem was verified\n  \
            seki --audit DIR              audit every .seki under DIR as one assurance report\n  \
            seki --proof FILE NAME        print the proof term the kernel accepted for NAME\n  \
            seki --min-confidence R ...   reject conclusions their assumptions warrant less than R\n  \
            seki --strict ...             reject theorems that are only sampled or axiom-dependent (or set SEKI_STRICT)\n  \
            seki --strict-match ...       non-exhaustive `match` is a parse error (or set SEKI_STRICT_MATCH)\n  \
            seki --list-builtins          print every Rust builtin (one per line)\n  \
            seki --list-builtins-doc      print every documented builtin's signature\n  \
            seki --builtin <name>         show full metadata for a builtin\n  \
            seki -V | --version           print version\n  \
            seki -h | --help              show this help\n\n\
         Program arguments:\n  \
            Positional args after the file (or after `--`) are exposed inside\n  \
            seki as `args : List String`.  Use `--` to disambiguate when an\n  \
            argument starts with a dash.\n\n\
         Library search:\n  \
            `import \"cas/calc.seki\"` finds the file under any of:\n  \
              - the current file's directory\n  \
              - SEKI_LIB_PATH (colon-separated env var)\n  \
              - <cwd>/lib\n  \
              - <binary's parent>/lib  (and ../lib, ../../lib)\n  \
              - ~/.seki/lib\n  \
              - any -I directory"
    );
}

fn run_inline_with(src: &str, extra_libs: Vec<PathBuf>, prog_args: Vec<String>) -> ExitCode {
    let mut state = Session::new();
    for p in extra_libs {
        state.lib_paths.insert(0, p);
    }
    set_program_args(&mut state.globals, prog_args);
    match state.run_source(src, false) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{}", e);
            ExitCode::FAILURE
        }
    }
}

fn run_file_with(
    path: &str,
    quiet: bool,
    extra_libs: Vec<PathBuf>,
    prog_args: Vec<String>,
) -> ExitCode {
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {}: {}", path, e);
            return ExitCode::from(2);
        }
    };
    let mut state = Session::new();
    for p in extra_libs {
        state.lib_paths.insert(0, p);
    }
    set_program_args(&mut state.globals, prog_args);
    // Use the input file's directory as the base for relative imports.
    if let Some(parent) = Path::new(path).parent() {
        if !parent.as_os_str().is_empty() {
            state.base_dirs.clear();
            state.base_dirs.push(parent.to_path_buf());
        }
    }
    match state.run_source(&src, quiet) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{}", e);
            ExitCode::FAILURE
        }
    }
}

/// Load `path`, then report what the kernel concluded about each theorem.
///
/// A green line means the proof term was re-established from primitives.
/// Anything else names the gap: an assumption it rests on, a tactic with no
/// witness form, or — worst — a check that only sampled an infinite domain.
fn audit_file(path: &str, extra_libs: Vec<PathBuf>, prog_args: Vec<String>) -> ExitCode {
    let mut state = Session::new();
    for p in extra_libs {
        state.lib_paths.insert(0, p);
    }
    set_program_args(&mut state.globals, prog_args);
    if let Some(parent) = Path::new(path).parent() {
        if !parent.as_os_str().is_empty() {
            state.base_dirs.clear();
            state.base_dirs.push(parent.to_path_buf());
        }
    }
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {}: {}", path, e);
            return ExitCode::from(2);
        }
    };
    if let Err(e) = state.run_source(&src, true) {
        eprintln!("{}", e);
        return ExitCode::FAILURE;
    }

    // Definitions whose annotation refines the return type make a claim
    // too, and it is checked the same way — so report them alongside.
    let mut def_names: Vec<&String> = state.globals.def_trust.keys().collect();
    def_names.sort();
    let mut names: Vec<&String> = state.globals.theorem_trust.keys().collect();
    names.sort();
    let mut counts = std::collections::BTreeMap::new();
    if !def_names.is_empty() {
        println!("{:<44}  {}", "refined definition", "how its type was checked");
        println!("{}", "-".repeat(78));
        for name in &def_names {
            let trust = state.globals.def_trust[*name];
            *counts.entry(trust).or_insert(0usize) += 1;
            let detail = if trust.is_sound() {
                "the obligation was proved and kernel-checked".to_string()
            } else {
                match state.globals.def_obligations.get(*name) {
                    Some((goal, _)) => format!(
                        "only sampled — the obligation `{}` was not proved",
                        goal
                    ),
                    None => "only sampled".to_string(),
                }
            };
            println!("{:<44}  {}", name, detail);
        }
        println!();
    }
    println!("{:<44}  {}", "theorem", "how it was verified");
    println!("{}", "-".repeat(78));
    for name in &names {
        let trust = state.globals.theorem_trust[*name];
        *counts.entry(trust).or_insert(0usize) += 1;
        let detail = match state.globals.theorem_verdicts.get(*name) {
            Some(v) if v.fully_checked && v.assumptions.is_empty() => {
                "kernel-checked from primitives".to_string()
            }
            // `assumptions` already names the tactic and the reason, so
            // listing `trusted_steps` separately would only repeat it.
            Some(v) => {
                let mut parts: Vec<String> = v.assumptions.clone();
                parts.sort();
                parts.dedup();
                parts.join("; ")
            }
            None => "no verdict recorded".to_string(),
        };
        println!("{:<44}  {}", name, detail);
        // A conclusion resting on assumptions that are *believed* rather
        // than asserted gets a second line: how much they warrant it.
        if let Some(v) = state.globals.theorem_verdicts.get(*name) {
            let c = seki::confidence::of_verdict(v, &state.globals);
            if !matches!(c, seki::confidence::Confidence::Unqualified) {
                println!("{:<44}  {}", "", c.describe());
            }
        }
    }
    println!("{}", "-".repeat(78));

    // What the file *assumes*.  An audit that lists only what was checked
    // is half a report: a decision rests as much on the assumptions nobody
    // proved, and those are exactly what a reader six months later needs to
    // see.  Axioms are listed whether or not a theorem cites one.
    let mut axiom_names: Vec<&String> = state.globals.axiom_props.keys().collect();
    axiom_names.sort();
    if !axiom_names.is_empty() {
        println!();
        println!("{:<44}  {}", "assumed without proof", "confidence and source");
        println!("{}", "-".repeat(78));
        for name in &axiom_names {
            let confidence = match state.globals.axiom_confidence.get(*name) {
                Some(c) => format!("{}", c),
                None => "asserted outright".to_string(),
            };
            let source = state
                .globals
                .axiom_provenance
                .get(*name)
                .map(|p| format!(" — {}", p))
                .unwrap_or_default();
            println!("{:<44}  {}{}", name, confidence, source);
        }
        // An assumption no conclusion rests on is usually a modelling
        // slip: the theorem restated the bound as its own hypothesis
        // instead of citing the axiom, so the stated confidence never
        // reaches the conclusion it was written for.
        let cited: std::collections::BTreeSet<&str> = state
            .globals
            .theorem_verdicts
            .values()
            .flat_map(|v| v.assumptions.iter())
            .map(|a| a.as_str())
            .collect();
        // Only axioms that carry a *confidence*: one was written to warrant
        // a conclusion, so one that reaches none is a modelling slip worth
        // pointing at.  A classical assumption an imported library declares
        // and this file happens not to use is not.
        let unused: Vec<&str> = axiom_names
            .iter()
            .map(|n| n.as_str())
            .filter(|n| state.globals.axiom_confidence.contains_key(*n))
            .filter(|n| !cited.iter().any(|a| a.contains(*n)))
            .collect();
        if !unused.is_empty() {
            let listed = unused
                .iter()
                .map(|n| format!("`{}`", n))
                .collect::<Vec<_>>()
                .join(", ");
            println!();
            println!("  note: no conclusion here rests on {},", listed);
            println!("  so the confidence stated for it warrants nothing.  A theorem that");
            println!("  restates an axiom's content as its own hypothesis does not cite it");
            println!("  — connect them with `by have h : <prop> := by apply <axiom> then ...`.");
        }
        println!("{}", "-".repeat(78));
    }

    let total: usize = counts.values().sum();
    println!(
        "{} claims ({} theorems, {} refined definitions)",
        total,
        names.len(),
        def_names.len()
    );
    for (level, n) in &counts {
        println!("  {:<10} {}", format!("{}:", level), n);
    }
    // A file whose every theorem is fully checked is the goal; say so
    // plainly rather than making the reader compare numbers.
    if counts.keys().all(|l| l.is_sound()) {
        println!("\nevery claim in this file was re-established by the kernel.");
        ExitCode::SUCCESS
    } else {
        // The same gate as `--audit DIR`: a file is one project, and a
        // build that asked for the report should not pass on a claim that
        // was only sampled because the argument happened to be a file.
        ExitCode::FAILURE
    }
}

/// Audit every `.seki` file under `dir` as one report.
///
/// A single file's audit answers "how was this theorem verified".  A system
/// is not one file, and the question a reviewer actually asks is about the
/// whole of it: what does this system claim, and on what grounds?  That
/// report — every claim sorted by how strong its evidence is, and every
/// assumption with its source — is the deliverable, not the program.
///
/// Files are audited independently, which is what makes the tally
/// meaningful: a claim is counted where it is stated.  A file that fails to
/// run is itself a finding and is listed rather than skipped silently.
fn audit_project(dir: &str, extra_libs: Vec<PathBuf>) -> ExitCode {
    let mut files: Vec<PathBuf> = Vec::new();
    collect_seki_files(Path::new(dir), &mut files);
    files.sort();
    if files.is_empty() {
        eprintln!("no .seki files under {}", dir);
        return ExitCode::from(2);
    }

    // `(level, name, file, detail)` for every claim, plus the assumptions.
    // `(level, name, file, how it was verified, what its assumptions warrant)`
    let mut claims: Vec<(TrustLevel, String, String, String, Option<String>)> =
        Vec::new();
    let mut assumptions: Vec<(String, String, String)> = Vec::new();
    let mut broken: Vec<(String, String)> = Vec::new();
    let mut per_file: Vec<(String, BTreeMap<TrustLevel, usize>)> = Vec::new();

    for path in &files {
        let rel = path.strip_prefix(dir).unwrap_or(path).display().to_string();
        let mut state = Session::new();
        for p in &extra_libs {
            state.lib_paths.insert(0, p.clone());
        }
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                state.base_dirs.clear();
                state.base_dirs.push(parent.to_path_buf());
            }
        }
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                broken.push((rel, format!("cannot read: {}", e)));
                continue;
            }
        };
        if let Err(e) = state.run_source(&src, true) {
            broken.push((rel, first_line(&format!("{}", e))));
            continue;
        }
        // Only what this file *declares*.  Importing a module registers
        // its theorems too, and counting them again in every importer
        // would make the tally say more than the project claims.
        let (declared, declared_axioms) = declared_names(&src);
        let mut counts: BTreeMap<TrustLevel, usize> = BTreeMap::new();
        let mut names: Vec<&String> = state
            .globals
            .theorem_trust
            .keys()
            .filter(|n| declared.contains(*n))
            .collect();
        names.sort();
        for name in names {
            let trust = state.globals.theorem_trust[name];
            *counts.entry(trust).or_insert(0) += 1;
            let detail = match state.globals.theorem_verdicts.get(name) {
                Some(v) if v.fully_checked && v.assumptions.is_empty() => {
                    "kernel-checked from primitives".to_string()
                }
                Some(v) => {
                    let mut parts = v.assumptions.clone();
                    parts.sort();
                    parts.dedup();
                    first_line(&parts.join("; "))
                }
                None => "no verdict recorded".to_string(),
            };
            // What the assumptions behind it warrant, when any of them
            // carries a confidence.  This is the number a reviewer acts on.
            let warrant = state.globals.theorem_verdicts.get(name).and_then(|v| {
                let c = seki::confidence::of_verdict(v, &state.globals);
                match c {
                    seki::confidence::Confidence::Unqualified => None,
                    other => Some(other.describe()),
                }
            });
            claims.push((trust, name.clone(), rel.clone(), detail, warrant));
        }
        for (name, prop) in &state.globals.axiom_props {
            let _ = prop;
            if !declared_axioms.contains(name) {
                continue;
            }
            let confidence = state
                .globals
                .axiom_confidence
                .get(name)
                .map(|c| format!("{}", c))
                .unwrap_or_else(|| "asserted outright".to_string());
            let source = state
                .globals
                .axiom_provenance
                .get(name)
                .cloned()
                .unwrap_or_default();
            if !assumptions.iter().any(|(n, _, _)| n == name) {
                assumptions.push((name.clone(), confidence, source));
            }
        }
        per_file.push((rel, counts));
    }

    // ---- the report ----------------------------------------------------
    // Built into a string and printed at the end: the audited programs run
    // for real, and anything they print would otherwise land in the middle
    // of the report.  The report is the artifact; it has to be contiguous.
    let mut out = String::new();
    use std::fmt::Write as _;
    let _ = writeln!(out, "assurance report for {}", dir);
    let _ = writeln!(out, "{}", "=".repeat(78));
    out.push('\n');

    // Everything that is *not* fully proved, first: that is the list a
    // reviewer works through, and burying it under the good news would be
    // the wrong way round.
    let mut weak: Vec<&(TrustLevel, String, String, String, Option<String>)> =
        claims.iter().filter(|(t, ..)| !t.is_sound()).collect();
    weak.sort_by_key(|(t, n, ..)| (std::cmp::Reverse(*t), n.clone()));
    if weak.is_empty() {
        let _ = writeln!(out, "every claim in this project was re-established by the kernel.");
    } else {
        let _ = writeln!(out, "claims resting on something other than a kernel proof");
        let _ = writeln!(out, "{}", "-".repeat(78));
        for (trust, name, file, detail, warrant) in &weak {
            let _ = writeln!(out, "  {:<11} {}  ({})", format!("{}", trust), name, file);
            let _ = writeln!(out, "              {}", detail);
            if let Some(w) = warrant {
                let _ = writeln!(out, "              {}", w);
            }
        }
    }
    out.push('\n');

    if !assumptions.is_empty() {
        assumptions.sort();
        let _ = writeln!(out, "assumed without proof");
        let _ = writeln!(out, "{}", "-".repeat(78));
        for (name, confidence, source) in &assumptions {
            if source.is_empty() {
                let _ = writeln!(out, "  {:<30} {}", name, confidence);
            } else {
                let _ = writeln!(out, "  {:<30} {} — {}", name, confidence, source);
            }
        }
        out.push('\n');
    }

    if !broken.is_empty() {
        let _ = writeln!(out, "files that did not run");
        let _ = writeln!(out, "{}", "-".repeat(78));
        for (file, why) in &broken {
            let _ = writeln!(out, "  {:<30} {}", file, why);
        }
        out.push('\n');
    }

    let _ = writeln!(out, "by file");
    let _ = writeln!(out, "{}", "-".repeat(78));
    for (file, counts) in &per_file {
        let summary: Vec<String> = counts
            .iter()
            .map(|(l, n)| format!("{} {}", n, l))
            .collect();
        let _ = writeln!(out, 
            "  {:<44} {}",
            file,
            if summary.is_empty() {
                "no claims".to_string()
            } else {
                summary.join(", ")
            }
        );
    }
    out.push('\n');

    let mut totals: BTreeMap<TrustLevel, usize> = BTreeMap::new();
    for (t, ..) in &claims {
        *totals.entry(*t).or_insert(0) += 1;
    }
    let _ = writeln!(out, "{}", "=".repeat(78));
    let _ = writeln!(out, 
        "{} claims across {} file(s), {} assumption(s)",
        claims.len(),
        files.len(),
        assumptions.len()
    );
    for (level, n) in &totals {
        let _ = writeln!(out, "  {:<12} {}", format!("{}:", level), n);
    }
    if !broken.is_empty() {
        let _ = writeln!(out, "  {:<12} {}", "unrunnable:", broken.len());
    }

    println!();
    print!("{}", out);

    // A project with nothing weak and nothing broken is the only clean
    // outcome; anything else should fail a build that asked for this.
    if weak.is_empty() && broken.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// The theorem and axiom names a file declares itself, as opposed to the
/// ones it inherits by importing.
fn declared_names(src: &str) -> (Vec<String>, Vec<String>) {
    let mut theorems = Vec::new();
    let mut axioms = Vec::new();
    if let Ok(decls) = parse_program(src) {
        for ld in decls {
            match ld.decl {
                Decl::Theorem { name, .. } => theorems.push(name),
                Decl::Axiom { name, .. } => axioms.push(name),
                _ => {}
            }
        }
    }
    (theorems, axioms)
}

fn collect_seki_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_seki_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "seki") {
            out.push(path);
        }
    }
}

/// Error messages carry a source excerpt; a table wants the first line.
fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").trim().to_string()
}

/// Print the proof term the kernel accepted for one theorem.
fn print_proof_term(
    path: &str,
    name: &str,
    extra_libs: Vec<PathBuf>,
    prog_args: Vec<String>,
) -> ExitCode {
    let mut state = Session::new();
    for p in extra_libs {
        state.lib_paths.insert(0, p);
    }
    set_program_args(&mut state.globals, prog_args);
    if let Some(parent) = Path::new(path).parent() {
        if !parent.as_os_str().is_empty() {
            state.base_dirs.clear();
            state.base_dirs.push(parent.to_path_buf());
        }
    }
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {}: {}", path, e);
            return ExitCode::from(2);
        }
    };
    if let Err(e) = state.run_source(&src, true) {
        eprintln!("{}", e);
        return ExitCode::FAILURE;
    }
    match state.globals.theorem_certs.get(name) {
        Some(cert) => {
            if let Some(prop) = state.globals.theorem_props.get(name) {
                println!("theorem {} : {}", name, prop);
            }
            println!("{}", cert.render());
            if let Some(v) = state.globals.theorem_verdicts.get(name) {
                println!("\nkernel verdict: {}", if v.fully_checked {
                    "every step re-established from primitives"
                } else {
                    "NOT fully checked"
                });
                for a in &v.assumptions {
                    println!("  rests on: {}", a);
                }
            }
            ExitCode::SUCCESS
        }
        None => {
            eprintln!("no theorem named `{}` in {}", name, path);
            ExitCode::from(2)
        }
    }
}

// -- Background search engine ----------------------------------------------
//
// The REPL offers two real-time inference features:
//
//   * `:prove <prop>`             — try to prove the proposition; report
//                                   which tactic closes it.
//   * `theorem t : P` (no `:=`)   — auto-search, register if found.
//
// Both run on a *worker thread* against a `clone_for_thread()` snapshot of
// globals.  The main loop pushes a `SearchTask` and continues; the worker
// posts a `SearchResult` back via channel.  Before painting the next prompt
// (and after every submitted line) the main loop drains the result channel
// and prints completed search outcomes.
//
// State transfer is safe because `Value` is `Send + Sync` (Phase 4 Rc→Arc
// migration), so cloning globals across thread boundaries is cheap.  On
// `SearchKind::AutoTheorem` success we re-verify on the *live* globals
// before committing the theorem, which keeps registration sound even if
// the user redefined a dependency mid-search.

#[derive(Clone)]
enum SearchKind {
    /// `:prove <expr>` — no registration; just report.
    Prove,
    /// `:why <expr>` — like `Prove` but the result is presented in terms
    /// of which existing lemmas the proof uses ("derivable using `gauss`")
    /// rather than just the raw tactic script.  No registration.
    Why,
    /// `theorem name : prop` submitted without `:=`; register on success.
    AutoTheorem { name: String, prop: Expr },
    /// Silent re-verification of a previously-proven theorem, triggered
    /// when the user redefines a function the theorem statement references.
    /// On success we say nothing (registration stays); on failure we warn
    /// the user that their redefinition has invalidated `name`.  Carries
    /// the stored proof AST so the worker can replay it directly without
    /// re-running portfolio search.
    ReCheck { name: String, proof: Proof, trigger: String },
}

enum SearchTask {
    Search {
        id: u64,
        prop: Expr,
        kind: SearchKind,
        snapshot: Globals,
    },
    Shutdown,
}

enum SearchOutcome {
    Found { proof: Proof },
    NotFound,
    Error { msg: String },
}

struct SearchResult {
    #[allow(dead_code)]
    id: u64,
    kind: SearchKind,
    outcome: SearchOutcome,
    elapsed_ms: u128,
}

fn spawn_search_worker(
    rx_task: mpsc::Receiver<SearchTask>,
    tx_result: mpsc::Sender<SearchResult>,
) -> thread::JoinHandle<()> {
    thread::spawn(move || {
        while let Ok(task) = rx_task.recv() {
            match task {
                SearchTask::Shutdown => break,
                SearchTask::Search { id, prop, kind, snapshot } => {
                    let started = Instant::now();
                    let ctx = EvalCtx::new(&snapshot);
                    let env = Env::new();
                    let prover = Prover::new(&ctx);
                    // Dispatch by kind:
                    //   ReCheck — replay the stored proof directly (no
                    //             portfolio search).
                    //   Why     — lemma-preferring portfolio.
                    //   else    — cost-ordered portfolio.
                    let outcome = match std::panic::catch_unwind(
                        std::panic::AssertUnwindSafe(|| match &kind {
                            SearchKind::ReCheck { proof, .. } => {
                                match prover.verify(&prop, proof, &env) {
                                    Ok(_) => Some(proof.clone()),
                                    Err(_) => None,
                                }
                            }
                            SearchKind::Why => {
                                prover.try_portfolio_lemma_first(&prop, &env)
                            }
                            _ => prover.try_portfolio(&prop, &env),
                        }),
                    ) {
                        Ok(Some(p)) => SearchOutcome::Found { proof: p },
                        Ok(None) => SearchOutcome::NotFound,
                        Err(_) => SearchOutcome::Error {
                            msg: "search panicked (likely a malformed expression)".into(),
                        },
                    };
                    let elapsed_ms = started.elapsed().as_millis();
                    let _ = tx_result.send(SearchResult { id, kind, outcome, elapsed_ms });
                }
            }
        }
    })
}

/// Drain every completed search result from the channel and report it to
/// the user.  For `AutoTheorem` results we re-verify on the *current*
/// globals before committing the theorem, since the user may have changed
/// a dependency since the snapshot.
fn drain_search_results(
    rx: &mpsc::Receiver<SearchResult>,
    state: &mut Session,
) {
    while let Ok(r) = rx.try_recv() {
        match (r.kind, r.outcome) {
            (SearchKind::Prove, SearchOutcome::Found { proof }) => {
                println!("  ✓ provable by `{}`  ({}ms)", proof, r.elapsed_ms);
            }
            (SearchKind::Prove, SearchOutcome::NotFound) => {
                println!(
                    "  ✗ no tactic in the portfolio closed the goal  ({}ms)",
                    r.elapsed_ms
                );
            }
            (SearchKind::Prove, SearchOutcome::Error { msg }) => {
                eprintln!("  ! search error: {}", msg);
            }
            (SearchKind::Why, SearchOutcome::Found { proof }) => {
                // Surface the *lemma chain* the proof leans on, so the
                // user sees which earlier theorems make this one derivable.
                let lemmas = seki::prover::extract_lemmas(&proof);
                if lemmas.is_empty() {
                    println!(
                        "  ✓ derivable without any earlier lemma\n    via `{}`  ({}ms)",
                        proof, r.elapsed_ms
                    );
                } else {
                    let chain = lemmas.join(", ");
                    println!(
                        "  ✓ derivable using lemma{}: {}\n    via `{}`  ({}ms)",
                        if lemmas.len() == 1 { "" } else { "s" },
                        chain,
                        proof,
                        r.elapsed_ms
                    );
                }
            }
            (SearchKind::Why, SearchOutcome::NotFound) => {
                println!(
                    "  ✗ no portfolio combination (including up to 2-lemma simp chains) closed the goal  ({}ms)",
                    r.elapsed_ms
                );
            }
            (SearchKind::Why, SearchOutcome::Error { msg }) => {
                eprintln!("  ! search error: {}", msg);
            }
            (
                SearchKind::AutoTheorem { name, prop },
                SearchOutcome::Found { proof },
            ) => {
                // Re-verify on live globals — the snapshot might be stale
                // if the user redefined something since submission.  Going
                // through `verify_and_register` is what records the proof's
                // trust level; this path used to skip it.
                match state.verify_and_register(&name, &prop, &proof) {
                    Ok(trust) => {
                        println!(
                            "  theorem {} ✓ proved by `{}`{}  ({}ms)",
                            name,
                            proof,
                            trust.marker(),
                            r.elapsed_ms
                        );
                    }
                    Err(e) => {
                        println!(
                            "  ⚠ theorem {} found `{}` on snapshot but stale on current state ({}); not registered",
                            name, proof, e
                        );
                    }
                }
            }
            (
                SearchKind::AutoTheorem { name, .. },
                SearchOutcome::NotFound,
            ) => {
                println!(
                    "  ✗ theorem {} — no tactic in the portfolio closed the goal  ({}ms)",
                    name, r.elapsed_ms
                );
            }
            (
                SearchKind::AutoTheorem { name, .. },
                SearchOutcome::Error { msg },
            ) => {
                eprintln!("  ! theorem {} search error: {}", name, msg);
            }
            // ReCheck success is silent — the theorem still holds after the
            // user's redefinition, so there's nothing to report.  Failure
            // means the redefinition broke the proof; warn loudly with the
            // proof AST so the user knows what to revisit.
            (SearchKind::ReCheck { name, .. }, SearchOutcome::Found { .. }) => {
                // The theorem still holds, but the redefinition may have
                // changed what its proof is *worth* (a `def` that grew a
                // case outside the sample, say), so recompute the level.
                let recomputed = state
                    .globals
                    .theorem_props
                    .get(&name)
                    .cloned()
                    .zip(state.globals.theorem_proofs.get(&name).cloned())
                    .map(|(prop, proof)| {
                        let ctx = EvalCtx::new(&state.globals);
                        Prover::new(&ctx).trust_of(&prop, &proof, &Env::new())
                    });
                if let Some(t) = recomputed {
                    let before = state.globals.theorem_trust.insert(name.clone(), t);
                    if before.map(|b| b != t).unwrap_or(false) {
                        eprintln!(
                            "  ⚠ theorem `{}` still holds, but is now {}{}",
                            name,
                            t,
                            t.marker()
                        );
                    }
                }
            }
            (
                SearchKind::ReCheck { name, proof, trigger },
                SearchOutcome::NotFound,
            ) => {
                eprintln!(
                    "  ⚠ redefinition of `{}` invalidated theorem `{}` (was: `{}`)",
                    trigger, name, proof
                );
            }
            (
                SearchKind::ReCheck { name, trigger, .. },
                SearchOutcome::Error { msg },
            ) => {
                eprintln!(
                    "  ! re-check of theorem `{}` (triggered by `{}`) errored: {}",
                    name, trigger, msg
                );
            }
        }
    }
}

/// Split a parsed decl list into (synchronous, async).  Theorems with proof
/// `by auto` are routed to the background worker instead of being run
/// inline (which would block the REPL on portfolio search).  All other
/// decls go through the normal path so definitions take effect immediately.
fn partition_async_theorems(
    decls: Vec<LocatedDecl>,
) -> (Vec<LocatedDecl>, Vec<(String, Expr)>) {
    let mut sync = Vec::new();
    let mut async_thms = Vec::new();
    for ld in decls {
        match ld.decl {
            Decl::Theorem { ref name, ref prop, proof: Proof::ByAuto } => {
                async_thms.push((name.clone(), prop.clone()));
            }
            _ => sync.push(ld),
        }
    }
    (sync, async_thms)
}

// -- REPL -------------------------------------------------------------------

fn repl_with(extra_libs: Vec<PathBuf>) -> ExitCode {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut state = Session::new();
    for p in extra_libs {
        state.lib_paths.insert(0, p);
    }

    // Background search engine: a worker thread that consumes `SearchTask`s
    // (sent for `:prove <expr>` and for `theorem t : P` submitted without
    // a proof body) and posts results back through `rx_result`.  We drain
    // the result channel at every prompt boundary so the user sees
    // completed searches between commands.
    let (tx_task, rx_task) = mpsc::channel::<SearchTask>();
    let (tx_result, rx_result) = mpsc::channel::<SearchResult>();
    let worker = spawn_search_worker(rx_task, tx_result);
    let mut next_search_id: u64 = 0;

    // Persistent command history.  We append every non-meta line the user
    // submits to ~/.seki_history.  This isn't readline-style arrow recall
    // (that needs raw-mode termios manipulation, which adds significant
    // platform code), but it does mean users can `grep` their history,
    // and a future Phase-10 LSP-aware shell can read it back.
    let history_path: Option<PathBuf> = std::env::var_os("HOME")
        .map(|h| PathBuf::from(h).join(".seki_history"));

    let print_version_line = || {
        let v = env!("CARGO_PKG_VERSION");
        match option_env!("SEKI_GIT_SHA") {
            Some(sha) if !sha.is_empty() => println!("seki {} ({})", v, sha),
            _ => println!("seki {}", v),
        }
    };
    print_version_line();
    println!("type :q to exit, :help for commands");
    let mut buf = String::new();
    loop {
        // Drain any completed background search results before painting the
        // next prompt.  Anything found, missed, or errored since the last
        // iteration is printed above the prompt line.
        drain_search_results(&rx_result, &mut state);
        // primary prompt
        print!("seki> ");
        stdout.lock().flush().ok();
        buf.clear();
        let n = match stdin.lock().read_line(&mut buf) {
            Ok(n) => n,
            Err(e) => {
                eprintln!("read error: {}", e);
                return ExitCode::FAILURE;
            }
        };
        if n == 0 {
            // EOF
            println!();
            break;
        }
        let line = buf.trim_end().to_string();
        if line.is_empty() {
            continue;
        }
        // Append every non-empty user line to the history file before
        // dispatch (so syntactically invalid lines are still recorded).
        if let Some(p) = history_path.as_ref() {
            use std::io::Write;
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true).append(true).open(p)
            {
                let _ = writeln!(f, "{}", line);
            }
        }
        match line.as_str() {
            ":q" | ":quit" | ":exit" => break,
            ":help" => {
                println!(
                    ":q | :quit            exit\n\
                     :help                 show this help\n\
                     :version              show seki version\n\
                     :defs                 list global definitions\n\
                     :builtins             list all Rust builtins (sorted)\n\
                     :builtins <prefix>    list builtins starting with <prefix>\n\
                     :load <file>          load a .seki file\n\
                     :type <expr>          show the inferred type of an expression\n\
                     :prove <prop>         try to prove <prop> via portfolio search (async)\n\
                     :why <prop>           like :prove, but report which earlier lemmas the proof uses\n\
                     :member <v> <set>     check membership (alias of `v in set`)\n\
                     :libpath              show library search paths\n\
                     :libpath add <dir>    prepend a directory to the library search path\n\
                     :history              path to the persisted command history\n\
                     anything else         is parsed as a declaration or expression\n\
                     \n\
                     Note: history is saved per-line at ~/.seki_history but the\n\
                     REPL doesn't support arrow-key recall.  `grep something\n\
                     ~/.seki_history` is the recommended way to find a past line."
                );
                continue;
            }
            ":version" => {
                print_version_line();
                continue;
            }
            ":history" => {
                match &history_path {
                    Some(p) => println!("{}", p.display()),
                    None    => println!("(HOME not set — history disabled)"),
                }
                continue;
            }
            ":builtins" => {
                let mut keys: Vec<&String> = state.globals.defs.iter()
                    .filter_map(|(k, v)| match v {
                        Value::Builtin(_) => Some(k),
                        _ => None,
                    }).collect();
                keys.sort();
                for k in keys { println!("  {}", k); }
                continue;
            }
            cmd if cmd.starts_with(":builtins ") => {
                let prefix = cmd[":builtins ".len()..].trim();
                let mut keys: Vec<&String> = state.globals.defs.iter()
                    .filter_map(|(k, v)| match v {
                        Value::Builtin(_) if k.starts_with(prefix) => Some(k),
                        _ => None,
                    }).collect();
                keys.sort();
                if keys.is_empty() {
                    println!("(no builtins starting with '{}')", prefix);
                } else {
                    for k in keys { println!("  {}", k); }
                }
                continue;
            }
            ":libpath" => {
                println!("Library search paths (in order):");
                for (i, p) in state.lib_paths.iter().enumerate() {
                    println!("  [{}] {}", i, p.display());
                }
                continue;
            }
            cmd if cmd.starts_with(":libpath add ") => {
                let p = cmd[":libpath add ".len()..].trim();
                state.lib_paths.insert(0, PathBuf::from(p));
                println!("added '{}' to library search paths", p);
                continue;
            }
            ":defs" => {
                let mut keys: Vec<&String> = state.globals.defs.keys().collect();
                keys.sort();
                for k in keys {
                    let v = &state.globals.defs[k];
                    println!("  {} = {}", k, v);
                }
                let mut tkeys: Vec<&String> = state.globals.theorems.keys().collect();
                tkeys.sort();
                for k in tkeys {
                    println!("  theorem {} ✓", k);
                }
                continue;
            }
            cmd if cmd.starts_with(":load ") => {
                let path = cmd[6..].trim();
                match std::fs::read_to_string(path) {
                    Ok(src) => {
                        if let Err(e) = state.run_source(&src, false) {
                            eprintln!("{}", e);
                        }
                    }
                    Err(e) => eprintln!("cannot read {}: {}", path, e),
                }
                continue;
            }
            cmd if cmd.starts_with(":type ") => {
                let expr = &cmd[6..];
                match parser::parse_expr_str(expr) {
                    Ok(e) => {
                        // Try full type inference first; fall back to shape.
                        let tenv = seki::typecheck::prelude_types(&state.globals);
                        match seki::typecheck::infer_type(&e, &tenv) {
                            Some(t) => println!("{}", t),
                            None => match seki::typecheck::check_shape(&e, &state.shapes) {
                                Ok(s) => println!("(shape) {:?}", s),
                                Err(err) => eprintln!("{}", err),
                            },
                        }
                    }
                    Err(err) => eprintln!("{}", err),
                }
                continue;
            }
            cmd if cmd.starts_with(":prove ") => {
                let expr_src = &cmd[7..];
                match parser::parse_expr_str(expr_src) {
                    Ok(e) => {
                        let id = next_search_id;
                        next_search_id += 1;
                        let snapshot = state.globals.clone_for_thread();
                        let _ = tx_task.send(SearchTask::Search {
                            id,
                            prop: e,
                            kind: SearchKind::Prove,
                            snapshot,
                        });
                        println!(
                            "  searching... (result will appear before the next prompt)"
                        );
                    }
                    Err(err) => eprintln!("{}", err),
                }
                continue;
            }
            cmd if cmd.starts_with(":why ") => {
                let expr_src = &cmd[5..];
                match parser::parse_expr_str(expr_src) {
                    Ok(e) => {
                        let id = next_search_id;
                        next_search_id += 1;
                        let snapshot = state.globals.clone_for_thread();
                        let _ = tx_task.send(SearchTask::Search {
                            id,
                            prop: e,
                            kind: SearchKind::Why,
                            snapshot,
                        });
                        println!(
                            "  searching for a derivation... (result will appear before the next prompt)"
                        );
                    }
                    Err(err) => eprintln!("{}", err),
                }
                continue;
            }
            _ => {}
        }

        // parse + run
        // try parsing; if it fails because of an unfinished construct, allow
        // multi-line continuation by reading until either parses or a blank line.
        let mut buf2 = line.clone();
        loop {
            match parse_program(&buf2) {
                Ok(decls) => {
                    // Split out `theorem ... := by auto` (and `theorem t : P`
                    // with no proof body, which the parser desugars to the
                    // same form) — dispatch those asynchronously so the
                    // REPL stays responsive while the portfolio runs.
                    let (sync_decls, async_thms) = partition_async_theorems(decls);
                    // Snapshot which names are about to be *redefined* (the
                    // name already exists in defs).  After running, every
                    // proven theorem whose statement mentions one of these
                    // names is silently re-verified — a stale proof against
                    // the new definition will surface as a warning, not as
                    // a corrupted theorem registry.
                    let redef_names: Vec<String> = sync_decls
                        .iter()
                        .filter_map(|ld| match &ld.decl {
                            Decl::Def { name, .. }
                                if state.globals.defs.contains_key(name) =>
                            {
                                Some(name.clone())
                            }
                            _ => None,
                        })
                        .collect();
                    if let Err(e) = state.run_decls(&sync_decls, false) {
                        eprintln!("{}", e);
                    }
                    // Enqueue re-checks for any theorem whose statement
                    // references a redefined name.  Skip names whose new
                    // value is identical to the old (no observable change).
                    for changed in &redef_names {
                        let dependents: Vec<(String, Expr, Proof)> = state
                            .globals
                            .theorem_props
                            .iter()
                            .filter_map(|(thm_name, stmt)| {
                                let mut syms = std::collections::HashSet::new();
                                seki::prover::collect_idents(stmt, &mut syms);
                                if syms.contains(changed) {
                                    state
                                        .globals
                                        .theorem_proofs
                                        .get(thm_name)
                                        .map(|p| {
                                            (thm_name.clone(), stmt.clone(), p.clone())
                                        })
                                } else {
                                    None
                                }
                            })
                            .collect();
                        for (thm_name, prop, proof) in dependents {
                            let id = next_search_id;
                            next_search_id += 1;
                            let snapshot = state.globals.clone_for_thread();
                            let _ = tx_task.send(SearchTask::Search {
                                id,
                                prop,
                                kind: SearchKind::ReCheck {
                                    name: thm_name,
                                    proof,
                                    trigger: changed.clone(),
                                },
                                snapshot,
                            });
                        }
                    }
                    for (name, prop) in async_thms {
                        // Pre-flight a shape check so trivially malformed
                        // propositions fail synchronously with a clear
                        // message rather than being silently queued.
                        if let Err(e) = check_shape(&prop, &state.shapes) {
                            eprintln!("{}", e);
                            continue;
                        }
                        let id = next_search_id;
                        next_search_id += 1;
                        let snapshot = state.globals.clone_for_thread();
                        let _ = tx_task.send(SearchTask::Search {
                            id,
                            prop: prop.clone(),
                            kind: SearchKind::AutoTheorem { name: name.clone(), prop },
                            snapshot,
                        });
                        println!("  theorem {} searching...", name);
                    }
                    break;
                }
                Err(SekiError::Parse(_)) => {
                    print!(".... ");
                    stdout.lock().flush().ok();
                    let mut more = String::new();
                    let nn = stdin.lock().read_line(&mut more).unwrap_or(0);
                    if nn == 0 {
                        eprintln!("incomplete input");
                        break;
                    }
                    if more.trim().is_empty() {
                        // give up
                        if let Err(e) = parse_program(&buf2) {
                            eprintln!("{}", e);
                        }
                        break;
                    }
                    buf2.push('\n');
                    buf2.push_str(&more);
                }
                Err(e) => {
                    eprintln!("{}", e);
                    break;
                }
            }
        }
    }
    // Drain any straggler results posted between the last prompt and the
    // exit signal, then ask the worker to stop and wait for it.  If a
    // search is in flight we don't kill it — `try_portfolio` is not
    // cancellable; the worker just finishes whatever was running.
    drain_search_results(&rx_result, &mut state);
    let _ = tx_task.send(SearchTask::Shutdown);
    let _ = worker.join();
    ExitCode::SUCCESS
}

// silence unused-import warnings: a couple of items are used only when the
// REPL paths exercise typecheck/lookups paths.
#[allow(dead_code)]
fn _touch_unused(_: &Arc<SetVal>) {}

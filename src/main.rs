//! seki — set-theory based theorem prover / programming language.
//!
//! Usage:
//!     seki              start REPL
//!     seki <file.seki>  run a source file
//!     seki --check FILE check a file without printing the value of each expr
//!     seki -e <expr>    evaluate one expression and print its value

use seki::ast::Decl;
use seki::eval::{make_prelude, set_program_args, EvalCtx};
use seki::prover::Prover;
use seki::typecheck::{check_shape, prelude_shapes, ShapeEnv};
use seki::value::{Env, Globals, SetVal, Value};
use seki::{parser, parse_program, SekiError, SekiResult};
use std::collections::HashSet;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

fn main() -> ExitCode {
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
            let state = ProgramState::new();
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
    let mut state = ProgramState::new();
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
    let mut state = ProgramState::new();
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

// -- mutable program state --------------------------------------------------

struct ProgramState {
    globals: Globals,
    shapes: ShapeEnv,
    /// Stack of base directories for resolving relative `import` paths.
    /// The top of the stack is the directory of the currently-executing file
    /// (or CWD if running from REPL / `-e`).
    base_dirs: Vec<PathBuf>,
    /// Files already loaded — avoids duplicate work and detects diamond
    /// imports (which are fine; we just skip the second load).
    loaded: HashSet<PathBuf>,
    /// Files currently being loaded — used to detect import cycles.
    loading: HashSet<PathBuf>,
    /// When `Some`, every name inserted into `globals` while loading a
    /// module is appended here so the loader can later add prefixed aliases
    /// (`M.name`) for them.  Stack-shaped to handle nested imports.
    insert_tracker: Vec<Vec<String>>,
    /// Stack of source texts for the currently-loading files, used by
    /// `annotate_error` to echo the offending source line.  The top is the
    /// file whose decls are being processed right now.
    source_stack: Vec<String>,
    /// Library search paths.  When an `import "path"` doesn't resolve
    /// relative to the importing file, each entry in this list is tried
    /// as a prefix.  This lets users write `import "cas/calc.seki"` and
    /// have it find `<lib_root>/cas/calc.seki` automatically.
    lib_paths: Vec<PathBuf>,
}

impl ProgramState {
    fn new() -> Self {
        Self {
            globals: make_prelude(),
            shapes: prelude_shapes(),
            base_dirs: vec![std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))],
            loaded: HashSet::new(),
            loading: HashSet::new(),
            insert_tracker: Vec::new(),
            source_stack: Vec::new(),
            lib_paths: default_lib_paths(),
        }
    }

    /// Look up line `line` (1-indexed) in the current top-of-stack source,
    /// if any.  Returns None when there is no active source or the line is
    /// out of range.
    fn current_source_line(&self, line: usize) -> Option<String> {
        let src = self.source_stack.last()?;
        let mut lines = src.lines();
        lines.nth(line.saturating_sub(1)).map(|s| s.to_string())
    }

    /// Record that `name` was just inserted into globals; consumed by the
    /// active import loader to apply alias prefixes.
    fn note_insert(&mut self, name: &str) {
        if let Some(top) = self.insert_tracker.last_mut() {
            top.push(name.to_string());
        }
    }

    fn current_base(&self) -> &Path {
        self.base_dirs.last().map(|p| p.as_path()).unwrap_or_else(|| Path::new("."))
    }

    /// Resolve an import path.  Tries in order:
    ///   1. If absolute, use as-is.
    ///   2. Relative to the file currently being loaded.
    ///   3. Each entry in `lib_paths` as a prefix.
    /// Returns the first candidate whose file exists; falls back to the
    /// relative-to-current-base path so the error message is informative.
    fn resolve_import(&self, path: &str) -> PathBuf {
        let p = Path::new(path);
        if p.is_absolute() {
            return p.to_path_buf();
        }
        let primary = self.current_base().join(p);
        if primary.exists() {
            return primary;
        }
        for lib in &self.lib_paths {
            let candidate = lib.join(p);
            if candidate.exists() {
                return candidate;
            }
        }
        primary  // fall back so the error message shows where we looked first
    }

    fn load_module(&mut self, path: &str, alias: Option<&str>) -> SekiResult<()> {
        let resolved = self.resolve_import(path);
        let canonical = resolved
            .canonicalize()
            .unwrap_or_else(|_| resolved.clone());
        if self.loaded.contains(&canonical) {
            // Diamond import — already loaded.  Re-applying alias would
            // duplicate names, so silently skip.
            return Ok(());
        }
        if self.loading.contains(&canonical) {
            return Err(SekiError::Runtime(format!(
                "cyclic import detected at '{}'",
                resolved.display()
            )));
        }
        self.loading.insert(canonical.clone());
        let src = std::fs::read_to_string(&resolved).map_err(|e| {
            SekiError::Runtime(format!(
                "cannot read import '{}': {}",
                resolved.display(),
                e
            ))
        })?;
        let decls = parse_program(&src)?;
        // Track every insert this module makes so we can later apply the
        // alias prefix.  Stack-shaped so nested imports work.
        self.insert_tracker.push(Vec::new());
        let module_dir = resolved
            .parent()
            .map(|p| p.to_path_buf())
            .unwrap_or_else(|| PathBuf::from("."));
        self.base_dirs.push(module_dir);
        self.source_stack.push(src.clone());
        for ld in &decls {
            self.run_decl(ld, true)?;
        }
        self.source_stack.pop();
        self.base_dirs.pop();
        let inserted = self.insert_tracker.pop().unwrap_or_default();
        // Apply alias prefix.  We add prefixed *aliases* of the module's
        // names; the bare names also remain in globals so the module's own
        // internal references still resolve.  This is mild namespace
        // pollution, accepted as a trade-off for implementation simplicity.
        if let Some(alias) = alias {
            for k in inserted {
                let prefixed = format!("{}.{}", alias, k);
                if let Some(v) = self.globals.defs.get(&k).cloned() {
                    self.globals.defs.insert(prefixed.clone(), v);
                } else if let Some(v) = self.globals.theorems.get(&k).cloned() {
                    self.globals.theorems.insert(prefixed.clone(), v);
                } else if let Some(v) = self.globals.axioms.get(&k).cloned() {
                    self.globals.axioms.insert(prefixed.clone(), v);
                } else {
                    continue;
                }
                self.shapes = self
                    .shapes
                    .extend(prefixed, seki::typecheck::Shape::Unknown);
            }
        }
        self.loading.remove(&canonical);
        self.loaded.insert(canonical);
        Ok(())
    }

    fn run_source(&mut self, src: &str, quiet: bool) -> SekiResult<()> {
        let decls = parse_program(src)?;
        self.source_stack.push(src.to_string());
        let result = self.run_decls(&decls, quiet);
        self.source_stack.pop();
        result
    }

    fn run_decls(&mut self, decls: &[seki::ast::LocatedDecl], quiet: bool) -> SekiResult<()> {
        for ld in decls {
            self.run_decl(ld, quiet)?;
        }
        Ok(())
    }

    fn run_decl(&mut self, ld: &seki::ast::LocatedDecl, quiet: bool) -> SekiResult<()> {
        // Wrap any error from this declaration with its source location so
        // the user can find the offending def/theorem/axiom.  When a
        // source text is on the stack, also echo the offending line with
        // a caret to indicate the column.
        let line = ld.line;
        let col = ld.col;
        let source_line = self.current_source_line(line);
        let result = self.run_decl_inner(&ld.decl, quiet);
        result.map_err(|e| annotate_error(e, line, col, source_line.as_deref()))
    }

    fn run_decl_inner(&mut self, d: &Decl, quiet: bool) -> SekiResult<()> {
        match d {
            Decl::Def { name, ty, value } => {
                // shape check first
                if let Some(t) = ty {
                    let _ = check_shape(t, &self.shapes)?;
                }
                let _ = check_shape(value, &self.shapes)?;
                // evaluate the body
                let val = {
                    let ctx = EvalCtx::new(&self.globals);
                    let env = Env::new();
                    ctx.eval(value, &env)?
                };
                // Insert *before* membership check so that recursive function
                // definitions can resolve their own name during sample-testing
                // of the Arrow type.
                let sh = shape_of(&val);
                self.shapes = self.shapes.extend(name.clone(), sh);
                self.globals.defs.insert(name.clone(), val.clone());
                self.note_insert(name);

                // Termination check: only meaningful when `value` is a
                // lambda (so it has named parameters in scope).  Issues a
                // warning, never an error — many genuinely-terminating
                // recursions (e.g. Ackermann, lex-decreasing) won't be
                // recognised by this conservative structural check.
                if let seki::ast::Expr::Lambda { params, body } = value {
                    let pnames: Vec<String> =
                        params.iter().map(|p| p.name.clone()).collect();
                    let status = seki::termination::check(name, &pnames, body);
                    if let seki::termination::TerminationStatus::Unknown(why) = status {
                        if !quiet {
                            eprintln!(
                                "warning: termination of `{}` not verified ({})",
                                name, why
                            );
                        }
                    }
                }

                // Run lightweight type inference on the body.  When the user
                // didn't write an annotation, we record the inferred type so
                // it shows up in `:type` and reflects in error messages.
                let inferred = ty.clone().or_else(|| {
                    let tenv = seki::typecheck::prelude_types(&self.globals);
                    seki::typecheck::infer_type(value, &tenv)
                });
                if let Some(t) = &inferred {
                    self.globals
                        .inferred_types
                        .insert(name.clone(), t.clone());
                }

                // optional set-membership check
                if let Some(t) = ty {
                    // Phase 5: IO monad enforcement.  If the return-type
                    // expression is `IO X` (anywhere in the curried Arrow
                    // chain), this function declares side effects and we
                    // must NOT sample-evaluate it during type-checking,
                    // because doing so would fire the side effects (println,
                    // writeFile, etc.) before the program actually runs.
                    // Conservative skip: the user takes responsibility for
                    // the signature; the body's effects are honored at real
                    // call sites.
                    if !returns_io(t) {
                        let ctx = EvalCtx::new(&self.globals);
                        let env = Env::new();
                        let tv = ctx.eval(t, &env)?;
                        let check_result = match tv {
                            Value::Set(set) => {
                                seki::typecheck::check_def_membership(&val, &set, &ctx, &env)
                            }
                            other => Err(SekiError::Type(format!(
                                "type annotation must be a Set, got {}",
                                other.type_name()
                            ))),
                        };
                        if let Err(e) = check_result {
                            // roll back so a failed annotation doesn't pollute
                            // the env for subsequent declarations.
                            self.globals.defs.remove(name.as_str());
                            return Err(e);
                        }
                    }
                }
                if !quiet {
                    if let Some(t) = &inferred {
                        println!("def {} : {} = {}", name, t, val);
                    } else {
                        println!("def {} = {}", name, val);
                    }
                }
            }
            Decl::Axiom { name, prop } => {
                // shape check the proposition
                let _ = check_shape(prop, &self.shapes)?;
                // accept verbatim — no proof needed
                let ctx = EvalCtx::new(&self.globals);
                let env = Env::new();
                // we don't *prove* the prop; we record it as if it were true
                let _ = ctx.eval(prop, &env).ok(); // best-effort eval to surface obvious errors
                self.globals
                    .axioms
                    .insert(name.clone(), Value::Bool(true));
                self.globals
                    .axiom_props
                    .insert(name.clone(), prop.clone());
                self.shapes = self
                    .shapes
                    .extend(name.clone(), seki::typecheck::Shape::Bool);
                self.note_insert(name);
                if !quiet {
                    println!("axiom {} accepted", name);
                }
            }
            Decl::Theorem { name, prop, proof } => {
                let _ = check_shape(prop, &self.shapes)?;
                let ctx = EvalCtx::new(&self.globals);
                let env = Env::new();
                let prover = Prover::new(&ctx);
                let v = prover.verify(prop, proof, &env)?;
                self.globals.theorems.insert(name.clone(), v);
                self.globals
                    .theorem_props
                    .insert(name.clone(), prop.clone());
                self.shapes = self
                    .shapes
                    .extend(name.clone(), seki::typecheck::Shape::Bool);
                self.note_insert(name);
                if !quiet {
                    println!("theorem {} ✓ proved", name);
                }
            }
            Decl::Expr(e) => {
                let _ = check_shape(e, &self.shapes)?;
                let ctx = EvalCtx::new(&self.globals);
                let env = Env::new();
                let v = ctx.eval(e, &env)?;
                if !quiet && !matches!(v, Value::Unit) {
                    println!("{}", v);
                }
            }
            Decl::Import { path, alias } => {
                self.load_module(path, alias.as_deref())?;
                if !quiet {
                    match alias {
                        Some(a) => println!("imported {} as {}", path, a),
                        None => println!("imported {}", path),
                    }
                }
            }
            Decl::ClassMeta { class_name, ctor_name, methods } => {
                self.globals
                    .class_ctor
                    .insert(class_name.clone(), ctor_name.clone());
                for m in methods {
                    self.globals
                        .class_methods
                        .insert(m.clone(), class_name.clone());
                }
            }
            Decl::InstanceMeta {
                instance_name,
                class_name,
                type_name,
            } => {
                self.globals.instances.insert(
                    (class_name.clone(), type_name.clone()),
                    instance_name.clone(),
                );
            }
            Decl::DataMeta { name, ctors } => {
                self.globals.data_info.insert(name.clone(), ctors.clone());
            }
        }
        Ok(())
    }
}

fn shape_of(v: &Value) -> seki::typecheck::Shape {
    use seki::typecheck::Shape::*;
    match v {
        Value::Int(_) => Int,
        Value::Real(_) => Real,
        Value::Bool(_) => Bool,
        Value::Str(_) => Str,
        Value::Set(_) => Set,
        Value::Tuple(_) => Tuple,
        Value::Closure { .. } | Value::Builtin(_) => Fn,
        Value::Unit => Unit,
        Value::Ref(_) | Value::Dict(_) | Value::Handle(_) => Tuple,
    }
}

/// True if the type expression contains an `IO _` application *anywhere*
/// in the return-position chain of curried arrows.  Used by the def-time
/// membership check to skip sample-evaluating functions that are declared
/// to have side effects.
fn returns_io(t: &seki::ast::Expr) -> bool {
    use seki::ast::Expr;
    match t {
        // `IO X` at the outermost position.
        Expr::App { func, args } => {
            args.len() == 1 && matches!(func.as_ref(), Expr::Var { name: n, .. } if n == "IO")
        }
        // Recurse through arrow chains so `A -> B -> IO C` is detected.
        Expr::Arrow(_, rhs) => returns_io(rhs),
        Expr::DepArrow { to, .. } => returns_io(to),
        _ => false,
    }
}

/// Build the default list of library search directories used by
/// `import` when a path isn't found relative to the current file.
///
/// Tried in order:
///   1. Each path in the `SEKI_LIB_PATH` environment variable (`:`-separated)
///   2. The current working directory's `lib/`
///   3. The seki binary's parent directory + `../lib`  (cargo workspace)
///      and `../../lib`  (release install)
///   4. `~/.seki/lib`  (user-level)
///
/// Only entries that point to existing directories are kept.
fn default_lib_paths() -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = Vec::new();
    // 1. SEKI_LIB_PATH environment variable
    if let Ok(env_var) = std::env::var("SEKI_LIB_PATH") {
        for seg in env_var.split(':') {
            if !seg.is_empty() {
                paths.push(PathBuf::from(seg));
            }
        }
    }
    // 2. CWD/lib
    if let Ok(cwd) = std::env::current_dir() {
        paths.push(cwd.join("lib"));
    }
    // 3. relative to the seki binary
    if let Ok(exe) = std::env::current_exe() {
        if let Some(parent) = exe.parent() {
            paths.push(parent.join("lib"));
            if let Some(grand) = parent.parent() {
                paths.push(grand.join("lib"));
                if let Some(great) = grand.parent() {
                    paths.push(great.join("lib"));
                }
            }
        }
    }
    // 4. ~/.seki/lib
    if let Some(home) = std::env::var_os("HOME") {
        let mut h = PathBuf::from(home);
        h.push(".seki");
        h.push("lib");
        paths.push(h);
    }
    // De-duplicate and keep only existing directories.
    let mut seen: std::collections::HashSet<PathBuf> = std::collections::HashSet::new();
    let mut out: Vec<PathBuf> = Vec::new();
    for p in paths {
        let canon = p.canonicalize().unwrap_or_else(|_| p.clone());
        if seen.contains(&canon) {
            continue;
        }
        if canon.is_dir() {
            seen.insert(canon.clone());
            out.push(canon);
        }
    }
    out
}

/// Re-emit an error with the source position prefix `[line:col]` and, when
/// a source line is available, append a Rust-style snippet with a caret
/// pointing at the column.  Lex/Parse errors already carry their own
/// positions and are passed through unchanged.
fn annotate_error(
    e: SekiError,
    line: usize,
    col: usize,
    source_line: Option<&str>,
) -> SekiError {
    // Phase 7: the evaluator may have already attached a precise span via
    // an `[at L:C]` prefix in the error body (currently only Expr::Var
    // carries this).  When present, prefer it over the decl-level position.
    let (real_line, real_col, body_e) = extract_at_prefix(&e)
        .map(|(l, c, body)| (l, c, body))
        .unwrap_or((line, col, e.clone()));

    // For older error shapes (no `[at L:C]` prefix), fall back to the
    // textual identifier scan to refine the column on the same line.
    let refined_col = if real_line == line {
        refine_col(&body_e, real_col, source_line)
    } else {
        real_col
    };
    let refined_len = refined_identifier_len(&body_e).unwrap_or(1);

    let prefix = format!("[{}:{}] ", real_line, refined_col);
    // From here on, work with the body sans `[at L:C]` prefix.
    let e = body_e;
    // The next match uses `e` to produce the final shape.
    let source_line = if real_line == line { source_line } else { None };
    let snippet = source_line.map(|line_text| {
        let trimmed = line_text.trim_end();
        let caret_indent = " ".repeat(refined_col.saturating_sub(1));
        let caret = "^".repeat(refined_len.max(1));
        format!(
            "\n  |\n  | {}\n  | {}{}",
            trimmed, caret_indent, caret
        )
    });
    let with_snippet = |body: String| -> String {
        match &snippet {
            Some(s) => format!("{}{}{}", prefix, body, s),
            None => format!("{}{}", prefix, body),
        }
    };
    match e {
        SekiError::Lex(_) | SekiError::Parse(_) => e,
        SekiError::Type(m) => SekiError::Type(with_snippet(m)),
        SekiError::Runtime(m) => SekiError::Runtime(with_snippet(m)),
        SekiError::Proof(m) => SekiError::Proof(with_snippet(m)),
    }
}

/// Strip an `[at L:C] rest` prefix from a SekiError body.  Returns the
/// `(line, col, error-with-prefix-removed)` tuple.  Used by `annotate_error`
/// to honor Expr-level spans (currently emitted by `Expr::Var` evaluation).
fn extract_at_prefix(e: &SekiError) -> Option<(usize, usize, SekiError)> {
    let body = match e {
        SekiError::Runtime(m) => m.as_str(),
        SekiError::Type(m)    => m.as_str(),
        _ => return None,
    };
    let s = body.strip_prefix("[at ")?;
    let close = s.find(']')?;
    let inner = &s[..close];
    let mut parts = inner.split(':');
    let l: usize = parts.next()?.trim().parse().ok()?;
    let c: usize = parts.next()?.trim().parse().ok()?;
    let rest = s[close + 1..].trim_start().to_string();
    let new_e = match e {
        SekiError::Runtime(_) => SekiError::Runtime(rest),
        SekiError::Type(_)    => SekiError::Type(rest),
        _ => return None,
    };
    Some((l, c, new_e))
}

/// Try to extract the failing identifier from `unbound identifier 'X'` style
/// runtime errors so the caret can point at `X` instead of the decl start.
fn extract_failing_ident(e: &SekiError) -> Option<&str> {
    let msg = match e {
        SekiError::Runtime(m) => m.as_str(),
        SekiError::Type(m)    => m.as_str(),
        _ => return None,
    };
    // Grab the first quoted name after "identifier"; works for the variants
    // we emit (unbound / type mismatch / etc).
    let key = msg.find("identifier '")?;
    let start = key + "identifier '".len();
    let end = msg[start..].find('\'')?;
    Some(&msg[start..start + end])
}

/// If we know what identifier failed, find its column on the source line
/// and use *that* instead of the decl-start column.  Falls back to the
/// passed-in `col` when no source or no match.
fn refine_col(e: &SekiError, decl_col: usize, source_line: Option<&str>) -> usize {
    let ident = match extract_failing_ident(e) { Some(s) => s, None => return decl_col };
    let line = match source_line { Some(s) => s, None => return decl_col };
    // Only accept matches that aren't substrings of a longer identifier:
    // require the surrounding chars to be non-alphanumeric / underscore.
    let bytes = line.as_bytes();
    let mut i = 0;
    while i + ident.len() <= bytes.len() {
        if &bytes[i..i + ident.len()] == ident.as_bytes() {
            let left_ok = i == 0
                || !is_ident_continue(bytes[i - 1] as char);
            let right_ok = i + ident.len() == bytes.len()
                || !is_ident_continue(bytes[i + ident.len()] as char);
            if left_ok && right_ok {
                // Convert byte index to a 1-indexed *character* column —
                // works for ASCII source which is the seki norm.
                return i + 1;
            }
        }
        i += 1;
    }
    decl_col
}

fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Length of the underlined region — equal to the failing identifier's
/// length when known, else 1 character.
fn refined_identifier_len(e: &SekiError) -> Option<usize> {
    extract_failing_ident(e).map(|s| s.chars().count())
}

// -- REPL -------------------------------------------------------------------

fn repl_with(extra_libs: Vec<PathBuf>) -> ExitCode {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut state = ProgramState::new();
    for p in extra_libs {
        state.lib_paths.insert(0, p);
    }

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
            _ => {}
        }

        // parse + run
        // try parsing; if it fails because of an unfinished construct, allow
        // multi-line continuation by reading until either parses or a blank line.
        let mut buf2 = line.clone();
        loop {
            match parse_program(&buf2) {
                Ok(decls) => {
                    if let Err(e) = state.run_decls(&decls, false) {
                        eprintln!("{}", e);
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
    ExitCode::SUCCESS
}

// silence unused-import warnings: a couple of items are used only when the
// REPL paths exercise typecheck/lookups paths.
#[allow(dead_code)]
fn _touch_unused(_: &Arc<SetVal>) {}

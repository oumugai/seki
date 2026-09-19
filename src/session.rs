//! The declaration driver: the thing that actually *runs* a seki program.
//!
//! A [`Session`] owns the globals, the shape environment, the import stack
//! and the library search path, and knows how to execute one declaration
//! against them.  Everything that gives a `.seki` file its meaning — `def`
//! membership checks, `theorem` verification, `import` resolution, the
//! termination warning — lives here.
//!
//! This used to sit inside `src/main.rs`, which meant the only way to reach
//! it was to run the binary.  Three consumers had to work around that:
//! `tests/integration.rs` reimplemented declaration handling (and its copy
//! could not do `import` at all), `src/lsp_main.rs` fell back to
//! parse-only diagnostics, and the `run` API that `src/lib.rs` documented
//! did not exist.  It is a library concern, so it lives in the library.

use crate::ast::{Decl, Expr, Proof};
use crate::eval::{make_prelude, EvalCtx};
use crate::prover::Prover;
use crate::typecheck::{check_shape, prelude_shapes, ShapeEnv};
use crate::value::{Env, Globals, Value};
use crate::trust::TrustLevel;
use crate::{parse_program, SekiError, SekiResult};
use std::collections::HashSet;
use std::path::{Path, PathBuf};

// -- mutable program state --------------------------------------------------

pub struct Session {
    pub globals: Globals,
    pub shapes: ShapeEnv,
    /// Stack of base directories for resolving relative `import` paths.
    /// The top of the stack is the directory of the currently-executing file
    /// (or CWD if running from REPL / `-e`).
    pub base_dirs: Vec<PathBuf>,
    /// Files already loaded — avoids duplicate work and detects diamond
    /// imports (which are fine; we just skip the second load).
    pub loaded: HashSet<PathBuf>,
    /// Files currently being loaded — used to detect import cycles.
    pub loading: HashSet<PathBuf>,
    /// When `Some`, every name inserted into `globals` while loading a
    /// module is appended here so the loader can later add prefixed aliases
    /// (`M.name`) for them.  Stack-shaped to handle nested imports.
    pub insert_tracker: Vec<Vec<String>>,
    /// Stack of source texts for the currently-loading files, used by
    /// `annotate_error` to echo the offending source line.  The top is the
    /// file whose decls are being processed right now.
    pub source_stack: Vec<String>,
    /// Library search paths.  When an `import "path"` doesn't resolve
    /// relative to the importing file, each entry in this list is tried
    /// as a prefix.  This lets users write `import "cas/calc.seki"` and
    /// have it find `<lib_root>/cas/calc.seki` automatically.
    pub lib_paths: Vec<PathBuf>,
    /// Refuse any theorem whose proof is not fully [`TrustLevel::Sound`] —
    /// the machine-checked form of the audit rule in
    /// `docs/spec/06-soundness.md` §6.0/§6.6.  Off by default (`--strict` on the
    /// command line turns it on) because a lot of perfectly useful
    /// exploratory work leans on `axiom`.
    pub strict: bool,
    /// Reject a conclusion its assumptions warrant less than this.
    ///
    /// Separate from `strict`: `strict` refuses *any* assumption, this one
    /// allows them but sets a floor on how much they have to be worth.
    /// See `crate::confidence`.
    pub min_confidence: Option<crate::algebra::Rat>,
}

impl Session {
    pub fn new() -> Self {
        Self {
            globals: make_prelude(),
            shapes: prelude_shapes(),
            base_dirs: vec![std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))],
            loaded: HashSet::new(),
            loading: HashSet::new(),
            insert_tracker: Vec::new(),
            source_stack: Vec::new(),
            lib_paths: default_lib_paths(),
            strict: std::env::var("SEKI_STRICT").is_ok(),
            min_confidence: std::env::var("SEKI_MIN_CONFIDENCE")
                .ok()
                .and_then(|v| v.parse::<f64>().ok())
                .and_then(crate::confidence::rational_from_decimal),
        }
    }

    /// Look up line `line` (1-indexed) in the current top-of-stack source,
    /// if any.  Returns None when there is no active source or the line is
    /// out of range.
    pub fn current_source_line(&self, line: usize) -> Option<String> {
        let src = self.source_stack.last()?;
        let mut lines = src.lines();
        lines.nth(line.saturating_sub(1)).map(|s| s.to_string())
    }

    /// Record that `name` was just inserted into globals; consumed by the
    /// active import loader to apply alias prefixes.
    pub fn note_insert(&mut self, name: &str) {
        if let Some(top) = self.insert_tracker.last_mut() {
            top.push(name.to_string());
        }
    }

    pub fn current_base(&self) -> &Path {
        self.base_dirs.last().map(|p| p.as_path()).unwrap_or_else(|| Path::new("."))
    }

    /// Resolve an import path.  Tries in order:
    ///   1. If absolute, use as-is.
    ///   2. Relative to the file currently being loaded.
    ///   3. Each entry in `lib_paths` as a prefix.
    /// Returns the first candidate whose file exists; falls back to the
    /// relative-to-current-base path so the error message is informative.
    pub fn resolve_import(&self, path: &str) -> PathBuf {
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

    pub fn load_module(&mut self, path: &str, alias: Option<&str>) -> SekiResult<()> {
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
                    .extend(prefixed, crate::typecheck::Shape::Unknown);
            }
        }
        self.loading.remove(&canonical);
        self.loaded.insert(canonical);
        Ok(())
    }

    pub fn run_source(&mut self, src: &str, quiet: bool) -> SekiResult<()> {
        let decls = parse_program(src)?;
        self.source_stack.push(src.to_string());
        let result = self.run_decls(&decls, quiet);
        self.source_stack.pop();
        result
    }

    pub fn run_decls(&mut self, decls: &[crate::ast::LocatedDecl], quiet: bool) -> SekiResult<()> {
        for ld in decls {
            self.run_decl(ld, quiet)?;
        }
        Ok(())
    }

    pub fn run_decl(&mut self, ld: &crate::ast::LocatedDecl, quiet: bool) -> SekiResult<()> {
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

    /// Verify one theorem and commit it to `globals`, recording what the
    /// proof is actually worth.
    ///
    /// The REPL's background `by auto` search commits theorems too; routing
    /// both through here is what keeps `theorem_trust` complete.  A missing
    /// entry reads as `Sound` in `Prover::name_trust`, so a path that
    /// forgot to fill it in would quietly launder a sampled proof.
    pub fn verify_and_register(
        &mut self,
        name: &str,
        prop: &Expr,
        proof: &Proof,
    ) -> SekiResult<TrustLevel> {
        let (cert, verdict) = {
            let ctx = EvalCtx::new(&self.globals);
            let env = Env::new();
            // The tactic searches, and hands back a proof term.
            let cert = Prover::new(&ctx).certify(prop, proof, &env)?;
            // The kernel then re-establishes that proof term from
            // primitives, in a context that cannot be talked into sampling
            // an infinite domain.  Nothing here calls back into a tactic.
            let kernel_ctx = EvalCtx::finite_only(&self.globals);
            let verdict = crate::kernel::check(prop, &cert, &kernel_ctx, &env)?;
            (cert, verdict)
        };
        let trust = TrustLevel::from_verdict(&verdict);
        if let Some(floor) = self.min_confidence {
            let c = crate::confidence::of_verdict(&verdict, &self.globals);
            if !c.meets(floor) {
                return Err(SekiError::Proof(format!(
                    "--min-confidence {}: `{}` is only warranted to {} — {}",
                    floor,
                    name,
                    c.lower_bound(),
                    if matches!(c, crate::confidence::Confidence::Unqualified) {
                        "it rests on no assumption carrying a confidence".to_string()
                    } else {
                        c.describe()
                    }
                )));
            }
        }
        if self.strict && !trust.is_sound() {
            return Err(SekiError::Proof(format!(
                "--strict: theorem `{}` is {}, not a proof — {}",
                name,
                trust,
                trust.rejection_reason().unwrap_or("")
            )));
        }
        self.globals
            .theorems
            .insert(name.to_string(), Value::Bool(true));
        self.globals
            .theorem_props
            .insert(name.to_string(), prop.clone());
        self.globals
            .theorem_proofs
            .insert(name.to_string(), proof.clone());
        self.globals.theorem_certs.insert(name.to_string(), cert);
        self.globals
            .theorem_verdicts
            .insert(name.to_string(), verdict);
        self.globals.theorem_trust.insert(name.to_string(), trust);
        self.shapes = self
            .shapes
            .extend(name.to_string(), crate::typecheck::Shape::Bool);
        Ok(trust)
    }

    /// Try to *prove* what a refinement annotation claims, instead of
    /// leaving it to the sample check.
    ///
    /// `def f : A -> {y in B | Q y}` asserts `forall x in A, Q[y := f x]`.
    /// That is an ordinary proposition, so it goes through the ordinary
    /// route: the portfolio searches for a proof, the prover turns what it
    /// finds into a proof term, and the kernel re-establishes it.  When
    /// none of that succeeds the definition still stands — the sample check
    /// already passed — but it is recorded as `Sampled`, so `--strict` can
    /// refuse it and `--audit` can name it.
    fn discharge_refinement(&mut self, name: &str, ty: &Expr) -> SekiResult<()> {
        let obligation = {
            let ctx = EvalCtx::new(&self.globals);
            match crate::obligation::for_definition(name, ty, &ctx, &Env::new()) {
                Some(o) => o,
                None => return Ok(()),
            }
        };
        let (trust, cert) = {
            let ctx = EvalCtx::new(&self.globals);
            let env = Env::new();
            let prover = Prover::new(&ctx);
            match prover.try_portfolio_sound(&obligation.goal, &env) {
                Some(proof) => match prover.certify(&obligation.goal, &proof, &env) {
                    Ok(cert) => {
                        let kernel_ctx = EvalCtx::finite_only(&self.globals);
                        match crate::kernel::check(&obligation.goal, &cert, &kernel_ctx, &env)
                        {
                            Ok(v) => (TrustLevel::from_verdict(&v), Some(cert)),
                            Err(_) => (TrustLevel::Sampled, None),
                        }
                    }
                    Err(_) => (TrustLevel::Sampled, None),
                },
                None => (TrustLevel::Sampled, None),
            }
        };
        if self.strict && !trust.is_sound() {
            self.globals.defs.remove(name);
            return Err(SekiError::Type(format!(
                "--strict: the type of `{}` claims `{}` for every argument, but that \
                 was only checked on a sample of the domain, not proved. The \
                 obligation is `{}`.",
                name, obligation.refinement, obligation.goal
            )));
        }
        self.globals
            .def_obligations
            .insert(name.to_string(), (obligation.goal, cert));
        self.globals.def_trust.insert(name.to_string(), trust);
        Ok(())
    }

    pub fn run_decl_inner(&mut self, d: &Decl, quiet: bool) -> SekiResult<()> {
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
                if let crate::ast::Expr::Lambda { params, body } = value {
                    let pnames: Vec<String> =
                        params.iter().map(|p| p.name.clone()).collect();
                    let status = crate::termination::check(name, &pnames, body);
                    if let crate::termination::TerminationStatus::Unknown(why) = status {
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
                    let tenv = crate::typecheck::prelude_types(&self.globals);
                    crate::typecheck::infer_type(value, &tenv)
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
                                crate::typecheck::check_def_membership(&val, &set, &ctx, &env)
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
                        // The sample check above only ever says "no
                        // counterexample among the points I tried".  If the
                        // annotation refines the return type, that claim is
                        // an ordinary proposition, so try to actually
                        // *prove* it — through the same prover and the same
                        // kernel a theorem goes through.
                        self.discharge_refinement(name, t)?;
                    }
                }
                if !quiet {
                    // Only a definition that made a refinement claim gets a
                    // marker, so ordinary definitions stay quiet.
                    let mark = self
                        .globals
                        .def_trust
                        .get(name)
                        .map(|t| t.marker())
                        .unwrap_or("");
                    if let Some(t) = &inferred {
                        println!("def {} : {} = {}{}", name, t, val, mark);
                    } else {
                        println!("def {} = {}{}", name, val, mark);
                    }
                }
            }
            Decl::Axiom { name, prop, confidence, provenance } => {
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
                // An assumption believed rather than asserted records how
                // much of one it is, and where it came from.  Neither
                // changes what the kernel does — see `crate::confidence`.
                if let Some(c) = confidence {
                    let ctx = EvalCtx::new(&self.globals);
                    let v = ctx.eval(c, &Env::new())?;
                    let r = match v {
                        Value::Real(f) => crate::confidence::rational_from_decimal(f),
                        Value::Int(n) => Some(crate::algebra::Rat::from_int(n as i128)),
                        other => {
                            return Err(SekiError::Type(format!(
                                "axiom {}: confidence must be a number in [0, 1], got {}",
                                name,
                                other.type_name()
                            )))
                        }
                    };
                    let r = r.ok_or_else(|| {
                        SekiError::Type(format!(
                            "axiom {}: confidence is not an exact rational",
                            name
                        ))
                    })?;
                    if r.sign() < 0 || r.sub(crate::algebra::Rat::from_int(1)).sign() > 0 {
                        return Err(SekiError::Type(format!(
                            "axiom {}: confidence must be in [0, 1], got {}",
                            name, r
                        )));
                    }
                    self.globals.axiom_confidence.insert(name.clone(), r);
                }
                if let Some(p) = provenance {
                    self.globals
                        .axiom_provenance
                        .insert(name.clone(), p.clone());
                }
                self.shapes = self
                    .shapes
                    .extend(name.clone(), crate::typecheck::Shape::Bool);
                self.note_insert(name);
                if !quiet {
                    match self.globals.axiom_confidence.get(name) {
                        Some(c) => println!("axiom {} assumed (confidence {})", name, c),
                        None => println!("axiom {} accepted", name),
                    }
                }
            }
            Decl::Theorem { name, prop, proof } => {
                let _ = check_shape(prop, &self.shapes)?;
                let trust = self.verify_and_register(name, prop, proof)?;
                self.note_insert(name);
                if !quiet {
                    println!("theorem {} ✓ proved{}", name, trust.marker());
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

pub fn shape_of(v: &Value) -> crate::typecheck::Shape {
    use crate::typecheck::Shape::*;
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
pub fn returns_io(t: &crate::ast::Expr) -> bool {
    use crate::ast::Expr;
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
pub fn default_lib_paths() -> Vec<PathBuf> {
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
pub fn annotate_error(
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


//! Recursive-descent parser for seki.
//!
//! Operator precedence (low → high), left-assoc unless noted:
//!   1. `->`           type arrow            (right-assoc)
//!   2. `or`
//!   3. `and`
//!   4. `not`          (prefix unary)
//!   5. comparison     `==`,`!=`,`<`,`<=`,`>`,`>=`,`in`,`notin`,`subset`
//!   6. set-additive   `union`,`diff`
//!   7. set-mul        `intersect`
//!   8. additive       `+`,`-`
//!   9. multiplicative `*`,`/`,`mod`
//!  10. unary `-`
//!  11. application    (juxtaposition, left-assoc)
//!  12. atom

use crate::ast::*;
use crate::lexer::{Tok, Token};
use crate::{SekiError, SekiResult};

struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
    /// Suppress treating `in` as the membership comparison operator while
    /// parsing the right-hand side of a `let x = … in body`, so the binder's
    /// `in` keyword isn't accidentally consumed as `5 in x * x`.
    suppress_in_op: bool,
    /// Class registry built during parsing.  Maps class name to the ordered
    /// list of its method names so that `instance C T where m1 = ...; m2 = ...`
    /// can emit the constructor application in the right slot order.
    classes: std::collections::HashMap<String, Vec<String>>,
    /// data type → list of constructor names (in declaration order).  Used
    /// for `match` exhaustiveness warnings.
    data_ctors: std::collections::HashMap<String, Vec<String>>,
    /// constructor name → data type it belongs to.  Inverse of `data_ctors`.
    ctor_to_data: std::collections::HashMap<String, String>,
}

impl<'a> Parser<'a> {
    fn new(toks: &'a [Token]) -> Self {
        Self {
            toks,
            pos: 0,
            suppress_in_op: false,
            classes: std::collections::HashMap::new(),
            data_ctors: std::collections::HashMap::new(),
            ctor_to_data: std::collections::HashMap::new(),
        }
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn peek_at(&self, k: usize) -> &Tok {
        if self.pos + k < self.toks.len() {
            &self.toks[self.pos + k].tok
        } else {
            &Tok::Eof
        }
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        self.pos += 1;
        t
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek(), Tok::Eof)
    }

    fn loc(&self) -> (usize, usize) {
        // Clamp past-end indexing (fuzz-test found this panicked on
        // unbalanced inputs that advanced past the EOF sentinel).  Fall
        // back to the last token's position when out of range.
        let i = self.pos.min(self.toks.len().saturating_sub(1));
        match self.toks.get(i) {
            Some(t) => (t.line, t.col),
            None    => (1, 1),  // wholly empty token stream
        }
    }

    fn expect(&mut self, tok: &Tok, ctx: &str) -> SekiResult<()> {
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(tok) {
            self.bump();
            Ok(())
        } else {
            let (l, c) = self.loc();
            Err(SekiError::Parse(format!(
                "expected {:?} but got {:?} at {}:{} ({})",
                tok,
                self.peek(),
                l,
                c,
                ctx
            )))
        }
    }

    // -- top level ----------------------------------------------------------

    fn parse_program(&mut self) -> SekiResult<Vec<crate::ast::LocatedDecl>> {
        let mut out = Vec::new();
        while !self.at_eof() {
            if matches!(self.peek(), Tok::Semi) {
                self.bump();
                continue;
            }
            // Capture the source position of the keyword that starts this
            // top-level form, before any tokens are consumed.  All decls
            // produced by a single `parse_top` call (e.g. multiple `def`s
            // from one `data` declaration) share that location.
            let (line, col) = self.loc();
            // A single syntactic top-level form may desugar into multiple
            // declarations (e.g. `data Foo = A | B Int` expands to `def A`
            // and `def B`).  Hence `parse_top` returns `Vec<Decl>`.
            for d in self.parse_top()? {
                out.push(crate::ast::LocatedDecl { decl: d, line, col });
            }
            if matches!(self.peek(), Tok::Semi) {
                self.bump();
            }
        }
        Ok(out)
    }

    fn parse_top(&mut self) -> SekiResult<Vec<Decl>> {
        match self.peek() {
            Tok::KwDef => Ok(vec![self.parse_def()?]),
            Tok::KwTheorem => Ok(vec![self.parse_theorem()?]),
            Tok::KwAxiom => Ok(vec![self.parse_axiom()?]),
            Tok::KwData => self.parse_data(),
            Tok::KwImport => Ok(vec![self.parse_import()?]),
            Tok::KwClass => self.parse_class(),
            Tok::KwInstance => self.parse_instance(),
            _ => {
                let e = self.parse_expr()?;
                Ok(vec![Decl::Expr(e)])
            }
        }
    }

    /// `import "path/file.seki"` or `import "path/file.seki" as Name`.
    fn parse_import(&mut self) -> SekiResult<Decl> {
        self.expect(&Tok::KwImport, "import")?;
        let path = match self.bump() {
            Tok::Str(s) => s,
            other => {
                return Err(SekiError::Parse(format!(
                    "import path must be a string literal, got {:?}",
                    other
                )))
            }
        };
        let mut alias = None;
        if matches!(self.peek(), Tok::KwAs) {
            self.bump();
            alias = Some(self.eat_ident("import alias")?);
        }
        Ok(Decl::Import { path, alias })
    }

    fn parse_def(&mut self) -> SekiResult<Decl> {
        self.expect(&Tok::KwDef, "def")?;
        let name = self.eat_ident("def name")?;

        // collect optional params: ident or (ident : type) ...
        let mut params: Vec<Param> = Vec::new();
        loop {
            match self.peek() {
                Tok::Ident(_) => {
                    let n = self.eat_ident("param")?;
                    params.push(Param { name: n, ty: None });
                }
                Tok::LParen => {
                    // could be a typed param or grouping; only treat as typed param
                    // if it looks like (ident : type)
                    if matches!(self.peek_at(1), Tok::Ident(_))
                        && matches!(self.peek_at(2), Tok::Colon)
                    {
                        self.bump(); // (
                        let n = self.eat_ident("param")?;
                        self.expect(&Tok::Colon, "param type")?;
                        let ty = self.parse_expr()?;
                        self.expect(&Tok::RParen, "param close")?;
                        params.push(Param {
                            name: n,
                            ty: Some(ty),
                        });
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }

        // optional return type ': T'
        let mut ret_ty: Option<Expr> = None;
        if matches!(self.peek(), Tok::Colon) {
            self.bump();
            ret_ty = Some(self.parse_expr()?);
        }

        self.expect(&Tok::Assign, "':=' in def")?;
        let body = self.parse_expr()?;

        // build full type and value
        let value = if params.is_empty() {
            body
        } else {
            Expr::Lambda {
                params: params.clone(),
                body: Box::new(body),
            }
        };
        let ty = if !params.is_empty() {
            // construct curried arrow type if every param has a type and ret_ty given
            let all_typed = params.iter().all(|p| p.ty.is_some());
            if all_typed && ret_ty.is_some() {
                let mut t = ret_ty.clone().unwrap();
                for p in params.iter().rev() {
                    t = Expr::Arrow(Box::new(p.ty.clone().unwrap()), Box::new(t));
                }
                Some(t)
            } else {
                ret_ty
            }
        } else {
            ret_ty
        };
        Ok(Decl::Def { name, ty, value })
    }

    fn parse_theorem(&mut self) -> SekiResult<Decl> {
        self.expect(&Tok::KwTheorem, "theorem")?;
        let name = self.eat_ident("theorem name")?;
        self.expect(&Tok::Colon, "':' in theorem")?;
        let prop = self.parse_expr()?;
        self.expect(&Tok::Assign, "':=' in theorem")?;
        let proof = self.parse_proof()?;
        Ok(Decl::Theorem { name, prop, proof })
    }

    /// `data Name [TypeParams] = Ctor1 [Args1] | Ctor2 [Args2] | ...`
    ///
    /// Pure parser-level desugar: each constructor `Ctor T1 T2 ... Tk` becomes
    /// a `def Ctor := \x1 x2 ... xk -> ("Ctor", (x1, (x2, (..., (xk, ())))))`.
    /// 0-ary constructors become `def Ctor := ("Ctor", ())`.
    /// The original `data` keyword leaves no AST trace — the runtime sees
    /// just the generated `def`s, fully backward-compatible with existing
    /// tagged-pair encoding.
    fn parse_data(&mut self) -> SekiResult<Vec<Decl>> {
        self.expect(&Tok::KwData, "data")?;
        let data_name = self.eat_ident("data type name")?;
        // Optional type params: any number of identifiers before `=`
        let mut _params: Vec<String> = Vec::new();
        while matches!(self.peek(), Tok::Ident(_)) {
            _params.push(self.eat_ident("data type param")?);
        }
        // accept either `=` or `:=` between header and body
        if matches!(self.peek(), Tok::Assign) {
            self.bump();
        } else {
            return Err(SekiError::Parse(
                "expected '=' or ':=' after data declaration header".into(),
            ));
        }
        // Constructors: Ctor [Args]  (| Ctor [Args])*
        let mut decls: Vec<Decl> = Vec::new();
        let mut ctor_names: Vec<String> = Vec::new();
        // Also keep per-ctor arg types as their textual rendering, so the
        // induction tactic can later detect recursive arguments (arg type
        // == data type name) without needing a full type system.
        let mut ctor_arities: Vec<(String, Vec<String>)> = Vec::new();
        let mut all_nullary = true;
        loop {
            let ctor_line = self.toks[self.pos].line;
            let ctor_name = self.eat_ident("constructor name")?;
            // Constructor argument types: atom-level expressions, on the
            // same line as the constructor name (or at strictly-greater
            // indent on a continuation line).  Multi-line ctor args can be
            // grouped inside parens.
            let mut arity = 0usize;
            let mut arg_types: Vec<String> = Vec::new();
            while self.starts_atom() {
                let next = &self.toks[self.pos];
                if next.line != ctor_line {
                    break;
                }
                let at = self.parse_atom()?;
                arg_types.push(format!("{}", at));
                arity += 1;
            }
            if arity > 0 {
                all_nullary = false;
            }
            decls.push(make_ctor_decl(&ctor_name, arity));
            ctor_names.push(ctor_name.clone());
            ctor_arities.push((ctor_name.clone(), arg_types));
            self.ctor_to_data
                .insert(ctor_name.clone(), data_name.clone());
            if matches!(self.peek(), Tok::Bar) {
                self.bump();
                continue;
            }
            break;
        }
        // When every constructor is nullary the data type is a finite enum
        // — auto-generate `def <DataName> := {C1, C2, ...}` so users can
        // write `forall x in DataName, P x` and have it work directly
        // through the standard finite-set enumeration of `by eval`.
        if all_nullary && !ctor_names.is_empty() {
            let elems: Vec<Expr> = ctor_names
                .iter()
                .map(|c| Expr::Var { name: c.clone(), line: 0, col: 0 })
                .collect();
            decls.push(Decl::Def {
                name: data_name.clone(),
                ty: None,
                value: Expr::SetEnum(elems),
            });
        }
        // Emit compiler-internal metadata so the prover can apply structural
        // induction on user-defined recursive ADTs.
        decls.push(Decl::DataMeta {
            name: data_name.clone(),
            ctors: ctor_arities,
        });
        self.data_ctors.insert(data_name, ctor_names);
        Ok(decls)
    }

    /// `class Name [TypeParams] where m1 : T1 ; m2 : T2 ; ...`
    ///
    /// Pure parser-level desugar to:
    ///   * `data NameDict P1 ... = MkNameDict T1 T2 ...` (the dictionary type)
    ///   * `def m1 := \dict -> match dict with | MkNameDict v _ ... -> v`
    ///     (one projection per method, with positional pattern matches)
    ///
    /// The class name and method order are recorded in `self.classes` so a
    /// later `instance` declaration knows the slot order.
    fn parse_class(&mut self) -> SekiResult<Vec<Decl>> {
        self.expect(&Tok::KwClass, "class")?;
        let class_name = self.eat_ident("class name")?;
        // Optional type params (single line, before `where`)
        let class_line = self.toks.get(self.pos.saturating_sub(1)).map(|t| t.line).unwrap_or(0);
        let mut type_params: Vec<String> = Vec::new();
        while matches!(self.peek(), Tok::Ident(_))
            && self.toks[self.pos].line == class_line
        {
            type_params.push(self.eat_ident("class type param")?);
        }
        self.expect(&Tok::KwWhere, "'where' in class")?;
        // Parse method signatures: `name : type` separated by `;` (or
        // implicit semicolons across lines).  Require the `<ident> :` shape
        // — anything else terminates the class block.
        let mut methods: Vec<(String, Expr)> = Vec::new();
        loop {
            if matches!(self.peek(), Tok::Semi) {
                self.bump();
                continue;
            }
            let is_method = matches!(self.peek(), Tok::Ident(_))
                && matches!(self.peek_at(1), Tok::Colon);
            if !is_method {
                break;
            }
            let mname = self.eat_ident("method name")?;
            self.bump(); // Colon (already verified)
            let mty = self.parse_expr()?;
            methods.push((mname, mty));
            if matches!(self.peek(), Tok::Semi) {
                self.bump();
            }
        }
        if methods.is_empty() {
            return Err(SekiError::Parse(format!(
                "class {} has no methods",
                class_name
            )));
        }
        // Remember the method order
        let method_names: Vec<String> = methods.iter().map(|(n, _)| n.clone()).collect();
        self.classes.insert(class_name.clone(), method_names.clone());

        // Generate decls.
        let dict_data_name = format!("{}Dict", class_name);
        let ctor_name = format!("Mk{}", dict_data_name);
        let mut decls: Vec<Decl> = Vec::new();
        // data NameDict params... = MkNameDict T1 T2 ...
        // Note: we emit the constructor decl directly (no intermediate
        // Decl::Data) by mirroring `make_ctor_decl`.
        decls.push(make_ctor_decl(&ctor_name, methods.len()));
        let _ = type_params; // currently unused at value level
        // Method projections.
        for (i, (mname, _ty)) in methods.iter().enumerate() {
            decls.push(make_method_projection(
                mname,
                &ctor_name,
                i,
                methods.len(),
            ));
        }
        // Emit metadata so the runtime can populate the class/method
        // registry used by automatic-dictionary resolution.
        decls.push(Decl::ClassMeta {
            class_name: class_name.clone(),
            ctor_name: ctor_name.clone(),
            methods: method_names,
        });
        Ok(decls)
    }

    /// `instance Name : Class TypeArg where m1 = e1 ; m2 = e2 ; ...`
    ///
    /// Desugars to `def Name := MkClassDict e1 e2 ...` using the method
    /// order recorded for `Class` at its `class` declaration.  Also emits
    /// an `InstanceMeta` decl so the runtime can register the
    /// `(class, TypeArg) -> Name` lookup for automatic dictionary
    /// resolution.
    fn parse_instance(&mut self) -> SekiResult<Vec<Decl>> {
        self.expect(&Tok::KwInstance, "instance")?;
        let inst_name = self.eat_ident("instance name")?;
        self.expect(&Tok::Colon, "':' in instance header")?;
        let class_name = self.eat_ident("class name in instance")?;
        // Capture the type argument (first atom on the same line).  This
        // is used as the key for auto-dictionary lookup.  We stringify it
        // (preserving the shape `Int`, `Bool`, `List Int`, ...).
        let head_line = self.toks.get(self.pos.saturating_sub(1)).map(|t| t.line).unwrap_or(0);
        let mut type_atoms: Vec<Expr> = Vec::new();
        while self.starts_atom() && self.toks[self.pos].line == head_line {
            type_atoms.push(self.parse_atom()?);
        }
        let type_name = type_atoms
            .iter()
            .map(|a| format!("{}", a))
            .collect::<Vec<_>>()
            .join(" ");
        self.expect(&Tok::KwWhere, "'where' in instance")?;
        // Look up class method order.
        let order = self.classes.get(&class_name).cloned().ok_or_else(|| {
            SekiError::Parse(format!(
                "instance {} references unknown class {}",
                inst_name, class_name
            ))
        })?;
        // Parse method bindings: `name = expr` separated by `;` or newlines.
        // We require `<ident> =` to start a binding; anything else (including
        // top-level keywords or a bare expression like `eq EqInt 3`) is taken
        // as the end of this instance block.
        let mut bindings: std::collections::HashMap<String, Expr> =
            std::collections::HashMap::new();
        loop {
            if matches!(self.peek(), Tok::Semi) {
                self.bump();
                continue;
            }
            // The instance ends as soon as the next token is not an Ident
            // followed by `=`/`:=`.
            let is_binding = matches!(self.peek(), Tok::Ident(_))
                && matches!(self.peek_at(1), Tok::Assign);
            if !is_binding {
                break;
            }
            let mname = self.eat_ident("instance method name")?;
            self.bump(); // Assign (already verified above)
            let body = self.parse_expr()?;
            bindings.insert(mname, body);
            if matches!(self.peek(), Tok::Semi) {
                self.bump();
            }
        }
        // Build the constructor application in declared method order.
        let ctor_name = format!("Mk{}Dict", class_name);
        let mut args: Vec<Expr> = Vec::new();
        for m in &order {
            let body = bindings.remove(m).ok_or_else(|| {
                SekiError::Parse(format!(
                    "instance {}: missing binding for method {}",
                    inst_name, m
                ))
            })?;
            args.push(body);
        }
        // Defensive: any unused bindings is an error.
        if let Some(unknown) = bindings.keys().next() {
            return Err(SekiError::Parse(format!(
                "instance {}: method {} not declared in class {}",
                inst_name, unknown, class_name
            )));
        }
        let value = Expr::App {
            func: Box::new(Expr::Var { name: ctor_name, line: 0, col: 0 }),
            args,
        };
        let def_decl = Decl::Def {
            name: inst_name.clone(),
            ty: None,
            value,
        };
        let meta = Decl::InstanceMeta {
            instance_name: inst_name,
            class_name,
            type_name,
        };
        Ok(vec![def_decl, meta])
    }

    fn parse_axiom(&mut self) -> SekiResult<Decl> {
        self.expect(&Tok::KwAxiom, "axiom")?;
        let name = self.eat_ident("axiom name")?;
        self.expect(&Tok::Colon, "':' in axiom")?;
        let prop = self.parse_expr()?;
        Ok(Decl::Axiom { name, prop })
    }

    fn parse_proof(&mut self) -> SekiResult<Proof> {
        match self.peek() {
            Tok::KwBy => {
                self.bump();
                // Parse a (possibly composed) tactic expression.  Single
                // tactics like `by algebra` produce the corresponding
                // `Proof` variant; composed `by t1 then t2 [then t3 ...]`
                // produce `Proof::Seq([t1, t2, ...])`.
                let head = self.parse_single_tactic()?;
                if matches!(self.peek(), Tok::KwThen) {
                    let mut seq = vec![head];
                    while matches!(self.peek(), Tok::KwThen) {
                        self.bump();
                        seq.push(self.parse_single_tactic()?);
                    }
                    Ok(Proof::Seq(seq))
                } else {
                    Ok(head)
                }
            }
            Tok::Ident(s) if s == "refl" => {
                self.bump();
                Ok(Proof::Refl)
            }
            _ => Ok(Proof::Term(self.parse_expr()?)),
        }
    }

    /// Parse exactly one tactic (no `then` composition).  Called from
    /// `parse_proof` repeatedly when a composed `by ... then ...` is seen.
    fn parse_single_tactic(&mut self) -> SekiResult<Proof> {
        let kw = self.eat_ident("proof tactic")?;
        match kw.as_str() {
            "eval" => Ok(Proof::ByEval),
            "algebra" => Ok(Proof::ByAlgebra),
            "induction" => Ok(Proof::ByInduction),
            "strong_induction" => Ok(Proof::ByStrongInduction),
            "intros" => Ok(Proof::ByIntros),
            "linarith" => Ok(Proof::ByLinarith),
            "decide" => Ok(Proof::ByDecide),
            "unfold" => {
                let name = self.eat_ident("function name to unfold")?;
                Ok(Proof::ByUnfold(name))
            }
            "simp" => {
                let lemmas = if matches!(self.peek(), Tok::LBracket) {
                    self.bump();
                    let mut names = Vec::new();
                    if !matches!(self.peek(), Tok::RBracket) {
                        names.push(self.eat_ident("simp lemma name")?);
                        while matches!(self.peek(), Tok::Comma) {
                            self.bump();
                            names.push(self.eat_ident("simp lemma name")?);
                        }
                    }
                    self.expect(&Tok::RBracket, "]")?;
                    names
                } else {
                    Vec::new()
                };
                Ok(Proof::BySimp { lemmas })
            }
            other => Err(SekiError::Parse(format!(
                "unknown proof tactic 'by {}'",
                other
            ))),
        }
    }

    // -- expressions --------------------------------------------------------

    fn parse_expr(&mut self) -> SekiResult<Expr> {
        // Special expression forms first (lambda, let, if, forall, exists, match, for)
        match self.peek() {
            Tok::KwLambda | Tok::Backslash => return self.parse_lambda(),
            Tok::KwLet => return self.parse_let(),
            Tok::KwIf => return self.parse_if(),
            Tok::KwForall => return self.parse_forall(),
            Tok::KwExists => return self.parse_exists(),
            Tok::KwMatch => return self.parse_match(),
            Tok::KwFor => return self.parse_for(),
            _ => {}
        }
        self.parse_arrow()
    }

    /// Phase 12: Python-flavoured for-loop sugar.
    ///
    /// ```text
    /// for x in xs do <body>
    /// ```
    ///
    /// Desugars to a call to the stdlib `forEach`:
    ///
    /// ```text
    /// forEach xs (\x -> <body>)
    /// ```
    ///
    /// The body is a single expression.  For compound statements use the
    /// usual `let _ = ... in ...` chain or parens.  This form is purely
    /// syntactic — semantics are identical to writing `forEach` directly.
    fn parse_for(&mut self) -> SekiResult<Expr> {
        self.expect(&Tok::KwFor, "for")?;
        // Binder name (a single identifier).
        let name = self.eat_ident("for-loop binder")?;
        self.expect(&Tok::KwIn, "for-loop 'in'")?;
        // The iterable expression.  Use parse_arrow so commas / operators
        // bind tighter than `do`; `for x in xs do f x` parses cleanly.
        let xs = self.parse_arrow()?;
        self.expect(&Tok::KwDo, "for-loop 'do'")?;
        let body = self.parse_expr()?;
        // Desugar: `forEach xs (\name -> body)`.
        let lambda = Expr::Lambda {
            params: vec![Param { name: name.clone(), ty: None }],
            body: Box::new(body),
        };
        Ok(Expr::App {
            func: Box::new(Expr::Var { name: "forEach".into(), line: 0, col: 0 }),
            args: vec![xs, lambda],
        })
    }

    fn parse_lambda(&mut self) -> SekiResult<Expr> {
        // either KwLambda or Backslash
        self.bump();
        let mut params: Vec<Param> = Vec::new();
        loop {
            match self.peek() {
                Tok::Ident(_) => {
                    let n = self.eat_ident("lambda param")?;
                    params.push(Param { name: n, ty: None });
                }
                Tok::LParen
                    if matches!(self.peek_at(1), Tok::Ident(_))
                        && matches!(self.peek_at(2), Tok::Colon) =>
                {
                    self.bump();
                    let n = self.eat_ident("lambda param")?;
                    self.expect(&Tok::Colon, "param type")?;
                    let ty = self.parse_expr()?;
                    self.expect(&Tok::RParen, "param close")?;
                    params.push(Param {
                        name: n,
                        ty: Some(ty),
                    });
                }
                _ => break,
            }
        }
        if params.is_empty() {
            return Err(SekiError::Parse("lambda with no parameters".into()));
        }
        self.expect(&Tok::Arrow, "'->' in lambda")?;
        let body = self.parse_expr()?;
        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
        })
    }

    fn parse_let(&mut self) -> SekiResult<Expr> {
        self.expect(&Tok::KwLet, "let")?;
        // Optional `rec` for self-recursive function bindings.
        let is_rec = matches!(self.peek(), Tok::Ident(s) if s == "rec");
        if is_rec {
            self.bump();
        }
        let name = self.eat_ident("let name")?;
        let mut ty = None;
        if matches!(self.peek(), Tok::Colon) {
            self.bump();
            ty = Some(Box::new(self.parse_expr_no_arrow()?));
        }
        // accept `=` or `:=`
        if matches!(self.peek(), Tok::Assign) {
            self.bump();
        } else {
            return Err(SekiError::Parse("expected '=' or ':=' in let".into()));
        }
        let prev = self.suppress_in_op;
        self.suppress_in_op = true;
        let value_res = self.parse_expr();
        self.suppress_in_op = prev;
        let value = value_res?;
        // After parsing the value, an optional `?` triggers Result-propagation
        // desugar.  `let x = expr ? in body` becomes:
        //   match expr with
        //   | Err __qe -> Err __qe          (re-wrap and propagate)
        //   | Ok x     -> body              (continue with bound name)
        let has_question = matches!(self.peek(), Tok::Question);
        if has_question {
            self.bump();
        }
        self.expect(&Tok::KwIn, "let ... in")?;
        let body = self.parse_expr()?;
        if has_question {
            let err_name = format!("__qe_{}", fresh_match_var());
            let arms = vec![
                (
                    Pattern::Ctor("Err".into(), vec![Pattern::Var(err_name.clone())]),
                    Expr::App {
                        func: Box::new(Expr::Var { name: "Err".into(), line: 0, col: 0 }),
                        args: vec![Expr::Var { name: err_name, line: 0, col: 0 }],
                    },
                ),
                (
                    Pattern::Ctor("Ok".into(), vec![Pattern::Var(name)]),
                    body,
                ),
            ];
            // Type annotation is dropped — meaningful only for the unwrapped `x`,
            // and re-attaching it would require synthesizing a different Result
            // structure.  Acceptable for `?` ergonomics.
            let _ = ty;
            return Ok(desugar_match(value, arms));
        }
        Ok(Expr::Let {
            name,
            ty,
            value: Box::new(value),
            body: Box::new(body),
            rec: is_rec,
        })
    }

    /// parse expression but stop before a top-level `->` so type-annotations
    /// in `let x : T = e` don't accidentally swallow the `=`.
    fn parse_expr_no_arrow(&mut self) -> SekiResult<Expr> {
        // For our use this is just parse_or — we don't allow lambdas as type
        // annotations at this position, which is fine.
        self.parse_or()
    }

    fn parse_if(&mut self) -> SekiResult<Expr> {
        self.expect(&Tok::KwIf, "if")?;
        let c = self.parse_expr()?;
        self.expect(&Tok::KwThen, "then")?;
        let t = self.parse_expr()?;
        self.expect(&Tok::KwElse, "else")?;
        let e = self.parse_expr()?;
        Ok(Expr::If {
            cond: Box::new(c),
            then_branch: Box::new(t),
            else_branch: Box::new(e),
        })
    }

    /// `match SCRUTINEE with | PAT1 -> BODY1 | PAT2 -> BODY2 | ...`
    ///
    /// Pure parser-level desugar to a chain of `if`/`let` over the scrutinee
    /// (bound once into `__match_NN`).  Each constructor pattern test reads
    /// `fst __match_NN == "Ctor"`; each variable pattern introduces a `let`
    /// in the arm's body that pulls the appropriate component out of the
    /// tagged-pair encoding.  An unmatched scrutinee falls through to a
    /// runtime call to the `error` builtin.
    fn parse_match(&mut self) -> SekiResult<Expr> {
        let (match_line, _) = self.loc();
        self.expect(&Tok::KwMatch, "match")?;
        let scrutinee = self.parse_expr()?;
        self.expect(&Tok::KwWith, "'with' in match")?;
        let mut arms: Vec<(Pattern, Expr)> = Vec::new();
        while matches!(self.peek(), Tok::Bar) {
            self.bump();
            let pat = self.parse_pattern()?;
            self.expect(&Tok::Arrow, "'->' in match arm")?;
            let body = self.parse_expr()?;
            arms.push((pat, body));
        }
        if arms.is_empty() {
            return Err(SekiError::Parse(
                "match expression has no arms (use `| pat -> body`)".into(),
            ));
        }
        // Exhaustiveness check (warning only): for matches against known
        // `data` types, report missing constructors.
        self.check_exhaustiveness(&arms, match_line);
        Ok(desugar_match(scrutinee, arms))
    }

    /// Emit a warning to stderr when a `match` is missing some constructors
    /// of a known `data` type.  Non-fatal: the runtime fallback
    /// `error "non-exhaustive match"` still catches misses at evaluation
    /// time.  Wildcard / Var patterns count as "all remaining covered".
    fn check_exhaustiveness(&self, arms: &[(Pattern, Expr)], match_line: usize) {
        // If any arm has a wildcard or var pattern, the match is
        // exhaustive (by construction).
        for (pat, _) in arms {
            if matches!(pat, Pattern::Wildcard | Pattern::Var(_)) {
                return;
            }
        }
        // Collect constructor names used in arms.
        let mut used: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut any_lit = false;
        let mut any_tuple = false;
        for (pat, _) in arms {
            match pat {
                Pattern::Ctor(name, _) => {
                    used.insert(name.clone());
                }
                Pattern::Lit(_) => any_lit = true,
                Pattern::Tuple(_) => any_tuple = true,
                _ => {}
            }
        }
        // Literal-only or tuple-only matches can't be statically checked
        // for exhaustiveness from `data` registry — skip.
        if any_lit || any_tuple || used.is_empty() {
            return;
        }
        // Determine the data type from any of the used constructors.
        let any_ctor = used.iter().next().unwrap();
        let data_name = match self.ctor_to_data.get(any_ctor) {
            Some(d) => d.clone(),
            None => return, // unknown constructor → ignore
        };
        let all_ctors = match self.data_ctors.get(&data_name) {
            Some(cs) => cs,
            None => return,
        };
        let mut missing: Vec<&String> = Vec::new();
        for c in all_ctors {
            if !used.contains(c) {
                missing.push(c);
            }
        }
        if !missing.is_empty() {
            let mut buf = String::new();
            for (i, c) in missing.iter().enumerate() {
                if i > 0 {
                    buf.push_str(", ");
                }
                buf.push_str(c);
            }
            eprintln!(
                "warning: non-exhaustive match at line {}: missing constructor(s) of `{}`: {}",
                match_line, data_name, buf
            );
        }
    }

    /// Parse a single `match` pattern, handling at most one constructor with
    /// its (atom-level) sub-patterns on the same line.  Use parens to nest
    /// deeper patterns.
    fn parse_pattern(&mut self) -> SekiResult<Pattern> {
        let head_line = self.toks[self.pos].line;
        let first = self.parse_atom_pattern()?;
        // If first is a 0-arg Ctor pattern, look for trailing sub-patterns
        // on the same line — those are this constructor's arguments.
        if let Pattern::Ctor(name, args) = &first {
            if !args.is_empty() {
                return Ok(first);
            }
            let mut subs = Vec::new();
            while self.starts_pattern_atom()
                && self.toks[self.pos].line == head_line
            {
                subs.push(self.parse_atom_pattern()?);
            }
            return Ok(Pattern::Ctor(name.clone(), subs));
        }
        Ok(first)
    }

    fn starts_pattern_atom(&self) -> bool {
        matches!(
            self.peek(),
            Tok::Ident(_)
                | Tok::Int(_)
                | Tok::Real(_)
                | Tok::Str(_)
                | Tok::KwTrue
                | Tok::KwFalse
                | Tok::LParen
        )
    }

    fn parse_atom_pattern(&mut self) -> SekiResult<Pattern> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.bump();
                if s == "_" {
                    return Ok(Pattern::Wildcard);
                }
                let cap = s.chars().next().map_or(false, |c| c.is_uppercase());
                if cap {
                    return Ok(Pattern::Ctor(s, vec![]));
                }
                Ok(Pattern::Var(s))
            }
            Tok::Int(n) => {
                self.bump();
                Ok(Pattern::Lit(Expr::Int(n)))
            }
            Tok::Real(r) => {
                self.bump();
                Ok(Pattern::Lit(Expr::Real(r)))
            }
            Tok::Str(s) => {
                self.bump();
                Ok(Pattern::Lit(Expr::Str(s)))
            }
            Tok::KwTrue => {
                self.bump();
                Ok(Pattern::Lit(Expr::Bool(true)))
            }
            Tok::KwFalse => {
                self.bump();
                Ok(Pattern::Lit(Expr::Bool(false)))
            }
            Tok::LParen => {
                // Parenthesized pattern OR tuple pattern.  We parse the
                // first inner pattern; if a comma follows, treat as a
                // tuple pattern with two-or-more elements.
                self.bump();
                let first = self.parse_pattern()?;
                if matches!(self.peek(), Tok::Comma) {
                    let mut elems = vec![first];
                    while matches!(self.peek(), Tok::Comma) {
                        self.bump();
                        elems.push(self.parse_pattern()?);
                    }
                    self.expect(&Tok::RParen, "')' to close tuple pattern")?;
                    Ok(Pattern::Tuple(elems))
                } else {
                    self.expect(&Tok::RParen, "')'")?;
                    Ok(first)
                }
            }
            other => {
                let (l, c) = self.loc();
                Err(SekiError::Parse(format!(
                    "expected a pattern, got {:?} at {}:{}",
                    other, l, c
                )))
            }
        }
    }

    fn parse_forall(&mut self) -> SekiResult<Expr> {
        self.expect(&Tok::KwForall, "forall")?;
        let vars = self.parse_quantifier_vars("forall var")?;
        self.expect(&Tok::KwIn, "'in' in forall")?;
        let domain = self.parse_or()?;
        self.expect(&Tok::Comma, "',' after forall domain")?;
        let body = self.parse_expr()?;
        Ok(build_nested_quantifier(true, &vars, domain, body))
    }

    fn parse_exists(&mut self) -> SekiResult<Expr> {
        self.expect(&Tok::KwExists, "exists")?;
        let vars = self.parse_quantifier_vars("exists var")?;
        self.expect(&Tok::KwIn, "'in' in exists")?;
        let domain = self.parse_or()?;
        self.expect(&Tok::Comma, "',' after exists domain")?;
        let body = self.parse_expr()?;
        Ok(build_nested_quantifier(false, &vars, domain, body))
    }

    /// Parse one or more variable names for a quantifier:
    ///   `x`                  → single var
    ///   `(x y z)`            → multiple vars, all sharing the same domain
    fn parse_quantifier_vars(&mut self, ctx: &str) -> SekiResult<Vec<String>> {
        if matches!(self.peek(), Tok::LParen) {
            self.bump();
            let mut names = Vec::new();
            while matches!(self.peek(), Tok::Ident(_)) {
                names.push(self.eat_ident(ctx)?);
            }
            self.expect(&Tok::RParen, "')' after quantifier vars")?;
            if names.is_empty() {
                return Err(SekiError::Parse(format!(
                    "{}: empty variable list `( )`",
                    ctx
                )));
            }
            Ok(names)
        } else {
            Ok(vec![self.eat_ident(ctx)?])
        }
    }

    fn parse_arrow(&mut self) -> SekiResult<Expr> {
        // Dependent arrow: `(x : A) -> B(x)`.  We detect it by lookahead
        // because `(IDENT : ...)` is otherwise ill-formed as an expression.
        if self.looks_like_dep_arrow_binder() {
            self.expect(&Tok::LParen, "(")?;
            let binder = self.eat_ident("dependent binder")?;
            self.expect(&Tok::Colon, "':' in dep binder")?;
            let from = self.parse_or()?;
            self.expect(&Tok::RParen, "')' to close dep binder")?;
            self.expect(&Tok::Arrow, "'->' after dep binder")?;
            let to = self.parse_arrow()?; // right-assoc — supports chained binders
            return Ok(Expr::DepArrow {
                binder,
                from: Box::new(from),
                to: Box::new(to),
            });
        }
        let lhs = self.parse_implies()?;
        if matches!(self.peek(), Tok::Arrow) {
            self.bump();
            let rhs = self.parse_arrow()?;
            Ok(Expr::Arrow(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    /// Propositional implication `P => Q`, right-associative.
    /// Desugared at parse time to `(not P) or Q` to keep the existing
    /// evaluator simple.  Lower-precedence than `or` so that
    /// `P or Q => R` parses as `(P or Q) => R`.
    fn parse_implies(&mut self) -> SekiResult<Expr> {
        let lhs = self.parse_or()?;
        if matches!(self.peek(), Tok::FatArrow) {
            self.bump();
            let rhs = self.parse_implies()?;
            // Desugar: P => Q  ≡  (not P) or Q
            Ok(Expr::BinOp(
                BinOp::Or,
                Box::new(Expr::UnOp(UnOp::Not, Box::new(lhs))),
                Box::new(rhs),
            ))
        } else {
            Ok(lhs)
        }
    }

    /// Lookahead: does the upcoming token sequence start with
    /// `( IDENT :  ...  ) ->` ?  If so, it's a dependent-arrow binder.
    /// We scan the matching close-paren to confirm the `->` follows.
    fn looks_like_dep_arrow_binder(&self) -> bool {
        if !matches!(self.peek(), Tok::LParen) {
            return false;
        }
        if !matches!(self.peek_at(1), Tok::Ident(_)) {
            return false;
        }
        if !matches!(self.peek_at(2), Tok::Colon) {
            return false;
        }
        // scan forward to find the matching close paren
        let mut depth = 1i32;
        let mut k = 3;
        loop {
            match self.peek_at(k) {
                Tok::LParen => depth += 1,
                Tok::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.peek_at(k + 1), Tok::Arrow);
                    }
                }
                Tok::Eof => return false,
                _ => {}
            }
            k += 1;
            if k > 1024 {
                return false; // give up to avoid pathological scans
            }
        }
    }

    fn parse_or(&mut self) -> SekiResult<Expr> {
        let mut lhs = self.parse_and()?;
        while matches!(self.peek(), Tok::KwOr) {
            self.bump();
            let rhs = self.parse_and()?;
            lhs = Expr::BinOp(BinOp::Or, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> SekiResult<Expr> {
        let mut lhs = self.parse_not()?;
        while matches!(self.peek(), Tok::KwAnd) {
            self.bump();
            let rhs = self.parse_not()?;
            lhs = Expr::BinOp(BinOp::And, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_not(&mut self) -> SekiResult<Expr> {
        if matches!(self.peek(), Tok::KwNot) {
            self.bump();
            let e = self.parse_not()?;
            Ok(Expr::UnOp(UnOp::Not, Box::new(e)))
        } else {
            self.parse_cmp()
        }
    }

    fn parse_cmp(&mut self) -> SekiResult<Expr> {
        let lhs = self.parse_set_additive()?;
        let op = match self.peek() {
            Tok::Eq => Some(BinOp::Eq),
            Tok::Neq => Some(BinOp::Neq),
            Tok::Lt => Some(BinOp::Lt),
            Tok::Le => Some(BinOp::Le),
            Tok::Gt => Some(BinOp::Gt),
            Tok::Ge => Some(BinOp::Ge),
            Tok::KwIn if !self.suppress_in_op => Some(BinOp::In),
            Tok::KwNotin => Some(BinOp::NotIn),
            Tok::KwSubset => Some(BinOp::Subset),
            _ => None,
        };
        if let Some(op) = op {
            self.bump();
            let rhs = self.parse_set_additive()?;
            Ok(Expr::BinOp(op, Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_set_additive(&mut self) -> SekiResult<Expr> {
        let mut lhs = self.parse_set_mul()?;
        loop {
            let op = match self.peek() {
                Tok::KwUnion => BinOp::Union,
                Tok::KwDiff => BinOp::Diff,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_set_mul()?;
            lhs = Expr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_set_mul(&mut self) -> SekiResult<Expr> {
        let mut lhs = self.parse_times()?;
        while matches!(self.peek(), Tok::KwIntersect) {
            self.bump();
            let rhs = self.parse_times()?;
            lhs = Expr::BinOp(BinOp::Intersect, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    /// Cartesian product of sets — tighter than `intersect`.
    fn parse_times(&mut self) -> SekiResult<Expr> {
        let mut lhs = self.parse_add()?;
        while matches!(self.peek(), Tok::KwTimes) {
            self.bump();
            let rhs = self.parse_add()?;
            lhs = Expr::BinOp(BinOp::Times, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_add(&mut self) -> SekiResult<Expr> {
        let start_line = self.toks[self.pos].line;
        let mut lhs = self.parse_mul()?;
        loop {
            // Same-line constraint: don't absorb `-` from the next line as
            // subtraction; a leading unary minus on its own line should start
            // a fresh expression statement.  `1\n - 2` is two statements,
            // not one.
            if self.toks[self.pos].line != start_line {
                break;
            }
            let op = match self.peek() {
                Tok::Plus => BinOp::Add,
                Tok::Minus => BinOp::Sub,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_mul()?;
            lhs = Expr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> SekiResult<Expr> {
        let start_line = self.toks[self.pos].line;
        let mut lhs = self.parse_unary()?;
        loop {
            if self.toks[self.pos].line != start_line {
                break;
            }
            let op = match self.peek() {
                Tok::Star => BinOp::Mul,
                Tok::Slash => BinOp::Div,
                Tok::KwMod => BinOp::Mod,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_unary()?;
            lhs = Expr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> SekiResult<Expr> {
        if matches!(self.peek(), Tok::Minus) {
            self.bump();
            let e = self.parse_unary()?;
            Ok(Expr::UnOp(UnOp::Neg, Box::new(e)))
        } else {
            self.parse_app()
        }
    }

    fn parse_app(&mut self) -> SekiResult<Expr> {
        let head_line = self.toks[self.pos].line;
        let head_col = self.toks[self.pos].col;
        let mut head = self.parse_atom()?;
        // Phase 11: C-style call syntax `f(a, b, c)`.  When the parsed atom
        // is immediately followed (no whitespace) by `(`, treat the parens
        // as a comma-separated argument list, not as a tuple/grouping atom.
        head = self.parse_trailing_calls(head)?;
        loop {
            // For juxtaposition to be considered an application argument the
            // following atom must be on the same line as the head, or be more
            // deeply indented (continuation).  This avoids accidentally
            // parsing `1 + 2\n10 mod 3` as `(1+2) 10 mod 3`.
            if self.starts_atom() {
                let next = &self.toks[self.pos];
                let same_line = next.line == head_line;
                let indented = next.line > head_line && next.col > head_col;
                if !(same_line || indented) {
                    break;
                }
                let mut arg = self.parse_atom()?;
                // Adjacent `(args)` immediately after a juxtaposition atom
                // is also a call: `f g(x)` = `f (g x)`.
                arg = self.parse_trailing_calls(arg)?;
                match &mut head {
                    Expr::App { args, .. } => args.push(arg),
                    _ => {
                        head = Expr::App {
                            func: Box::new(head),
                            args: vec![arg],
                        };
                    }
                }
            } else {
                break;
            }
        }
        Ok(head)
    }

    /// Phase 11: parse zero-or-more `(a, b, c)` call suffixes that are
    /// immediately adjacent (no whitespace) to the head expression.  Each
    /// suffix becomes one `App` node; chains like `f(a)(b)` are supported
    /// for higher-order calls.
    ///
    /// Returns `head` unchanged when there's no adjacent `(`.
    fn parse_trailing_calls(&mut self, mut head: Expr) -> SekiResult<Expr> {
        while self.at_adjacent_lparen() {
            self.bump(); // consume `(`
            let mut args: Vec<Expr> = Vec::new();
            if !matches!(self.peek(), Tok::RParen) {
                args.push(self.parse_expr()?);
                while matches!(self.peek(), Tok::Comma) {
                    self.bump();
                    args.push(self.parse_expr()?);
                }
            }
            self.expect(&Tok::RParen, "call argument list")?;
            // Empty `f()` desugars to `f ()` (unit application) so builtins
            // like `nowSecs()` work the same as the existing `nowSecs ()`.
            if args.is_empty() {
                args.push(Expr::SetEnum(vec![]));
            }
            head = Expr::App {
                func: Box::new(head),
                args,
            };
        }
        Ok(head)
    }

    /// True iff the next token is `(` on the same line, in the column
    /// immediately after the previously-consumed token (no whitespace).
    /// Used to distinguish `f(a, b)` (call) from `f (a, b)` (tuple arg).
    fn at_adjacent_lparen(&self) -> bool {
        if self.pos == 0 { return false; }
        if !matches!(self.peek(), Tok::LParen) { return false; }
        let cur = &self.toks[self.pos];
        let prev = &self.toks[self.pos - 1];
        cur.line == prev.line && cur.col == prev.end_col
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Tok::Int(_)
                | Tok::Real(_)
                | Tok::Str(_)
                | Tok::Ident(_)
                | Tok::LParen
                | Tok::LBrace
                | Tok::LBracket
                | Tok::KwTrue
                | Tok::KwFalse
                | Tok::KwProp
                | Tok::KwSet
                | Tok::KwNat
                | Tok::KwIntT
                | Tok::KwRealT
                | Tok::KwBoolT
                | Tok::KwStringT
        )
    }

    fn parse_atom(&mut self) -> SekiResult<Expr> {
        let (l, c) = self.loc();
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(Expr::Int(n))
            }
            Tok::Real(r) => {
                self.bump();
                Ok(Expr::Real(r))
            }
            Tok::Str(s) => {
                self.bump();
                Ok(Expr::Str(s))
            }
            Tok::KwTrue => {
                self.bump();
                Ok(Expr::Bool(true))
            }
            Tok::KwFalse => {
                self.bump();
                Ok(Expr::Bool(false))
            }
            Tok::Ident(s) => {
                // Capture the identifier's source position *before* bumping
                // so errors that mention this Var can point at it.  Phase 7
                // soundness deliverable: real Span on the most common error
                // source (unbound identifier / typo).
                let (line, col) = self.loc();
                self.bump();
                // Compound identifier: `Module.name` is a single Var lookup
                // for the literally-named global `Module.name` populated by
                // `import "..." as Module`.  We chain through any further
                // dots so `pkg.sub.name` works too.
                let mut name = s;
                while matches!(self.peek(), Tok::Dot)
                    && matches!(self.peek_at(1), Tok::Ident(_))
                {
                    self.bump(); // dot
                    let next = self.eat_ident("identifier after '.'")?;
                    name = format!("{}.{}", name, next);
                }
                Ok(Expr::Var { name, line: line as u32, col: col as u32 })
            }
            // built-in type names — represented as variables resolved in env
            Tok::KwProp => {
                self.bump();
                Ok(Expr::Var { name: "Prop".into(), line: 0, col: 0 })
            }
            Tok::KwSet => {
                self.bump();
                Ok(Expr::Var { name: "Set".into(), line: 0, col: 0 })
            }
            Tok::KwNat => {
                self.bump();
                Ok(Expr::Var { name: "Nat".into(), line: 0, col: 0 })
            }
            Tok::KwIntT => {
                self.bump();
                Ok(Expr::Var { name: "Int".into(), line: 0, col: 0 })
            }
            Tok::KwRealT => {
                self.bump();
                Ok(Expr::Var { name: "Real".into(), line: 0, col: 0 })
            }
            Tok::KwBoolT => {
                self.bump();
                Ok(Expr::Var { name: "Bool".into(), line: 0, col: 0 })
            }
            Tok::KwStringT => {
                self.bump();
                Ok(Expr::Var { name: "String".into(), line: 0, col: 0 })
            }
            Tok::LParen => {
                self.bump();
                if matches!(self.peek(), Tok::RParen) {
                    self.bump();
                    // unit value — represented as empty enum set for now
                    return Ok(Expr::SetEnum(vec![]));
                }
                let first = self.parse_expr()?;
                // tuple? — at least one comma at this paren level makes it a tuple.
                if matches!(self.peek(), Tok::Comma) {
                    let mut items = vec![first];
                    while matches!(self.peek(), Tok::Comma) {
                        self.bump();
                        if matches!(self.peek(), Tok::RParen) {
                            break; // trailing comma
                        }
                        items.push(self.parse_expr()?);
                    }
                    self.expect(&Tok::RParen, "')'")?;
                    return Ok(Expr::Tuple(items));
                }
                self.expect(&Tok::RParen, "')'")?;
                Ok(first)
            }
            Tok::LBrace => self.parse_set_literal(),
            Tok::LBracket => self.parse_list_literal(),
            other => Err(SekiError::Parse(format!(
                "unexpected token {:?} at {}:{}",
                other, l, c
            ))),
        }
    }

    fn parse_list_literal(&mut self) -> SekiResult<Expr> {
        self.expect(&Tok::LBracket, "'['")?;
        // Collect raw items, then desugar as nested `cons`-applications terminated by `nil`.
        // The seki stdlib provides nil/cons via tagged-pair encoding; this lets the language's
        // most common collection literal share the same set-theoretic foundation as user code.
        let mut items = Vec::new();
        if !matches!(self.peek(), Tok::RBracket) {
            items.push(self.parse_expr()?);
            while matches!(self.peek(), Tok::Comma) {
                self.bump();
                if matches!(self.peek(), Tok::RBracket) {
                    break;
                }
                items.push(self.parse_expr()?);
            }
        }
        self.expect(&Tok::RBracket, "']'")?;
        // Build  cons a (cons b (cons c nil))  right-associatively.
        let mut acc: Expr = Expr::Var { name: "nil".to_string(), line: 0, col: 0 };
        for it in items.into_iter().rev() {
            acc = Expr::App {
                func: Box::new(Expr::Var { name: "cons".to_string(), line: 0, col: 0 }),
                args: vec![it, acc],
            };
        }
        Ok(acc)
    }

    fn parse_set_literal(&mut self) -> SekiResult<Expr> {
        self.expect(&Tok::LBrace, "'{'")?;
        // empty set: {}
        if matches!(self.peek(), Tok::RBrace) {
            self.bump();
            return Ok(Expr::SetEnum(vec![]));
        }
        // Look ahead: comprehension is `ident in <domain> | <pred>`
        // We need to distinguish `{x in S | P}` from `{1, 2, 3}`.
        // Try: parse first expression and check if it's a Var followed by `in`.
        // A clean heuristic: if next is Ident AND token after is `in`, it's
        // probably a comprehension binder.  We need to be careful that `1 in S`
        // is NOT a comprehension (no binder on left).
        let is_comp = matches!(self.peek(), Tok::Ident(_))
            && matches!(self.peek_at(1), Tok::KwIn)
            && contains_bar_before_brace(self.toks, self.pos);
        if is_comp {
            let var = self.eat_ident("comp var")?;
            self.expect(&Tok::KwIn, "'in' in comprehension")?;
            let domain = self.parse_or()?; // up to `|`
            self.expect(&Tok::Bar, "'|' in comprehension")?;
            let pred = self.parse_expr()?;
            self.expect(&Tok::RBrace, "'}' to close comprehension")?;
            return Ok(Expr::SetComp {
                var,
                domain: Box::new(domain),
                pred: Box::new(pred),
            });
        }
        // enumeration
        let mut items = Vec::new();
        items.push(self.parse_expr()?);
        while matches!(self.peek(), Tok::Comma) {
            self.bump();
            if matches!(self.peek(), Tok::RBrace) {
                break;
            }
            items.push(self.parse_expr()?);
        }
        self.expect(&Tok::RBrace, "'}' to close set")?;
        Ok(Expr::SetEnum(items))
    }

    fn eat_ident(&mut self, ctx: &str) -> SekiResult<String> {
        match self.bump() {
            Tok::Ident(s) => Ok(s),
            other => {
                let (l, c) = self.loc();
                Err(SekiError::Parse(format!(
                    "expected identifier ({}) but got {:?} near {}:{}",
                    ctx, other, l, c
                )))
            }
        }
    }
}

/// Look ahead from `pos` and check whether a `|` (Bar) appears before the
/// matching `}` at the current brace depth.  Used to decide if a `{` literal
/// is a comprehension or an enumeration when it begins with `ident in ...`.
fn contains_bar_before_brace(toks: &[Token], pos: usize) -> bool {
    let mut depth = 1; // we are *inside* one `{` already
    let mut i = pos;
    while i < toks.len() {
        match &toks[i].tok {
            Tok::LBrace => depth += 1,
            Tok::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return false;
                }
            }
            Tok::Bar if depth == 1 => return true,
            Tok::Eof => return false,
            _ => {}
        }
        i += 1;
    }
    false
}

pub fn parse_program(toks: &[Token]) -> SekiResult<Vec<crate::ast::LocatedDecl>> {
    let mut p = Parser::new(toks);
    p.parse_program()
}

/// Build a nested chain of `Forall`/`Exists` for a multi-variable quantifier.
/// All vars share the same domain expression (re-cloned per binder).
/// `is_forall` == true → forall; false → exists.
fn build_nested_quantifier(
    is_forall: bool,
    vars: &[String],
    domain: Expr,
    body: Expr,
) -> Expr {
    let mut cur = body;
    for name in vars.iter().rev() {
        cur = if is_forall {
            Expr::Forall {
                var: name.clone(),
                domain: Box::new(domain.clone()),
                body: Box::new(cur),
            }
        } else {
            Expr::Exists {
                var: name.clone(),
                domain: Box::new(domain.clone()),
                body: Box::new(cur),
            }
        };
    }
    cur
}

// -- match patterns and desugaring -----------------------------------------

#[derive(Clone, Debug)]
enum Pattern {
    Wildcard,
    Var(String),
    Lit(Expr),
    Ctor(String, Vec<Pattern>),
    /// `(p1, p2, ..., pk)` — matches a flat k-tuple, with sub-patterns
    /// applied to the i-th element via `__tupproj i scrut`.
    Tuple(Vec<Pattern>),
}

/// Counter for generating unique scrutinee bindings in nested matches.
/// We don't need the exact variable name (it's bound and discarded), only
/// a guarantee of uniqueness within a single `parse_match` call.
fn fresh_match_var() -> String {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    let i = N.fetch_add(1, Ordering::Relaxed);
    format!("__match_{}", i)
}

/// Desugar `match SCRUTINEE with | PAT1 -> BODY1 | ... | PATn -> BODYn`
/// into  `let __m = SCRUTINEE in <if-chain>`.
///
/// For each arm:
///   * Wildcard / Var      : no test — body becomes the result (Var binds it).
///   * Lit                 : test is `__m == LIT`.
///   * Ctor("C", subs)     : test is `fst __m == "C"`, sub-patterns are
///                           applied to component projections of `snd __m`.
///
/// A non-matching scrutinee falls through to `error "non-exhaustive match"`.
fn desugar_match(scrutinee: Expr, arms: Vec<(Pattern, Expr)>) -> Expr {
    let v = fresh_match_var();
    let v_expr = Expr::Var { name: v.clone(), line: 0, col: 0 };
    let no_match: Expr = Expr::App {
        func: Box::new(Expr::Var { name: "error".to_string(), line: 0, col: 0 }),
        args: vec![Expr::Str("non-exhaustive match".to_string())],
    };
    // Build chain right-to-left so the deepest else falls through to no_match.
    let chain = arms.into_iter().rev().fold(no_match, |else_branch, (pat, body)| {
        let (test, bound_body) = compile_pattern(&v_expr, &pat, body);
        match test {
            None => bound_body, // unconditional (Wildcard / Var / Wildcard ctor in last)
            Some(t) => Expr::If {
                cond: Box::new(t),
                then_branch: Box::new(bound_body),
                else_branch: Box::new(else_branch),
            },
        }
    });
    Expr::Let {
        name: v,
        ty: None,
        value: Box::new(scrutinee),
        body: Box::new(chain),
        rec: false,
    }
}

/// Compile a pattern against a scrutinee variable.  Returns `(test, body')`
/// where `test` is `Some(cond)` if the pattern is conditional, and `body'`
/// is `body` wrapped in `let`-bindings that bind any pattern variables.
fn compile_pattern(scrut: &Expr, pat: &Pattern, body: Expr) -> (Option<Expr>, Expr) {
    match pat {
        Pattern::Wildcard => (None, body),
        Pattern::Var(name) => (
            None,
            Expr::Let {
                name: name.clone(),
                ty: None,
                value: Box::new(scrut.clone()),
                body: Box::new(body),
                rec: false,
            },
        ),
        Pattern::Lit(lit) => (
            Some(Expr::BinOp(
                BinOp::Eq,
                Box::new(scrut.clone()),
                Box::new(lit.clone()),
            )),
            body,
        ),
        Pattern::Tuple(elems) => {
            // Compile each element against `__tupproj i scrut`, collecting
            // optional tests and chaining let-bindings.
            let mut wrapped = body;
            let mut sub_tests: Vec<Expr> = Vec::new();
            // Process right-to-left so that the first sub-pattern's
            // bindings are the outermost let.
            for (i, sp) in elems.iter().enumerate().rev() {
                let access = Expr::App {
                    func: Box::new(Expr::Var { name: "__tupproj".into(), line: 0, col: 0 }),
                    args: vec![Expr::Int(i as i64), scrut.clone()],
                };
                let (sub_test, sub_body) = compile_pattern(&access, sp, wrapped);
                wrapped = sub_body;
                if let Some(t) = sub_test {
                    sub_tests.push(t);
                }
            }
            // Combine sub-tests with `and`.
            let combined = if sub_tests.is_empty() {
                None
            } else {
                let mut it = sub_tests.into_iter().rev();
                let first = it.next().unwrap();
                Some(it.fold(first, |a, b| {
                    Expr::BinOp(BinOp::And, Box::new(a), Box::new(b))
                }))
            };
            (combined, wrapped)
        }
        Pattern::Ctor(name, subs) => {
            // test: fst scrut == "name"
            let tag_test = Expr::BinOp(
                BinOp::Eq,
                Box::new(Expr::App {
                    func: Box::new(Expr::Var { name: "fst".into(), line: 0, col: 0 }),
                    args: vec![scrut.clone()],
                }),
                Box::new(Expr::Str(name.clone())),
            );
            // Build the body: peel off (snd scrut) into a chain of
            // (head, rest) projections matching each sub-pattern in turn.
            let mut wrapped = body;
            // Sub-patterns are matched right-to-left so we wrap let-bindings
            // outermost = first sub-pattern.
            let mut sub_tests: Vec<Expr> = Vec::new();
            let body_expr = Expr::App {
                func: Box::new(Expr::Var { name: "snd".into(), line: 0, col: 0 }),
                args: vec![scrut.clone()],
            };
            // iterate sub-patterns from last to first to wrap let-bindings
            // such that the first sub-pattern is the outermost let
            // (so its variable is in scope of all later sub-patterns).
            //
            // For `Ctor p0 p1 p2`, the body is `(p0_val, (p1_val, (p2_val, ())))`
            // accessed as:
            //   p0_val = fst body_expr
            //   p1_val = fst (snd body_expr)
            //   p2_val = fst (snd (snd body_expr))
            // We chain `let` bindings respecting this access pattern.
            for (i, sp) in subs.iter().enumerate().rev() {
                let access = nth_access(&body_expr, i);
                let (sub_test, sub_body) = compile_pattern(&access, sp, wrapped);
                wrapped = sub_body;
                if let Some(t) = sub_test {
                    sub_tests.push(t);
                }
            }
            // Combine the tag test and any sub-tests with `and`.
            let mut total_test = tag_test;
            for t in sub_tests.into_iter().rev() {
                total_test = Expr::BinOp(BinOp::And, Box::new(total_test), Box::new(t));
            }
            (Some(total_test), wrapped)
        }
    }
}

/// Build the access expression for the i-th sub-pattern of a tagged-pair
/// constructor.  Body shape: `(a0, (a1, (a2, (..., (a_{k-1}, ())))))`.
/// Access:
///   i=0  :  fst body
///   i=1  :  fst (snd body)
///   i=k  :  fst (snd^k body)
fn nth_access(body: &Expr, i: usize) -> Expr {
    let mut e = body.clone();
    for _ in 0..i {
        e = Expr::App {
            func: Box::new(Expr::Var { name: "snd".into(), line: 0, col: 0 }),
            args: vec![e],
        };
    }
    Expr::App {
        func: Box::new(Expr::Var { name: "fst".into(), line: 0, col: 0 }),
        args: vec![e],
    }
}

/// Generate a method-projection function for a class.  Given:
///   ctor_name = "MkEqDict",
///   method_index = 0 (which slot to extract),
///   arity = 2 (total methods)
/// produce:
///   def <method_name> := \dict ->
///       match dict with | MkEqDict m0 m1 -> m_<index>
fn make_method_projection(method_name: &str, ctor_name: &str, idx: usize, arity: usize) -> Decl {
    // Build a Pattern::Ctor with `arity` Var sub-patterns; the i-th names
    // the slot of interest (`__slot`), the rest are wildcards.
    let mut subs: Vec<Pattern> = Vec::with_capacity(arity);
    let slot_name = "__class_method_slot".to_string();
    for i in 0..arity {
        if i == idx {
            subs.push(Pattern::Var(slot_name.clone()));
        } else {
            subs.push(Pattern::Wildcard);
        }
    }
    let pat = Pattern::Ctor(ctor_name.to_string(), subs);
    let body = Expr::Var { name: slot_name, line: 0, col: 0 };
    let arms = vec![(pat, body)];
    let scrutinee = Expr::Var { name: "__class_dict".to_string(), line: 0, col: 0 };
    let match_expr = desugar_match(scrutinee, arms);
    Decl::Def {
        name: method_name.to_string(),
        ty: None,
        value: Expr::Lambda {
            params: vec![crate::ast::Param {
                name: "__class_dict".to_string(),
                ty: None,
            }],
            body: Box::new(match_expr),
        },
    }
}

/// Generate a `def` declaration for a constructor of the given name and
/// arity.  The body is a curried lambda that builds the tagged-pair value
/// `("Ctor", (a1, (a2, (..., (ak, ())))))`.  For a 0-arity constructor we
/// emit a direct value `("Ctor", ())` instead of a thunk.
fn make_ctor_decl(name: &str, arity: usize) -> Decl {
    let tag_lit = Expr::Str(name.to_string());
    let unit = Expr::SetEnum(vec![]);
    if arity == 0 {
        // def Ctor := ("Ctor", ())
        let value = Expr::Tuple(vec![tag_lit, unit]);
        return Decl::Def {
            name: name.to_string(),
            ty: None,
            value,
        };
    }
    // Build nested-pair body: (a1, (a2, (..., (ak, ()))))
    let params: Vec<crate::ast::Param> = (0..arity)
        .map(|i| crate::ast::Param {
            name: format!("__ctor_arg_{}", i),
            ty: None,
        })
        .collect();
    let mut body = unit;
    for i in (0..arity).rev() {
        body = Expr::Tuple(vec![
            Expr::Var { name: params[i].name.clone(), line: 0, col: 0 },
            body,
        ]);
    }
    // The whole tagged pair: ("Ctor", body)
    let tagged = Expr::Tuple(vec![tag_lit, body]);
    let value = Expr::Lambda {
        params,
        body: Box::new(tagged),
    };
    Decl::Def {
        name: name.to_string(),
        ty: None,
        value,
    }
}

pub fn parse_expr_str(src: &str) -> SekiResult<Expr> {
    let toks = crate::lexer::tokenize(src)?;
    let mut p = Parser::new(&toks);
    let e = p.parse_expr()?;
    if !p.at_eof() {
        return Err(SekiError::Parse(format!(
            "trailing tokens after expression near {:?}",
            p.peek()
        )));
    }
    Ok(e)
}

//! seki: a set-theory based theorem prover / programming language.
//!
//! Module layout:
//!   lexer     — tokenizer
//!   ast       — abstract syntax tree
//!   parser    — recursive-descent parser
//!   value     — runtime values, sets, environment
//!   eval      — evaluator + builtins (lambda calculus β-reduction)
//!   typecheck — set-theoretic type checker
//!   prover    — theorem verification driver
//!
//! The crate exposes a `run` API used by the binary (REPL / file runner).

pub mod algebra;
pub mod ast;
pub mod builtin_meta;
pub mod bytecode;
pub mod eval;
pub mod lexer;
pub mod linarith;
pub mod parser;
pub mod prover;
pub mod termination;
pub mod typecheck;
pub mod value;

use std::fmt;

#[derive(Debug, Clone)]
pub enum SekiError {
    Lex(String),
    Parse(String),
    Type(String),
    Runtime(String),
    Proof(String),
}

impl SekiError {
    /// Stable machine-readable code for this error category.  Useful for
    /// test assertions and (future) LSP diagnostics.  Codes are stable
    /// across versions; new categories get new codes appended.
    pub fn code(&self) -> &'static str {
        match self {
            SekiError::Lex(_) => "E001",
            SekiError::Parse(_) => "E002",
            SekiError::Type(_) => "E003",
            SekiError::Runtime(_) => "E004",
            SekiError::Proof(_) => "E005",
        }
    }

    /// Human-readable category name used as the prefix in `Display`.
    pub fn category(&self) -> &'static str {
        match self {
            SekiError::Lex(_) => "lex",
            SekiError::Parse(_) => "parse",
            SekiError::Type(_) => "type",
            SekiError::Runtime(_) => "runtime",
            SekiError::Proof(_) => "proof",
        }
    }

    /// The underlying message text without any category prefix.
    pub fn message(&self) -> &str {
        match self {
            SekiError::Lex(m)
            | SekiError::Parse(m)
            | SekiError::Type(m)
            | SekiError::Runtime(m)
            | SekiError::Proof(m) => m,
        }
    }

    /// Whether this is a proof-tactic failure (useful for tests that want
    /// to assert "the proof tactic rejected this" specifically).
    pub fn is_proof_error(&self) -> bool {
        matches!(self, SekiError::Proof(_))
    }
}

impl fmt::Display for SekiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} error: {}", self.category(), self.message())
    }
}

impl std::error::Error for SekiError {}

pub type SekiResult<T> = Result<T, SekiError>;

/// Convenience: parse a complete program string into a list of declarations.
pub fn parse_program(src: &str) -> SekiResult<Vec<ast::LocatedDecl>> {
    let toks = lexer::tokenize(src)?;
    parser::parse_program(&toks)
}

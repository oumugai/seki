//! Lexer for seki.
//!
//! Per the language design we use *words* in place of math symbols
//! (`forall`, `exists`, `in`, `union`, `intersect`, `subset`, `lambda`, …).
//! ASCII operators (`->`, `=>`, `:=`, `==`, `<=` …) are also recognized so
//! Haskell/ML-like syntax stays comfortable.

use crate::{SekiError, SekiResult};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    // literals
    Int(i64),
    Real(f64),
    Str(String),
    Ident(String),

    // keywords
    KwDef,
    KwLet,
    KwIn, // also used as "x in S" — context distinguishes
    KwWhere,
    KwIf,
    KwThen,
    KwElse,
    KwLambda,
    KwForall,
    KwExists,
    KwTheorem,
    KwAxiom,
    KwType,
    KwBy,
    KwData,
    KwMatch,
    KwWith,
    KwImport,
    KwAs,
    KwClass,
    KwInstance,
    KwTrue,
    KwFalse,
    KwAnd,
    KwOr,
    KwNot,
    KwSubset,
    KwUnion,
    KwIntersect,
    KwDiff,
    KwTimes,
    KwNotin,
    KwMod,
    KwFor,    // `for x in xs do body`  (Python-flavoured loop sugar)
    KwDo,     // body separator in `for ... do ...`
    KwProp,
    KwSet,
    KwNat,
    KwIntT,
    KwRealT,
    KwBoolT,
    KwStringT,

    // punctuation / operators
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    Bar,       // |
    Arrow,     // ->
    FatArrow,  // =>
    Assign,    // :=
    Eq,        // ==
    Neq,       // !=
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Backslash, // \  (lambda shorthand)
    Dot,
    Question,  // ?  (Result-propagation operator)
    Eof,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    pub line: usize,
    pub col: usize,
    /// Column index *one past the last character* of this token, on the
    /// same line.  Used by the parser to detect adjacency between tokens
    /// (e.g. `f(args)` vs `f (args)`).
    pub end_col: usize,
}

pub fn tokenize(src: &str) -> SekiResult<Vec<Token>> {
    let mut out = Vec::new();
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut line = 1usize;
    let mut col = 1usize;

    let bump = |i: &mut usize, line: &mut usize, col: &mut usize, c: char| {
        *i += 1;
        if c == '\n' {
            *line += 1;
            *col = 1;
        } else {
            *col += 1;
        }
    };

    while i < chars.len() {
        let c = chars[i];

        // whitespace
        if c.is_whitespace() {
            bump(&mut i, &mut line, &mut col, c);
            continue;
        }
        // line comment: -- ... \n     (Haskell-like)
        if c == '-' && i + 1 < chars.len() && chars[i + 1] == '-' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
            continue;
        }
        // block comment: {- ... -}
        // Require whitespace after the opener so that set literals beginning
        // with a negative number — `{-3, 0, 3}` — are not mistaken for an
        // unterminated block comment.
        if c == '{'
            && i + 2 < chars.len()
            && chars[i + 1] == '-'
            && chars[i + 2].is_whitespace() {
            i += 2;
            col += 2;
            let mut depth = 1;
            while i < chars.len() && depth > 0 {
                if i + 1 < chars.len() && chars[i] == '{' && chars[i + 1] == '-' {
                    depth += 1;
                    i += 2;
                    col += 2;
                } else if i + 1 < chars.len() && chars[i] == '-' && chars[i + 1] == '}' {
                    depth -= 1;
                    i += 2;
                    col += 2;
                } else {
                    let ch = chars[i];
                    bump(&mut i, &mut line, &mut col, ch);
                }
            }
            continue;
        }

        let start_line = line;
        let start_col = col;

        // number — Int or Real (Real has a `.` followed by digits)
        if c.is_ascii_digit() {
            let mut s = String::new();
            while i < chars.len() && chars[i].is_ascii_digit() {
                s.push(chars[i]);
                i += 1;
                col += 1;
            }
            // Detect a fractional part `.` followed by at least one digit.
            // We *don't* consume `.` if the next char isn't a digit, so that
            // `xs.0` (hypothetical record access) wouldn't break.
            let mut is_real = false;
            if i + 1 < chars.len() && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                is_real = true;
                s.push('.');
                i += 1;
                col += 1;
                while i < chars.len() && chars[i].is_ascii_digit() {
                    s.push(chars[i]);
                    i += 1;
                    col += 1;
                }
            }
            // Optional exponent `e±?digit+`.  Conservative: only after a
            // fractional part so we don't conflict with `1e10` ≈ identifiers.
            if is_real
                && i < chars.len()
                && (chars[i] == 'e' || chars[i] == 'E')
            {
                let mut peek_idx = i + 1;
                if peek_idx < chars.len() && (chars[peek_idx] == '+' || chars[peek_idx] == '-')
                {
                    peek_idx += 1;
                }
                if peek_idx < chars.len() && chars[peek_idx].is_ascii_digit() {
                    s.push(chars[i]);
                    i += 1;
                    col += 1;
                    if chars[i] == '+' || chars[i] == '-' {
                        s.push(chars[i]);
                        i += 1;
                        col += 1;
                    }
                    while i < chars.len() && chars[i].is_ascii_digit() {
                        s.push(chars[i]);
                        i += 1;
                        col += 1;
                    }
                }
            }
            if is_real {
                let r: f64 = s
                    .parse()
                    .map_err(|_| SekiError::Lex(format!("bad real number {}", s)))?;
                out.push(Token {
                    tok: Tok::Real(r),
                    line: start_line,
                    col: start_col,
                    end_col: col,
                });
            } else {
                let n: i64 = s
                    .parse()
                    .map_err(|_| SekiError::Lex(format!("bad integer {}", s)))?;
                out.push(Token {
                    tok: Tok::Int(n),
                    line: start_line,
                    col: start_col,
                    end_col: col,
                });
            }
            continue;
        }

        // string literal
        if c == '"' {
            i += 1;
            col += 1;
            let mut s = String::new();
            while i < chars.len() && chars[i] != '"' {
                let ch = chars[i];
                if ch == '\\' && i + 1 < chars.len() {
                    let esc = chars[i + 1];
                    let r = match esc {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        '\\' => '\\',
                        '"' => '"',
                        other => other,
                    };
                    s.push(r);
                    i += 2;
                    col += 2;
                } else {
                    s.push(ch);
                    bump(&mut i, &mut line, &mut col, ch);
                }
            }
            if i >= chars.len() {
                return Err(SekiError::Lex("unterminated string".into()));
            }
            i += 1;
            col += 1; // close quote
            out.push(Token {
                tok: Tok::Str(s),
                line: start_line,
                col: start_col,
                end_col: col,
            });
            continue;
        }

        // identifier / keyword
        if c.is_alphabetic() || c == '_' {
            let mut s = String::new();
            while i < chars.len()
                && (chars[i].is_alphanumeric() || chars[i] == '_' || chars[i] == '\'')
            {
                s.push(chars[i]);
                i += 1;
                col += 1;
            }
            let tok = match s.as_str() {
                "def" => Tok::KwDef,
                "let" => Tok::KwLet,
                "in" => Tok::KwIn,
                "where" => Tok::KwWhere,
                "if" => Tok::KwIf,
                "then" => Tok::KwThen,
                "else" => Tok::KwElse,
                "lambda" | "fn" => Tok::KwLambda,
                "forall" => Tok::KwForall,
                "exists" => Tok::KwExists,
                "theorem" => Tok::KwTheorem,
                "axiom" => Tok::KwAxiom,
                "type" => Tok::KwType,
                "by" => Tok::KwBy,
                "data" => Tok::KwData,
                "match" => Tok::KwMatch,
                "with" => Tok::KwWith,
                "import" => Tok::KwImport,
                "as" => Tok::KwAs,
                "class" => Tok::KwClass,
                "instance" => Tok::KwInstance,
                "true" => Tok::KwTrue,
                "false" => Tok::KwFalse,
                "and" => Tok::KwAnd,
                "or" => Tok::KwOr,
                "not" => Tok::KwNot,
                "subset" => Tok::KwSubset,
                "union" => Tok::KwUnion,
                "intersect" => Tok::KwIntersect,
                "diff" => Tok::KwDiff,
                "times" => Tok::KwTimes,
                "notin" => Tok::KwNotin,
                "mod" => Tok::KwMod,
                "for" => Tok::KwFor,
                "do"  => Tok::KwDo,
                "Prop" => Tok::KwProp,
                "Set" => Tok::KwSet,
                "Nat" => Tok::KwNat,
                "Int" => Tok::KwIntT,
                "Real" => Tok::KwRealT,
                "Bool" => Tok::KwBoolT,
                "String" => Tok::KwStringT,
                _ => Tok::Ident(s),
            };
            out.push(Token {
                tok,
                line: start_line,
                col: start_col,
                end_col: col,
            });
            continue;
        }

        // operators / punctuation
        let two = if i + 1 < chars.len() {
            Some((chars[i], chars[i + 1]))
        } else {
            None
        };

        let two_eq = |a: char, b: char| -> bool {
            i + 1 < chars.len() && chars[i] == a && chars[i + 1] == b
        };
        let (tok, eaten) = match (c, two) {
            ('-', _) if two_eq('-', '>') => (Tok::Arrow, 2),
            ('=', _) if two_eq('=', '>') => (Tok::FatArrow, 2),
            (':', _) if two_eq(':', '=') => (Tok::Assign, 2),
            ('=', _) if two_eq('=', '=') => (Tok::Eq, 2),
            ('!', _) if two_eq('!', '=') => (Tok::Neq, 2),
            ('<', _) if two_eq('<', '=') => (Tok::Le, 2),
            ('>', _) if two_eq('>', '=') => (Tok::Ge, 2),
            ('(', _) => (Tok::LParen, 1),
            (')', _) => (Tok::RParen, 1),
            ('{', _) => (Tok::LBrace, 1),
            ('}', _) => (Tok::RBrace, 1),
            ('[', _) => (Tok::LBracket, 1),
            (']', _) => (Tok::RBracket, 1),
            (',', _) => (Tok::Comma, 1),
            (';', _) => (Tok::Semi, 1),
            (':', _) => (Tok::Colon, 1),
            ('|', _) => (Tok::Bar, 1),
            ('<', _) => (Tok::Lt, 1),
            ('>', _) => (Tok::Gt, 1),
            ('+', _) => (Tok::Plus, 1),
            ('-', _) => (Tok::Minus, 1),
            ('*', _) => (Tok::Star, 1),
            ('/', _) => (Tok::Slash, 1),
            ('\\', _) => (Tok::Backslash, 1),
            ('.', _) => (Tok::Dot, 1),
            ('?', _) => (Tok::Question, 1),
            ('=', _) => (Tok::Assign, 1), // single '=' is also accepted as assign-in-let
            _ => {
                return Err(SekiError::Lex(format!(
                    "unexpected char {:?} at {}:{}",
                    c, line, col
                )))
            }
        };
        // Compute end_col before bumping so it's stable even if the token
        // contains characters that advance the line.
        let end_col = start_col + eaten;
        out.push(Token {
            tok,
            line: start_line,
            col: start_col,
            end_col,
        });
        for _ in 0..eaten {
            let ch = chars[i];
            bump(&mut i, &mut line, &mut col, ch);
        }
    }

    out.push(Token {
        tok: Tok::Eof,
        line,
        col,
        end_col: col,
    });
    Ok(out)
}

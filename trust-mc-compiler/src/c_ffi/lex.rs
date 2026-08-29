// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tokenizer for the restricted C fragment ingested from `--c-lib`.
//!
//! Deliberately NOT a C preprocessor. A `#`-directive line is DROPPED, not
//! interpreted: an object-like macro is therefore never expanded, so a body
//! that uses one leaves an unresolvable identifier and the whole function is
//! refused back to the effect frame. That is the fail-closed direction — the
//! alternative (guessing a macro's expansion) is exactly the mis-translation
//! the front-end must never commit.

/// One C token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Tok {
    Ident(String),
    /// An integer constant, already widened to `i128`. The C suffix (`u`, `l`,
    /// `ul`, …) is recorded so the parser can honour its type.
    Num {
        value: i128,
        unsigned_suffix: bool,
    },
    /// A string literal. Never given a value — nothing in the accepted fragment
    /// consumes one, so its mere presence refuses the enclosing declaration.
    Str,
    /// A character constant's numeric value (`'A'` → 65).
    Char(i128),
    Punct(&'static str),
}

impl Tok {
    pub(crate) fn is_punct(&self, p: &str) -> bool {
        matches!(self, Tok::Punct(q) if *q == p)
    }
    pub(crate) fn ident(&self) -> Option<&str> {
        match self {
            Tok::Ident(s) => Some(s.as_str()),
            _ => None,
        }
    }
}

/// Multi-character punctuators, longest first so `<<=` wins over `<<` over `<`.
const PUNCTS: &[&str] = &[
    "<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "+", "-", "*", "/", "%", "=", "<", ">", "!", "~",
    "&", "|", "^", "?", ":", ";", ",", ".", "(", ")", "[", "]", "{", "}",
];

/// Tokenize `src`, or return `None` if it contains a byte sequence this lexer
/// does not model (an unterminated comment or literal, or a stray character).
///
/// `None` refuses the entire translation unit — every symbol in it keeps the
/// fail-closed effect frame.
pub(crate) fn tokenize(src: &str) -> Option<Vec<Tok>> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    let mut at_line_start = true;
    while i < b.len() {
        match b[i] {
            b'\n' => {
                at_line_start = true;
                i += 1;
            }
            c if c.is_ascii_whitespace() => i += 1,
            b'#' if at_line_start => {
                // Drop the directive, honouring backslash-newline splices.
                while i < b.len() {
                    if b[i] == b'\\' && i + 1 < b.len() && b[i + 1] == b'\n' {
                        i += 2;
                        continue;
                    }
                    if b[i] == b'\n' {
                        break;
                    }
                    i += 1;
                }
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'/' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'*' => {
                i += 2;
                let mut closed = false;
                while i + 1 < b.len() {
                    if b[i] == b'*' && b[i + 1] == b'/' {
                        i += 2;
                        closed = true;
                        break;
                    }
                    i += 1;
                }
                if !closed {
                    return None;
                }
                at_line_start = false;
            }
            b'"' => {
                i += 1;
                let mut closed = false;
                while i < b.len() {
                    match b[i] {
                        b'\\' => i += 2,
                        b'"' => {
                            i += 1;
                            closed = true;
                            break;
                        }
                        _ => i += 1,
                    }
                }
                if !closed {
                    return None;
                }
                out.push(Tok::Str);
                at_line_start = false;
            }
            b'\'' => {
                let (tok, next) = lex_char(b, i)?;
                out.push(tok);
                i = next;
                at_line_start = false;
            }
            c if c.is_ascii_digit() => {
                let (tok, next) = lex_number(b, i)?;
                out.push(tok);
                i = next;
                at_line_start = false;
            }
            c if c.is_ascii_alphabetic() || c == b'_' || c == b'$' => {
                let start = i;
                while i < b.len() && is_ident_byte(b[i]) {
                    i += 1;
                }
                out.push(Tok::Ident(src[start..i].to_owned()));
                at_line_start = false;
            }
            b'\\' => {
                // A line splice outside a directive.
                i += 1;
                if i < b.len() && b[i] == b'\n' {
                    i += 1;
                } else {
                    return None;
                }
            }
            _ => {
                let rest = &src[i..];
                let p = PUNCTS.iter().find(|p| rest.starts_with(**p))?;
                out.push(Tok::Punct(p));
                i += p.len();
                at_line_start = false;
            }
        }
    }
    Some(out)
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
}

/// A character constant. Only the single-character and simple-escape forms are
/// modelled; anything else (multi-character, `\x`, `\0oo`, wide/UTF prefixes)
/// refuses the translation unit rather than guessing a value.
fn lex_char(b: &[u8], start: usize) -> Option<(Tok, usize)> {
    let mut i = start + 1;
    if i >= b.len() {
        return None;
    }
    let value: i128 = if b[i] == b'\\' {
        i += 1;
        let v = match *b.get(i)? {
            b'n' => 10,
            b't' => 9,
            b'r' => 13,
            b'0' => 0,
            b'\\' => 92,
            b'\'' => 39,
            b'"' => 34,
            _ => return None,
        };
        i += 1;
        v
    } else {
        let v = b[i] as i128;
        i += 1;
        if !b[i - 1].is_ascii() {
            return None;
        }
        v
    };
    if *b.get(i)? != b'\'' {
        return None;
    }
    Some((Tok::Char(value), i + 1))
}

/// An integer constant. Floating constants are refused outright — the accepted
/// fragment has no float arithmetic, and silently truncating one would be a
/// mis-translation.
fn lex_number(b: &[u8], start: usize) -> Option<(Tok, usize)> {
    let mut i = start;
    let (radix, digits_start) = if b[i] == b'0' && matches!(b.get(i + 1), Some(b'x' | b'X')) {
        (16u32, i + 2)
    } else if b[i] == b'0' && b.get(i + 1).is_some_and(|c| c.is_ascii_digit()) {
        (8u32, i + 1)
    } else {
        (10u32, i)
    };
    i = digits_start;
    while i < b.len() && (b[i] as char).is_digit(radix) {
        i += 1;
    }
    if i == digits_start {
        return None;
    }
    // A `.`, exponent, or float suffix means this is not an integer constant.
    if matches!(b.get(i), Some(b'.')) {
        return None;
    }
    if radix != 16 && matches!(b.get(i), Some(b'e' | b'E')) {
        return None;
    }
    if matches!(b.get(i), Some(b'f' | b'F')) {
        return None;
    }
    let text = std::str::from_utf8(&b[digits_start..i]).ok()?;
    let value = i128::from_str_radix(text, radix).ok()?;
    let mut unsigned_suffix = false;
    while i < b.len() && matches!(b[i], b'u' | b'U' | b'l' | b'L') {
        if matches!(b[i], b'u' | b'U') {
            unsigned_suffix = true;
        }
        i += 1;
    }
    // A suffix that runs into an identifier is not a constant we model.
    if i < b.len() && is_ident_byte(b[i]) {
        return None;
    }
    Some((Tok::Num { value, unsigned_suffix }, i))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn directives_and_comments_are_dropped() {
        let toks = tokenize("#include <stdint.h>\n// c\n/* b */ int x;\n").unwrap();
        assert_eq!(toks, vec![Tok::Ident("int".into()), Tok::Ident("x".into()), Tok::Punct(";"),]);
    }

    #[test]
    fn a_float_constant_refuses_the_unit() {
        assert!(tokenize("double d = 1.5;").is_none());
        assert!(tokenize("float f = 1e3;").is_none());
    }

    #[test]
    fn longest_punctuator_wins() {
        let toks = tokenize("a <<= b; c -> d; e ++;").unwrap();
        assert!(toks.contains(&Tok::Punct("<<=")));
        assert!(toks.contains(&Tok::Punct("->")));
        assert!(toks.contains(&Tok::Punct("++")));
    }

    #[test]
    fn unterminated_block_comment_refuses() {
        assert!(tokenize("int f(void) { /* nope \n").is_none());
    }

    #[test]
    fn integer_suffixes_and_radices() {
        let toks = tokenize("0x10 010 12u").unwrap();
        assert_eq!(
            toks,
            vec![
                Tok::Num { value: 16, unsigned_suffix: false },
                Tok::Num { value: 8, unsigned_suffix: false },
                Tok::Num { value: 12, unsigned_suffix: true },
            ]
        );
    }
}

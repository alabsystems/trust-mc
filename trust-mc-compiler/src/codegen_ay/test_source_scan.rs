// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The source scanner the single-rule lints share
//! (`test_const_pointer_single_rule.rs`, `test_mono_ty_single_rule.rs`):
//! comments and string literals blanked (lines kept), then tokens with their
//! lines. A lint guards spellings, not semantics.

#![allow(clippy::unwrap_used)]

use std::path::{Path, PathBuf};

/// `src` with every comment and string/char literal replaced by spaces
/// (newlines kept, so line numbers survive).
pub(super) fn strip_comments_and_strings(src: &str) -> String {
    let b = src.as_bytes();
    let n = b.len();
    let mut out = Vec::with_capacity(n);
    let blank = |out: &mut Vec<u8>, bytes: &[u8]| {
        out.extend(bytes.iter().map(|&c| if c == b'\n' { b'\n' } else { b' ' }));
    };
    let ident_before = |i: usize| i > 0 && (b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_');
    let mut i = 0;
    while i < n {
        // Line comment (doc comments included).
        if b[i..].starts_with(b"//") {
            let end = b[i..].iter().position(|&c| c == b'\n').map_or(n, |p| i + p);
            blank(&mut out, &b[i..end]);
            i = end;
            continue;
        }
        // Block comment, nested.
        if b[i..].starts_with(b"/*") {
            let mut depth = 0usize;
            let mut j = i;
            while j < n {
                if b[j..].starts_with(b"/*") {
                    depth += 1;
                    j += 2;
                } else if b[j..].starts_with(b"*/") {
                    depth -= 1;
                    j += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    j += 1;
                }
            }
            blank(&mut out, &b[i..j]);
            i = j;
            continue;
        }
        // Raw string: r"..", r#".."#, br"..".
        if !ident_before(i) {
            let prefix = if b[i..].starts_with(b"br") {
                2
            } else if b[i] == b'r' {
                1
            } else {
                0
            };
            if prefix > 0 {
                let mut j = i + prefix;
                let mut hashes = 0;
                while j < n && b[j] == b'#' {
                    hashes += 1;
                    j += 1;
                }
                if j < n && b[j] == b'"' {
                    let mut close = vec![b'"'];
                    close.extend(std::iter::repeat_n(b'#', hashes));
                    let body = j + 1;
                    let end = b[body..]
                        .windows(close.len())
                        .position(|w| w == close.as_slice())
                        .map_or(n, |p| body + p + close.len());
                    blank(&mut out, &b[i..end]);
                    i = end;
                    continue;
                }
            }
        }
        // String or byte string.
        if b[i] == b'"' || (b[i] == b'b' && i + 1 < n && b[i + 1] == b'"' && !ident_before(i)) {
            let mut j = if b[i] == b'b' { i + 2 } else { i + 1 };
            while j < n && b[j] != b'"' {
                j += if b[j] == b'\\' { 2 } else { 1 };
            }
            let end = (j + 1).min(n);
            blank(&mut out, &b[i..end]);
            i = end;
            continue;
        }
        // Char literal (a lifetime `'a` is kept).
        if b[i] == b'\'' {
            let char_end = if i + 2 < n && b[i + 1] == b'\\' {
                // `'\n'`, `'\''`, `'\\'`, `'\x41'`, `'\u{..}'`: the escaped
                // character is at i + 2, the closing quote after it.
                b[i + 3..].iter().position(|&c| c == b'\'').map(|p| i + 3 + p + 1)
            } else {
                // One UTF-8 scalar then a closing quote.
                let rest = &src[i + 1..];
                rest.chars().next().and_then(|c| {
                    let after = i + 1 + c.len_utf8();
                    (after < n && b[after] == b'\'').then_some(after + 1)
                })
            };
            if let Some(end) = char_end {
                blank(&mut out, &b[i..end]);
                i = end;
                continue;
            }
        }
        out.push(b[i]);
        i += 1;
    }
    String::from_utf8(out).unwrap()
}

/// The tokens of stripped source with their 1-based lines: identifiers,
/// `::`, and every other non-space character on its own.
pub(super) fn tokens(stripped: &str) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    let mut line = 1;
    let mut chars = stripped.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        if c == '\n' {
            line += 1;
        } else if c.is_whitespace() {
        } else if c.is_alphanumeric() || c == '_' {
            let mut end = i + c.len_utf8();
            while let Some(&(j, d)) = chars.peek() {
                if d.is_alphanumeric() || d == '_' {
                    end = j + d.len_utf8();
                    chars.next();
                } else {
                    break;
                }
            }
            out.push((stripped[i..end].to_string(), line));
        } else if c == ':' && chars.peek().is_some_and(|&(_, d)| d == ':') {
            chars.next();
            out.push(("::".to_string(), line));
        } else {
            out.push((c.to_string(), line));
        }
    }
    out
}

pub(super) fn is_test_file(rel: &str) -> bool {
    let parts: Vec<&str> = rel.split('/').collect();
    let base = parts.last().copied().unwrap_or("");
    parts[..parts.len().saturating_sub(1)].contains(&"tests")
        || base.starts_with("test_")
        || base.ends_with("_tests.rs")
        || base == "tests.rs"
}

pub(super) fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap().flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension() == Some("rs".as_ref()) {
            out.push(path);
        }
    }
}

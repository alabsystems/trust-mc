// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! ADT sort naming: unique SMT sort names from generic ADT definitions.
//!
//! Extracted from names.rs — Part of #2408.

use std::fmt::Write as _;

use rustc_public::CrateDef;
use rustc_public::ty::{AdtDef, GenericArgKind, GenericArgs};

/// Z3 built-in sort names that cannot be used as user-defined datatype names.
/// Declaring a datatype with any of these names causes Z3 `(error "sort already
/// defined ...")` which overrides valid PROOF verdicts to FAILURE. Part of #3348.
const Z3_RESERVED_SORT_NAMES: &[&str] = &["Array", "Bool", "Int", "Real", "String"];

/// Build a unique SMT sort name for a generic ADT.
///
/// This prevents collisions between different instantiations like `Option<u32>` and `Option<u64>`.
///
/// REQUIRES: `def` is a valid ADT definition.
/// ENSURES: Returned name is a valid SMT identifier (no spaces or special chars).
/// ENSURES: Different generic instantiations produce different names.
/// ENSURES: Name does not collide with Z3 built-in sort names (#3348).
pub fn adt_sort_name(def: AdtDef, args: &GenericArgs) -> String {
    let base = def.trimmed_name();
    let name = adt_sort_name_from_base(&base, args);
    // Prefix with "Adt_" if the name collides with a Z3 built-in sort.
    // User-defined `struct Array` produces sort name "Array" which conflicts
    // with Z3's built-in Array theory sort, causing "(error "sort already
    // defined Array")" that overrides valid PROOF verdicts.
    if Z3_RESERVED_SORT_NAMES.contains(&name.as_str()) {
        let mut prefixed = String::with_capacity(name.len() + 4);
        prefixed.push_str("Adt_");
        prefixed.push_str(&name);
        prefixed
    } else {
        name
    }
}

fn adt_sort_name_from_base(base: &str, args: &GenericArgs) -> String {
    if args.0.is_empty() {
        return base.to_owned();
    }

    let mut result = String::from(base);
    // Reusable buffer for type/const formatting (Part of #2267): avoids
    // 2 intermediate String allocations per generic arg.
    let mut buf = String::new();
    for arg in &args.0 {
        result.push('_');
        match arg {
            GenericArgKind::Type(ty) => {
                buf.clear();
                let _ = write!(&mut buf, "{ty}");
                let canonical = erase_lifetime_tokens(&buf);
                sanitize_adt_suffix_into(canonical.as_ref(), &mut result);
            }
            GenericArgKind::Const(const_val) => {
                buf.clear();
                let _ = write!(&mut buf, "{const_val:?}");
                sanitize_adt_suffix_into(&buf, &mut result);
            }
            GenericArgKind::Lifetime(_) => result.push_str("lt"),
        }
    }
    result
}

/// Sanitize a type suffix for use in SMT sort names.
///
/// Converts type strings into valid SMT identifiers by:
/// - Replacing `&mut ` with `refmut_` and `&` with `ref_` (#806)
/// - Replacing `*mut ` with `ptrmut_` and `*const ` with `ptrconst_`
/// - Replacing other special characters with underscores
/// - Collapsing consecutive underscores
/// - Removing trailing underscores
///
/// This prevents naming inconsistencies like Option__u32 vs Option_u32 where
/// the double underscore comes from `&u32` being sanitized to `_u32`.
///
/// REQUIRES: (no preconditions - handles any string including empty)
/// ENSURES: Returned string contains only ASCII alphanumerics and underscores.
/// ENSURES: Returned string has no consecutive underscores.
/// ENSURES: Returned string has no trailing underscore.
/// ENSURES: Returned string is non-empty (returns "t" for empty/whitespace input).
pub fn sanitize_adt_suffix(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len() + 8);
    sanitize_adt_suffix_into(raw, &mut out);
    out
}

/// Drop concrete lifetime names from nested type displays before SMT naming.
///
/// `adt_sort_name()` encodes direct lifetime generic args with the stable `lt`
/// marker. Nested type-arg displays like `Wrapper<Inner<'a>>` historically
/// leaked the concrete region name from `Display(Ty)` into the outer sort name,
/// producing `Wrapper_Inner_a` on one path and `Wrapper_Inner` on another after
/// region erasure. Removing the lifetime token keeps sort names stable across
/// those paths while preserving the direct `lt` marker on `Inner<'a>` itself.
fn erase_lifetime_tokens(raw: &str) -> std::borrow::Cow<'_, str> {
    if !raw.contains('\'') {
        return std::borrow::Cow::Borrowed(raw);
    }

    let mut out = String::with_capacity(raw.len());
    let mut chars = raw.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '\'' {
            while let Some(next) = chars.peek() {
                if next.is_ascii_alphanumeric() || *next == '_' {
                    chars.next();
                } else {
                    break;
                }
            }
            continue;
        }
        out.push(ch);
    }
    std::borrow::Cow::Owned(out)
}

/// Append a sanitized type suffix directly into an existing buffer (Part of #2267).
///
/// Same semantics as `sanitize_adt_suffix` but avoids an intermediate `String`
/// allocation by writing directly into the caller's buffer. Used by
/// `adt_sort_name_from_base` to eliminate 2 allocations per generic arg.
pub(crate) fn sanitize_adt_suffix_into(raw: &str, out: &mut String) {
    // Single-pass: replace reference/pointer markers and sanitize simultaneously.
    let start_len = out.len();
    let mut last_was_underscore = false;
    let bytes = raw.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        if bytes[i] == b'&' {
            if raw[i..].starts_with("&mut ") {
                out.push_str("refmut_");
                last_was_underscore = true;
                i += 5;
            } else {
                out.push_str("ref_");
                last_was_underscore = true;
                i += 1;
            }
        } else if bytes[i] == b'*' {
            if raw[i..].starts_with("*mut ") {
                out.push_str("ptrmut_");
                last_was_underscore = true;
                i += 5;
            } else if raw[i..].starts_with("*const ") {
                out.push_str("ptrconst_");
                last_was_underscore = true;
                i += 7;
            } else {
                if !last_was_underscore {
                    out.push('_');
                    last_was_underscore = true;
                }
                i += 1;
            }
        } else if bytes[i].is_ascii_alphanumeric() {
            out.push(bytes[i] as char);
            last_was_underscore = false;
            i += 1;
        } else {
            // Underscore, space, punctuation, etc. — collapse into single underscore
            if !last_was_underscore {
                out.push('_');
                last_was_underscore = true;
            }
            i += 1;
        }
    }

    // Remove trailing underscore
    if out.ends_with('_') {
        out.pop();
    }

    // If nothing was appended, push the fallback "t"
    if out.len() == start_len {
        out.push('t');
    }
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).

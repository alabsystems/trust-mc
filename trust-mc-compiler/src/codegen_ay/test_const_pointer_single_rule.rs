// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source lint: the constant-pointer rule is stated ONCE
//! (`shared/const_pointer.rs`), so only that module may spell rustc's
//! constant representation.
//!
//! Every non-test `.rs` file under `src/codegen_ay/` other than the module
//! is scanned AFTER its comments and string literals are removed, and none
//! may spell:
//! - `provenance` as a field (`.provenance`, whitespace-insensitive, so a
//!   chain split across lines is caught);
//! - `ProvenanceMap`;
//! - an `Allocation { .. }` struct literal;
//! - `GlobalAlloc`;
//! - `eval_initializer`;
//! - `ConstantKind::Allocated` or `TyConstKind::Value` (a constant's bytes
//!   enter only through `const_pointer::const_bytes` and its scalar readers);
//! - any `rustc_middle::mir::interpret` path.
//!
//! A reader that spells none of these can reach a constant's bytes only
//! through a `ConstRead`, whose accessors apply the slot clause (relocated
//! bytes are never data), and a constant pointer's address only through
//! `ConstPtr::address`.
//!
//! The ALLOWLIST is empty. A new reader must go through the module.
//!
//! Evidence rung: a test. It guards spellings, not semantics: a reader that
//! reaches rustc's constant representation through a spelling not in the
//! list is not caught. Out of scope (outside `codegen_ay/`, and code-read to
//! never decode bytes or form addresses): `kani_middle/reachability.rs` and
//! the two `check_uninit` visitors, which enumerate relocation targets for
//! reachability and instrumentation.

#![allow(clippy::unwrap_used)]

use std::path::Path;

use super::test_source_scan::{collect_rs_files, is_test_file, strip_comments_and_strings, tokens};

/// The forbidden spellings, each a token sequence.
const FORBIDDEN: &[(&str, &[&str])] = &[
    ("`.provenance` field", &[".", "provenance"]),
    ("`ProvenanceMap`", &["ProvenanceMap"]),
    ("`Allocation { .. }` literal", &["Allocation", "{"]),
    ("`GlobalAlloc`", &["GlobalAlloc"]),
    ("`eval_initializer`", &["eval_initializer"]),
    ("`ConstantKind::Allocated`", &["ConstantKind", "::", "Allocated"]),
    ("`TyConstKind::Value`", &["TyConstKind", "::", "Value"]),
    ("`rustc_middle::mir::interpret`", &["rustc_middle", "::", "mir", "::", "interpret"]),
];

/// Files (relative to `src/codegen_ay/`) allowed to spell a forbidden token.
/// EMPTY: the rule's only spelling is `shared/const_pointer.rs`, which is not
/// scanned.
const ALLOWLIST: &[&str] = &[];

/// The one module that states the rule.
const RULE_MODULE: &str = "shared/const_pointer.rs";

/// Every forbidden spelling in `src`: (what, line).
fn violations_in(src: &str) -> Vec<(&'static str, usize)> {
    let toks = tokens(&strip_comments_and_strings(src));
    let mut found = Vec::new();
    for start in 0..toks.len() {
        for (what, seq) in FORBIDDEN {
            if toks.len() - start >= seq.len()
                && seq.iter().zip(&toks[start..]).all(|(want, (got, _))| want == got)
            {
                found.push((*what, toks[start].1));
            }
        }
    }
    found
}

#[test]
fn const_pointer_rule_is_spelled_only_in_its_module() {
    let root =
        Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../trust-mc-compiler/src/codegen_ay"));
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    assert!(
        files.iter().any(|p| p.ends_with(RULE_MODULE)),
        "the rule module {RULE_MODULE} must exist under {}",
        root.display()
    );
    let mut scanned = 0;
    let mut report = Vec::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/");
        if rel == RULE_MODULE || is_test_file(&rel) || ALLOWLIST.contains(&rel.as_str()) {
            continue;
        }
        scanned += 1;
        let src = std::fs::read_to_string(path).unwrap();
        for (what, line) in violations_in(&src) {
            report.push(format!("  src/codegen_ay/{rel}:{line}: {what}"));
        }
    }
    assert!(scanned > 100, "expected to scan the codegen_ay tree, scanned {scanned} files");
    assert!(
        report.is_empty(),
        "rustc's constant representation spelled outside shared/const_pointer.rs \
         (read a constant through `const_pointer::const_bytes` / `fixed_pointee` / \
         `target_bytes`, and form its address with `ConstPtr::address`):\n{}",
        report.join("\n")
    );
}

/// The scanner itself: each forbidden spelling in code is found, with its
/// line; the same text in a comment or a string literal is not.
#[test]
fn const_pointer_rule_scanner_sees_code_not_comments() {
    let in_code: &[(&str, &str)] = &[
        ("let p = alloc\n    .provenance\n    .ptrs;", "`.provenance` field"),
        ("let m = ProvenanceMap { ptrs: vec![] };", "`ProvenanceMap`"),
        (
            "let a = Allocation { bytes, provenance, align, mutability };",
            "`Allocation { .. }` literal",
        ),
        ("use rustc_public::mir::alloc::GlobalAlloc;", "`GlobalAlloc`"),
        ("let init = def.eval_initializer();", "`eval_initializer`"),
        ("match k { ConstantKind :: Allocated(a) => a, _ => x }", "`ConstantKind::Allocated`"),
        ("if let TyConstKind::Value(_, a) = k {}", "`TyConstKind::Value`"),
        ("use rustc_middle::mir::interpret::Scalar;", "`rustc_middle::mir::interpret`"),
    ];
    for (src, what) in in_code {
        let src = format!("fn f() {{\n{src}\n}}");
        let found = violations_in(&src);
        assert!(
            found.iter().any(|(w, line)| w == what && *line >= 2),
            "{what} in code must be found in {src:?}, found {found:?}"
        );
    }
    let not_code = [
        "// alloc.provenance.ptrs, GlobalAlloc::Memory, eval_initializer()\nfn f() {}",
        "/* ConstantKind::Allocated /* nested TyConstKind::Value */ Allocation { } */\nfn f() {}",
        "/// `rustc_middle::mir::interpret` and `ProvenanceMap`\nfn f() {}",
        "fn f() -> &'static str { \"GlobalAlloc::from(id).provenance\" }",
        "fn f() -> &'static str { r#\"ConstantKind::Allocated \"quoted\" \"# }",
        "fn f<'a>(x: &'a u8) -> char { let _ = b\"eval_initializer\"; '\\'' }",
        "struct AllocationSite { provenance_count: usize }\nfn f(s: AllocationSite) -> usize { s.provenance_count }",
    ];
    for src in not_code {
        assert!(
            violations_in(src).is_empty(),
            "no violation expected in {src:?}: {:?}",
            violations_in(src)
        );
    }
}

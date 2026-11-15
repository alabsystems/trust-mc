// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source lint: Rule A (the type of a field, and of a body local) is stated
//! ONCE, in `shared/mono_ty.rs`, so only that module may reach a rustc query
//! that panics on non-monomorphic input or read a field's declared type.
//!
//! Every non-test `.rs` file under `src/codegen_ay/` other than the module is
//! scanned AFTER its comments and string literals are removed
//! (`test_source_scan`), and none may spell:
//! - `resolve_generic_ty` or `resolve_adt_field_ty` (the shallow resolvers
//!   Rule A deleted);
//! - `ty_with_args` (rustc_public's PANICKING field instantiation; use
//!   `mono_ty::field_ty`);
//! - `resolve_drop_in_place` (use `mono_ty::drop_in_place`);
//! - `instantiate_mir_and_normalize_erasing_regions`,
//!   `instantiate_and_normalize_erasing_regions` or `normalize_erasing_regions`
//!   (the panicking normalizers; the `try_` ones are distinct tokens);
//! - the shallow parameter guards Rule A deleted
//!   (`ty_has_unresolved_non_region_params`, `bmc_ty_has_unresolved_params`,
//!   `ty_has_params`, `ty_has_unresolved_params`);
//! - `.has_param()` outside [`HAS_PARAM_ALLOWLIST`] (which asks whether an
//!   IMPL is generic, a different question);
//! - a bare `FieldDef::ty()` read: `field.ty()`, `f.ty()`, `field_def.ty()`,
//!   `fld.ty()`, `….fields()[i].ty()`, `fields[i].ty()`,
//!   `….fields().first()?.ty()`, `….fields().get(i)?.ty()`.
//!
//! Evidence rung: a test. It guards spellings, not semantics: a field read
//! through a binding name the patterns do not list is not caught.
//! `kani_middle/` is out of scope (design residual 8).
//!
//! Run by `scripts/check-trust-lane-build.sh` (`-- single_rule`).

#![allow(clippy::unwrap_used)]

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::path::Path;

use super::test_source_scan::{collect_rs_files, is_test_file, strip_comments_and_strings, tokens};

/// Forbidden token sequences.
const FORBIDDEN: &[(&str, &[&str])] = &[
    ("`resolve_generic_ty` (use `mono_ty::field_ty`)", &["resolve_generic_ty"]),
    ("`resolve_adt_field_ty` (use `mono_ty::field_ty`)", &["resolve_adt_field_ty"]),
    ("`ty_with_args` (panics; use `mono_ty::field_ty`)", &["ty_with_args"]),
    ("`resolve_drop_in_place` (use `mono_ty::drop_in_place`)", &["resolve_drop_in_place"]),
    (
        "`instantiate_mir_and_normalize_erasing_regions` (use `mono_ty::body_ty`)",
        &["instantiate_mir_and_normalize_erasing_regions"],
    ),
    (
        "`instantiate_and_normalize_erasing_regions` (use `mono_ty::field_ty`)",
        &["instantiate_and_normalize_erasing_regions"],
    ),
    (
        "`normalize_erasing_regions` (panics; use a `try_` normalizer)",
        &["normalize_erasing_regions"],
    ),
    (
        "shallow guard `ty_has_unresolved_non_region_params`",
        &["ty_has_unresolved_non_region_params"],
    ),
    ("shallow guard `bmc_ty_has_unresolved_params`", &["bmc_ty_has_unresolved_params"]),
    ("shallow guard `ty_has_params`", &["ty_has_params"]),
    ("shallow guard `ty_has_unresolved_params`", &["ty_has_unresolved_params"]),
];

/// Files (relative to `src/codegen_ay/`) whose `.has_param()` asks whether an
/// impl is generic, with their counts.
const HAS_PARAM_ALLOWLIST: &[(&str, usize)] =
    &[("chc/dyn_coercion.rs", 2), ("chc/dyn_coercion_resolve.rs", 1)];

/// The one module that states the rule.
const RULE_MODULE: &str = "shared/mono_ty.rs";

/// Bare `FieldDef::ty()` reads, over stripped source.
const BARE_FIELD_TY: &[&str] = &[
    r"\.fields\(\)\s*\[[^\]]*\]\s*\.\s*ty\(\)",
    r"\b(field|f|field_def|fld)\s*\.\s*ty\(\)",
    r"\bfields\w*\s*\[[^\]]*\]\s*\.\s*ty\(\)",
    r"\.fields\(\)\s*\.\s*(first|last)\(\)\s*\??\s*\.\s*ty\(\)",
    r"\.fields\(\)\s*\.\s*get\([^)]*\)\s*\??\s*\.\s*ty\(\)",
];

#[derive(Default)]
struct Findings {
    forbidden: Vec<(&'static str, usize)>,
    has_param: Vec<usize>,
    bare_field_ty: Vec<usize>,
}

fn line_of(src: &str, offset: usize) -> usize {
    src[..offset].bytes().filter(|&b| b == b'\n').count() + 1
}

fn findings_in(src: &str) -> Findings {
    let stripped = strip_comments_and_strings(src);
    let toks = tokens(&stripped);
    let mut out = Findings::default();
    for start in 0..toks.len() {
        for (what, seq) in FORBIDDEN {
            if toks.len() - start >= seq.len()
                && seq.iter().zip(&toks[start..]).all(|(want, (got, _))| want == got)
            {
                out.forbidden.push((*what, toks[start].1));
            }
        }
        let tok = toks[start].0.as_str();
        if tok == "has_param"
            && start > 0
            && toks[start - 1].0 == "."
            && toks.get(start + 1).is_some_and(|(t, _)| t == "(")
        {
            out.has_param.push(toks[start].1);
        }
    }
    for pattern in BARE_FIELD_TY {
        let re = regex::Regex::new(pattern).unwrap();
        for m in re.find_iter(&stripped) {
            out.bare_field_ty.push(line_of(&stripped, m.start()));
        }
    }
    out.bare_field_ty.sort_unstable();
    out.bare_field_ty.dedup();
    out
}

fn allowance(list: &[(&str, usize)], rel: &str) -> usize {
    list.iter().find(|(file, _)| *file == rel).map_or(0, |(_, n)| *n)
}

#[test]
fn mono_ty_rule_is_spelled_only_in_its_module() {
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
        if rel == RULE_MODULE || is_test_file(&rel) {
            continue;
        }
        scanned += 1;
        let found = findings_in(&std::fs::read_to_string(path).unwrap());
        for (what, line) in found.forbidden {
            report.push(format!("  src/codegen_ay/{rel}:{line}: {what}"));
        }
        for line in &found.bare_field_ty {
            report.push(format!(
                "  src/codegen_ay/{rel}:{line}: a bare `FieldDef::ty()` read (use `mono_ty::field_ty`)"
            ));
        }
        if found.has_param.len() != allowance(HAS_PARAM_ALLOWLIST, &rel) {
            for line in &found.has_param {
                report.push(format!(
                    "  src/codegen_ay/{rel}:{line}: `.has_param()` (use `mono_ty::has_unresolved_params`; \
                     the allowlist is for impl-genericity checks only, {} allowed here)",
                    allowance(HAS_PARAM_ALLOWLIST, &rel)
                ));
            }
        }
    }
    assert!(scanned > 100, "expected to scan the codegen_ay tree, scanned {scanned} files");
    assert!(
        report.is_empty(),
        "Rule A (shared/mono_ty.rs) spelled elsewhere:\n{}",
        report.join("\n")
    );
}

/// The scanner sees each forbidden spelling in code, with its line; the same
/// text in a comment or a string literal is not seen.
#[test]
fn mono_ty_rule_scanner_sees_code_not_comments() {
    let cases: &[(&str, fn(&Findings) -> bool)] = &[
        ("let t = Self::resolve_generic_ty(f, &args);", |f| !f.forbidden.is_empty()),
        ("let i = Instance::resolve_drop_in_place(ty);", |f| !f.forbidden.is_empty()),
        ("let t = tcx.normalize_erasing_regions(env, v);", |f| !f.forbidden.is_empty()),
        ("let t = i.instantiate_mir_and_normalize_erasing_regions(tcx, e, b);", |f| {
            !f.forbidden.is_empty()
        }),
        ("if internal.has_param() { return; }", |f| f.has_param.len() == 1),
        ("let t = field.ty_with_args(&args);", |f| !f.forbidden.is_empty()),
        ("let t = field.ty();", |f| f.bare_field_ty.len() == 1),
        ("let t = f\n    .ty();", |f| f.bare_field_ty.len() == 1),
        ("let t = v.fields()[0].ty();", |f| f.bare_field_ty.len() == 1),
        ("let t = fields[i].ty();", |f| f.bare_field_ty.len() == 1),
        ("let t = v.fields().first()?.ty();", |f| f.bare_field_ty.len() == 1),
        ("let t = v.fields().get(idx)?.ty();", |f| f.bare_field_ty.len() == 1),
    ];
    for (src, check) in cases {
        let src = format!("fn f() {{\n{src}\n}}");
        let found = findings_in(&src);
        assert!(check(&found), "a violation must be found in {src:?}");
    }
    let not_code = [
        "// resolve_generic_ty, resolve_drop_in_place, field.ty(), x.has_param()\nfn f() {}",
        "/* normalize_erasing_regions /* nested field.ty_with_args(a) */ */\nfn f() {}",
        "fn f() -> &'static str { \"f.ty() and fields[0].ty()\" }",
        "fn f(t: Ty) -> bool { t.try_normalize_erasing_regions(e, v).is_ok() }",
        "fn f(x: &Place, b: &Body) { let _ = x.ty(b.locals()); let _ = op.ty(locals); }",
        "fn f(i: Instance) -> Ty { i.ty() }",
        "fn f(s: &S) -> bool { s.has_params }",
    ];
    for src in not_code {
        let found = findings_in(src);
        assert!(
            found.forbidden.is_empty()
                && found.has_param.is_empty()
                && found.bare_field_ty.is_empty(),
            "no violation expected in {src:?}"
        );
    }
}

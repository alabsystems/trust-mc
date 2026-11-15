// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source lint: Rule E (design trust-mc-reds-final §4.4) — a fresh CHC value is
//! minted only through `chc/codegen_ctx/fresh_vars.rs` (`ExactVar`, `Havoc`),
//! which states why it is fresh.
//!
//! `globals::declare_pending_var` is private to `codegen_ctx`, so the compiler
//! already refuses a call outside it; this lint also holds the spelling (a
//! re-export would reopen it) and the lower-level route around it:
//! `push_pending_var_decl` declares a variable without making the value, and a
//! site that paired it with `Expr::var` would mint an unbooked value again. It
//! is allowed only where it declares a state variable's input/output column
//! pair (a relation column, not a fresh value).
//!
//! Every non-test `.rs` file under `src/codegen_ay/` is scanned after its
//! comments and string literals are removed (`test_source_scan`).
//!
//! Evidence rung: a test plus the module privacy the compiler enforces. Whether
//! a site chose the right constructor is a review (the classes and their rules
//! in `docs/DECISION_QUEUE.md`, REDS-REST).
//!
//! Run by `scripts/check-trust-lane-build.sh` (`-- single_rule`).

#![allow(clippy::unwrap_used)]

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::path::Path;

use super::test_source_scan::{collect_rs_files, is_test_file, strip_comments_and_strings, tokens};

/// Files (relative to `src/codegen_ay/`) that may spell `declare_pending_var`.
const DECLARE_ALLOWED: &[&str] = &["chc/codegen_ctx/globals.rs", "chc/codegen_ctx/fresh_vars.rs"];

/// Files that may call `push_pending_var_decl`: its definition, and the one
/// that declares a state variable's input/output column pair
/// (`ChcCtx::declare_state_column_pair` and the late-array twins beside it).
const PUSH_ALLOWED: &[&str] = &["chc/codegen_ctx/globals.rs", "chc/codegen_ctx/late_state_vars.rs"];

/// `(token, line)` of every forbidden spelling in `src` (a file at `rel`).
fn findings_in(rel: &str, src: &str) -> Vec<(&'static str, usize)> {
    let stripped = strip_comments_and_strings(src);
    let mut out = Vec::new();
    for (tok, line) in tokens(&stripped) {
        let (name, allowed): (&'static str, &[&str]) = match tok.as_str() {
            "declare_pending_var" => ("declare_pending_var", DECLARE_ALLOWED),
            "push_pending_var_decl" => ("push_pending_var_decl", PUSH_ALLOWED),
            _ => continue,
        };
        if !allowed.contains(&rel) {
            out.push((name, line));
        }
    }
    out
}

#[test]
fn fresh_values_are_minted_only_by_the_rule_e_constructors() {
    let root =
        Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../trust-mc-compiler/src/codegen_ay"));
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    assert!(files.len() > 100, "scanned too few files ({}): wrong root?", files.len());
    let mut violations = Vec::new();
    for file in &files {
        let rel = file.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/");
        if is_test_file(&rel) {
            continue;
        }
        let src = std::fs::read_to_string(file).unwrap();
        for (what, line) in findings_in(&rel, &src) {
            violations.push(format!("src/codegen_ay/{rel}:{line}: `{what}`"));
        }
    }
    assert!(
        violations.is_empty(),
        "a fresh value is minted outside the Rule E constructors; use \
         `ExactVar::{{defined, nondet, unobserved}}`, `Havoc::mint` or `Havoc::booked`:\n{}",
        violations.join("\n")
    );
}

/// The scanner sees code, not comments or strings, and honours the allowlists.
#[test]
fn fresh_var_single_rule_catches_each_spelling() {
    let caught = |rel: &str, src: &str| !findings_in(rel, src).is_empty();
    assert!(caught("chc/x.rs", "fn f() { super::declare_pending_var(n, s); }"));
    assert!(caught("chc/x.rs", "use super::codegen_ctx::declare_pending_var;"));
    assert!(caught("chc/x.rs", "fn f() { push_pending_var_decl(n, s); }"));
    assert!(!caught("chc/x.rs", "// declare_pending_var(n, s)\nfn f() {}"));
    assert!(!caught("chc/x.rs", "fn f() -> &'static str { \"declare_pending_var\" }"));
    assert!(!caught("chc/codegen_ctx/fresh_vars.rs", "fn f() { declare_pending_var(n, s); }"));
    assert!(!caught(
        "chc/codegen_ctx/late_state_vars.rs",
        "fn f() { push_pending_var_decl(n, s); }"
    ));
    assert!(caught("chc/codegen_ctx/late_state_vars.rs", "fn f() { declare_pending_var(n, s); }"));
}

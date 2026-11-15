// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source lint: a sort's NAME is read only by the naming module
//! (design trust-mc-reds-final §7.2, T3-1).
//!
//! The naming module (`trust-mc-codegen-types/src/names`) builds every sort
//! name, so it alone knows the scheme: an ADT's sort is its definition path
//! sanitized and then its arguments (`names::adt_sort_name`), a model sort has
//! a fixed prefix (`Slice_`, `Dyn_`, `VecIntoIter_`, ...). A string test of a
//! sort name elsewhere (`dt.name.starts_with("Option_")`) silently changes
//! meaning when the scheme does: the switch of the ADT base from the trimmed
//! name to the path would have stopped `Option` sorts from reading as Option.
//! Such a test asks the module instead (`names::is_option_sort_name`,
//! `names::adt_sort_is`).
//!
//! Every non-test `.rs` file under `src/codegen_ay/` is scanned; a match counts
//! only where the code is code (the same offset of `test_source_scan`'s
//! comment- and string-blanked copy is not blank). Forbidden: a string
//! predicate (`starts_with`, `ends_with`, `contains`, `strip_prefix`,
//! `strip_suffix`, `find`, `split`) or a comparison with a string literal, on
//! - `<dt>.name`, where the receiver is a `DatatypeSort` binding (`dt`, `sdt`,
//!   `fdt`, `tgt`, `*_dt`, `*_tgt`);
//! - a binding named `dt_name`, `sort_name`, `*_dt_name` or `*_sort_name`;
//! - the parameter of a closure applied to `datatype_name()`.
//!
//! Evidence rung: a test. It guards spellings: a sort name read through a
//! binding name the patterns do not list is not caught. Names of RUST items
//! (`def.trimmed_name()`, `def.name()`) are another question and are not
//! scanned.
//!
//! Run by `scripts/check-trust-lane-build.sh` (`-- single_rule`).

#![allow(clippy::unwrap_used)]

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::path::Path;

use super::test_source_scan::{collect_rs_files, is_test_file, strip_comments_and_strings};

const PREDICATE: &str = r"(?:starts_with|ends_with|contains|strip_prefix|strip_suffix|find|split)";

/// Receivers that hold a sort's name.
fn patterns() -> Vec<(&'static str, regex::Regex)> {
    let dt_field = r"\b(?:dt|sdt|fdt|tgt|[a-z_]+_dt|[a-z_]+_tgt)\.name\b";
    let name_binding = r"\b(?:dt_name|sort_name|[a-z_]+_dt_name|[a-z_]+_sort_name)\b";
    [
        ("a string predicate on `<dt>.name`", format!(r"{dt_field}\s*\.\s*{PREDICATE}\s*\(")),
        ("a string-literal comparison of `<dt>.name`", format!(r#"{dt_field}\s*(?:==|!=)\s*""#)),
        ("a string predicate on a sort-name binding", format!(r"{name_binding}\s*\.\s*{PREDICATE}\s*\(")),
        ("a string-literal comparison of a sort-name binding", format!(r#"{name_binding}\s*(?:==|!=)\s*""#)),
        (
            "a string predicate in a closure over `datatype_name()`",
            format!(
                r"datatype_name\(\)\s*\.\s*\w+\s*\(\s*(?:false\s*,\s*)?\|\s*(\w+)\s*\|\s*\w+\s*\.\s*{PREDICATE}\s*\("
            ),
        ),
    ]
    .into_iter()
    .map(|(what, pattern)| (what, regex::Regex::new(&pattern).unwrap()))
    .collect()
}

fn line_of(src: &str, offset: usize) -> usize {
    src[..offset].bytes().filter(|&b| b == b'\n').count() + 1
}

/// `(what, line)` of every forbidden spelling in `src` that is code.
fn findings_in(src: &str) -> Vec<(&'static str, usize)> {
    let stripped = strip_comments_and_strings(src);
    let is_code =
        |offset: usize| stripped.as_bytes().get(offset).is_some_and(|b| !b.is_ascii_whitespace());
    let mut out = Vec::new();
    for (what, re) in patterns() {
        for m in re.find_iter(src) {
            if is_code(m.start()) {
                out.push((what, line_of(src, m.start())));
            }
        }
    }
    out.sort_unstable_by_key(|&(_, line)| line);
    out
}

#[test]
fn sort_names_are_read_only_by_the_naming_module() {
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
        for (what, line) in findings_in(&src) {
            violations.push(format!("src/codegen_ay/{rel}:{line}: {what}"));
        }
    }
    assert!(
        violations.is_empty(),
        "a sort name is read outside the naming module; ask `names` instead \
         (`names::is_option_sort_name`, `names::adt_sort_is`, ...):\n{}",
        violations.join("\n")
    );
}

/// The patterns catch each spelling they name, and only in code.
#[test]
fn sort_name_single_rule_catches_each_spelling() {
    let caught = |src: &str| !findings_in(src).is_empty();
    assert!(caught("fn f(dt: &D) -> bool { dt.name.starts_with(\"Option_\") }"));
    assert!(caught("fn f(tgt_dt: &D) -> bool { tgt_dt.name == \"Layout\" }"));
    assert!(caught("fn f(inner_tgt: &D) -> bool { inner_tgt.name.starts_with(\"Dyn_\") }"));
    assert!(caught("fn f(dt_name: &str) -> bool { dt_name.contains(\"HashMap\") }"));
    assert!(caught("fn f(vec_sort_name: &str) -> bool { vec_sort_name != \"Vec\" }"));
    assert!(caught(
        "fn f(s: &S) -> bool { s.datatype_name().is_some_and(|n| n.contains(\"Slice\")) }"
    ));
    assert!(caught(
        "fn f(s: &S) -> bool { s.datatype_name().map_or(false, |n| n.starts_with(\"Slice_\")) }"
    ));
    assert!(!caught("// dt.name.starts_with(\"Option_\")\nfn f() {}"));
    assert!(!caught("fn f() -> &'static str { \"dt.name.starts_with(x)\" }"));
    assert!(!caught("fn f(dt: &D) -> bool { names::is_option_sort_name(&dt.name) }"));
    assert!(!caught("fn f(dt: &D, other: &str) -> bool { dt.name == other }"));
}

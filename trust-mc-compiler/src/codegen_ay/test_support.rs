// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Name helpers shared by the `chc` and `statement` unit tests (design
//! trust-mc-reds-final §5).
//!
//! A test source compiles as the crate `testcrate_<n>`, `<n>` a per-run
//! counter, and the encoder names a static's state variable by the static's
//! crate-qualified path: `static GLOBAL` in harness `probe` is
//! `_static_probe_testcrate_7::GLOBAL`. A test compares the part that does not
//! depend on the counter.

/// Whether `var` is the CHC state variable `names::static_var_name` gives the
/// static `short` in the harness `fn_name`: `_static_<fn_name>_<path>::<short>`
/// (the path is crate-qualified).
pub(in crate::codegen_ay) fn is_static_state_var(var: &str, fn_name: &str, short: &str) -> bool {
    var.strip_prefix(&super::names::static_var_name(fn_name, ""))
        .is_some_and(|rest| rest == short || rest.ends_with(&format!("::{short}")))
}

/// The sort name of a test source's own ADT without its crate segment:
/// `names::adt_sort_name` puts the definition path first, so `Outer<Inner>` of
/// `testcrate_7` is `testcrate_7_Outer_Inner`, and this returns `Outer_Inner`.
/// Panics unless `name` starts with `testcrate_<n>_`.
pub(in crate::codegen_ay) fn local_sort_name(name: &str) -> &str {
    let rest = name
        .strip_prefix("testcrate_")
        .unwrap_or_else(|| panic!("{name} is not a test crate's sort name"));
    let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
    assert!(digits > 0, "{name} has no test crate counter");
    rest[digits..]
        .strip_prefix('_')
        .unwrap_or_else(|| panic!("{name} has no item after its test crate segment"))
}

#[test]
fn local_sort_name_drops_the_test_crate_segment() {
    assert_eq!(local_sort_name("testcrate_12_Outer_Inner"), "Outer_Inner");
    assert!(std::panic::catch_unwind(|| local_sort_name("Outer_Inner")).is_err());
}

#[test]
fn is_static_state_var_matches_the_crate_qualified_name() {
    let var = format!("{}testcrate_3::GLOBAL", super::names::static_var_name("probe", ""));
    assert!(is_static_state_var(&var, "probe", "GLOBAL"));
    assert!(!is_static_state_var(&var, "probe", "OTHER"));
    assert!(!is_static_state_var(&var, "other_probe", "GLOBAL"));
}

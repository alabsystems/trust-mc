// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ordering regression tests for the CHC call dispatch chain.
//!
//! The dispatch chain in `codegen_call.rs` has ordering invariants where
//! specialized handlers MUST appear before general handlers. Misplacing a
//! handler causes silent fallthrough to the catch-all, producing
//! OverApproximation CTREX with no warning.
//!
//! Part of #3380: dispatch ordering regression test.
//! Part of #3575: inner dispatch chain ordering regression test.

use regex::Regex;

/// Extract dispatch step names from `codegen_call.rs` source in order.
///
/// Recognizes three patterns:
/// - `self.try_dispatch_call_<NAME>(dcx)` → step name `<NAME>`
/// - `self.is_foreign_call(...)` → step name `foreign`
/// - `self.codegen_call_primitive_cmp(dcx)` → step name `primitive_cmp`
fn extract_dispatch_steps(source: &str) -> Vec<String> {
    let try_re = Regex::new(r"self\.try_dispatch_call_(\w+)\(dcx\)")
        .expect("invariant: try_dispatch regex is valid");
    let foreign_re =
        Regex::new(r"self\.is_foreign_call\(").expect("invariant: foreign regex is valid");
    let catchall_re = Regex::new(r"self\.codegen_call_primitive_cmp\(dcx\)")
        .expect("invariant: catchall regex is valid");

    let mut steps = Vec::new();
    let mut foreign_seen = false;
    for line in source.lines() {
        let trimmed = line.trim();
        if let Some(cap) = try_re.captures(trimmed) {
            steps.push(cap[1].to_string());
        } else if foreign_re.is_match(trimmed) {
            // Multiple is_foreign_call blocks are valid (posix_memalign,
            // pthread noop, undefined catch-all). Record "foreign" once
            // at the position of the first occurrence.
            if !foreign_seen {
                steps.push("foreign".to_string());
                foreign_seen = true;
            }
        } else if catchall_re.is_match(trimmed) {
            steps.push("primitive_cmp".to_string());
        }
    }
    steps
}

/// Find the position of a step name in the dispatch chain.
/// Panics if the step is not found.
fn position(steps: &[String], name: &str) -> usize {
    steps
        .iter()
        .position(|s| s == name)
        .unwrap_or_else(|| panic!("dispatch step '{name}' not found in chain: {steps:?}"))
}

fn assert_before(steps: &[String], earlier: &str, later: &str) {
    let earlier_pos = position(steps, earlier);
    let later_pos = position(steps, later);
    assert!(
        earlier_pos < later_pos,
        "{earlier} (pos {earlier_pos}) must come before {later} (pos {later_pos})"
    );
}

/// Verify the main dispatch chain ordering invariants.
///
/// These invariants are documented in comments in `codegen_call.rs` but were
/// not previously tested. A refactoring that reorders handlers or inserts a
/// new handler at the wrong position would silently break verification.
#[test]
fn test_dispatch_chain_ordering() {
    let source = include_str!("../call/codegen_call.rs");
    let steps = extract_dispatch_steps(source);

    // Sanity: chain must have at least 25 steps (current count: 27).
    assert!(
        steps.len() >= 25,
        "dispatch chain too short ({} steps) — expected at least 25: {steps:?}",
        steps.len()
    );

    assert_eq!(steps[0], "kani", "kani hooks must be the first dispatch step, found: {}", steps[0]);

    let pre_inline_handlers = [
        "pow",
        "euclid",
        "wrapping_abs",
        "overflowing_arith",
        "math_intrinsic",
        "atomic",
        "simd",
        "misc_intrinsic",
        "struct_map_constructor",
        "vec_builder",
        "struct_map_accessor",
    ];
    for handler in &pre_inline_handlers {
        assert_before(&steps, handler, "fn_inline");
    }

    assert_before(&steps, "fn_inline", "fn_ptr");
    assert_before(&steps, "fn_ptr", "foreign");
    assert_before(&steps, "struct_clone", "misc");
    assert_before(&steps, "struct_map_accessor", "struct_method_passthrough");

    // Catch-all must stay last.
    let catchall_pos = position(&steps, "primitive_cmp");
    assert_eq!(
        catchall_pos,
        steps.len() - 1,
        "catch-all (primitive_cmp) must be the last step, but found at pos {catchall_pos} of {}",
        steps.len()
    );
}

/// Verify that the dispatch chain has no duplicate step names.
///
/// Each handler should appear exactly once in the main dispatch chain.
/// Duplicates indicate copy-paste errors or accidental double-dispatch.
#[test]
fn test_dispatch_chain_no_duplicates() {
    let source = include_str!("../call/codegen_call.rs");
    let steps = extract_dispatch_steps(source);

    let mut seen = std::collections::HashSet::new();
    for step in &steps {
        assert!(seen.insert(step.as_str()), "duplicate dispatch step '{step}' in chain");
    }
}

const PRIMARY_HELPER_STEPS: &[&str] = &["step_unchecked", "primitive_cmp_compare"];
const ARITHMETIC_HELPER_STEPS: &[&str] = &[
    "wrapping_arithmetic",
    "checked_arithmetic",
    "saturating_arithmetic",
    "exact_div",
    "pow",
    "euclid",
];
const INTRINSIC_HELPER_STEPS: &[&str] = &[
    "bit_intrinsics",
    "float_predicates",
    "fast_math",
    "misc_intrinsics",
    "range_contains",
    "slice_contains",
    "slice_as_array",
];

fn helper_dispatch_steps(trimmed: &str) -> Option<&'static [&'static str]> {
    if trimmed.contains("self.try_codegen_cmp_string_primary_dispatch(") {
        Some(PRIMARY_HELPER_STEPS)
    } else if trimmed.contains("self.try_codegen_cmp_string_arithmetic_dispatch(") {
        Some(ARITHMETIC_HELPER_STEPS)
    } else if trimmed.contains("self.try_codegen_cmp_string_intrinsic_dispatch(") {
        Some(INTRINSIC_HELPER_STEPS)
    } else {
        None
    }
}

fn direct_inner_dispatch_step(trimmed: &str) -> Option<&'static str> {
    if trimmed.contains("Self::step_unchecked_method(") {
        Some("step_unchecked")
    } else if trimmed.contains("primitive_cmp_method") && trimmed.starts_with("let ") {
        Some("primitive_cmp_compare")
    } else if trimmed.contains("Self::wrapping_arithmetic_method(") {
        Some("wrapping_arithmetic")
    } else if trimmed.contains("Self::checked_arithmetic_method(") {
        Some("checked_arithmetic")
    } else if trimmed.contains("Self::saturating_arithmetic_method(") {
        Some("saturating_arithmetic")
    } else if trimmed.contains("Self::is_exact_div(") {
        Some("exact_div")
    } else if trimmed.contains("Self::is_pow_method(") {
        Some("pow")
    } else if trimmed.contains("Self::euclid_method(") {
        Some("euclid")
    } else if trimmed.contains("bit_intrinsics::detect_bit_intrinsic(") {
        Some("bit_intrinsics")
    } else if trimmed.contains("float_predicates::detect_float_predicate(") {
        Some("float_predicates")
    } else if trimmed.contains("fast_math::detect_fast_math_intrinsic(") {
        Some("fast_math")
    } else if trimmed.contains("misc_intrinsics::detect_misc_intrinsic(") {
        Some("misc_intrinsics")
    } else if trimmed.contains("range_contains::detect_range_contains(") {
        Some("range_contains")
    } else if trimmed.contains("slice_contains::detect_slice_contains(") {
        Some("slice_contains")
    } else if trimmed.contains("slice_as_array::detect_slice_as_array(") {
        Some("slice_as_array")
    } else if trimmed.contains("Self::is_formatting_path(") {
        Some("formatting_path")
    } else if trimmed.contains("Self::is_range_constructor(") {
        Some("range_constructor")
    } else if trimmed.contains("Self::is_known_stdlib_unconstrained(") {
        Some("known_stdlib")
    } else if trimmed.contains("self.diagnostics.unhandled_call") {
        Some("catch_all")
    } else {
        None
    }
}

fn extend_dispatch_steps(steps: &mut Vec<String>, names: &[&str]) {
    steps.extend(names.iter().copied().map(str::to_string));
}

/// Extract inner dispatch step names from `codegen_call_primitive_cmp` in
/// `codegen_call_cmp_string/dispatch_chain.rs`.
///
/// The inner chain uses method-detection patterns rather than `try_dispatch_call_*`.
/// Each `if` block that returns early is a dispatch step. The final unguarded block
/// is the catch-all.
///
/// Part of #3575.
fn extract_inner_dispatch_steps(source: &str) -> Vec<String> {
    // Find the implementation (not the trait declaration) of codegen_call_primitive_cmp.
    // The trait declaration has `;` after the signature; the implementation has `{`.
    // Use rfind to get the last match, which is the impl body (trait decl is first).
    let fn_start = source
        .rfind("fn codegen_call_primitive_cmp(")
        .expect("codegen_call_primitive_cmp not found");
    let fn_body = &source[fn_start..];

    let mut steps = Vec::new();
    for line in fn_body.lines() {
        let trimmed = line.trim();
        if let Some(names) = helper_dispatch_steps(trimmed) {
            extend_dispatch_steps(&mut steps, names);
        } else if let Some(step) = direct_inner_dispatch_step(trimmed) {
            steps.push(step.to_string());
        }
    }
    steps
}

fn extract_tail_dispatch_steps(source: &str) -> Vec<String> {
    let fn_start =
        source.rfind("fn codegen_tail_dispatch(").expect("codegen_tail_dispatch not found");
    let fn_body = &source[fn_start..];

    let mut steps = Vec::new();
    let mut seen_catch_all = false;
    for line in fn_body.lines() {
        let trimmed = line.trim();
        if trimmed.contains("Self::is_formatting_path(") {
            steps.push("formatting_path".to_string());
        } else if trimmed.contains("Self::is_range_constructor(") {
            steps.push("range_constructor".to_string());
        } else if trimmed.contains("Self::is_known_stdlib_unconstrained(") {
            steps.push("known_stdlib".to_string());
        } else if trimmed.contains("self.diagnostics.unhandled_call") && !seen_catch_all {
            steps.push("catch_all".to_string());
            seen_catch_all = true;
        }
    }
    steps
}

/// Verify the inner dispatch chain ordering invariants in `codegen_call_primitive_cmp`.
///
/// The inner chain handles Step, comparison, arithmetic, intrinsics, formatting,
/// known stdlib, and the ultimate catch-all. Ordering invariants:
/// 1. Formatting path must come after all math/intrinsic handlers
/// 2. Known stdlib must come before the catch-all
/// 3. Catch-all must be the final step
///
/// Part of #3575.
#[test]
fn test_inner_dispatch_chain_ordering() {
    let source = include_str!("../call/codegen_call_cmp_string/dispatch_chain.rs");
    let tail_source = include_str!("../call/codegen_call_cmp_string/tail_dispatch.rs");
    let mut steps = extract_inner_dispatch_steps(source);
    steps.extend(extract_tail_dispatch_steps(tail_source));

    // Sanity: inner chain must include the extracted tail-dispatch steps.
    assert!(
        steps.len() >= 19,
        "inner dispatch chain too short ({} steps) — expected at least 19: {steps:?}",
        steps.len()
    );

    // INVARIANT 1: All math/intrinsic handlers must come before formatting_path.
    // Formatting functions on panic paths should only be blocked after all
    // real math handlers have had a chance to claim the call.
    let fmt_pos = position(&steps, "formatting_path");
    let math_handlers = [
        "wrapping_arithmetic",
        "checked_arithmetic",
        "saturating_arithmetic",
        "exact_div",
        "pow",
        "euclid",
        "bit_intrinsics",
        "float_predicates",
        "fast_math",
        "misc_intrinsics",
    ];
    for handler in &math_handlers {
        let pos = position(&steps, handler);
        assert!(
            pos < fmt_pos,
            "{handler} (pos {pos}) must come before formatting_path (pos {fmt_pos})"
        );
    }
    assert_before(&steps, "range_contains", "formatting_path");
    assert_before(&steps, "slice_contains", "formatting_path");
    assert_before(&steps, "slice_as_array", "formatting_path");
    assert_before(&steps, "slice_as_array", "known_stdlib");

    // INVARIANT 2: formatting_path must come before known_stdlib.
    // Formatting paths get error-blocked (no successor rule), which is a
    // stronger treatment than known_stdlib's unconstrained goto. If known_stdlib
    // matched first, formatting calls would get unconstrained returns instead
    // of being properly blocked.
    let known_pos = position(&steps, "known_stdlib");
    assert!(
        fmt_pos < known_pos,
        "formatting_path (pos {fmt_pos}) must come before known_stdlib (pos {known_pos})"
    );
    assert_before(&steps, "range_constructor", "known_stdlib");

    // INVARIANT 3: known_stdlib must come before the catch-all.
    // Known stdlib functions get a dedicated counter (known_stdlib_unconstrained)
    // instead of being lumped into unhandled_call + record_fallback.
    let catchall_pos = position(&steps, "catch_all");
    assert!(
        known_pos < catchall_pos,
        "known_stdlib (pos {known_pos}) must come before catch_all (pos {catchall_pos})"
    );

    // INVARIANT 4: catch_all must be the final step.
    assert_eq!(
        catchall_pos,
        steps.len() - 1,
        "catch_all must be the last inner dispatch step, found at pos {catchall_pos} of {}",
        steps.len()
    );
}

/// Verify the inner dispatch chain has no duplicate step names.
///
/// Part of #3575.
#[test]
fn test_inner_dispatch_chain_no_duplicates() {
    let source = include_str!("../call/codegen_call_cmp_string/dispatch_chain.rs");
    let tail_source = include_str!("../call/codegen_call_cmp_string/tail_dispatch.rs");
    let mut steps = extract_inner_dispatch_steps(source);
    steps.extend(extract_tail_dispatch_steps(tail_source));

    let mut seen = std::collections::HashSet::new();
    for step in &steps {
        assert!(
            seen.insert(step.as_str()),
            "duplicate inner dispatch step '{step}' in chain: {steps:?}"
        );
    }
}

fn assert_array_eq_shim_matches_leaf_imports(
    facade_source: &str,
    leaf_source: &str,
    historical_path: &str,
    facade_label: &str,
    leaf_label: &str,
) {
    if !leaf_source.contains(historical_path) {
        return;
    }

    assert!(
        facade_source.contains("mod codegen_expr_array_eq {"),
        "{facade_label} must keep the compatibility shim while {leaf_label} still imports `{historical_path}`"
    );
    assert!(
        facade_source.contains("pub(super) use super::super::codegen_expr_array_eq::{"),
        "{facade_label} shim must re-export build/recover helpers while {leaf_label} still uses `{historical_path}`"
    );
}

#[test]
fn test_call_array_eq_facade_shim_matches_leaf_imports() {
    let facade_source = include_str!("../call/mod.rs");
    let tail_dispatch_source = include_str!("../call/codegen_call_cmp_string/tail_dispatch.rs");

    assert_array_eq_shim_matches_leaf_imports(
        facade_source,
        tail_dispatch_source,
        "use super::super::super::codegen_expr_array_eq::{",
        "call/mod.rs",
        "call/codegen_call_cmp_string/tail_dispatch.rs",
    );
}

#[test]
fn test_stmt_array_eq_facade_shim_matches_leaf_imports() {
    let facade_source = include_str!("../stmt/mod.rs");
    let rvalue_source = include_str!("../stmt/codegen_stmt_rvalue.rs");

    assert_array_eq_shim_matches_leaf_imports(
        facade_source,
        rvalue_source,
        "use super::codegen_expr_array_eq::{",
        "stmt/mod.rs",
        "stmt/codegen_stmt_rvalue.rs",
    );
}

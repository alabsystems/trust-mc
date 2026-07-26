// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// Additional primitive_cmp_method edge cases (Part of #2016)
// =============================================================================

/// Test primitive_cmp_method rejects BigRational paths (not just BigInt/BigUint).
#[test]
fn test_primitive_cmp_method_rejects_bigrational() {
    assert_eq!(ChcCtx::primitive_cmp_method("num_rational::BigRational::cmp"), None);
    assert_eq!(ChcCtx::primitive_cmp_method("num_rational::BigRational::lt"), None);
}

/// Test primitive_cmp_method returns None for non-comparison method names.
#[test]
fn test_primitive_cmp_method_non_comparison() {
    assert_eq!(ChcCtx::primitive_cmp_method("std::ops::Add::add"), None);
    assert_eq!(ChcCtx::primitive_cmp_method("std::fmt::Display::fmt"), None);
    assert_eq!(ChcCtx::primitive_cmp_method("std::clone::Clone::clone"), None);
}

/// Test step_unchecked_method rejects non-Step paths even with matching suffix.
#[test]
fn test_step_unchecked_rejects_non_step_paths() {
    // Has "forward_unchecked" suffix but no "Step" in path — should return None
    assert_eq!(ChcCtx::step_unchecked_method("custom::forward_unchecked"), None);
}

/// Test step_unchecked_method rejects generic Step-like paths without the right suffix.
#[test]
fn test_step_unchecked_rejects_wrong_suffix() {
    assert_eq!(ChcCtx::step_unchecked_method("std::iter::Step::forward_checked"), None);
    assert_eq!(ChcCtx::step_unchecked_method("std::iter::Step::steps_between"), None);
}

// Deleted 9 trivial atomic counter tests:
//   test_bigint_unsound_skip_count_accessible, test_iterator_unsound_skip_count_accessible,
//   test_bigint_unsound_skip_count_increment, test_iterator_unsound_skip_count_increment,
//   test_bigint_unsound_skip_count_accessor_reflects_counter,
//   test_iterator_unsound_skip_count_accessor_reflects_counter,
//   test_coerce_eq_dropped_constraint_count_accessible,
//   test_coerce_eq_dropped_constraint_count_increment,
//   test_coerce_eq_dropped_constraint_count_accessor_reflects_counter
// Reason: #2312 — tested AtomicUsize::fetch_add (std library), not production codegen.
// Counter behavior is already covered by test_push_coerced_eq_constraint_* which
// exercises the production push_coerced_eq_constraint path end-to-end.

/// Test push_coerced_eq_constraint records dropped constraints on sort mismatch.
/// Part of #2906: reads per-ctx diagnostics instead of global atomic — no Mutex needed.
#[test]
fn test_push_coerced_eq_constraint_mismatch_increments_drop_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_push_coerce_drop(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_coerce_drop");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_push_coerce_drop", ChcConfig::default());

        // Use Int→Bool as the incompatible pair. Int→BV is now a valid
        // coercion path (int2bv, added in #2875), so it can no longer serve
        // as an incompatible test case.
        let dest_var = Expr::var("dest", Sort::bool());
        let mut constraints = Vec::new();

        let pushed = chc_ctx.push_coerced_eq_constraint(
            &mut constraints,
            &dest_var,
            Expr::int_const(7),
            &Sort::bool(),
            1,
            "test_push_coerced_eq_constraint_mismatch_increments_drop_counter",
        );

        assert!(!pushed, "incompatible Int->Bool coercion should not push constraint");
        assert!(constraints.is_empty(), "constraint list must remain empty when coercion fails");
        assert!(
            chc_ctx.diagnostics.coerce_eq_dropped_constraint.get() > 0,
            "per-ctx coerce_eq_dropped_constraint counter should increment on mismatch"
        );
    });
}

/// Test per-function drop metric records harness-local coerce_eq failures.
/// Part of #2906: reads per-ctx diagnostics instead of global map — no Mutex needed.
#[test]
fn test_push_coerced_eq_constraint_records_per_function_drop_metric() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_push_coerce_drop_by_fn(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_coerce_drop_by_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_push_coerce_drop_by_fn", ChcConfig::default());

        // Use Int→Bool as the incompatible pair. Int→BV is now a valid
        // coercion path (int2bv, added in #2875), so it can no longer serve
        // as an incompatible test case.
        let dest_var = Expr::var("dest", Sort::bool());
        let mut constraints = Vec::new();

        let pushed = chc_ctx.push_coerced_eq_constraint(
            &mut constraints,
            &dest_var,
            Expr::int_const(11),
            &Sort::bool(),
            1,
            "test_push_coerced_eq_constraint_records_per_function_drop_metric",
        );
        assert!(!pushed, "incompatible Int->Bool coercion should not push constraint");
        assert!(constraints.is_empty(), "constraint list must remain empty when coercion fails");

        // Per-ctx diagnostics track per-function drops without global state.
        let count = chc_ctx
            .diagnostics
            .coerce_dropped_by_fn
            .get("probe_push_coerce_drop_by_fn")
            .copied()
            .unwrap_or(0);
        assert!(
            count > 0,
            "per-ctx coerce_dropped_by_fn should record failed coerce_eq constraints: {:?}",
            chc_ctx.diagnostics.coerce_dropped_by_fn
        );
    });
}

/// Regression guard: call-family files must route through push_coerced_eq_constraint.
///
/// Part of #2235: direct `if let Some(eq) = Self::coerce_eq_constraint(...)` in
/// `codegen_call_*.rs` silently dropped destination constraints on mismatch.
#[test]
#[allow(clippy::panic)]
fn test_call_family_files_do_not_silently_drop_coerce_eq_constraints() {
    use std::fs;
    use std::path::Path;

    let chc_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/codegen_ay/chc");
    let call_dir = chc_dir.join("call");

    // Dynamically discover all codegen_call_*.rs files so new files are automatically checked.
    // Exclude codegen_call_coerce.rs — it implements the coerce_eq_constraint helper itself,
    // so it legitimately contains the pattern (and pushes the result to constraints).
    let mut call_family_files = Vec::new();
    for dir in [&call_dir, &chc_dir] {
        if !dir.exists() {
            continue;
        }
        for entry in
            fs::read_dir(dir).unwrap_or_else(|e| panic!("failed to read {}: {e}", dir.display()))
        {
            let entry = entry
                .unwrap_or_else(|e| panic!("failed to read dir entry in {}: {e}", dir.display()));
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if name.starts_with("codegen_call_")
                && name.ends_with(".rs")
                && name != "codegen_call_coerce.rs"
            {
                call_family_files.push(path);
            }
        }
    }

    assert!(
        call_family_files.len() >= 8,
        "expected at least 8 codegen_call_*.rs files, found {}",
        call_family_files.len()
    );

    let silent_drop_patterns =
        ["if let Some(eq) = Self::coerce_eq_constraint", "if let Some(eq) = coerce_eq_constraint"];

    for path in &call_family_files {
        let source = fs::read_to_string(path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
        for pattern in &silent_drop_patterns {
            assert!(
                !source.contains(pattern),
                "found silent coerce_eq drop pattern in {}: call handlers must use push_coerced_eq_constraint",
                path.display()
            );
        }
    }
}

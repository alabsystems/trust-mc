// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for property tracking.
//!
//! Extracted from properties/mod.rs as part of #2836.

use super::super::with_test_ay_ctx;
use super::*;
use ay_bindings::Sort;

fn smt_text(ctx: &AYCtx<'_, '_>) -> String {
    ctx.program.to_string()
}

// =========================================================================
// label_to_property_kind — all label → PropertyKind mappings
// =========================================================================

#[test]
fn test_label_to_property_kind_assertion() {
    assert_eq!(AYCtx::label_to_property_kind("kani_assert"), PropertyKind::Assertion);
}

#[test]
fn test_label_to_property_kind_assumption() {
    assert_eq!(AYCtx::label_to_property_kind("kani_assume"), PropertyKind::Assumption);
}

#[test]
fn test_label_to_property_kind_out_of_bounds() {
    assert_eq!(AYCtx::label_to_property_kind("bounds_check"), PropertyKind::OutOfBounds);
}

#[test]
fn test_label_to_property_kind_div_by_zero_variants() {
    assert_eq!(AYCtx::label_to_property_kind("div_by_zero_check"), PropertyKind::DivisionByZero);
    assert_eq!(AYCtx::label_to_property_kind("mod_by_zero_check"), PropertyKind::DivisionByZero);
    assert_eq!(AYCtx::label_to_property_kind("division_by_zero"), PropertyKind::DivisionByZero);
}

#[test]
fn test_label_to_property_kind_overflow_variants() {
    assert_eq!(AYCtx::label_to_property_kind("overflow_check"), PropertyKind::ArithmeticOverflow);
    assert_eq!(
        AYCtx::label_to_property_kind("overflow_check_neg"),
        PropertyKind::ArithmeticOverflow
    );
    // starts_with("overflow_check_") prefix match
    assert_eq!(
        AYCtx::label_to_property_kind("overflow_check_shl"),
        PropertyKind::ArithmeticOverflow
    );
}

#[test]
fn test_label_to_property_kind_null_pointer() {
    assert_eq!(AYCtx::label_to_property_kind("null_pointer_check"), PropertyKind::NullPointer);
}

#[test]
fn test_label_to_property_kind_memory_safety_variants() {
    assert_eq!(AYCtx::label_to_property_kind("alignment_check"), PropertyKind::MemorySafety);
    assert_eq!(AYCtx::label_to_property_kind("pointer_invalid"), PropertyKind::MemorySafety);
    assert_eq!(AYCtx::label_to_property_kind("dead_object"), PropertyKind::MemorySafety);
    assert_eq!(AYCtx::label_to_property_kind("use_after_free_check"), PropertyKind::MemorySafety);
    assert_eq!(AYCtx::label_to_property_kind("double_free_check"), PropertyKind::MemorySafety);
    assert_eq!(AYCtx::label_to_property_kind("dealloc_size_mismatch"), PropertyKind::MemorySafety);
}

#[test]
fn test_label_to_property_kind_shift_distance() {
    assert_eq!(
        AYCtx::label_to_property_kind("shift_distance_check"),
        PropertyKind::ArithmeticOverflow
    );
    assert_eq!(
        AYCtx::label_to_property_kind("shift_distance_check_negative"),
        PropertyKind::ArithmeticOverflow
    );
}

#[test]
fn test_label_to_property_kind_pointer_overflow() {
    assert_eq!(
        AYCtx::label_to_property_kind("offset_value_overflow"),
        PropertyKind::PointerOverflow
    );
    assert_eq!(
        AYCtx::label_to_property_kind("offset_bytes_overflow"),
        PropertyKind::PointerOverflow
    );
    assert_eq!(
        AYCtx::label_to_property_kind("offset_result_overflow"),
        PropertyKind::PointerOverflow
    );
}

#[test]
fn test_label_to_property_kind_undefined_behavior() {
    assert_eq!(AYCtx::label_to_property_kind("enum_check"), PropertyKind::UndefinedBehavior);
    assert_eq!(AYCtx::label_to_property_kind("coroutine_check"), PropertyKind::UndefinedBehavior);
}

#[test]
fn test_label_to_property_kind_unreachable() {
    assert_eq!(AYCtx::label_to_property_kind("unsupported_cfg_cycle"), PropertyKind::Unreachable);
}

#[test]
fn test_label_to_property_kind_panic() {
    assert_eq!(AYCtx::label_to_property_kind("panic"), PropertyKind::Panic);
}

#[test]
fn test_label_to_property_kind_unknown_maps_to_other() {
    assert_eq!(AYCtx::label_to_property_kind("some_unknown_label"), PropertyKind::Other);
    assert_eq!(AYCtx::label_to_property_kind(""), PropertyKind::Other);
}

// =========================================================================
// record_property_violation
// =========================================================================

#[test]
fn test_kani_assert_maps_to_assertion_kind() {
    with_test_ay_ctx(|mut ctx| {
        ctx.record_property_violation(Expr::bool_const(true), "kani_assert");
        assert_eq!(ctx.bmc_vc.violations.len(), 1);
        assert_eq!(ctx.bmc_vc.violations[0].kind, PropertyKind::Assertion);
    });
}

#[test]
fn test_record_property_violation_increments_counters() {
    with_test_ay_ctx(|mut ctx| {
        ctx.record_property_violation(Expr::bool_const(true), "bounds_check");
        ctx.record_property_violation(Expr::bool_const(false), "div_by_zero_check");
        assert_eq!(ctx.bmc_vc.violations.len(), 2);
        assert_eq!(ctx.bmc_vc.violations[0].kind, PropertyKind::OutOfBounds);
        assert_eq!(ctx.bmc_vc.violations[1].kind, PropertyKind::DivisionByZero);
    });
}

#[test]
fn test_memory_safety_checks_filter_memory_properties() {
    with_test_ay_ctx(|mut ctx| {
        ctx.config.memory_safety_checks = false;
        ctx.record_property_violation(Expr::bool_const(true), "bounds_check");
        ctx.record_property_violation(Expr::bool_const(true), "null_pointer_check");
        ctx.record_property_violation(Expr::bool_const(true), "offset_result_overflow");
        ctx.record_property_violation(Expr::bool_const(true), "kani_assert");
        assert_eq!(ctx.bmc_vc.violations.len(), 1);
        assert_eq!(ctx.bmc_vc.violations[0].kind, PropertyKind::Assertion);
    });
}

#[test]
fn test_overflow_checks_filter_arithmetic_overflow_properties() {
    with_test_ay_ctx(|mut ctx| {
        ctx.config.overflow_checks = false;
        ctx.record_property_violation(Expr::bool_const(true), "overflow_check_add");
        ctx.record_property_violation(Expr::bool_const(true), "overflow_check_neg");
        ctx.record_property_violation(Expr::bool_const(true), "div_by_zero_check");
        assert_eq!(ctx.bmc_vc.violations.len(), 1);
        assert_eq!(ctx.bmc_vc.violations[0].kind, PropertyKind::DivisionByZero);
    });
}

#[test]
fn test_record_property_violation_with_location() {
    with_test_ay_ctx(|mut ctx| {
        let loc = SourceLocation::new("test.rs", 42);
        ctx.record_property_violation_with_location(
            Expr::bool_const(true),
            "kani_assert",
            Some(loc),
        );
        assert_eq!(ctx.bmc_vc.violations.len(), 1);
        let viol = &ctx.bmc_vc.violations[0];
        assert!(viol.location.is_some(), "location should be recorded");
        assert_eq!(viol.location.as_ref().expect("location should be set").line, 42);
    });
}

// =========================================================================
// finalize_counterexample_query
// =========================================================================

#[test]
fn test_finalize_counterexample_no_violations() {
    with_test_ay_ctx(|mut ctx| {
        // With no violations, the disjunction should be just `false`
        ctx.finalize_counterexample_query();
        let smt = smt_text(&ctx);
        assert!(
            smt.contains("false"),
            "empty violation set should produce (assert false), got:\n{smt}"
        );
    });
}

#[test]
fn test_finalize_counterexample_single_violation() {
    with_test_ay_ctx(|mut ctx| {
        ctx.record_property_violation(Expr::bool_const(true), "kani_assert");
        ctx.finalize_counterexample_query();
        let smt = smt_text(&ctx);
        assert!(
            smt.contains("ay_violation_kani_assert_0"),
            "finalized query should reference the violation variable, got:\n{smt}"
        );
    });
}

#[test]
fn test_finalize_counterexample_multiple_violations_ored() {
    with_test_ay_ctx(|mut ctx| {
        ctx.record_property_violation(Expr::bool_const(true), "bounds_check");
        ctx.record_property_violation(Expr::bool_const(true), "div_by_zero_check");
        ctx.finalize_counterexample_query();
        let smt = smt_text(&ctx);
        assert!(smt.contains("ay_violation_bounds_check_0"), "should contain first violation");
        assert!(
            smt.contains("ay_violation_div_by_zero_check_1"),
            "should contain second violation"
        );
    });
}

// =========================================================================
// record_kani_any_var / add_get_value_for_kani_any
// =========================================================================

#[test]
fn test_record_kani_any_var_tracks_vars() {
    with_test_ay_ctx(|mut ctx| {
        let var1 = ctx.declare_var("x", Sort::bitvec(32));
        let var2 = ctx.declare_var("y", Sort::bitvec(8));
        ctx.record_kani_any_var(var1);
        ctx.record_kani_any_var(var2);
        // add_get_value should not panic when there are vars
        ctx.add_get_value_for_kani_any();
        let smt = smt_text(&ctx);
        assert!(smt.contains("get-value"), "should emit get-value for any vars");
    });
}

#[test]
fn test_add_get_value_for_kani_any_empty_is_noop() {
    with_test_ay_ctx(|mut ctx| {
        // No any_vars recorded
        ctx.add_get_value_for_kani_any();
        let smt = smt_text(&ctx);
        assert!(!smt.contains("get-value"), "no get-value when no any vars exist");
    });
}

// =========================================================================
// record_cover_property_with_location
// =========================================================================

#[test]
fn test_record_cover_property_returns_unique_ids() {
    with_test_ay_ctx(|mut ctx| {
        let id1 = ctx.record_cover_property_with_location(Expr::bool_const(true), None, None);
        let id2 = ctx.record_cover_property_with_location(Expr::bool_const(false), None, None);
        assert_ne!(id1, id2, "cover property IDs should be unique");
    });
}

#[test]
fn test_record_cover_property_with_location_and_message() {
    with_test_ay_ctx(|mut ctx| {
        let loc = SourceLocation::new("src/main.rs", 10);
        let _id = ctx.record_cover_property_with_location(
            Expr::bool_const(true),
            Some(loc),
            Some("reachability check".into()),
        );
        assert_eq!(ctx.cover_metadata.len(), 1);
        let meta = &ctx.cover_metadata[0];
        assert!(meta.location.is_some());
        assert_eq!(meta.location.as_ref().expect("location should be set").line, 10);
        assert_eq!(meta.message.as_deref(), Some("reachability check"));
    });
}

#[test]
fn test_add_get_value_for_covers_empty_is_noop() {
    with_test_ay_ctx(|mut ctx| {
        ctx.add_get_value_for_covers();
        let smt = smt_text(&ctx);
        assert!(!smt.contains("get-value"), "no get-value when no covers exist");
    });
}

#[test]
fn test_add_get_value_for_covers_emits_query() {
    with_test_ay_ctx(|mut ctx| {
        ctx.record_cover_property_with_location(Expr::bool_const(true), None, None);
        ctx.add_get_value_for_covers();
        let smt = smt_text(&ctx);
        assert!(smt.contains("get-value"), "should emit get-value for cover properties");
    });
}

// =========================================================================
// add_get_value_for_violations
// =========================================================================

#[test]
fn test_add_get_value_for_violations_empty_is_noop() {
    with_test_ay_ctx(|mut ctx| {
        ctx.add_get_value_for_violations();
        let smt = smt_text(&ctx);
        assert!(!smt.contains("get-value"), "no get-value when no violations exist");
    });
}

#[test]
fn test_add_get_value_for_violations_emits_query() {
    with_test_ay_ctx(|mut ctx| {
        ctx.record_property_violation(Expr::bool_const(true), "kani_assert");
        ctx.add_get_value_for_violations();
        let smt = smt_text(&ctx);
        assert!(smt.contains("get-value"), "should emit get-value for violation vars");
    });
}

// =========================================================================
// unsupported construct tracking
// =========================================================================

#[test]
fn test_unsupported_records_construct_with_location() {
    with_test_ay_ctx(|mut ctx| {
        ctx.unsupported("inline_asm", "src/lib.rs:42");
        ctx.unsupported("inline_asm", "src/lib.rs:99");
        ctx.unsupported("union_access", "src/foo.rs:10");
        assert_eq!(ctx.unsupported_constructs.len(), 2, "should have 2 distinct constructs");
        let asm_locs = ctx.unsupported_constructs.get("inline_asm").expect("inline_asm entry");
        assert_eq!(asm_locs.len(), 2, "inline_asm should have 2 locations");
    });
}

// =========================================================================
// emit_bmc preserves violation names (original test)
// =========================================================================

#[test]
fn test_emit_bmc_preserves_recorded_kani_assert_name() {
    with_test_ay_ctx(|mut ctx| {
        ctx.record_property_violation(Expr::bool_const(true), "kani_assert");
        ctx.finalize_emit_bmc();
        let (_, program) = ctx.split_emit_bmc();
        let smt = program.to_string();
        assert!(
            smt.contains("(declare-const ay_violation_kani_assert_0 Bool)"),
            "expected emit_bmc to preserve recorded violation name, got:\n{smt}"
        );
    });
}

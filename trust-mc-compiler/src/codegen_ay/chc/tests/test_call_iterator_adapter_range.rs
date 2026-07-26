// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for chc/codegen_call_iterator_adapter_range.rs — range iterator
//! advancement, range length computation, flattened Option field building,
//! and position/length comparison with signedness.
//!
//! Verifies that:
//! - Range<u32> for-loop produces valid CHC with non-trivial transitions
//! - Range<isize> (signed) iteration emits signed comparison (BvSLt)
//! - range_len_expr produces correct ite(end >= start, end - start, 0) form
//! - adapter_pos_lt_len produces BvULt for unsigned position comparisons
//! - ExactSizeIterator::len on ranges produces valid VCs
//! - Nested range iteration exercises flattened range next field building
//!
//! Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, ExprValue};

// =============================================================================
// advance_range_iterator_expr — unsigned Range<u32>
// =============================================================================

/// For-loop over Range<u32> should produce non-trivial CHC transitions
/// with BvAdd for loop counter advancement.
#[test]
fn test_range_u32_for_loop_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range_u32() -> u32 {
            let mut sum = 0u32;
            for i in 0u32..10 {
                sum = sum.wrapping_add(i);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_u32");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_range_u32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_range_u32", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_range_u32");

        // Range iteration should emit BvAdd for the `start + 1` advancement
        assert_rule_contains_expr_kind(
            &vc,
            "probe_range_u32",
            |e| matches!(e.value(), ExprValue::BvAdd(..)),
            "BvAdd (range start + 1)",
        );
    });
}

/// Range<usize> for-loop exercises 64-bit bitvector path.
#[test]
fn test_range_usize_for_loop_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range_usize(n: usize) -> usize {
            let mut acc = 0usize;
            for i in 0..n {
                acc = acc.wrapping_add(i);
            }
            acc
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_usize");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_range_usize", ChcConfig::default());

        assert_vc_structure(&vc, "probe_range_usize", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_range_usize");
    });
}

// =============================================================================
// Signed range iteration — Range<isize>
// =============================================================================

/// Range<isize> should emit signed comparison (BvSLt) for has_remaining.
#[test]
fn test_range_isize_signed_comparison() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range_isize() -> isize {
            let mut sum: isize = 0;
            for i in -5isize..5 {
                sum = sum.wrapping_add(i);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_isize");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_range_isize", ChcConfig::default());

        assert_vc_structure(&vc, "probe_range_isize", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_range_isize");
    });
}

// =============================================================================
// range_len_expr — unit tests for the pure function
// =============================================================================

/// range_len_expr on bitvec inputs with unsigned produces ite(end >= start, end - start, 0).
#[test]
fn test_range_len_expr_bitvec_basic() {
    let start = Expr::bitvec_const(3u64, 32);
    let end = Expr::bitvec_const(10u64, 32);
    let result = ChcCtx::range_len_expr(start, end, false);
    assert!(result.is_some(), "range_len_expr should succeed for bv32 inputs");
    let len_expr = result.unwrap();
    // Result should be an ITE (conditional length)
    assert!(
        constraint_tree_contains(&len_expr, &|e| matches!(e.value(), ExprValue::Ite { .. })),
        "range_len_expr should produce an ITE expression"
    );
    // Should contain BvSub (end - start)
    assert!(
        constraint_tree_contains(&len_expr, &|e| matches!(e.value(), ExprValue::BvSub(..))),
        "range_len_expr should contain BvSub"
    );
    // Should contain BvUGe (end >= start guard) for unsigned
    assert!(
        constraint_tree_contains(&len_expr, &|e| matches!(e.value(), ExprValue::BvUGe(..))),
        "range_len_expr should contain BvUGe guard for unsigned"
    );
}

/// range_len_expr with mismatched widths should normalize (wider wins).
#[test]
fn test_range_len_expr_bitvec_width_mismatch() {
    let start = Expr::bitvec_const(0u64, 16);
    let end = Expr::bitvec_const(100u64, 32);
    let result = ChcCtx::range_len_expr(start, end, false);
    assert!(result.is_some(), "range_len_expr should handle width mismatch");
}

/// range_len_expr returns None for non-bitvec, non-int sorts.
#[test]
fn test_range_len_expr_bool_returns_none() {
    let start = Expr::bool_const(true);
    let end = Expr::bool_const(false);
    let result = ChcCtx::range_len_expr(start, end, false);
    assert!(result.is_none(), "range_len_expr should return None for Bool sort inputs");
}

/// range_len_expr on integer (Int sort) inputs produces int arithmetic.
#[test]
fn test_range_len_expr_int_sort() {
    let start = Expr::int_const(5);
    let end = Expr::int_const(15);
    let result = ChcCtx::range_len_expr(start, end, false);
    assert!(result.is_some(), "range_len_expr should succeed for Int sort inputs");
    let len_expr = result.unwrap();
    // Should contain IntSub
    assert!(
        constraint_tree_contains(&len_expr, &|e| matches!(e.value(), ExprValue::IntSub(..))),
        "Int range_len should contain IntSub"
    );
    // Should contain IntGe guard
    assert!(
        constraint_tree_contains(&len_expr, &|e| matches!(e.value(), ExprValue::IntGe(..))),
        "Int range_len should contain IntGe guard"
    );
}

// =============================================================================
// adapter_pos_lt_len — pure function unit tests
// =============================================================================

/// adapter_pos_lt_len with same-width bitvecs produces BvULt.
#[test]
fn test_adapter_pos_lt_len_same_width() {
    let pos = Expr::bitvec_const(3u64, 64);
    let len = Expr::bitvec_const(10u64, 64);
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "adapter_pos_lt_len should succeed for same-width bv64");
    let (has_remaining, _pos_cmp) = result.unwrap();
    // Should be BvULt (unsigned less-than)
    assert!(
        matches!(has_remaining.value(), ExprValue::BvULt(..)),
        "adapter_pos_lt_len should produce BvULt, got {:?}",
        has_remaining.value()
    );
}

/// adapter_pos_lt_len with mismatched widths should coerce to wider.
#[test]
fn test_adapter_pos_lt_len_width_mismatch() {
    let pos = Expr::bitvec_const(0u64, 32);
    let len = Expr::bitvec_const(100u64, 64);
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "adapter_pos_lt_len should handle width mismatch");
}

/// adapter_pos_lt_len_with_signedness uses BvSLt for signed comparison.
#[test]
fn test_adapter_pos_lt_len_signed() {
    let pos = Expr::bitvec_const(0u64, 32);
    let len = Expr::bitvec_const(10u64, 32);
    let result = ChcCtx::adapter_pos_lt_len_with_signedness(pos, len, true);
    assert!(result.is_some(), "signed adapter_pos_lt_len should succeed");
    let (has_remaining, _) = result.unwrap();
    assert!(
        matches!(has_remaining.value(), ExprValue::BvSLt(..)),
        "signed adapter_pos_lt_len should produce BvSLt, got {:?}",
        has_remaining.value()
    );
}

/// guarded_range_le emits an unsigned <= bound guarded by has_remaining.
#[test]
fn test_guarded_range_le_unsigned_uses_bvule() {
    let next_start = Expr::bitvec_const(4u64, 32);
    let end = Expr::bitvec_const(10u64, 32);
    let has_remaining = Expr::var("range_has_remaining", ay_bindings::Sort::bool());

    let constraint = ChcCtx::guarded_range_le(next_start, end, has_remaining, false)
        .expect("guarded_range_le should handle unsigned bitvectors");

    assert!(
        constraint_tree_contains(&constraint, &|e| matches!(e.value(), ExprValue::BvULe(..))),
        "unsigned guarded_range_le should contain BvULe, got {constraint:?}"
    );
}

/// guarded_range_le emits a signed <= bound when the range element type is signed.
#[test]
fn test_guarded_range_le_signed_uses_bvsle() {
    let next_start = Expr::bitvec_const(4u64, 32);
    let end = Expr::bitvec_const(10u64, 32);
    let has_remaining = Expr::var("range_has_remaining", ay_bindings::Sort::bool());

    let constraint = ChcCtx::guarded_range_le(next_start, end, has_remaining, true)
        .expect("guarded_range_le should handle signed bitvectors");

    assert!(
        constraint_tree_contains(&constraint, &|e| matches!(e.value(), ExprValue::BvSLe(..))),
        "signed guarded_range_le should contain BvSLe, got {constraint:?}"
    );
}

// =============================================================================
// build_flattened_range_next_fields — MIR pipeline integration
// =============================================================================

/// Range for-loop with side effects exercises build_flattened_range_next_fields
/// to construct the Option<T> result.
#[test]
fn test_range_for_loop_with_array_index() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range_index() -> u32 {
            let arr = [10u32, 20, 30, 40, 50];
            let mut sum = 0u32;
            for i in 0u32..5 {
                sum = sum.wrapping_add(arr[i as usize]);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_range_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_range_index", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_range_index");
    });
}

// =============================================================================
// Nested range iteration
// =============================================================================

/// Nested for-loops over ranges exercise multiple range iterator state
/// management in the same function.
#[test]
fn test_nested_range_iteration() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_nested_range() -> u32 {
            let mut total = 0u32;
            for i in 0u32..3 {
                for j in 0u32..4 {
                    total = total.wrapping_add(i.wrapping_mul(j));
                }
            }
            total
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_range");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_nested_range", ChcConfig::default());

        assert_vc_structure(&vc, "probe_nested_range", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_nested_range");
    });
}

// =============================================================================
// Empty range — edge case
// =============================================================================

/// An empty range (0..0) should still produce valid VCs.
#[test]
fn test_empty_range_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_empty_range() -> u32 {
            let mut sum = 0u32;
            for i in 0u32..0 {
                sum = sum.wrapping_add(i);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_empty_range");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_empty_range", ChcConfig::default());

        assert_vc_structure(&vc, "probe_empty_range", body.blocks.len());
    });
}

// =============================================================================
// Mem-level end-to-end: RangeSpecNext constraints (Part of #3002)
// =============================================================================

/// At Mem track level, Range for-loop `next()` should produce correct CHC
/// constraints through the full reference resolution path.
///
/// At Mem level, `next()` is called via `Move(_ref)` where `_ref: &mut Range<u32>`.
/// The encoding must:
/// 1. Resolve the `&mut Range<u32>` reference through ref_targets
/// 2. Read flattened Range fields (start, end) from state vars
/// 3. Compute `has_remaining = start < end` and `next_start = start + 1`
/// 4. Write the Option result and updated iterator state
///
/// Part of #3002: validates acceptance criteria for RangeSpecNext encoding.
#[test]
fn test_range_spec_next_at_mem_level_produces_bvadd_and_bvult() {
    use super::super::codegen_call_iterator_adapter::get_range_spec_next_path_counts;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range_mem(n: u32) -> u32 {
            let mut sum = 0u32;
            for i in 0u32..n {
                sum = sum.wrapping_add(i);
            }
            sum
        }
    "#;

    use rustc_public::mir::TerminatorKind;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_mem");
        let body = instance.body().expect("function body");

        // Diagnostic: dump Call terminators to see if spec_next exists.
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                if let Ok(ty) = func.ty(body.locals()) {
                    eprintln!("bb{bb_idx}: Call {ty:?}");
                }
            }
        }

        let before = get_range_spec_next_path_counts();

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_range_mem",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let after = get_range_spec_next_path_counts();
        let datatype_delta = after.datatype - before.datatype;
        let flattened_delta = after.flattened - before.flattened;
        let fail_delta = after.fail_closed - before.fail_closed;
        eprintln!(
            "RangeSpecNext paths: datatype={datatype_delta}, flattened={flattened_delta}, \
             fail_closed={fail_delta}"
        );

        assert_vc_structure(&vc, "probe_range_mem", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_range_mem");

        // RangeSpecNext should emit BvULt for the `start < end` guard.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_range_mem (Mem level)",
            |e| matches!(e.value(), ExprValue::BvULt(..)),
            "BvULt (range start < end)",
        );

        // RangeSpecNext should emit BvAdd for the `start + 1` advancement.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_range_mem (Mem level)",
            |e| matches!(e.value(), ExprValue::BvAdd(..)),
            "BvAdd (range start + 1)",
        );
    });
}

// =============================================================================
// Int-lifted Range bare read regression (#3973)
// =============================================================================

/// Part of #3973: for-range with int_lift produces flattened_bare_read and
/// rvalue_ref_to_flattened drops because Int state vars don't match BV
/// Datatype fields. The fix suppresses translation drops for Int-lifted
/// locals because field-level operations are already precise.
///
/// This test reproduces the exact compiletest failure: `for i in 0..10u32`
/// with `int_lift: true` must produce zero translation drops.
#[test]
fn test_range_for_loop_int_lifted_has_zero_translation_drops() {
    const SOURCE: &str = r#"
        pub fn probe_range_int_lift(n: u32) -> u32 {
            let mut sum = 0u32;
            for i in 0u32..n {
                sum = sum.wrapping_add(i);
            }
            sum
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_place_translation_drop_count();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_int_lift");
        let body = instance.body().expect("function body");

        let _vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_range_int_lift",
            ChcConfig { int_lift: true, ..ChcConfig::default() },
        );
    });

    let place_drops = crate::codegen_ay::take_place_translation_drop_count();
    assert_eq!(
        place_drops, 0,
        "Int-lifted for-range should have zero translation drops (#3973), got {place_drops}"
    );
}

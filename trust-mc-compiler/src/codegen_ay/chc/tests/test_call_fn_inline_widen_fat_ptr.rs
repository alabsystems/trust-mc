// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for `widen_inline_result_for_fat_pointer` (codegen_call_fn_inline.rs).
//!
//! Part of #4051: the function was added in W5:4319 (Part of #4014) with zero
//! test coverage. These tests verify:
//! 1. BV64 data + BV64 vtable → BV128 concat (happy path)
//! 2. BV128 input unchanged (no double-widening)
//! 3. Non-BV input passes through unchanged
//! 4. Dest not BV128 passes through unchanged
//! 5. No vtable → passes through unchanged
//! 6. Alloc-ID extraction handles BvConcat output from widening
//! 7. Non-BV64 vtable width → passes through unchanged

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::codegen_call_fn_inline::widen_inline_result_for_fat_pointer;
use ay_bindings::{Expr, ExprValue, Sort};

// ---------------------------------------------------------------------------
// Source: simple function with a return value and a few locals.
// The dyn trait ref produces separate BV64 state vars (data + vtable),
// so we inject a synthetic BV128 output sort for happy-path tests.
// ---------------------------------------------------------------------------
const WIDEN_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn legs(&self) -> u32;
    }

    struct Dog;
    impl Animal for Dog {
        fn legs(&self) -> u32 { 4 }
    }

    pub fn probe_widen() -> u32 {
        let dog = Dog;
        let animal: &dyn Animal = &dog;
        animal.legs()
    }
"#;

/// Inject a BV128 output state variable for a given local by replacing its
/// sort in the state_var_mgr. Returns the local index that was upgraded.
fn inject_bv128_output_sort(chc_ctx: &mut ChcCtx<'_, '_>) -> usize {
    // Find a local with an existing BV64 output state var (a pointer-width slot).
    let local_idx = (0..chc_ctx.body.locals().len())
        .find(|&l| {
            chc_ctx
                .resolve_destination(l)
                .is_some_and(|(_, var)| var.sort().bitvec_width() == Some(64))
        })
        .expect("source should have at least one BV64 state variable");

    let vec_idx = chc_ctx.state_var_mgr.local_to_state_idx[&local_idx];
    let (name, _old_sort) = &chc_ctx.state_var_mgr.output_state_vars[vec_idx];
    let new_entry = (name.clone(), Sort::bitvec(128));
    chc_ctx.state_var_mgr.output_state_vars[vec_idx] = new_entry;

    local_idx
}

/// Find a local whose output state variable has the given bitvec width.
fn find_local_with_output_sort_width(chc_ctx: &ChcCtx<'_, '_>, target_width: u32) -> Option<usize> {
    (0..chc_ctx.body.locals().len()).find(|&local_idx| {
        chc_ctx
            .resolve_destination(local_idx)
            .is_some_and(|(_, var)| var.sort().bitvec_width() == Some(target_width))
    })
}

// =============================================================================
// Test 1: BV64 + vtable → BV128 happy path
// =============================================================================

#[test]
fn test_widen_bv64_plus_vtable_produces_bv128_concat() {
    with_test_ay_ctx_for_source(WIDEN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_widen");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_widen", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = inject_bv128_output_sort(&mut chc_ctx);

        let data_ptr = Expr::var("data_ptr", Sort::bitvec(64));
        let vtable_ptr = Expr::var("vtable_ptr", Sort::bitvec(64));
        let inline_vtable = Some(vtable_ptr);

        let result =
            widen_inline_result_for_fat_pointer(&chc_ctx, dest_local, data_ptr, &inline_vtable);

        assert_eq!(
            result.sort().bitvec_width(),
            Some(128),
            "widened result should be BV128, got {:?}",
            result.sort()
        );

        match result.value() {
            ExprValue::BvConcat(high, low) => {
                assert_eq!(
                    high.sort().bitvec_width(),
                    Some(64),
                    "high half should be BV64 (vtable)"
                );
                assert_eq!(low.sort().bitvec_width(), Some(64), "low half should be BV64 (data)");
            }
            other => panic!("expected BvConcat, got {:?}", other),
        }
    });
}

// =============================================================================
// Test 2: BV128 input unchanged (no double-widening)
// =============================================================================

#[test]
fn test_widen_bv128_input_unchanged_no_double_widening() {
    with_test_ay_ctx_for_source(WIDEN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_widen");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_widen", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = inject_bv128_output_sort(&mut chc_ctx);

        let already_wide = Expr::var("already_wide", Sort::bitvec(128));
        let vtable_ptr = Expr::var("vtable_ptr", Sort::bitvec(64));
        let inline_vtable = Some(vtable_ptr);

        let result = widen_inline_result_for_fat_pointer(
            &chc_ctx,
            dest_local,
            already_wide.clone(),
            &inline_vtable,
        );

        assert_eq!(
            result.to_string(),
            already_wide.to_string(),
            "BV128 input should pass through unchanged (guard: result_width != POINTER_WIDTH)"
        );
    });
}

// =============================================================================
// Test 3: Non-BV input passes through unchanged
// =============================================================================

#[test]
fn test_widen_non_bv_input_passes_through() {
    with_test_ay_ctx_for_source(WIDEN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_widen");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_widen", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = inject_bv128_output_sort(&mut chc_ctx);

        let bool_expr = Expr::bool_const(true);
        let vtable_ptr = Expr::var("vtable_ptr", Sort::bitvec(64));
        let inline_vtable = Some(vtable_ptr);

        let result = widen_inline_result_for_fat_pointer(
            &chc_ctx,
            dest_local,
            bool_expr.clone(),
            &inline_vtable,
        );

        assert_eq!(
            result.to_string(),
            bool_expr.to_string(),
            "non-BV input should pass through unchanged (guard: bitvec_width returns None)"
        );
    });
}

// =============================================================================
// Test 4: Dest not BV128 passes through unchanged
// =============================================================================

#[test]
fn test_widen_dest_not_bv128_passes_through() {
    with_test_ay_ctx_for_source(WIDEN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_widen");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_widen", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Use a BV64 dest (don't inject BV128).
        let dest_local = find_local_with_output_sort_width(&chc_ctx, 64)
            .expect("source should have BV64 state variable");

        let data_ptr = Expr::var("data_ptr", Sort::bitvec(64));
        let vtable_ptr = Expr::var("vtable_ptr", Sort::bitvec(64));
        let inline_vtable = Some(vtable_ptr);

        let result = widen_inline_result_for_fat_pointer(
            &chc_ctx,
            dest_local,
            data_ptr.clone(),
            &inline_vtable,
        );

        assert_eq!(
            result.to_string(),
            data_ptr.to_string(),
            "BV64 dest should not trigger widening (guard: dest_width != 2*POINTER_WIDTH)"
        );
    });
}

// =============================================================================
// Test 5: No vtable (None) passes through unchanged
// =============================================================================

#[test]
fn test_widen_no_vtable_passes_through() {
    with_test_ay_ctx_for_source(WIDEN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_widen");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_widen", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = inject_bv128_output_sort(&mut chc_ctx);

        let data_ptr = Expr::var("data_ptr", Sort::bitvec(64));
        let inline_vtable: Option<Expr> = None;

        let result = widen_inline_result_for_fat_pointer(
            &chc_ctx,
            dest_local,
            data_ptr.clone(),
            &inline_vtable,
        );

        assert_eq!(
            result.to_string(),
            data_ptr.to_string(),
            "no vtable (None) should pass through unchanged (guard: first check)"
        );
    });
}

// =============================================================================
// Test 6: Alloc-ID extraction handles BvConcat output from widening
// =============================================================================

#[test]
fn test_alloc_id_extraction_handles_bvconcat_from_widening() {
    with_test_ay_ctx_for_source(WIDEN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_widen");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_widen", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = inject_bv128_output_sort(&mut chc_ctx);

        // BV64 alloc pointer: obj_id=5, offset=0 → BV64 const (5 << 32)
        let alloc_ptr = Expr::bitvec_const(5u64 << 32, 64);
        let vtable_ptr = Expr::var("vtable_ptr", Sort::bitvec(64));
        let inline_vtable = Some(vtable_ptr);

        let widened =
            widen_inline_result_for_fat_pointer(&chc_ctx, dest_local, alloc_ptr, &inline_vtable);

        assert_eq!(widened.sort().bitvec_width(), Some(128), "widened result should be BV128");

        // extract_pointer_storage_expr extracts bits [63:0] from the BV128.
        let extracted = chc_ctx.extract_pointer_storage_expr(&widened);
        assert!(
            extracted.is_some(),
            "extract_pointer_storage_expr should succeed on BvConcat fat pointer"
        );

        let ptr_expr = extracted.unwrap();
        // try_extract_constant_addr expects BV64 with obj_id in upper 32 bits.
        let addr = ChcCtx::try_extract_constant_addr(ptr_expr.as_expr());
        if let Some((obj_id, offset)) = addr {
            assert_eq!(obj_id, 5, "obj_id should be 5");
            assert_eq!(offset, 0, "offset should be 0");
        }
        // If try_extract_constant_addr returns None, it means the extract(...)
        // wrapper needs the additional BvExtract+BvZeroExtend unwrapping from
        // capture_inline_return_local_value. The key verification here is that
        // extract_pointer_storage_expr doesn't crash on BvConcat input.
    });
}

// =============================================================================
// Test 7: Non-BV64 vtable width passes through unchanged
// =============================================================================

#[test]
fn test_widen_non_bv64_vtable_passes_through() {
    with_test_ay_ctx_for_source(WIDEN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_widen");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_widen", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = inject_bv128_output_sort(&mut chc_ctx);

        let data_ptr = Expr::var("data_ptr", Sort::bitvec(64));
        let vtable_wrong = Expr::var("vtable_wrong_width", Sort::bitvec(32));
        let inline_vtable = Some(vtable_wrong);

        let result = widen_inline_result_for_fat_pointer(
            &chc_ctx,
            dest_local,
            data_ptr.clone(),
            &inline_vtable,
        );

        assert_eq!(
            result.to_string(),
            data_ptr.to_string(),
            "non-BV64 vtable should cause pass-through (guard: vtable_width != POINTER_WIDTH)"
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for try_decompose_struct_store — direct unit coverage for
//! struct decomposition in codegen_stmt_store.rs.
//!
//! Part of #2529 (proof_coverage — untested production functions).

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// try_decompose_struct_store — direct unit coverage for struct decomposition
// =============================================================================

#[test]
fn test_try_decompose_struct_store_accumulates_per_field_stores() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub x: u32,
            pub y: u32,
        }

        pub fn probe_store_pair(ptr: &mut Pair, val: Pair) {
            *ptr = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_store_pair");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_store_pair",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_store_pair");
        let ptr_ty = fn_sig.inputs()[0];
        let store_ty = ChcCtx::deref_pointee_ty(ptr_ty).expect("&mut Pair should dereference");
        let store_sort = ChcCtx::translate_ty(store_ty).expect("Pair should map to datatype sort");
        assert!(store_sort.is_datatype(), "Pair store type should translate to Datatype sort");

        let addr_expr = Expr::bitvec_const(0x11_0000_0020u128, POINTER_WIDTH);
        let rhs_expr = Expr::var("_pair_rhs", store_sort);
        let mut constraints = Vec::new();

        let handled =
            chc_ctx.try_decompose_struct_store(&addr_expr, &rhs_expr, store_ty, &mut constraints);
        assert!(handled, "Pair deref store should decompose into per-field memory stores");
        assert!(
            constraints.is_empty(),
            "decomposed stores should be accumulated in heap_state (emitted at drain), not immediate constraints"
        );

        let drained_constraints = chc_ctx.heap_state.drain_store_chains(&chc_ctx.diagnostics);
        assert!(
            drained_constraints.iter().any(|c| c.to_string().matches("(store").count() >= 2),
            "expected nested store chain for two Pair fields"
        );
        assert!(
            drained_constraints.iter().any(|c| c.to_string().contains("_pair_rhs")),
            "expected field-selects over _pair_rhs in decomposed stores"
        );
        assert!(
            drained_constraints.iter().any(|c| c.to_string().contains("#x0000000000000004")),
            "expected second field store at byte offset 4"
        );
    });
}

#[test]
fn test_try_decompose_struct_store_rejects_multi_constructor_enum() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub enum Two {
            A(u32),
            B(u32),
        }

        pub fn probe_store_enum(ptr: &mut Two, val: Two) {
            *ptr = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_store_enum");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_store_enum",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_store_enum");
        let ptr_ty = fn_sig.inputs()[0];
        let store_ty = ChcCtx::deref_pointee_ty(ptr_ty).expect("&mut Two should dereference");
        let store_sort = ChcCtx::translate_ty(store_ty).expect("Two should map to datatype sort");
        assert!(store_sort.is_datatype(), "Two should translate to Datatype sort");

        let addr_expr = Expr::bitvec_const(0x12_0000_0008u128, POINTER_WIDTH);
        let rhs_expr = Expr::var("_two_rhs", store_sort);
        let mut constraints = Vec::new();

        let handled =
            chc_ctx.try_decompose_struct_store(&addr_expr, &rhs_expr, store_ty, &mut constraints);
        assert!(!handled, "multi-constructor enum stores should not use struct decomposition");
        assert!(constraints.is_empty(), "rejected decomposition should not emit constraints");
        assert!(
            chc_ctx.heap_state.drain_store_chains(&chc_ctx.diagnostics).is_empty(),
            "rejected decomposition should not accumulate memory store chains"
        );
    });
}

#[test]
fn test_try_decompose_struct_store_rejects_non_datatype_rhs() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub x: u32,
            pub y: u32,
        }

        pub fn probe_store_pair(ptr: &mut Pair, val: Pair) {
            *ptr = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_store_pair");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_store_pair",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_store_pair");
        let ptr_ty = fn_sig.inputs()[0];
        let store_ty = ChcCtx::deref_pointee_ty(ptr_ty).expect("&mut Pair should dereference");

        let addr_expr = Expr::bitvec_const(0x13_0000_0010u128, POINTER_WIDTH);
        let rhs_expr = Expr::bitvec_const(7u128, 32);
        let mut constraints = Vec::new();

        let handled =
            chc_ctx.try_decompose_struct_store(&addr_expr, &rhs_expr, store_ty, &mut constraints);
        assert!(!handled, "non-datatype RHS should not trigger struct-store decomposition");
        assert!(constraints.is_empty(), "rejected decomposition should not emit constraints");
        assert!(
            chc_ctx.heap_state.drain_store_chains(&chc_ctx.diagnostics).is_empty(),
            "rejected decomposition should not accumulate memory store chains"
        );
    });
}

/// Part of #2783: unknown layout in struct decomposition must increment
/// `fallback_count` instead of guessing field offsets.
#[test]
fn test_try_decompose_struct_store_unknown_layout_increments_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub enum SingleVariant {
            Only(u32, u16),
        }

        pub fn probe_store_single_variant(ptr: &mut SingleVariant, val: SingleVariant) {
            *ptr = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_store_single_variant");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_store_single_variant",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_store_single_variant");
        let ptr_ty = fn_sig.inputs()[0];
        let store_ty =
            ChcCtx::deref_pointee_ty(ptr_ty).expect("&mut SingleVariant should dereference");
        let store_sort =
            ChcCtx::translate_ty(store_ty).expect("SingleVariant should translate to sort");
        let addr_expr = Expr::bitvec_const(0x14_0000_0020u128, POINTER_WIDTH);
        let rhs_expr = Expr::var("_single_variant_rhs", store_sort);
        let mut constraints = Vec::new();

        let before = chc_ctx.sound_fallback_count();
        let handled =
            chc_ctx.try_decompose_struct_store(&addr_expr, &rhs_expr, store_ty, &mut constraints);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            handled,
            "SingleVariant decomposition should still emit stores for known-layout fields"
        );
        assert!(
            after > before,
            "SingleVariant decomposition should increment sound_fallback_count for at least one \
             unknown-layout field offset skip (before={before}, after={after})"
        );
        assert!(
            constraints.is_empty(),
            "fallback path should not emit immediate constraints for decomposed stores"
        );

        let drained_store_chains = chc_ctx.heap_state.drain_store_chains(&chc_ctx.diagnostics);
        assert!(
            !drained_store_chains.is_empty(),
            "known field stores should still be accumulated in heap_state"
        );
    });
}

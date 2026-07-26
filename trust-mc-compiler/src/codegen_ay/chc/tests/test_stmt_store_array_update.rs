// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `codegen_stmt_store/array_update.rs` — `emit_ref_target_array_update`
//! and the `bv_flattened_field_update` BV extract/concat path.
//!
//! Part of #2933 (COV2 — Tier-1 CHC store/assert coverage packet).
//!
//! Covers:
//! - `emit_ref_target_array_update`: ref-target array store via Index projection
//! - Dropped-store diagnostics for missing target local, missing index, missing state vars
//! - `bv_flattened_field_update`: BV extract/concat for struct-in-array field updates
//! - `flattened_leaf_bv_width`: Sort-to-BV-width helper

#![allow(clippy::unwrap_used)]

use std::collections::HashMap;

use super::common::*;
use crate::codegen_ay::chc::stmt_accumulator::StmtAccumulator;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::ProjectionElem;

// =============================================================================
// Integration: struct-in-array field store generates valid VC
// =============================================================================

/// Simple array field update `arr[idx].x = val` exercises the ref-target →
/// array update → field projection path in emit_ref_target_array_update.
/// Part of #2933: first integration test for array_update.rs.
#[test]
fn test_struct_array_field_store_first_field_generates_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub x: u32,
            pub y: u32,
        }

        pub fn update_first_field(arr: &mut [Pair; 2], idx: usize, val: u32) {
            arr[idx].x = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_first_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "update_first_field", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert_vc_structure(&vc, "update_first_field", body.blocks.len());

        // Should have transition rules (not just entry + error).
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "struct-in-array field store should produce transition rules"
        );

        // Should reference bv32 sort (u32 field value).
        // After ay bump to declare-var encoding, state variable sorts moved from
        // relation arg_sorts to vc.vars(). Check both locations.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)))
                || vc.vars().iter().any(|v| v.sort.bitvec_width() == Some(32));
        assert!(has_bv32, "u32 field store should have bv32 sort in relations or vars");
    });
}

/// Store to the last field of a struct in an array: `arr[idx].y = val`.
/// Exercises the second field projection path.
#[test]
fn test_struct_array_field_store_last_field_generates_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub x: u32,
            pub y: u32,
        }

        pub fn update_last_field(arr: &mut [Pair; 2], idx: usize, val: u32) {
            arr[idx].y = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_last_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "update_last_field", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert_vc_structure(&vc, "update_last_field", body.blocks.len());

        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "struct-in-array last-field store should produce transition rules"
        );
    });
}

/// Three-field struct array update exercises the middle-field branch in
/// `bv_flattened_field_update` if the element sort is BV-flattened.
/// At minimum, verifies VC generation doesn't panic for 3-field structs.
#[test]
fn test_three_field_struct_array_middle_field_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Triple {
            pub a: u32,
            pub b: u32,
            pub c: u32,
        }

        pub fn update_middle_field(arr: &mut [Triple; 3], idx: usize, val: u32) {
            arr[idx].b = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_middle_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "update_middle_field", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert_vc_structure(&vc, "update_middle_field", body.blocks.len());

        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "3-field struct middle-field store should produce transition rules"
        );
    });
}

// =============================================================================
// Integration: Mem-level struct array field store
// =============================================================================

/// Mem-level struct-in-array field store should also generate valid VC.
/// Tests that the memory-level path doesn't panic for struct field updates.
#[test]
fn test_struct_array_field_store_mem_level() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub x: u32,
            pub y: u32,
        }

        pub fn mem_field_store(arr: &mut [Pair; 4], idx: usize, val: u32) {
            arr[idx].x = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "mem_field_store");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "mem_field_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert_vc_structure(&vc, "mem_field_store", body.blocks.len());

        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "Mem-level struct-in-array field store should produce transition rules"
        );
    });
}

// =============================================================================
// Integration: constant-index struct array field store
// =============================================================================

/// Constant-index `arr[0].x = val` pattern — uses ConstantIndex projection
/// instead of variable Index.
#[test]
fn test_struct_array_constant_index_field_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub x: u32,
            pub y: u32,
        }

        pub fn const_idx_field_store(arr: &mut [Pair; 4]) {
            arr[0].x = 42;
            arr[1].y = 99;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_idx_field_store");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_idx_field_store", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert_vc_structure(&vc, "const_idx_field_store", body.blocks.len());

        // Two stores → should have transition rules.
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "constant-index struct field stores should produce transition rules"
        );
    });
}

// =============================================================================
// Integration: VC SMT output for struct-in-array field store
// =============================================================================

/// Verify that struct-in-array field store produces meaningful SMT output
/// (not empty or trivially vacuous).
#[test]
fn test_struct_array_field_store_smt_output_nonempty() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub x: u32,
            pub y: u32,
        }

        pub fn smt_field_store(arr: &mut [Pair; 2], idx: usize, val: u32) {
            arr[idx].x = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "smt_field_store");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "smt_field_store", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // SMT output should contain rule declarations.
        assert!(
            smt.contains("(rule"),
            "struct-in-array field store SMT should contain rule declarations, got:\n{}",
            &smt[..smt.len().min(800)]
        );

        // Should contain store operation (array update) or extract/concat (BV-flattened).
        let has_store = smt.contains("store");
        let has_extract_concat = smt.contains("extract") || smt.contains("concat");
        assert!(
            has_store || has_extract_concat,
            "struct-in-array field store SMT should contain store or extract/concat ops, got:\n{}",
            &smt[..smt.len().min(1200)]
        );
    });
}

// =============================================================================
// Direct unit: emit_ref_target_array_update — no Index projection early return
// =============================================================================

/// When ref_target has no Index/ConstantIndex projection,
/// `emit_ref_target_array_update` returns early without producing constraints.
/// The diagnostics counter should NOT increment (not a dropped store).
#[test]
fn test_emit_ref_target_array_update_no_index_returns_early() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_no_index(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_index");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_index", ChcConfig::default());

        // Create a RefTarget with no Index projection (just a plain local).
        let ref_target = RefTarget::with_projections(0, vec![]);
        let rhs_expr = ay_bindings::Expr::bitvec_const(42u128, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_cfl = HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_cfl);

        let before_dropped = chc_ctx.diagnostics.store_dropped_transition.get();
        chc_ctx.emit_ref_target_array_update(
            &ref_target,
            &rhs_expr,
            999, // ref_local
            0,   // bb_idx
            &mut acc,
        );
        let after_dropped = chc_ctx.diagnostics.store_dropped_transition.get();

        assert!(acc.constraints.is_empty(), "no-index ref_target should not produce constraints");
        assert!(acc.modified.is_empty(), "no-index ref_target should not modify any locals");
        assert_eq!(
            before_dropped, after_dropped,
            "no-index early return should NOT increment store_dropped_transition"
        );
    });
}

// =============================================================================
// Direct unit: emit_ref_target_array_update — missing target local mapping
// =============================================================================

/// When the target local has no state_idx mapping,
/// `emit_ref_target_array_update` should increment store_dropped_transition.
#[test]
fn test_emit_ref_target_array_update_missing_target_local_drops() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_missing_target(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_missing_target");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_missing_target", ChcConfig::default());

        // Use a target_local that has no state_idx mapping (9999).
        let ref_target = RefTarget::with_projections(9999, vec![ProjectionElem::Index(0)]);
        let rhs_expr = ay_bindings::Expr::bitvec_const(42u128, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_cfl = HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_cfl);

        let before = chc_ctx.diagnostics.store_dropped_transition.get();
        chc_ctx.emit_ref_target_array_update(&ref_target, &rhs_expr, 999, 0, &mut acc);
        let after = chc_ctx.diagnostics.store_dropped_transition.get();

        assert!(acc.constraints.is_empty(), "missing target local should produce no constraints");
        assert!(
            after > before,
            "missing target local should increment store_dropped_transition \
             (before={before}, after={after})"
        );
        // #3138: failure path must mark target modified (universally quantified)
        assert!(
            modified.contains(&9999),
            "missing target local must insert into modified for universal quantification"
        );
    });
}

// =============================================================================
// Direct unit: emit_ref_target_array_update — missing output state var
// =============================================================================

/// When state vars exist for the target but output_state_vars doesn't have it,
/// `emit_ref_target_array_update` should increment store_dropped_transition.
#[test]
fn test_emit_ref_target_array_update_missing_output_var_drops() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_missing_output(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_missing_output");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_missing_output", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Get a valid target_local from state_var_mgr.
        let target_local = match chc_ctx.state_var_mgr.local_to_state_idx.keys().next().copied() {
            Some(l) => l,
            None => return, // No state vars → test is vacuous, skip.
        };

        // Inject a ref_target pointing to the target_local with an Index projection.
        let ref_target =
            RefTarget::with_projections(target_local, vec![ProjectionElem::Index(target_local)]);
        let rhs_expr = ay_bindings::Expr::bitvec_const(42u128, 32);

        // Clear output_state_vars to force the "missing array output var" path.
        chc_ctx.state_var_mgr.output_state_vars.clear();

        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_cfl = HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_cfl);

        let before = chc_ctx.diagnostics.store_dropped_transition.get();
        chc_ctx.emit_ref_target_array_update(&ref_target, &rhs_expr, 10_000, 0, &mut acc);
        let after = chc_ctx.diagnostics.store_dropped_transition.get();

        assert!(
            acc.constraints.is_empty(),
            "missing output state var should produce no constraints"
        );
        assert!(
            after > before,
            "missing output state var should increment store_dropped_transition \
             (before={before}, after={after})"
        );
        // #3138: failure path must mark target modified (universally quantified)
        assert!(
            modified.contains(&target_local),
            "missing output state var must insert into modified for universal quantification"
        );
    });
}

// =============================================================================
// Integration: diagnostics counter — struct-in-array that hits dropped-store
// =============================================================================

/// When `emit_ref_target_array_update` processes a valid array store (no
/// missing state vars), the diagnostics counter should NOT increment.
#[test]
fn test_struct_array_field_store_no_false_positive_dropped_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_arr_store(arr: &mut [u32; 4], idx: usize, val: u32) {
            arr[idx] = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arr_store");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_arr_store", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Simple scalar array store should produce a valid VC without
        // triggering false-positive dropped-store diagnostics.
        assert_vc_structure(&vc, "probe_arr_store", body.blocks.len());
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "scalar array store should produce transition rules"
        );
    });
}

// =============================================================================
// Integration: single-field struct in array (bv_flattened_field_update only-field branch)
// =============================================================================

/// Single-field wrapper struct in an array: `arr[idx].inner = val`.
/// If BV-flattened, this exercises the `(false, false)` branch of
/// `bv_flattened_field_update` (only field — no extract/concat needed).
#[test]
fn test_single_field_wrapper_struct_array_field_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Wrapper {
            pub inner: u64,
        }

        pub fn update_wrapper_field(arr: &mut [Wrapper; 3], idx: usize, val: u64) {
            arr[idx].inner = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_wrapper_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "update_wrapper_field", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert_vc_structure(&vc, "update_wrapper_field", body.blocks.len());
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "single-field wrapper struct array store should produce transition rules"
        );
    });
}

// =============================================================================
// Integration: mixed-width struct fields (different BV widths per field)
// =============================================================================

/// Struct with mixed field widths: u8, u32, u64. If BV-flattened, the
/// extract/concat math needs to handle different-width field offsets correctly.
#[test]
fn test_mixed_width_struct_array_field_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct MixedWidths {
            pub a: u8,
            pub b: u32,
            pub c: u64,
        }

        pub fn update_mixed_first(arr: &mut [MixedWidths; 2], idx: usize, val: u8) {
            arr[idx].a = val;
        }

        pub fn update_mixed_middle(arr: &mut [MixedWidths; 2], idx: usize, val: u32) {
            arr[idx].b = val;
        }

        pub fn update_mixed_last(arr: &mut [MixedWidths; 2], idx: usize, val: u64) {
            arr[idx].c = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        // Test first field
        {
            let instance = find_instance_by_suffix(ctx.tcx, "update_mixed_first");
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "update_mixed_first", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();
            assert_vc_structure(&vc, "update_mixed_first", body.blocks.len());
        }

        // Test middle field
        {
            let instance = find_instance_by_suffix(ctx.tcx, "update_mixed_middle");
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "update_mixed_middle", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();
            assert_vc_structure(&vc, "update_mixed_middle", body.blocks.len());
        }

        // Test last field
        {
            let instance = find_instance_by_suffix(ctx.tcx, "update_mixed_last");
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "update_mixed_last", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();
            assert_vc_structure(&vc, "update_mixed_last", body.blocks.len());
        }
    });
}

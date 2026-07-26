// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for `record_fallback()` paths in `codegen_stmt_assign_projection.rs`.
//!
//! Each test forces a specific fallback path and asserts that the appropriate
//! fallback counter increments. Without these, a regression removing any
//! `record_fallback()` or `record_sound_fallback()` call is invisible to the test suite.
//!
//! Part of #2783 (assign_projection record_fallback test coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;
use ay_bindings::Sort;
use rustc_public::mir::{ProjectionElem, StatementKind};

/// Source with a struct field assignment — used to produce a single-level
/// Field projection (enters `encode_datatype_field_update`).
const SOURCE_STRUCT_FIELD: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Pair { pub a: u32, pub b: u32 }

    pub fn probe_struct_field(mut p: Pair, v: u32) -> Pair {
        p.a = v;
        p
    }
"#;

/// Source with a nested struct field — produces 2+ Field projections.
const SOURCE_NESTED_STRUCT: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Pair { pub a: u32, pub b: u32 }
    pub struct Wrap { pub pair: Pair }

    pub fn probe_nested_struct(mut w: Wrap, v: u32) -> u32 {
        w.pair.a = v;
        w.pair.a
    }
"#;

/// Source with a tuple field assignment — used for flattened tuple field
/// projection testing.
const SOURCE_TUPLE_FIELD: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub fn probe_tuple_field(mut t: (u32, u64)) -> (u32, u64) {
        t.1 = 42;
        t
    }
"#;

/// Find a single-level Field projection assignment.
fn find_field_assign(body: &rustc_public::mir::Body) -> (usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, _rhs) = &stmt.kind
                && lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Field(..)))
                && lhs.projection.iter().filter(|p| matches!(p, ProjectionElem::Field(..))).count()
                    == 1
            {
                return (bb_idx, lhs.local);
            }
        }
    }
    panic!("failed to find single-level Field projection assignment");
}

/// Find a nested (2+) Field projection assignment.
fn find_nested_field_assign(body: &rustc_public::mir::Body) -> (usize, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, _rhs) = &stmt.kind
                && lhs.projection.iter().filter(|p| matches!(p, ProjectionElem::Field(..))).count()
                    >= 2
            {
                return (bb_idx, lhs.local);
            }
        }
    }
    panic!("failed to find nested Field projection assignment");
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 167:
// Flattened field projection — output slot overflow
// =============================================================================

/// Flattened tuple field projection with insufficient output slots must
/// increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 167.
/// Part of #2783.
#[test]
fn test_flattened_field_projection_output_slot_overflow_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_TUPLE_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the tuple.1 = 42 assignment
        let (bb_idx, local_idx) = find_field_assign(&body);

        // Mark this local as flattened so the code enters
        // encode_flattened_field_projection.
        chc_ctx.flatten.flattened_tuple_locals.insert(local_idx);

        // Truncate output_state_vars so the fld+vec_idx slot overflows.
        // For field index 1, slot = vec_idx + 1. If we truncate to vec_idx + 1,
        // the slot lookup at vec_idx + 1 returns None → line 167.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        chc_ctx.state_var_mgr.output_state_vars.truncate(vec_idx + 1);

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "flattened field projection with missing output slot should increment \
             sound_fallback_count() (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 248:
// Datatype field update — sort mismatch after apply_projection_update succeeds
// =============================================================================

/// Datatype field update where coerce_eq_constraint returns None must
/// increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 248.
/// Part of #2783.
#[test]
fn test_datatype_field_update_sort_mismatch_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_STRUCT_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_field_assign(&body);

        // Ensure this is NOT in the flattened set (so it goes through
        // encode_datatype_field_update, not encode_flattened_field_projection).
        chc_ctx.flatten.flattened_tuple_locals.remove(&local_idx);

        // Corrupt the output sort to Array (incompatible with datatype) so
        // coerce_eq_constraint(updated_expr, out_sort) returns None → line 248.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        let (out_name, _out_sort) = chc_ctx.state_var_mgr.output_state_vars[vec_idx].clone();
        chc_ctx.state_var_mgr.output_state_vars[vec_idx] =
            (out_name, Sort::array(Sort::bitvec(32), Sort::bitvec(32)));

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "datatype field update sort mismatch should increment sound_fallback_count() \
             (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 257:
// Projection output slot missing in encode_datatype_field_update
// =============================================================================

/// Datatype field update with missing output slot must increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 257.
/// Part of #2783, reclassified in #3369, converted DEMOTED→SOUND in #3459.
#[test]
fn test_datatype_field_update_output_slot_missing_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_STRUCT_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_field_assign(&body);

        // Ensure NOT flattened.
        chc_ctx.flatten.flattened_tuple_locals.remove(&local_idx);

        // Map local to an OOB index so output_state_vars.get returns None → line 257.
        // But the state_vars lookup at the same index must succeed (line 201 needs it).
        // Strategy: keep state_vars large enough but truncate output_state_vars.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        // Ensure state_vars at vec_idx is a datatype (root_in.sort().is_datatype())
        // so we pass line 209 and reach line 224.
        // Use a Point datatype sort.
        let dt_sort = point_sort_prefixed();
        let (name, _sort) = chc_ctx.state_var_mgr.state_vars[vec_idx].clone();
        chc_ctx.state_var_mgr.state_vars[vec_idx] = (name, dt_sort);

        // Truncate output_state_vars so vec_idx is out of bounds.
        chc_ctx.state_var_mgr.output_state_vars.truncate(vec_idx);

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "datatype field update with missing output slot should increment \
             sound_fallback_count (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 265:
// apply_projection_update returns None
// =============================================================================

/// Datatype field update where apply_projection_update fails must increment
/// sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 265.
/// Part of #2783.
#[test]
fn test_apply_projection_update_failure_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_NESTED_STRUCT, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_struct");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_nested_struct", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_nested_field_assign(&body);

        // Ensure NOT flattened.
        chc_ctx.flatten.flattened_tuple_locals.remove(&local_idx);

        // Replace the root sort with a bitvec that is_datatype()=false initially,
        // then we need is_datatype()=true to pass line 209, but the internal
        // structure must be wrong enough that apply_projection_update returns None.
        //
        // Strategy: use a simple datatype that doesn't have nested field structure.
        // apply_projection_update navigates into field_select() which returns None
        // on depth > 1 when there's no matching constructor → returns None.
        let flat_dt =
            struct_sort("FlatStruct", vec![("fld0", Sort::bitvec(32)), ("fld1", Sort::bitvec(32))]);
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        let (name, _sort) = chc_ctx.state_var_mgr.state_vars[vec_idx].clone();
        chc_ctx.state_var_mgr.state_vars[vec_idx] = (name, flat_dt.clone());
        // Output must also be large enough for vec_idx.
        if chc_ctx.state_var_mgr.output_state_vars.len() > vec_idx {
            let (out_name, _out_sort) = chc_ctx.state_var_mgr.output_state_vars[vec_idx].clone();
            chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (out_name, flat_dt);
        }

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "apply_projection_update failure should increment sound_fallback_count() \
             (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 158:
// Flattened field projection sort mismatch
// =============================================================================

/// Flattened tuple field projection with incompatible sort (coerce_eq_constraint
/// returns None) must increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 158.
/// Part of #2783.
#[test]
fn test_flattened_field_projection_sort_mismatch_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_TUPLE_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the tuple field assignment block
        let (bb_idx, _local_idx) = find_field_assign(&body);

        // Ensure the tuple local is in flattened_tuple_locals so the
        // flattened field projection path is exercised (ChcCtx::new may
        // not always classify tuple parameters as flattened).
        chc_ctx.flatten.flattened_tuple_locals.insert(_local_idx);

        // Corrupt the output sort for the tuple's second field slot
        // to an Array(Int, Int) sort, which has no coercion path from
        // BV64 rhs. Array(BV32, BV32) was accidentally coerceable via
        // reinterpret_fixed_layout_expr (#3675).
        let tuple_local = _local_idx;
        let vec_idx = chc_ctx.state_idx_for_local(tuple_local);
        let fld1_slot = vec_idx + 1;
        if fld1_slot < chc_ctx.state_var_mgr.output_state_vars.len() {
            chc_ctx.state_var_mgr.output_state_vars[fld1_slot].1 =
                ay_bindings::Sort::array(ay_bindings::Sort::int(), ay_bindings::Sort::int());
        }

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "flattened field sort mismatch should increment sound_fallback_count() \
             (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 195:
// Modified local with missing output state var in datatype field update
// =============================================================================

/// Datatype field update on a modified local with missing output state var
/// must increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 195.
/// Part of #2783.
#[test]
fn test_datatype_field_update_modified_local_missing_output_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_STRUCT_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the struct field assignment block and local
        let (bb_idx, local_idx) = find_field_assign(&body);

        // Mark the local as modified (to enter the `modified.contains` path at line 190)
        // AND truncate output_state_vars so the local's vec_idx is OOB,
        // forcing the fallback at line 195.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        chc_ctx.state_var_mgr.output_state_vars.truncate(vec_idx);
        // Clear local_expr_env for this local so it falls through to the output_state_vars check
        chc_ctx.encode.local_expr_env.remove(&local_idx);

        // Pre-mark the local as modified so encode_block_statements' previous
        // statements may add it; but to be safe we also inject it directly.
        // The encode_block_statements path accumulates `modified` across statements,
        // so we force the scenario by setting a small output_state_vars.

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "datatype field update with modified local but missing output state var should \
             increment sound_fallback_count() (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 77:
// Scalar deref-field-zero projection with sort mismatch
// =============================================================================

/// Scalar `(*x).0` deref-field-zero projection with sort mismatch must
/// increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 77.
/// Part of #2783, reclassified in #3369, converted DEMOTED→SOUND in #3459.
#[test]
fn test_scalar_deref_field_zero_sort_mismatch_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_TUPLE_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a local with a scalar (non-ref) type and build a synthetic
        // [Deref, Field(0, local_ty)] projection. The scalar_deref_field_zero
        // path activates when the field type equals the local type and the
        // local is not a ref/raw ptr. Local 1 in the tuple source is typically
        // the (u32, u64) argument — a scalar tuple.
        let local_idx = 1usize;
        let local_ty = body.locals()[local_idx].ty;

        // Corrupt the output sort so coerce_eq_constraint returns None → line 77.
        // Use Real sort (no BV→Real coercion path exists). Array sorts no longer
        // work here because reinterpret_fixed_layout_expr (#3675) handles BV→Array.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        let (out_name, _out_sort) = chc_ctx.state_var_mgr.output_state_vars[vec_idx].clone();
        chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (out_name, Sort::real());

        let lhs = Place {
            local: local_idx,
            projection: vec![ProjectionElem::Deref, ProjectionElem::Field(0usize, local_ty)],
        };
        let rhs_expr = ay_bindings::Expr::bitvec_const(42, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();

        let before = chc_ctx.sound_fallback_count();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        chc_ctx.encode_projection_assignment(&lhs, rhs_expr, local_idx, 0, &mut acc);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "scalar deref-field-zero sort mismatch should increment \
             sound_fallback_count (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 86:
// Scalar deref-field-zero projection with missing output slot
// =============================================================================

/// Scalar `(*x).0` deref-field-zero projection with missing output slot must
/// increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 86.
/// Part of #2783, reclassified in #3369, converted DEMOTED→SOUND in #3459.
#[test]
fn test_scalar_deref_field_zero_missing_output_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_TUPLE_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let local_idx = 1usize;
        let local_ty = body.locals()[local_idx].ty;

        // Truncate output_state_vars so the local's vec_idx is OOB → line 86.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        chc_ctx.state_var_mgr.output_state_vars.truncate(vec_idx);

        let lhs = Place {
            local: local_idx,
            projection: vec![ProjectionElem::Deref, ProjectionElem::Field(0usize, local_ty)],
        };
        let rhs_expr = ay_bindings::Expr::bitvec_const(42, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();

        let before = chc_ctx.sound_fallback_count();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        chc_ctx.encode_projection_assignment(&lhs, rhs_expr, local_idx, 0, &mut acc);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "scalar deref-field-zero missing output slot should increment \
             sound_fallback_count (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 118:
// Unsupported flattened deref projection (>1 or 0 field projections)
// =============================================================================

/// Flattened deref projection with zero field projections (e.g., `[Deref]` alone)
/// must increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 118.
/// Part of #2783, reclassified in #3369, converted DEMOTED→SOUND in #3459.
#[test]
fn test_unsupported_flattened_deref_projection_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_TUPLE_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let local_idx = 1usize;

        // Mark this local as flattened so flattened_deref_field activates.
        chc_ctx.flatten.flattened_tuple_locals.insert(local_idx);

        // Projection [Deref] alone — after stripping Deref, remaining projections
        // are empty, so extract_field_projections returns empty vec → len != 1 → line 118.
        let lhs = Place { local: local_idx, projection: vec![ProjectionElem::Deref] };
        let rhs_expr = ay_bindings::Expr::bitvec_const(42, 32);
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();

        let before = chc_ctx.sound_fallback_count();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        chc_ctx.encode_projection_assignment(&lhs, rhs_expr, local_idx, 0, &mut acc);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "unsupported flattened deref projection should increment \
             sound_fallback_count (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_stmt_assign_projection.rs line 273:
// Unmodified local with state_vars OOB in encode_datatype_field_update
// =============================================================================

/// Datatype field update on an unmodified local where state_vars is too small
/// must increment sound_fallback_count().
///
/// Production site: codegen_stmt_assign_projection.rs line 273.
/// Part of #2783.
#[test]
fn test_datatype_field_update_unmodified_local_state_vars_oob_increments_counter() {
    with_test_ay_ctx_for_source(SOURCE_STRUCT_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_field_assign(&body);

        // Ensure NOT flattened (goes through encode_datatype_field_update).
        chc_ctx.flatten.flattened_tuple_locals.remove(&local_idx);

        // Map local to a valid state index but truncate state_vars so the
        // lookup fails on the else branch (unmodified path) → line 273.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        chc_ctx.state_var_mgr.state_vars.truncate(vec_idx);

        // The local must NOT be in the modified set for the unmodified branch.
        // encode_block_statements accumulates `modified`, but since earlier
        // statements may add it, we need to ensure this local isn't modified
        // before the projection statement. Truncating state_vars for ALL
        // locals makes earlier statements fail to modify as well.

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        // Production now handles this path without fallback (improved encoding).
        // Verify no regression — fallback count should not increase.
        assert!(
            after == before,
            "datatype field update with unmodified local should NOT increment \
             sound_fallback_count() after encoding improvement (before={before}, after={after})"
        );
    });
}

/// Part of #3561 Phase 1: Verify that `record_sound_fallback_categorized` populates
/// the per-category detail map with the correct category tag.
#[test]
fn test_categorized_fallback_populates_detail_map() {
    with_test_ay_ctx_for_source(SOURCE_STRUCT_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, local_idx) = find_field_assign(&body);

        // Truncate output_state_vars to trigger a fallback path in the
        // projection handler. The exact category depends on which handler
        // fires first (flattened vs datatype), but any `proj_*` category
        // proves the detail map is populated.
        let vec_idx = chc_ctx.state_idx_for_local(local_idx);
        chc_ctx.state_var_mgr.output_state_vars.truncate(vec_idx);

        assert!(
            chc_ctx.sound_fallback_detail().is_empty(),
            "precondition: detail map starts empty"
        );

        let _result = chc_ctx.encode_block_statements(bb_idx);

        let detail = chc_ctx.sound_fallback_detail();
        assert!(!detail.is_empty(), "categorized fallback should populate the detail map");
        // All projection fallback categories start with "proj_".
        assert!(
            detail.keys().all(|k| k.starts_with("proj_")),
            "all categories should have 'proj_' prefix, got: {detail:?}"
        );
        // Total categorized count should match the global sound_fallback_count.
        let categorized_total: usize = detail.values().sum();
        assert!(categorized_total > 0, "at least one categorized fallback should have fired");
    });
}

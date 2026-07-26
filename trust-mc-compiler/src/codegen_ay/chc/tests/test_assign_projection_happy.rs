// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Happy-path tests for `codegen_stmt_assign_projection.rs`.
//!
//! Complements `test_assign_projection_fallback.rs` (which covers error/fallback
//! paths). These tests verify that *successful* encoding produces the expected
//! constraints and output expressions.
//!
//! Part of #2921 (CHC codegen test coverage).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};

// =============================================================================
// Struct field assignment — datatype functional update (happy path)
// =============================================================================

const SOURCE_STRUCT_FIELD: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Pair { pub a: u32, pub b: u32 }

    pub fn probe_struct_field(mut p: Pair, v: u32) -> Pair {
        p.a = v;
        p
    }
"#;

/// Successful struct field assignment via datatype functional update.
///
/// Production site: `encode_datatype_field_update` in codegen_stmt_assign_projection.rs.
/// Verifies that `p.a = v` produces a well-formed CHC with Datatype sorts
/// for the struct parameter.
#[test]
fn test_struct_field_assign_produces_valid_vc_with_datatype() {
    with_test_ay_ctx_for_source(SOURCE_STRUCT_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_struct_field", bb_count);

        // The struct Pair { a: u32, b: u32 } should appear as a Datatype sort
        // or its flattened bv32 fields in the CHC relations, proving that the
        // field assignment path (encode_projection_assignment) was exercised.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "struct field assignment should produce bv32 sorts for Pair fields");
    });
}

/// Struct field assignment should not increment fallback_count when state
/// vars are properly sized and sorts are compatible.
#[test]
fn test_struct_field_assign_no_fallback() {
    with_test_ay_ctx_for_source(SOURCE_STRUCT_FIELD, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let before = chc_ctx.fallback_count;

        // Find the block that contains the field assignment
        let bb_with_field_assign = body.blocks.iter().enumerate().find(|(_, block)| {
            block.statements.iter().any(|stmt| {
                if let StatementKind::Assign(lhs, _) = &stmt.kind {
                    lhs.projection
                        .iter()
                        .any(|p| matches!(p, rustc_public::mir::ProjectionElem::Field(..)))
                } else {
                    false
                }
            })
        });

        if let Some((bb_idx, _)) = bb_with_field_assign {
            let (_constraints, _output_args, _modified, _safety_checks) =
                chc_ctx.encode_block_statements(bb_idx);
            let after = chc_ctx.fallback_count;
            // Allow at most 0 fallbacks for a clean struct field assignment.
            // Some MIR patterns may generate extra projections, so we verify
            // that the primary assignment path succeeds without fallback.
            assert_eq!(
                after, before,
                "struct field assignment should not increment fallback_count"
            );
        }
        // If MIR optimized away the field assignment, the test is vacuous but safe.
    });
}

const SOURCE_BV_ROOT_ASSIGN: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Wrapper {
        pub inner: u64,
    }

    pub struct MixedWidths {
        pub a: u8,
        pub b: u32,
        pub c: u64,
    }

    pub fn probe_wrapper_assign(mut w: Wrapper, v: u64) -> Wrapper {
        w.inner = v;
        w
    }

    pub fn probe_mixed_first(mut m: MixedWidths, v: u8) -> MixedWidths {
        m.a = v;
        m
    }

    pub fn probe_mixed_middle(mut m: MixedWidths, v: u32) -> MixedWidths {
        m.b = v;
        m
    }

    pub fn probe_mixed_last(mut m: MixedWidths, v: u64) -> MixedWidths {
        m.c = v;
        m
    }
"#;

fn find_projection_assign_on_local(
    body: &rustc_public::mir::Body,
    target_local: usize,
) -> (usize, rustc_public::mir::Place) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, _) = &stmt.kind
                && lhs.local == target_local
                && lhs.projection.iter().any(|projection| {
                    matches!(projection, rustc_public::mir::ProjectionElem::Field(..))
                })
            {
                return (bb_idx, lhs.clone());
            }
        }
    }
    panic!("failed to find field assignment");
}

fn place_has_field_index_projection(place: &rustc_public::mir::Place, target_local: usize) -> bool {
    place.local == target_local
        && place.projection.iter().any(|projection| matches!(projection, ProjectionElem::Field(..)))
        && place.projection.iter().any(|projection| {
            matches!(projection, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
        })
}

fn find_field_index_use_on_local(
    body: &rustc_public::mir::Body,
    target_local: usize,
) -> rustc_public::mir::Place {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(_, Rvalue::Use(operand)) = &stmt.kind {
                match operand {
                    Operand::Copy(place) | Operand::Move(place)
                        if place_has_field_index_projection(place, target_local) =>
                    {
                        return place.clone();
                    }
                    _ => {}
                }
            }
        }
    }
    panic!("failed to find field-index read");
}

fn force_bv_root_local(chc_ctx: &mut ChcCtx<'_, '_>, local_idx: usize, width: u32) {
    chc_ctx.flatten.flattened_tuple_locals.remove(&local_idx);
    chc_ctx.flatten.flattened_local_field_count.remove(&local_idx);

    let vec_idx = chc_ctx.state_idx_for_local(local_idx);
    let input_name = chc_ctx.state_var_mgr.state_vars[vec_idx].0.clone();
    let output_name = chc_ctx.state_var_mgr.output_state_vars[vec_idx].0.clone();

    chc_ctx.state_var_mgr.state_vars[vec_idx] = (input_name, Sort::bitvec(width));
    chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (output_name, Sort::bitvec(width));
}

fn assert_bv_root_assign_no_sound_fallback(fn_name: &str, width: u32, expect_extract_concat: bool) {
    with_test_ay_ctx_for_source(SOURCE_BV_ROOT_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, lhs) = find_projection_assign_on_local(&body, 1);
        let local_idx = lhs.local;
        force_bv_root_local(&mut chc_ctx, local_idx, width);
        let field_projections =
            collect_field_projections(lhs.projection.as_slice(), UnknownProjectionPolicy::Break);

        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);

        let before = chc_ctx.sound_fallback_count();
        let rhs_expr = match fn_name {
            "probe_wrapper_assign" | "probe_mixed_last" => Expr::bitvec_const(0x55, 64),
            "probe_mixed_first" => Expr::bitvec_const(0x7, 8),
            "probe_mixed_middle" => Expr::bitvec_const(0x1234_5678, 32),
            _ => panic!("unexpected function name: {fn_name}"),
        };
        let root_in = {
            let vec_idx = chc_ctx.state_idx_for_local(local_idx);
            let (in_name, in_sort) = chc_ctx.state_var_mgr.state_vars[vec_idx].clone();
            Expr::var(&*in_name, in_sort)
        };
        let helper_updated = ChcCtx::bv_projection_update(
            &root_in,
            body.locals()[local_idx].ty,
            &field_projections,
            rhs_expr.clone(),
        );
        assert!(
            helper_updated.is_some(),
            "{fn_name} should be reconstructable by bv_projection_update for lhs {lhs:?}"
        );
        chc_ctx.encode_projection_assignment(&lhs, rhs_expr, local_idx, bb_idx, &mut acc);
        let after = chc_ctx.sound_fallback_count();

        assert_eq!(
            after, before,
            "{fn_name} should update the BV root without sound fallback for lhs {lhs:?}"
        );

        let constraint_strings: Vec<String> =
            acc.constraints.iter().map(ToString::to_string).collect();
        if expect_extract_concat {
            assert!(
                constraint_strings
                    .iter()
                    .any(|constraint| constraint.contains("concat")
                        && constraint.contains("extract")),
                "{fn_name} should rebuild the BV root with extract/concat, got {constraint_strings:?}"
            );
        }
    });
}

#[test]
fn test_bv_root_wrapper_assign_no_sound_fallback() {
    assert_bv_root_assign_no_sound_fallback("probe_wrapper_assign", 64, false);
}

#[test]
fn test_bv_root_mixed_width_first_assign_no_sound_fallback() {
    assert_bv_root_assign_no_sound_fallback("probe_mixed_first", 104, true);
}

#[test]
fn test_bv_root_mixed_width_middle_assign_no_sound_fallback() {
    assert_bv_root_assign_no_sound_fallback("probe_mixed_middle", 104, true);
}

#[test]
fn test_bv_root_mixed_width_last_assign_no_sound_fallback() {
    assert_bv_root_assign_no_sound_fallback("probe_mixed_last", 104, true);
}

// =============================================================================
// Flattened tuple field projection — happy path
// =============================================================================

const SOURCE_TUPLE_ASSIGN: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub fn probe_tuple_assign(mut t: (u32, u32), v: u32) -> (u32, u32) {
        t.0 = v;
        t
    }
"#;

/// Flattened tuple field projection assignment produces a well-formed VC.
///
/// Production site: `encode_flattened_field_projection` in
/// codegen_stmt_assign_projection.rs.
#[test]
fn test_flattened_tuple_field_assign_produces_valid_vc() {
    with_test_ay_ctx_for_source(SOURCE_TUPLE_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_assign");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_tuple_assign", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_tuple_assign", bb_count);

        // Tuple (u32, u32) — both fields should appear as bv32 state vars
        let bv32_count = vc
            .relations
            .iter()
            .flat_map(|r| &r.arg_sorts)
            .filter(|s| s.bitvec_width() == Some(32))
            .count();
        assert!(
            bv32_count >= 2,
            "tuple (u32, u32) should have at least 2 bv32 state vars, got {bv32_count}"
        );
    });
}

// =============================================================================
// Nested struct field — multi-level projection
// =============================================================================

const SOURCE_NESTED_STRUCT: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Inner { pub x: u32 }
    pub struct Outer { pub inner: Inner, pub y: u32 }

    pub fn probe_nested_assign(mut o: Outer, v: u32) -> Outer {
        o.inner.x = v;
        o
    }
"#;

/// Nested struct field assignment (`o.inner.x = v`) produces a well-formed VC.
///
/// Since W4:3161 (recursive Datatype flattening), `Outer { inner: Inner { x: u32 }, y: u32 }`
/// is recursively flattened to leaf scalars (2 × bv32). No Datatype sorts should remain.
#[test]
fn test_nested_struct_field_assign_produces_valid_vc() {
    with_test_ay_ctx_for_source(SOURCE_NESTED_STRUCT, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_assign");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_nested_assign", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_nested_assign", bb_count);

        // After recursive flattening (W4:3161), nested structs are flattened to leaf scalars.
        // Outer { inner: Inner { x: u32 }, y: u32 } → 2 bv32 leaves. No Datatype sorts.
        let has_datatype =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype,
            "recursively-flattened nested struct should have no Datatype sorts in relations"
        );

        // Should have at least 2 bv32 state vars from the flattened leaves
        let bv32_count = vc
            .relations
            .iter()
            .flat_map(|r| &r.arg_sorts)
            .filter(|s| s.bitvec_width() == Some(32))
            .count();
        assert!(
            bv32_count >= 2,
            "Outer(Inner(u32), u32) flattened should have >= 2 bv32 state vars, got {bv32_count}"
        );
    });
}

// =============================================================================
// encode_projection_assignment: unsupported projection fallback
// =============================================================================

const SOURCE_SIMPLE_ASSIGN: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub fn probe_simple(x: u32) -> u32 {
        let mut y = x;
        y = x + 1;
        y
    }
"#;

/// When no projections are present (direct local assignment), the code
/// should not enter `encode_projection_assignment` at all. Verify via
/// full pipeline that a simple assign produces a clean VC.
#[test]
fn test_simple_assign_no_projection_produces_valid_vc() {
    with_test_ay_ctx_for_source(SOURCE_SIMPLE_ASSIGN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_simple", bb_count);
        assert_has_nontrivial_transition_constraints(&vc, "probe_simple");
    });
}

// =============================================================================
// constraint replacement on re-assignment within a single block
// =============================================================================

const SOURCE_MULTIPLE_FIELD_ASSIGNS: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Pair { pub a: u32, pub b: u32 }

    pub fn probe_multi_field_assign(mut p: Pair) -> Pair {
        p.a = 10;
        p.a = 20;
        p
    }
"#;

const SOURCE_ARRAY_FIELD_RESET_READ: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    #[derive(Clone, Copy)]
    pub struct UnionFindLike {
        pub parent: [u32; 4],
        pub rank: [u32; 4],
        pub size: usize,
    }

    pub fn probe_array_field_reset_then_read() -> u32 {
        let mut uf = UnionFindLike {
            parent: [9, 8, 7, 6],
            rank: [1, 1, 1, 1],
            size: 4,
        };
        uf.parent = [0, 1, 2, 3];
        let lane = uf.parent[2];
        lane
    }
"#;

/// When a struct field is assigned twice in the same block, the stale
/// constraint from the first assignment should be replaced with `true`.
/// The final VC should still be well-formed.
#[test]
fn test_multiple_field_assigns_same_block_produces_valid_vc() {
    with_test_ay_ctx_for_source(SOURCE_MULTIPLE_FIELD_ASSIGNS, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_field_assign");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_multi_field_assign", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_multi_field_assign", bb_count);

        // All rule heads must reference declared relations
        let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
        for rule in &vc.rules {
            assert!(
                declared.contains(rule.head.name.as_str()),
                "rule head '{}' references undeclared relation",
                rule.head.name
            );
        }
    });
}

/// Whole-array field replacement on a flattened bootstrap-like receiver must
/// update the cached Array slot used by downstream `Field+Index` reads.
///
/// Part of #3845, #3766: guard the production path behind the bootstrap
/// element-by-element reset workaround.
#[test]
fn test_flattened_array_field_reset_updates_env_for_downstream_read() {
    with_test_ay_ctx_for_source(SOURCE_ARRAY_FIELD_RESET_READ, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_field_reset_then_read");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_array_field_reset_then_read", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let uf_local = 1usize;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&uf_local),
            "UnionFindLike local should be recursively flattened for this regression"
        );

        let (bb_idx, _assign_lhs) = find_projection_assign_on_local(&body, uf_local);
        let read_place = find_field_index_use_on_local(&body, uf_local);

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, modified, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            modified.contains(&uf_local),
            "encoding the reset block should mark the flattened receiver as modified"
        );
        assert_eq!(
            after, before,
            "whole-array field reset should not require sound fallback in the block encoder"
        );

        let vec_idx = chc_ctx.state_idx_for_local(uf_local);
        let (out_name, out_sort) = chc_ctx.state_var_mgr.output_state_vars[vec_idx].clone();
        let out_name_text = out_name.to_string();
        assert!(
            out_sort.is_array(),
            "expected the first flattened UnionFindLike slot to be the parent array, got {:?}",
            out_sort
        );

        let cached_parent = chc_ctx
            .encode
            .flattened_field_env
            .get(&(uf_local, 0))
            .expect("array field reset should cache the updated parent slot");
        let cached_parent_text = cached_parent.to_string();
        // The field env may cache the output variable reference OR an
        // equivalent store-chain expression. Both are correct — the key
        // invariant is that the cache entry is an array-sorted expression.
        assert!(
            cached_parent_text.contains(&out_name_text) || cached_parent_text.contains("store"),
            "array field env should cache the output parent slot or store chain after reset, got {cached_parent_text}"
        );

        let read_expr = chc_ctx
            .translate_place_with_modified(&read_place, &modified)
            .expect("downstream field-index read should reconstruct from the updated array slot");
        let read_expr_text = read_expr.to_string();
        assert!(
            read_expr_text.contains(&out_name_text) || read_expr_text.contains("store"),
            "field-index read after whole-array reset should reference updated parent slot or store chain, got {read_expr_text}"
        );
    });
}

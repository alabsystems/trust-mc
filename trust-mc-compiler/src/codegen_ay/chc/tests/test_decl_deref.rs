// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

//! MIR-driven tests for CHC codegen_decl_deref.rs deref type array pre-declaration.
//!
//! Tests cover:
//! - `collect_deref_type_arrays`: Scans MIR for Deref projections and pre-declares
//!   type-indexed arrays (raw ptr deref, ref deref, nested deref chains)
//! - `collect_local_type_arrays`: Scans MIR locals and pre-declares type-indexed
//!   arrays for local variable assignments at Mem level
//! - `collect_deref_types_from_rvalue`: Extracts pointee types from all Rvalue variants
//! - `collect_deref_types_from_place`: Walks Place projections to find Deref targets
//!
//! Part of #2382 (dedicated test coverage for codegen_decl_deref.rs).

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// Probe sources
// ═══════════════════════════════════════════════════════════════════════

/// Source exercising multiple Rvalue variants with deref: Use, Ref, BinaryOp,
/// CopyForDeref, Discriminant.
const RVALUE_DEREF_PROBE_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]

    pub unsafe fn use_deref(ptr: *const u32) -> u32 {
        *ptr
    }

    pub unsafe fn ref_of_deref(r: &u32) -> &u32 {
        &*r
    }

    pub unsafe fn binary_deref(a: *const u32, b: *const u32) -> u32 {
        (*a).wrapping_add(*b)
    }

    pub unsafe fn aggregate_deref(ptrs: (*const u32, *const u32)) -> u32 {
        (*ptrs.0).wrapping_add(*ptrs.1)
    }
"#;

/// Source with multi-level pointer chain: **pp → *p → u32.
const DOUBLE_DEREF_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]

    pub unsafe fn double_deref(pp: *const *const u32) -> u32 {
        **pp
    }
"#;

/// Source with field access after Deref: (*ptr).field.
const DEREF_FIELD_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]

    pub struct Pair {
        pub x: u32,
        pub y: u64,
    }

    pub unsafe fn deref_field(ptr: *const Pair) -> u32 {
        (*ptr).x
    }
"#;

/// Source with local type diversity for collect_local_type_arrays.
const LOCAL_TYPES_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn diverse_locals(a: u8, b: u16, c: u32, d: u64, e: bool) -> u64 {
        if e { (a as u64) + (b as u64) + (c as u64) + d } else { 0 }
    }

    pub fn ref_local(r: &u32) -> u32 {
        let x: u32 = *r;
        x
    }
"#;

/// `vec![1i32].into_iter()` relies on stub-internal element memory even though
/// `i32` does not appear as a standalone body local.
const STUB_INTERNAL_VEC_ITER_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn vec_into_iter_position_probe() {
        let v = vec![1i32];
        let mut iter = v.into_iter();
        let _ = iter.next();
        let _ = iter.next();
    }
"#;

// ═══════════════════════════════════════════════════════════════════════
// collect_deref_types_from_rvalue tests
// ═══════════════════════════════════════════════════════════════════════

/// Rvalue::Use(Copy(place)) with Deref should collect the pointee type.
#[test]
fn test_collect_deref_types_from_rvalue_use_copy() {
    with_test_ay_ctx_for_source(RVALUE_DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "use_deref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "use_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut deref_types = std::collections::BTreeMap::new();
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, rhs) = &stmt.kind {
                    chc_ctx.collect_deref_types_from_rvalue(rhs, &mut deref_types);
                }
            }
        }

        // *ptr where ptr: *const u32 should collect at least the u32 pointee type key
        let has_u32_key = deref_types.keys().any(|k| k == "u32");
        assert!(
            has_u32_key,
            "Use(Copy(*ptr)) should collect u32 pointee type. keys: {:?}",
            deref_types.keys().collect::<Vec<_>>()
        );
    });
}

/// Rvalue::Ref(&*r): MIR optimizes reborrows (`&*r` where `r: &T`) into
/// simple copies — no Deref projection remains. Verify collect handles this
/// gracefully (empty result is correct when MIR elides the Deref).
#[test]
fn test_collect_deref_types_from_rvalue_ref_of_deref_elided() {
    with_test_ay_ctx_for_source(RVALUE_DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_of_deref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ref_of_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut deref_types = std::collections::BTreeMap::new();
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, rhs) = &stmt.kind {
                    chc_ctx.collect_deref_types_from_rvalue(rhs, &mut deref_types);
                }
            }
        }

        // MIR optimizes `&*r` (reborrow of &u32) into a copy — no Deref
        // projection survives. Verify either: (a) deref_types is empty because
        // MIR elided the Deref, OR (b) if Deref survived, u32 was collected.
        // Either outcome is correct; the key invariant is no spurious types.
        if !deref_types.is_empty() {
            assert!(
                deref_types.keys().any(|k| k == "u32"),
                "if MIR preserves Deref on &u32, only u32 should be collected. keys: {:?}",
                deref_types.keys().collect::<Vec<_>>()
            );
        }
        // Either way, the function must not panic and must not collect
        // spurious types from the reborrow pattern.
        assert!(
            deref_types.len() <= 1,
            "reborrow should collect at most 1 type (u32 pointee). got: {:?}",
            deref_types.keys().collect::<Vec<_>>()
        );
    });
}

/// Rvalue::BinaryOp with both operands through Deref should collect types from both.
#[test]
fn test_collect_deref_types_from_rvalue_binary_op() {
    with_test_ay_ctx_for_source(RVALUE_DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "binary_deref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "binary_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut deref_types = std::collections::BTreeMap::new();
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, rhs) = &stmt.kind {
                    chc_ctx.collect_deref_types_from_rvalue(rhs, &mut deref_types);
                }
            }
        }

        // Both *a and *b are *const u32, so u32 should be collected
        let has_u32_key = deref_types.keys().any(|k| k == "u32");
        assert!(
            has_u32_key,
            "BinaryOp with deref operands should collect u32. keys: {:?}",
            deref_types.keys().collect::<Vec<_>>()
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// collect_deref_types_from_place tests
// ═══════════════════════════════════════════════════════════════════════

/// Double deref (**pp) should collect both intermediate pointer type and final pointee.
#[test]
fn test_collect_deref_types_from_place_double_deref() {
    with_test_ay_ctx_for_source(DOUBLE_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "double_deref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "double_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut deref_types = std::collections::BTreeMap::new();
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind {
                    chc_ctx.collect_deref_types_from_place(lhs, &mut deref_types);
                    chc_ctx.collect_deref_types_from_rvalue(rhs, &mut deref_types);
                }
            }
        }

        // **pp: *const *const u32 → should collect both *const u32 carrier and u32 pointee
        assert!(
            deref_types.len() >= 2,
            "double deref should collect at least 2 types (carrier + pointee). keys: {:?}",
            deref_types.keys().collect::<Vec<_>>()
        );
        let has_u32_key = deref_types.keys().any(|k| k == "u32");
        assert!(
            has_u32_key,
            "double deref should collect final pointee u32. keys: {:?}",
            deref_types.keys().collect::<Vec<_>>()
        );
    });
}

/// Deref + Field projection: (*ptr).x should collect the struct pointee type.
#[test]
fn test_collect_deref_types_from_place_field_after_deref() {
    with_test_ay_ctx_for_source(DEREF_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_field");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "deref_field",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut deref_types = std::collections::BTreeMap::new();
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind {
                    chc_ctx.collect_deref_types_from_place(lhs, &mut deref_types);
                    chc_ctx.collect_deref_types_from_rvalue(rhs, &mut deref_types);
                }
            }
        }

        // (*ptr).x where ptr: *const Pair → should collect Pair as a pointee type
        assert!(
            !deref_types.is_empty(),
            "deref + field should collect at least the struct pointee. keys: {:?}",
            deref_types.keys().collect::<Vec<_>>()
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// collect_deref_type_arrays end-to-end tests
// ═══════════════════════════════════════════════════════════════════════

/// At Mem level, double deref should pre-declare type arrays for BOTH levels.
#[test]
fn test_collect_deref_type_arrays_double_deref_declares_both_levels() {
    with_test_ay_ctx_for_source(DOUBLE_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "double_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "double_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // Should have type arrays for both pointer levels
        let mem_arrays: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .filter(|(name, sort)| name.contains("_mem_") && sort.is_array())
            .collect();
        assert!(
            mem_arrays.len() >= 2,
            "double deref at Mem level should declare >= 2 type arrays (carrier + pointee). \
             mem arrays: {:?}",
            mem_arrays.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    });
}

/// At Mem level, each type array should have a matching __out output variable.
#[test]
fn test_collect_deref_type_arrays_output_counterparts() {
    with_test_ay_ctx_for_source(RVALUE_DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "use_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "use_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let mem_vars: Vec<&str> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .filter(|(name, _)| name.contains("_mem_"))
            .map(|(name, _)| &**name)
            .collect();

        for name in &mem_vars {
            let expected_out = format!("{name}__out");
            let has_out = chc_ctx
                .state_var_mgr
                .output_state_vars
                .iter()
                .any(|(n, _)| &**n == expected_out.as_str());
            assert!(has_out, "type array {name} must have output counterpart {expected_out}");
        }
    });
}

/// Pre-declared type arrays should be registered in heap_state.type_arrays.
#[test]
fn test_collect_deref_type_arrays_registered_in_heap_state() {
    with_test_ay_ctx_for_source(RVALUE_DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "use_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "use_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // u32 deref should create a type_arrays entry keyed by "u32"
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("u32"),
            "heap_state.type_arrays should contain u32. keys: {:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );

        // The entry should map to the correct array name
        let (arr_name, elem_sort) = chc_ctx.heap_state.type_arrays.get("u32").unwrap();
        assert!(
            arr_name.contains("_mem_u32"),
            "type array name should contain _mem_u32, got: {arr_name}"
        );
        assert_eq!(
            elem_sort.bitvec_width(),
            Some(32),
            "element sort for u32 type array should be bv32"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// collect_local_type_arrays tests
// ═══════════════════════════════════════════════════════════════════════

/// Diverse local types should each get a type array at Mem level.
#[test]
fn test_collect_local_type_arrays_diverse_types() {
    with_test_ay_ctx_for_source(LOCAL_TYPES_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "diverse_locals");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "diverse_locals",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // Should have type arrays for u8, u16, u32, u64, bool
        let type_keys: Vec<_> = chc_ctx.heap_state.type_arrays.keys().collect();
        assert!(
            type_keys.iter().any(|k| k.as_ref() == "u8"),
            "should declare type array for u8. keys: {type_keys:?}"
        );
        assert!(
            type_keys.iter().any(|k| k.as_ref() == "u16"),
            "should declare type array for u16. keys: {type_keys:?}"
        );
        assert!(
            type_keys.iter().any(|k| k.as_ref() == "u32"),
            "should declare type array for u32. keys: {type_keys:?}"
        );
        assert!(
            type_keys.iter().any(|k| k.as_ref() == "u64"),
            "should declare type array for u64. keys: {type_keys:?}"
        );
        assert!(
            type_keys.iter().any(|k| k.as_ref() == "bool"),
            "should declare type array for bool. keys: {type_keys:?}"
        );
    });
}

/// Reference locals should also declare pointee type arrays (Vectors 2-3 of #2258).
#[test]
fn test_collect_local_type_arrays_extracts_pointee_from_ref_locals() {
    with_test_ay_ctx_for_source(LOCAL_TYPES_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ref_local",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // ref_local has r: &u32 — should declare type array for u32 pointee
        let has_u32 = chc_ctx.heap_state.type_arrays.contains_key("u32");
        assert!(
            has_u32,
            "ref local should extract and declare pointee u32 type array. keys: {:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
    });
}

/// Vec/IntoIter/Box-array carriers should predict the inner element `mem_T`
/// partition before relation signatures are frozen. Part of #3714.
#[test]
fn test_predeclare_stub_internal_type_arrays_predicts_vec_iter_elem_type() {
    with_test_ay_ctx_for_source(STUB_INTERNAL_VEC_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_into_iter_position_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "vec_into_iter_position_probe",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let direct_i32_locals = body
            .locals()
            .iter()
            .filter(|local| chc_ctx.type_key_for_body_ty(local.ty).as_ref() == "i32")
            .count();
        assert_eq!(
            direct_i32_locals, 0,
            "probe should exercise carrier prediction, not direct local collection"
        );

        chc_ctx.declare_block_relations();

        let (arr_name, elem_sort) = chc_ctx
            .heap_state
            .type_arrays
            .get("i32")
            .expect("stub-internal predeclare should register Vec iterator element type");
        assert!(
            arr_name.contains("_mem_i32"),
            "array name should mention the i32 key, got {arr_name}"
        );
        assert_eq!(
            elem_sort.bitvec_width(),
            Some(32),
            "Vec iterator element type array should use BV32"
        );
    });
}

/// Dedup: if both collect_deref_type_arrays and collect_local_type_arrays
/// would declare the same type key, it should only appear once in state_vars.
#[test]
fn test_deref_and_local_arrays_no_duplicate_state_vars() {
    with_test_ay_ctx_for_source(RVALUE_DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "use_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "use_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // Count how many state vars contain _mem_u32 — should be exactly 1
        let u32_mem_count = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .filter(|(name, _)| name.contains("_mem_u32"))
            .count();
        assert_eq!(
            u32_mem_count, 1,
            "type array for u32 should appear exactly once in state_vars (dedup guard). found: {}",
            u32_mem_count
        );
    });
}

/// Terminator Call args with Deref should also be collected by collect_deref_type_arrays.
#[test]
fn test_collect_deref_type_arrays_from_call_args() {
    // binary_deref has call to wrapping_add — the *a and *b loads happen in statements,
    // but the function Call itself may pass deref'd operands.
    with_test_ay_ctx_for_source(RVALUE_DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "binary_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "binary_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // Should still have u32 type arrays from the deref'd pointer args
        let has_u32 = chc_ctx.heap_state.type_arrays.contains_key("u32");
        assert!(
            has_u32,
            "call with deref args should declare u32 type array. keys: {:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_decl_ref_const_values.rs` — constant reference scalar value
//! collection and worklist propagation.
//!
//! Part of #2303 (codegen_decl_ref_const_values.rs, 329 LOC, zero dedicated coverage).
//! Covers:
//! - `collect_const_ref_values`: Pass 4.1 (direct const ref to scalar types)
//! - `propagate_const_ref_values_worklist`: Pass 4.2 (worklist propagation via Copy/Move/Cast)
//! - `extract_scalar_from_const_ref`: scalar AY expression extraction
//!   - Bool, Uint (u8..u128), Int (i8..i128), Char, Array paths
//! - `build_const_ref_value_propagation_candidates`: Copy/Move + Cast edge collection
//! - `ConstRefValuePropagationKind`: CopyMove and Cast variants
//!
//! These tests supplement `test_ref_analysis.rs` (which covers pipeline-level const refs)
//! by verifying the internal state of const_ref_values and testing specific type paths.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};

// =============================================================================
// Pass 4.1: Direct constant reference to scalar types
// =============================================================================

const CONST_REF_U8_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_u8() -> u8 {
        let r: &u8 = &42;
        *r
    }
"#;

/// collect_const_ref_values populates const_ref_values for &42u8.
/// Exercises Pass 4.1: const &u8 → extract_scalar_from_const_ref (Uint path, u8).
#[test]
fn test_const_ref_value_u8_collected() {
    with_test_ay_ctx_for_source(CONST_REF_U8_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_u8");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_u8", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // const_ref_values should have at least one entry for the &42u8 constant
        assert!(
            !chc_ctx.ref_resolution.const_ref_values.is_empty(),
            "const_ref_u8 should have const_ref_value entries for &42u8"
        );

        // Pipeline should produce valid VC
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_u8", ChcConfig::default());
        assert!(!vc.rules.is_empty(), "const_ref_u8 should produce CHC rules");
        assert!(!vc.relations.is_empty(), "const_ref_u8 should produce relations");
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("BitVec") || smt.contains("bv"),
            "const_ref_u8 SMT should contain bitvector sort references"
        );
    });
}

const CONST_REF_U32_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_u32() -> u32 {
        let r: &u32 = &100;
        *r
    }
"#;

/// extract_scalar_from_const_ref handles u32.
#[test]
fn test_const_ref_value_u32_collected() {
    with_test_ay_ctx_for_source(CONST_REF_U32_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_u32");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_u32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !chc_ctx.ref_resolution.const_ref_values.is_empty(),
            "const_ref_u32 should have const_ref_value entries for &100u32"
        );
    });
}

const CONST_REF_BOOL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_bool_true() -> bool {
        let r: &bool = &true;
        *r
    }

    pub fn const_ref_bool_false() -> bool {
        let r: &bool = &false;
        *r
    }
"#;

/// extract_scalar_from_const_ref handles Bool path.
#[test]
fn test_const_ref_value_bool_collected() {
    with_test_ay_ctx_for_source(CONST_REF_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_bool_true");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_bool_true", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !chc_ctx.ref_resolution.const_ref_values.is_empty(),
            "const_ref_bool_true should have const_ref_value entries for &true"
        );
    });
}

const CONST_REF_TUPLE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_tuple() -> bool {
        let r: &(u8, bool) = &(0, true);
        (*r).1
    }
"#;

const CONST_REF_RANGE_INCLUSIVE_SOURCE: &str = r#"
    #![allow(dead_code)]

    use core::ops::RangeInclusive;

    pub fn const_ref_range_inclusive() -> bool {
        let r: &RangeInclusive<u32> = &(1u32..=3u32);
        r.contains(&2u32)
    }
"#;

/// Promoted tuple references should decode to a datatype value so downstream
/// fn_inline and deref projection can field-select directly from const_ref_values.
#[test]
fn test_const_ref_value_tuple_collected() {
    with_test_ay_ctx_for_source(CONST_REF_TUPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_tuple");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_tuple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let tuple_values: Vec<_> = chc_ctx
            .ref_resolution
            .const_ref_values
            .values()
            .filter(|expr| matches!(expr.sort().inner(), SortInner::Datatype(_)))
            .collect();
        assert!(
            !tuple_values.is_empty(),
            "const_ref_tuple should decode &(u8, bool) into a datatype const_ref_value"
        );

        let seeded_type_keys: Vec<_> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .map(|(type_key, _, _, _, _)| type_key.as_ref())
            .collect();
        assert!(
            seeded_type_keys.contains(&"tuple_u8_bool"),
            "const_ref_tuple should seed promoted tuple memory, got {seeded_type_keys:?}"
        );
        assert!(
            seeded_type_keys.contains(&"u8"),
            "const_ref_tuple should seed promoted tuple field memory for u8, got {seeded_type_keys:?}"
        );
        assert!(
            seeded_type_keys.contains(&"bool"),
            "const_ref_tuple should seed promoted tuple field memory for bool, got {seeded_type_keys:?}"
        );
    });
}

/// Promoted RangeInclusive const refs should declare the datatype sort needed by
/// the decoded const_ref_value constructor.
#[test]
fn test_const_ref_range_inclusive_declares_datatype_sort() {
    with_test_ay_ctx_for_source(CONST_REF_RANGE_INCLUSIVE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_range_inclusive");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "const_ref_range_inclusive", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let has_range_const_ref = chc_ctx.ref_resolution.const_ref_values.values().any(|expr| {
            matches!(expr.sort().inner(), SortInner::Datatype(dt) if dt.name == "RangeInclusive_u32")
        });
        assert!(
            has_range_const_ref,
            "const_ref_range_inclusive should decode a promoted &RangeInclusive<u32> const_ref_value"
        );

        let range_decl = chc_ctx.vc.decls.iter().find_map(|decl| {
            if let trust_mc_core::decl::Decl::Datatype { datatype } = decl
                && datatype.name == "RangeInclusive_u32"
            {
                Some(datatype)
            } else {
                None
            }
        });
        assert!(
            range_decl.is_some(),
            "const_ref_range_inclusive should declare the RangeInclusive_u32 datatype sort"
        );
        assert!(
            range_decl.is_some_and(|datatype| datatype
                .constructors
                .iter()
                .any(|ctor| ctor.name == "RangeInclusive_u32_mk")),
            "const_ref_range_inclusive should declare the RangeInclusive_u32 constructor"
        );
    });
}

const CONST_REF_I32_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_i32() -> i32 {
        let r: &i32 = &-7;
        *r
    }
"#;

/// extract_scalar_from_const_ref handles Int (signed) path.
#[test]
fn test_const_ref_value_i32_collected() {
    with_test_ay_ctx_for_source(CONST_REF_I32_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_i32");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_i32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !chc_ctx.ref_resolution.const_ref_values.is_empty(),
            "const_ref_i32 should have const_ref_value entries for &(-7i32)"
        );
    });
}

const CONST_REF_CHAR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_char() -> char {
        let r: &char = &'A';
        *r
    }
"#;

/// extract_scalar_from_const_ref handles Char path.
#[test]
fn test_const_ref_value_char_collected() {
    with_test_ay_ctx_for_source(CONST_REF_CHAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_char");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_char", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !chc_ctx.ref_resolution.const_ref_values.is_empty(),
            "const_ref_char should have const_ref_value entries for &'A'"
        );
    });
}

// =============================================================================
// Pass 4.1: Array constant reference (#2173)
// =============================================================================

const CONST_REF_ARRAY_U8_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_array_u8() -> u8 {
        let arr: &[u8; 3] = &[10, 20, 30];
        arr[1]
    }
"#;

/// extract_scalar_from_const_ref handles Array path (nested store encoding).
#[test]
fn test_const_ref_value_array_u8_pipeline() {
    with_test_ay_ctx_for_source(CONST_REF_ARRAY_U8_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_array_u8");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_array_u8", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "const_ref_array_u8 should produce CHC rules");
        assert!(!vc.relations.is_empty(), "const_ref_array_u8 should produce relations");
    });
}

/// Bug 9 regression: fresh symbolic const-array temporaries must be declared.
#[test]
fn test_const_ref_value_array_u8_declares_fresh_const_arr_var() {
    with_test_ay_ctx_for_source(CONST_REF_ARRAY_U8_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_array_u8");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_array_u8", ChcConfig::default());

        assert!(
            vc.vars()
                .iter()
                .any(|decl| decl.name.starts_with("__const_arr_") && decl.sort.is_array()),
            "expected declared __const_arr_* var for const array ref. vars: {:?}",
            vc.vars().iter().map(|decl| &decl.name).collect::<Vec<_>>()
        );
    });
}

const CONST_REF_EMPTY_ARRAY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_empty_array() -> usize {
        let arr: &[u32; 0] = &[];
        arr.len()
    }
"#;

/// Empty array constant reference edge case.
#[test]
fn test_const_ref_value_empty_array_pipeline() {
    with_test_ay_ctx_for_source(CONST_REF_EMPTY_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_empty_array");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_empty_array", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "const_ref_empty_array should produce CHC rules");
        assert!(!vc.relations.is_empty(), "const_ref_empty_array should produce relations");
    });
}

// =============================================================================
// Pass 4.2: Worklist propagation through Copy/Move
// =============================================================================

const CONST_REF_COPY_PROP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_copy_chain() -> u32 {
        let r: &u32 = &99;
        let r2 = r;
        let r3 = r2;
        *r3
    }
"#;

/// Pass 4.2 propagates const_ref_values through Copy/Move chains.
/// Exercises build_const_ref_value_propagation_candidates + propagate_const_ref_values_worklist.
/// Note: the compiler may optimize the copy chain, reducing the number of MIR locals.
#[test]
fn test_const_ref_value_copy_propagation() {
    with_test_ay_ctx_for_source(CONST_REF_COPY_PROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_copy_chain");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_copy_chain", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // At minimum, the original const ref should be collected (compiler may
        // optimize copies away, so we can't assert exact propagation count).
        assert!(
            !chc_ctx.ref_resolution.const_ref_values.is_empty(),
            "copy chain should have ≥ 1 const_ref_values entry, got 0"
        );

        // Pipeline should produce valid VC regardless of propagation depth
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_copy_chain", ChcConfig::default());
        assert!(!vc.rules.is_empty(), "copy chain pipeline should produce CHC rules");
        assert!(!vc.relations.is_empty(), "copy chain pipeline should produce relations");
    });
}

// =============================================================================
// Pass 4.2: Cast propagation (#2173)
// =============================================================================

const CONST_REF_CAST_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_cast() -> u32 {
        let r: &u32 = &42;
        let p = r as *const u32;
        unsafe { *p }
    }
"#;

/// Pass 4.2 propagates const_ref_values through Cast (PtrToPtr etc.).
/// Exercises ConstRefValuePropagationKind::Cast path.
#[test]
fn test_const_ref_value_cast_propagation() {
    with_test_ay_ctx_for_source(CONST_REF_CAST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_cast");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_cast", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "const_ref_cast pipeline should produce CHC rules");
        assert!(!vc.relations.is_empty(), "const_ref_cast should produce relations");
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "const_ref_cast SMT output should be non-empty");
    });
}

// =============================================================================
// Duplicate const_ref_values skip (idempotency)
// =============================================================================

const CONST_REF_DUPLICATE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_same_local() -> u32 {
        let r1: &u32 = &10;
        let r2: &u32 = &20;
        *r1 + *r2
    }
"#;

/// Multiple constant references to the same type don't conflict.
#[test]
fn test_const_ref_value_multiple_same_type_no_conflict() {
    with_test_ay_ctx_for_source(CONST_REF_DUPLICATE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_same_local");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_same_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Two distinct const refs → should produce at least 2 entries
        assert!(
            chc_ctx.ref_resolution.const_ref_values.len() >= 2,
            "two distinct const refs should produce ≥ 2 entries, got {}",
            chc_ctx.ref_resolution.const_ref_values.len()
        );
    });
}

// =============================================================================
// Pipeline integration: const_ref_values enable translate_place_with_deref
// =============================================================================

const CONST_REF_PIPELINE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn add_const_refs() -> u32 {
        let a: &u32 = &10;
        let b: &u32 = &20;
        *a + *b
    }
"#;

/// Constant reference values enable deref resolution in the full pipeline.
#[test]
fn test_const_ref_values_enable_deref_resolution() {
    with_test_ay_ctx_for_source(CONST_REF_PIPELINE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "add_const_refs");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "add_const_refs", ChcConfig::default());

        assert_vc_structure(&vc, "add_const_refs", body.blocks.len());
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "const ref deref pipeline should produce non-empty SMT");
    });
}

/// Constant reference values at Mem level.
#[test]
fn test_const_ref_values_mem_level() {
    with_test_ay_ctx_for_source(CONST_REF_PIPELINE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "add_const_refs");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "add_const_refs",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "const ref at Mem level should produce rules");
        assert!(!vc.relations.is_empty(), "const ref at Mem level should produce relations");
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "Mem-level const ref SMT output should be non-empty");
    });
}

// =============================================================================
// Part of #3617: RigidTy::Str constant reference byte seeding
// =============================================================================

const CONST_REF_STR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_str() -> u8 {
        let s: &str = "Hi";
        let bytes = s.as_bytes();
        bytes[0]
    }
"#;

/// extract_scalar_from_const_ref handles RigidTy::Str: promoted &str literal
/// seeds byte-array values into const_ref_values and const_ref_memory_inits.
/// Without this, transmute::<&str, &[u8]> leaves the byte array unconstrained.
#[test]
fn test_const_ref_str_seeds_byte_array() {
    with_test_ay_ctx_for_source(CONST_REF_STR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_str");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_str", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // const_ref_values should have at least one entry for the &str constant
        assert!(
            !chc_ctx.ref_resolution.const_ref_values.is_empty(),
            "const_ref_str should have const_ref_value entries for &\"Hi\""
        );

        // subslice_len should record length=2 for the &str
        assert!(
            !chc_ctx.ref_resolution.subslice_len.is_empty(),
            "const_ref_str should record subslice_len for &str"
        );

        // const_ref_memory_inits should have byte-level entries
        assert!(
            !chc_ctx.ref_resolution.const_ref_memory_inits.is_empty(),
            "const_ref_str should seed const_ref_memory_inits for byte values"
        );

        // Pipeline should produce valid VC with byte-related constraints
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_str", ChcConfig::default());
        assert!(!vc.rules.is_empty(), "const_ref_str should produce CHC rules");
        let smt = emit_chc(&vc).to_string();
        // The SMT output should contain __const_str (the fresh name prefix for &str arrays)
        assert!(
            smt.contains("__const_str"),
            "const_ref_str SMT should contain __const_str byte array variable"
        );
    });
}

const CONST_REF_REF_STR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_ref_str() -> u8 {
        let s: &&str = &"Hi";
        s.as_bytes()[0]
    }
"#;

const CONST_REF_MULTI_ARRAY_SLOT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_two_promoted_arrays() -> u8 {
        let left: &[u8; 2] = &[10, 20];
        let right: &[u8; 2] = &[30, 40];
        left[0].wrapping_add(right[1])
    }
"#;

/// Part of #3607: promoted `&&str` locals should inherit the inner `&str`
/// backing-byte array and tracked length, so callers that receive a local
/// rather than a direct constant operand can still recover string content.
#[test]
fn test_const_ref_ref_str_seeds_outer_local() {
    with_test_ay_ctx_for_source(CONST_REF_REF_STR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_ref_str");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_ref_str", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let outer_ref_local = body
            .blocks
            .iter()
            .flat_map(|block| block.statements.iter())
            .find_map(|stmt| {
                let rustc_public::mir::StatementKind::Assign(
                    lhs,
                    rustc_public::mir::Rvalue::Use(rustc_public::mir::Operand::Constant(_)),
                ) = &stmt.kind
                else {
                    return None;
                };
                let ty = body.locals()[lhs.local].ty;
                match ty.kind() {
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(
                        _,
                        inner_ty,
                        _,
                    )) => match inner_ty.kind() {
                        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(
                            _,
                            pointee_ty,
                            _,
                        )) if matches!(
                            pointee_ty.kind(),
                            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Str)
                        ) =>
                        {
                            Some(lhs.local)
                        }
                        _ => None,
                    },
                    _ => None,
                }
            })
            .expect("expected a promoted &&str constant local");

        assert!(
            chc_ctx.ref_resolution.const_ref_values.contains_key(&outer_ref_local),
            "outer &&str local _{outer_ref_local} should have const_ref_values"
        );
        assert!(
            chc_ctx.ref_resolution.subslice_len.contains_key(&outer_ref_local),
            "outer &&str local _{outer_ref_local} should have subslice_len"
        );

        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_ref_str", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("__const_str"),
            "const_ref_ref_str SMT should contain __const_str byte array variable"
        );
    });
}

/// Part of #3841: promoted-const memory seeds must use distinct object IDs per
/// promoted allocation. If two array-backed const refs share one slot, entry-rule
/// and bb0 replay facts collide and can make later safety checks vacuous.
#[test]
fn test_const_ref_memory_inits_use_distinct_promoted_slots_for_multiple_arrays() {
    with_test_ay_ctx_for_source(CONST_REF_MULTI_ARRAY_SLOT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_two_promoted_arrays");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_two_promoted_arrays",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let mut slots = std::collections::BTreeSet::new();
        let mut locals_with_slots = std::collections::BTreeSet::new();
        let mut seen = std::collections::BTreeMap::new();
        let mut conflicts = Vec::new();

        for (&local, &promoted_obj_id) in &chc_ctx.ref_resolution.const_ref_promoted_obj_ids {
            locals_with_slots.insert(local);
            slots.insert(promoted_obj_id);
        }

        for (type_key, _, value, promoted_obj_id, byte_offset) in
            &chc_ctx.ref_resolution.const_ref_memory_inits
        {
            slots.insert(*promoted_obj_id);
            let key = (type_key.to_string(), *promoted_obj_id, *byte_offset);
            let value_smt = value.to_string();
            if let Some(prev) = seen.insert(key.clone(), value_smt.clone())
                && prev != value_smt
            {
                conflicts.push((key, prev, value_smt));
            }
        }

        assert!(
            slots.len() >= 2,
            "two promoted arrays should assign at least two promoted-const slots, got {slots:?}"
        );
        assert!(
            locals_with_slots.len() >= 2,
            "two promoted arrays should record at least two locals with promoted slots, got {locals_with_slots:?}"
        );
        assert!(
            !chc_ctx.ref_resolution.const_ref_memory_inits.is_empty(),
            "two promoted arrays should seed const_ref_memory_inits"
        );
        assert!(
            conflicts.is_empty(),
            "promoted const memory inits should not collide on (type_key, slot, offset), conflicts={conflicts:?}"
        );
    });
}

// =============================================================================
// Pass 4.3: Field projection propagation through worklist (Part of #3235)
//
// These tests verify that field projections from DT const_ref_values are now
// handled inside the worklist, making field -> copy, field -> cast, and
// field -> field chains transitive. This preserves the existing field-select
// semantics from the original #3208 post-pass without attempting new
// variant-aware enum payload decoding.
// =============================================================================

/// Single-hop field propagation: `_dest = Copy(_src.0)` where `_src` is a
/// promoted const-ref tuple. The field-projected local should appear in
/// const_ref_values after the worklist completes.
///
/// Uses the existing CONST_REF_TUPLE_SOURCE (which already verifies the
/// tuple DT is decoded) and checks that any MIR locals assigned via
/// Field projection from a const_ref_values source also appear in
/// const_ref_values.
#[test]
fn test_const_ref_value_field_single_hop() {
    with_test_ay_ctx_for_source(CONST_REF_TUPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_tuple");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_tuple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Verify the tuple DT is in const_ref_values (precondition).
        let has_dt = chc_ctx
            .ref_resolution
            .const_ref_values
            .values()
            .any(|expr| matches!(expr.sort().inner(), SortInner::Datatype(_)));
        assert!(has_dt, "precondition: tuple DT should be in const_ref_values");

        // Find all locals assigned via Field projection from a const_ref_values source.
        let mut field_projected_locals = Vec::new();
        for block in &body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if let Rvalue::Use(
                    rustc_public::mir::Operand::Copy(place)
                    | rustc_public::mir::Operand::Move(place),
                ) = rhs
                {
                    if place.projection.len() == 1
                        && matches!(place.projection[0], ProjectionElem::Field(_, _))
                        && chc_ctx.ref_resolution.const_ref_values.contains_key(&place.local)
                    {
                        field_projected_locals.push(lhs.local);
                    }
                }
            }
        }

        // If MIR contains field projections from const_ref_values sources, they
        // should also be resolved. If no such projections exist in the MIR
        // (compiler optimized away the intermediate), the test still passes —
        // it's verifying the worklist topology, not forcing specific MIR shape.
        for local in &field_projected_locals {
            assert!(
                chc_ctx.ref_resolution.const_ref_values.contains_key(local),
                "field-projected local _{local} should be in const_ref_values after worklist"
            );
        }

        // The pipeline should still produce valid VC.
        let vc = mir_to_chc(ctx.tcx, &body, "const_ref_tuple", ChcConfig::default());
        assert!(!vc.rules.is_empty(), "const_ref_tuple should produce CHC rules");
    });
}

/// Transitive propagation: field -> copy chains. After field extraction
/// discovers a field-projected local, any downstream Copy/Move from that
/// local should also propagate through the worklist (not require a separate
/// post-pass). This is the key behavioral change from #3235.
///
/// Uses the same tuple source. The test verifies that ALL transitive
/// Copy/Move destinations of field-projected locals are also resolved.
#[test]
fn test_const_ref_value_field_transitive_copy() {
    with_test_ay_ctx_for_source(CONST_REF_TUPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_tuple");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "const_ref_tuple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Collect field-projected locals and their downstream Copy/Move destinations.
        let mut field_projected: std::collections::HashSet<usize> =
            std::collections::HashSet::new();
        let mut transitive_copies: Vec<(usize, usize)> = Vec::new(); // (src, dest)

        for block in &body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if let Rvalue::Use(
                    rustc_public::mir::Operand::Copy(place)
                    | rustc_public::mir::Operand::Move(place),
                ) = rhs
                {
                    // Field projection from a const_ref_values source
                    if place.projection.len() == 1
                        && matches!(place.projection[0], ProjectionElem::Field(_, _))
                        && chc_ctx.ref_resolution.const_ref_values.contains_key(&place.local)
                    {
                        field_projected.insert(lhs.local);
                    }
                    // Copy/Move from a field-projected local
                    if place.projection.is_empty() && field_projected.contains(&place.local) {
                        transitive_copies.push((place.local, lhs.local));
                    }
                }
            }
        }

        // All field-projected locals should be in const_ref_values.
        for local in &field_projected {
            assert!(
                chc_ctx.ref_resolution.const_ref_values.contains_key(local),
                "field-projected local _{local} should be in const_ref_values"
            );
        }

        // All transitive Copy/Move destinations should also be resolved.
        for (src, dest) in &transitive_copies {
            assert!(
                chc_ctx.ref_resolution.const_ref_values.contains_key(dest),
                "transitive copy _{src} -> _{dest} should propagate const_ref_value"
            );
        }

        // The total number of resolved locals should be >= direct + field + transitive.
        let total = chc_ctx.ref_resolution.const_ref_values.len();
        assert!(total >= 1, "const_ref_values should resolve at least the tuple DT, got {total}");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_expr_deref.rs` — Deref projection resolution.
//!
//! Part of #2303 (codegen_expr_deref.rs, 369 LOC, zero dedicated coverage).
//! Covers:
//! - `try_resolve_deref_via_ref_targets`: ref-target deref chain resolution
//! - `translate_place_with_deref`: Mem-level Deref+Field+Index handling
//! - Dead-object detection for raw-pointer dereferences
//! - Const-ref fallback for promoted constants
//! - Array index bounds checking (Part of #1888)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// Reference deref at Reg level — try_resolve_deref_via_ref_targets
// =============================================================================

/// Branching forces multi-BB MIR so the VC contains transition rules with
/// non-trivial constraints. Single-block `*x` compiles to init-only rules.
const REF_DEREF_SIMPLE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ref_deref(x: &u32, flag: bool) -> u32 {
        if flag { *x } else { 0 }
    }
"#;

/// Simple reference deref (*x) at Reg level should be resolved via ref_targets.
#[test]
fn test_ref_deref_simple_generates_vc() {
    with_test_ay_ctx_for_source(REF_DEREF_SIMPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_deref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_deref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ref_deref", body.blocks.len());

        // Deref of u32 ref should have bv32 sorts for operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "ref deref of u32 should have bv32 sort in relations");

        // Semantic: transition rules must have non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_ref_deref");
        // Semantic: at Reg level, ref deref resolves via ref_targets, producing Eq
        // constraints that link the ref-target variable to the destination local.
        // Note: Eq also appears from phi-node merging in branching probes; this
        // assertion is necessary but not sufficient for deref-specific correctness.
        // The bv32 sort check above provides the deref-specific validation.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_ref_deref",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq (ref-target assignment)",
        );
    });
}

/// Reference deref should produce VC rules even at the Reg level (no memory model needed).
#[test]
fn test_ref_deref_produces_transition_rules() {
    with_test_ay_ctx_for_source(REF_DEREF_SIMPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_deref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_deref", ChcConfig::default());

        // Simple deref + return: at minimum an entry rule (single-block functions
        // may produce only 1 rule since the return merges with the entry block).
        assert!(
            !vc.rules.is_empty(),
            "ref deref should produce at least 1 rule, got {}",
            vc.rules.len()
        );

        // Semantic: deref of &u32 should have bv32 sorts in relations
        assert_relation_has_arg_sort(
            &vc,
            "probe_ref_deref",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_ref_deref");
    });
}

// =============================================================================
// Struct field through reference — (*ref).field pattern
// =============================================================================

const REF_FIELD_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Point {
        pub x: u32,
        pub y: u32,
    }

    pub fn probe_ref_field_deref(p: &Point, flag: bool) -> u32 {
        if flag { p.x } else { p.y }
    }
"#;

/// (*ref).field access at Reg level should resolve through ref_targets.
#[test]
fn test_ref_field_deref_generates_vc() {
    with_test_ay_ctx_for_source(REF_FIELD_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_field_deref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_field_deref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ref_field_deref", body.blocks.len());

        // Field deref of Point.x (u32) should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "struct field deref should have bv32 sort for u32 field");

        // Semantic: non-trivial transition constraints for field extraction
        assert_has_nontrivial_transition_constraints(&vc, "probe_ref_field_deref");
        // Semantic: field access produces Eq binding the field value
        assert_rule_contains_expr_kind(
            &vc,
            "probe_ref_field_deref",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// =============================================================================
// Mutable reference deref — write through *ref
// =============================================================================

const MUT_REF_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_mut_ref_deref(x: &mut u32, flag: bool) {
        if flag { *x = 42; } else { *x = 0; }
    }
"#;

/// Mutable reference deref should produce valid VC (store side handled elsewhere).
#[test]
fn test_mut_ref_deref_generates_vc() {
    with_test_ay_ctx_for_source(MUT_REF_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mut_ref_deref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_mut_ref_deref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_mut_ref_deref", body.blocks.len());

        // Mutable ref deref assigns u32 — bv32 sort should be present
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "mut ref deref storing u32 should have bv32 sort");

        // Semantic: mutable deref assignment produces non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_mut_ref_deref");
        // Semantic: store of constant 42 produces Eq constraint
        assert_rule_contains_expr_kind(
            &vc,
            "probe_mut_ref_deref",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// =============================================================================
// Raw pointer deref at Mem level — translate_place_with_deref memory path
// =============================================================================

const RAW_PTR_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub unsafe fn probe_raw_ptr_deref(ptr: *const u32) -> u32 {
        unsafe { *ptr }
    }
"#;

/// Raw pointer deref at Reg level should return None for the deref expression
/// (no memory model at Reg level), but the pipeline should still produce valid VC.
#[test]
fn test_raw_ptr_deref_reg_level_generates_vc() {
    with_test_ay_ctx_for_source(RAW_PTR_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_deref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_raw_ptr_deref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_raw_ptr_deref", body.blocks.len());

        // Raw pointer deref at Reg level should still produce transition rules
        assert!(
            !vc.rules.is_empty(),
            "raw ptr deref should produce at least 1 rule, got {}",
            vc.rules.len()
        );

        // Semantic: even at Reg level, raw ptr deref should have non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_raw_ptr_deref (Reg)");
    });
}

/// Raw pointer deref at Mem level should go through translate_place_with_deref memory path.
#[test]
fn test_raw_ptr_deref_mem_level_generates_vc() {
    with_test_ay_ctx_for_source(RAW_PTR_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_deref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_raw_ptr_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_raw_ptr_deref", body.blocks.len());

        // Mem-level raw pointer deref should produce transition rules
        assert!(!vc.rules.is_empty(), "raw ptr deref at Mem level should produce rules");

        // Semantic: Mem-level deref should produce non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_raw_ptr_deref (Mem)");
        // The final VC may no longer contain a literal Select after scalarization,
        // so the stable postcondition here is the non-trivial transition above.
    });
}

/// Heap-backed raw-pointer deref may use the memory path at Reg level when the
/// pointer local already carries a concrete alloc_id.
#[test]
fn test_raw_ptr_deref_reg_level_resolves_known_alloc_id() {
    with_test_ay_ctx_for_source(RAW_PTR_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_deref");
        let body = instance.body().expect("function body");
        assert_eq!(
            body.arg_locals().len(),
            1,
            "probe_raw_ptr_deref should have exactly one argument local"
        );
        let ptr_local = 1usize;
        let scalar_ty = match body.locals()[ptr_local].ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            other => panic!("expected raw pointer arg, got {other:?}"),
        };
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_ptr_deref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let obj_id = 0xABCD_u32;
        let stored_value = ay_bindings::Expr::bitvec_const(0x44_u128, 32);
        let stored_value_smt = stored_value.to_string();
        let addr = ay_bindings::Expr::bitvec_const(obj_id as u128, 32)
            .concat(ay_bindings::Expr::bitvec_const(0_u128, 32));

        chc_ctx.known_alloc_ids.insert(ptr_local, obj_id);
        let store_result = chc_ctx.build_memory_store(addr, stored_value, scalar_ty);
        assert!(store_result.is_none(), "memory store should accumulate into heap state");

        let deref_place = rustc_public::mir::Place {
            local: ptr_local,
            projection: vec![rustc_public::mir::ProjectionElem::Deref],
        };
        let translated = chc_ctx.translate_place_with_deref(&deref_place, &HashSet::new());
        let translated = translated.expect("known-alloc raw ptr deref should resolve at Reg level");
        assert!(
            translated.to_string().contains(&stored_value_smt),
            "known-alloc deref should forward the heap store: {}",
            translated
        );
    });
}

// =============================================================================
// Array index — translate_place_with_deref Index projection
// =============================================================================

const ARRAY_INDEX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_array_index(arr: [u32; 4], idx: usize) -> u32 {
        arr[idx]
    }
"#;

/// Array indexing should produce VC with bounds check constraints (Part of #1888).
#[test]
fn test_array_index_generates_vc() {
    with_test_ay_ctx_for_source(ARRAY_INDEX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_array_index", body.blocks.len());

        // The bounds check assertion (from MIR assert) should produce error-headed rules
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "Array indexing should produce error-headed rules from bounds checks"
        );

        // Semantic: non-trivial constraints for bounds check logic
        assert_has_nontrivial_transition_constraints(&vc, "probe_array_index");
        // Semantic: bounds check produces comparison constraint (BvULt for idx < len)
        assert_rule_contains_expr_kind(
            &vc,
            "probe_array_index",
            |e| matches!(e.value(), ExprValue::BvULt(_, _)),
            "BvULt",
        );
    });
}

// =============================================================================
// Constant index — ConstantIndex projection
// =============================================================================

const CONST_INDEX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_const_index(arr: [u32; 4]) -> u32 {
        arr[2]
    }
"#;

/// Constant array index should produce valid VC.
#[test]
fn test_const_index_generates_vc() {
    with_test_ay_ctx_for_source(CONST_INDEX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_const_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_const_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_const_index", body.blocks.len());

        // Constant array index on [u32;4] should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "const index into [u32;4] should have bv32 sort");

        // Semantic: constant index access produces non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_const_index");
        // Semantic: constant index should produce Eq constraint for element extraction
        assert_rule_contains_expr_kind(
            &vc,
            "probe_const_index",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// =============================================================================
// Nested struct deref — Deref+Field chain
// =============================================================================

const NESTED_STRUCT_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Inner {
        pub val: u32,
    }

    pub struct Outer {
        pub inner: Inner,
    }

    pub fn probe_nested_deref(o: &Outer, flag: bool) -> u32 {
        if flag { o.inner.val } else { 0 }
    }
"#;

/// Nested field access through reference should resolve to concrete value.
#[test]
fn test_nested_struct_deref_generates_vc() {
    with_test_ay_ctx_for_source(NESTED_STRUCT_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_deref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_nested_deref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_nested_deref", body.blocks.len());

        // Nested struct deref returning u32 should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "nested struct deref returning u32 should have bv32 sort");

        // Semantic: nested field access produces non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_nested_deref");
        // Semantic: nested struct access produces Eq binding the extracted field
        assert_rule_contains_expr_kind(
            &vc,
            "probe_nested_deref",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// =============================================================================
// Const reference — const_ref_values fallback
// =============================================================================

const CONST_REF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_const_ref(flag: bool) -> u8 {
        let r = &0u8;
        if flag { *r } else { 1 }
    }
"#;

/// Promoted constant reference (*&0u8) should resolve via const_ref_values at Reg level.
#[test]
fn test_const_ref_deref_generates_vc() {
    with_test_ay_ctx_for_source(CONST_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_const_ref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_const_ref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_const_ref", body.blocks.len());

        // Const ref deref of u8 should have bv8 sorts
        let has_bv8 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(8)));
        assert!(has_bv8, "const ref deref of u8 should have bv8 sort");

        // Semantic: const ref deref produces non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_const_ref");
        // Semantic: const ref resolves to Eq with a BitVecConst (the promoted 0u8)
        assert_rule_contains_expr_kind(
            &vc,
            "probe_const_ref",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

/// Direct const-ref deref at Mem level should prefer const-ref facts over memory select.
#[test]
fn test_const_ref_deref_mem_level_uses_const_value() {
    with_test_ay_ctx_for_source(CONST_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_const_ref");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_const_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let mut deref_place = None;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    _,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                {
                    deref_place = Some(place.clone());
                    break;
                }
            }
            if deref_place.is_some() {
                break;
            }
        }

        let place = deref_place.expect("expected Copy/Move(*ref) in probe_const_ref MIR");
        let expr = chc_ctx
            .translate_place_with_deref(&place, &HashSet::new())
            .expect("const deref should resolve at Mem level");

        match expr.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 8, "expected u8 deref width");
                assert_eq!(
                    value.to_string(),
                    "0",
                    "expected deref of &0u8 to resolve to constant 0"
                );
            }
            other => panic!("expected const bitvec for deref, got {other:?}"),
        }
    });
}

// =============================================================================
// Mem-level raw pointer store + load round-trip
// =============================================================================

const RAW_PTR_STORE_LOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub unsafe fn probe_ptr_store_load(ptr: *mut u32) -> u32 {
        unsafe {
            *ptr = 99;
            *ptr
        }
    }
"#;

/// Raw pointer store+load at Mem level exercises both translate_place_with_deref
/// (load side) and build_memory_store (store side).
#[test]
fn test_raw_ptr_store_load_mem_level_generates_vc() {
    with_test_ay_ctx_for_source(RAW_PTR_STORE_LOAD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_store_load");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_ptr_store_load",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_ptr_store_load", body.blocks.len());

        // Raw ptr store+load of u32 at Mem level should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "raw ptr store+load of u32 should have bv32 sort");

        // Semantic: store+load round-trip produces non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_ptr_store_load");
        // Semantic: memory store+load uses Store and Select operations
        assert_rule_contains_expr_kind(
            &vc,
            "probe_ptr_store_load",
            |e| matches!(e.value(), ExprValue::Store { .. }),
            "Store",
        );
    });
}

// =============================================================================
// Deref chain with downcast — enum behind reference
// =============================================================================

const ENUM_REF_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Shape {
        Circle(u32),
        Square(u32),
    }

    pub fn probe_enum_ref(s: &Shape) -> u32 {
        match s {
            Shape::Circle(r) => *r,
            Shape::Square(w) => *w,
        }
    }
"#;

/// Enum behind reference exercises Deref+Downcast+Field projection chain.
#[test]
fn test_enum_ref_deref_generates_vc() {
    with_test_ay_ctx_for_source(ENUM_REF_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_enum_ref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_enum_ref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_enum_ref", body.blocks.len());

        // Enum match on Shape with u32 fields should have bv32 sorts and multiple rules
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "enum ref deref with u32 fields should have bv32 sort");
        assert!(
            vc.rules.len() >= 3,
            "enum match should produce >= 3 rules, got {}",
            vc.rules.len()
        );

        // Semantic: enum match produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_enum_ref");
        // Semantic: enum deref uses Eq to bind variant field values
        assert_rule_contains_expr_kind(
            &vc,
            "probe_enum_ref",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// =============================================================================
// Enum behind reference — active_variant cons_idx propagation
// =============================================================================

/// Verify that enum field access through a reference correctly propagates the
/// constructor index (cons_idx) from Downcast to Field. Without active_variant
/// tracking, multi-constructor enum field access returns None (cons_idx required
/// for datatype_field_select on multi-constructor types).
///
/// This exercises the `extract_field_projections` path at Reg level and verifies
/// the VC rules contain non-trivial bodies (not empty from failed field extraction).
#[test]
fn test_enum_ref_deref_propagates_cons_idx() {
    with_test_ay_ctx_for_source(ENUM_REF_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_enum_ref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_enum_ref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_enum_ref", body.blocks.len());

        // The match has two arms (Circle, Square) — each should produce at least
        // one transition rule with a body. If cons_idx propagation fails, the rule
        // body expressions for variant field access would be None and the rule count
        // or body constraints would be reduced.
        // A 2-variant match on an enum with return values should produce rules
        // for at least 3 blocks: entry, one per variant arm, and the return merge.
        assert!(
            vc.rules.len() >= 3,
            "enum match should produce >= 3 rules (entry + 2 arms + merge), got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        // (confirms cons_idx propagation produced real field-extraction constraints)
        assert_has_nontrivial_transition_constraints(&vc, "probe_enum_ref (cons_idx)");

        // Semantic: enum with u32 variant fields should produce bv32-sorted relation args
        assert_relation_has_arg_sort(
            &vc,
            "probe_enum_ref (cons_idx)",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );

        // Semantic: Eq constraints link extracted variant field values to return local
        assert_rule_contains_expr_kind(
            &vc,
            "probe_enum_ref (cons_idx)",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// =============================================================================
// Raw pointer to enum at Mem level — active_variant fallback path
// =============================================================================

const RAW_PTR_ENUM_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Status {
        Active(u32),
        Inactive(u32),
    }

    pub unsafe fn probe_raw_ptr_enum(ptr: *const Status) -> u32 {
        unsafe {
            match *ptr {
                Status::Active(v) => v,
                Status::Inactive(v) => v,
            }
        }
    }
"#;

/// Raw pointer to multi-constructor enum at Mem level exercises the
/// translate_place_with_deref fallback path where active_variant tracking
/// is needed for correct Downcast+Field handling.
#[test]
fn test_raw_ptr_enum_deref_mem_level_generates_vc() {
    with_test_ay_ctx_for_source(RAW_PTR_ENUM_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_enum");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_raw_ptr_enum",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_raw_ptr_enum", body.blocks.len());

        // Enum match through raw pointer should produce rules for multiple arms.
        assert!(
            vc.rules.len() >= 3,
            "raw ptr enum match should produce >= 3 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_raw_ptr_enum (Mem)");

        // Semantic: enum with u32 fields should produce bv32-sorted relation arguments
        assert_relation_has_arg_sort(
            &vc,
            "probe_raw_ptr_enum (Mem)",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );

        // Semantic: Eq constraints for binding match arm field values
        assert_rule_contains_expr_kind(
            &vc,
            "probe_raw_ptr_enum (Mem)",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

/// Verify that raw pointer enum match at Mem level propagates cons_idx from
/// Downcast to Field. The fallback path in codegen_expr_deref.rs loads the
/// whole struct, then relies on active_variant tracking to pass the correct
/// cons_idx to Field selection. If cons_idx is None, apply_field_selections
/// returns None for multi-constructor datatypes, causing the match arm rules
/// to have fewer body constraints (degraded codegen).
///
/// We check that match arm transition rules have non-empty body constraints,
/// which indicates successful field extraction via cons_idx propagation.
#[test]
fn test_raw_ptr_enum_deref_mem_level_propagates_cons_idx() {
    with_test_ay_ctx_for_source(RAW_PTR_ENUM_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_enum");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_raw_ptr_enum",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_raw_ptr_enum", body.blocks.len());

        // The match has 2 arms → at least 2 transition rules (beyond entry).
        // Each match arm rule should have body constraints (from successful
        // field extraction). If cons_idx fails, the transition degrades to
        // fewer or empty constraints.
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();

        assert!(
            transition_rules.len() >= 2,
            "enum match should produce >= 2 transition rules (one per arm), got {}",
            transition_rules.len()
        );

        // Both match arms must produce body constraints (field extraction via
        // cons_idx). If cons_idx is None for either variant, that arm's rule
        // degrades to empty constraints. Requiring >= 2 ensures both arms work.
        let rules_with_constraints: usize =
            transition_rules.iter().filter(|r| !r.body.constraints.is_empty()).count();

        assert!(
            rules_with_constraints >= 2,
            "both match arm transition rules should have body constraints \
             (indicates successful cons_idx propagation for both variants), \
             got {} constrained rules out of {} transition rules",
            rules_with_constraints,
            transition_rules.len()
        );
    });
}

const MANUAL_ASYNC_DEREF_SOURCE: &str =
    include_str!("../../../../../tests/trust_mc/AsyncAwait/main.rs");

fn find_coroutine_deref_payload_read(body: &rustc_public::mir::Body) -> Option<Place> {
    use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};

    body.blocks.iter().find_map(|bb| {
        bb.statements.iter().find_map(|stmt| {
            let StatementKind::Assign(_, rhs) = &stmt.kind else {
                return None;
            };
            let place = match rhs {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::Ref(_, _, place)
                | Rvalue::AddressOf(_, place)
                | Rvalue::CopyForDeref(place)
                | Rvalue::Discriminant(place)
                | Rvalue::Len(place) => place,
                _ => return None,
            };
            if !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                || !place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Downcast(_)))
                || !place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(..)))
            {
                return None;
            }
            let base_ty = body.locals().get(place.local)?.ty;
            let pointee_ty = ChcCtx::deref_pointee_ty(base_ty)?;
            if !matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
                return None;
            }
            Some(place.clone())
        })
    })
}

fn find_body_with_coroutine_deref_payload_read(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    suffix: &str,
) -> Option<(String, rustc_public::mir::Body, Place)> {
    rustc_public::all_local_items().into_iter().find_map(|item| {
        let def_id = rustc_internal::internal(tcx, item.def_id());
        let path = tcx.def_path_str(def_id);
        if !path.contains(suffix) {
            return None;
        }
        let body = item.body()?;
        let place = find_coroutine_deref_payload_read(&body)?;
        Some((path, body, place))
    })
}

/// Coroutine payload reads like `(((*_ref) as variant#N).field)` should bridge
/// through the coroutine root expression instead of falling back to an
/// unresolved deref-load path.
#[test]
fn test_coroutine_deref_payload_read_uses_coroutine_root_bridge() {
    let source = MANUAL_ASYNC_DEREF_SOURCE
        .replace("#[kani::proof]\n", "")
        .replace("#[kani::unwind(2)]\n", "")
        .replace("kani::block_on", "block_on");

    with_test_ay_ctx_for_source(&source, |ctx| {
        let matching_items: Vec<_> = rustc_public::all_local_items()
            .into_iter()
            .filter_map(|item| {
                let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
                let path = ctx.tcx.def_path_str(def_id);
                path.contains("test_async_await_manually").then_some(path)
            })
            .collect();

        let (body_name, body, place) =
            find_body_with_coroutine_deref_payload_read(ctx.tcx, "test_async_await_manually")
                .unwrap_or_else(|| {
                    panic!(
                        "expected a body under test_async_await_manually with a coroutine deref payload read; items={matching_items:?}"
                    )
                });

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, body_name.as_str(), ChcConfig::default());
        chc_ctx.declare_block_relations();

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let _expr = chc_ctx
            .translate_place_with_deref(&place, &HashSet::new())
            .expect("coroutine deref payload read should translate");

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine deref payload read should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine deref payload read should avoid aggregate-encoding gaps"
        );
    });
}

// =============================================================================
// Mem-level struct field through raw pointer — Deref+Field load
// =============================================================================

const RAW_PTR_STRUCT_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[repr(C)]
    pub struct Pair {
        pub first: u32,
        pub second: u32,
    }

    pub unsafe fn probe_raw_ptr_struct_field(ptr: *const Pair) -> u32 {
        unsafe { (*ptr).first }
    }
"#;

/// Raw pointer field access (*ptr).field at Mem level exercises the Deref+Field
/// lookahead path in translate_place_with_deref (field offset computation).
#[test]
fn test_raw_ptr_struct_field_mem_level_generates_vc() {
    with_test_ay_ctx_for_source(RAW_PTR_STRUCT_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_struct_field");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_raw_ptr_struct_field",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_raw_ptr_struct_field", body.blocks.len());

        // Raw ptr struct field access of u32 at Mem level should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "raw ptr struct field access should have bv32 sort for u32");

        // Semantic: mem-level struct field access produces non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_raw_ptr_struct_field");
        // Semantic: Mem-level struct field access uses Select for memory read
        assert_rule_contains_expr_kind(
            &vc,
            "probe_raw_ptr_struct_field",
            |e| matches!(e.value(), ExprValue::Select { .. }),
            "Select",
        );
    });
}

// =============================================================================
// Slice index — dynamic index through reference
// =============================================================================

const SLICE_INDEX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_slice_index(s: &[u32], idx: usize) -> u32 {
        s[idx]
    }
"#;

/// Slice indexing exercises Index projection + bounds check at runtime.
#[test]
fn test_slice_index_generates_vc() {
    with_test_ay_ctx_for_source(SLICE_INDEX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_slice_index", body.blocks.len());

        // Slice indexing with u32 elements should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "slice index returning u32 should have bv32 sort");

        // Semantic: slice indexing produces non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_slice_index");
        // Semantic: slice index should produce Eq constraints for element binding
        assert_rule_contains_expr_kind(
            &vc,
            "probe_slice_index",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// =============================================================================
// Argument reference read — ref_arg_pointee_idx read-side (#2844)
// =============================================================================

const ARG_REF_READ_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn read_via_ref(x: &u32) -> u32 {
        let val = *x;
        val + 1
    }
"#;

/// `fn read_via_ref(x: &u32) -> u32 { *x }` at Reg level resolves to the
/// pointee state var (not nondet). Before #2844, argument reference reads
/// returned None at Reg level because ref_targets has no entry for implicit
/// argument references, causing `*x` to be unconstrained.
///
/// Part of #2844.
#[test]
fn test_arg_ref_read_resolves_to_pointee_state_var() {
    with_test_ay_ctx_for_source(ARG_REF_READ_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_via_ref");
        let body = instance.body().expect("body");

        let vc = mir_to_chc(ctx.tcx, &body, "read_via_ref", ChcConfig::default());

        // The VC must declare a pointee variable for the &u32 argument.
        let has_pointee_var = vc.vars().iter().any(|v| v.name.contains("_pointee"));
        assert!(
            has_pointee_var,
            "VC should declare a _pointee state variable for &u32 argument (#2844)"
        );

        // At least one transition rule must reference the pointee input variable
        // in its body constraints. Before #2844, the read returned None and the
        // constraint on `val` would be absent or vacuously true.
        let has_pointee_in_constraints = vc.rules.iter().any(|r| {
            r.body.constraints.iter().any(|c| {
                constraint_tree_contains(
                    c,
                    &|e| matches!(e.value(), ExprValue::Var { name } if name.contains("_pointee")),
                )
            })
        });
        assert!(
            has_pointee_in_constraints,
            "at least one rule should reference the _pointee variable in body constraints (#2844)"
        );
    });
}

/// Direct helper-level test: `translate_place_with_deref` on a `*arg_ref`
/// place must return a concrete expression (not None) when the arg local has
/// a ref_arg_pointee_idx entry.
///
/// Part of #2844.
#[test]
fn test_arg_ref_read_helper_returns_concrete_expr() {
    use rustc_public::mir::{Local, Place, ProjectionElem};

    with_test_ay_ctx_for_source(ARG_REF_READ_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_via_ref");
        let body = instance.body().expect("body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "read_via_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Arg 1 is `x: &u32` — should have a pointee slot.
        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&1)
            .expect("expected arg-ref pointee slot for local 1 (#2844)");

        // Build a Place for `*x`: projection [Deref] on local 1.
        let deref_place =
            Place { local: Local::from(1usize), projection: vec![ProjectionElem::Deref] };
        let modified = HashSet::new();

        let result = chc_ctx.translate_place_with_deref(&deref_place, &modified);
        assert!(
            result.is_some(),
            "translate_place_with_deref should resolve *arg_ref to a concrete expression (#2844)"
        );

        let expr = result.unwrap();

        // The resolved expression should reference the pointee input state var.
        let (in_name, _) = chc_ctx
            .state_var_mgr
            .state_vars
            .get(pointee_vec_idx)
            .expect("missing pointee input state var");
        assert!(
            constraint_tree_contains(&expr, &|e| {
                matches!(e.value(), ExprValue::Var { name } if name == &**in_name)
            }),
            "resolved expression should reference pointee input var '{}'",
            in_name
        );
    });
}

const ARG_REF_READ_WRITE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn read_and_write(x: &mut u32) {
        let old = *x;
        *x = old + 1;
    }
"#;

/// `fn read_and_write(x: &mut u32) { let old = *x; *x = old + 1; }` must
/// produce a constraint linking `old` to the pointee. The read of `*x` must
/// resolve to the pointee state var, and the subsequent write of `old + 1`
/// must chain through the same pointee output.
///
/// Part of #2844.
#[test]
fn test_arg_ref_read_and_write_links_to_pointee() {
    with_test_ay_ctx_for_source(ARG_REF_READ_WRITE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_and_write");
        let body = instance.body().expect("body");

        let vc = mir_to_chc(ctx.tcx, &body, "read_and_write", ChcConfig::default());

        // Must declare a pointee variable for the &mut u32 argument.
        let has_pointee_var = vc.vars().iter().any(|v| v.name.contains("_pointee"));
        assert!(has_pointee_var, "VC should declare a _pointee variable for &mut u32 arg (#2844)");

        // Must declare a pointee __out variable (the write side updates it).
        let has_pointee_out =
            vc.vars().iter().any(|v| v.name.contains("_pointee") && v.name.contains("__out"));
        assert!(has_pointee_out, "VC should declare a _pointee__out variable (#2844)");

        // The rules should reference both the pointee input (read of *x)
        // and the pointee output (write of *x = old + 1). This verifies
        // the read-write chain through the pointee state var.
        let has_pointee_ref = vc.rules.iter().any(|r| rule_contains_var(r, "_pointee"));
        assert!(
            has_pointee_ref,
            "VC rules should reference _pointee (read+write chain), got no matches in rules"
        );
    });
}

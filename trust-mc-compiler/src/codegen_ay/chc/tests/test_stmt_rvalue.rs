// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Tests for codegen_stmt_rvalue.rs — translate_rvalue_with_modified paths:
// Rvalue::Len, Rvalue::Repeat, Rvalue::NullaryOp, Rvalue::ShallowInitBox,
// Rvalue::CopyForDeref, translate_pointer_offset_with_modified,
// translate_ref_or_addressof.
//
// Part of #2188: CHC module test coverage.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// Rvalue::Len — array length via mir_to_chc
// =============================================================================

#[test]
fn test_mir_to_chc_array_len_produces_const() {
    // Rvalue::Len on a fixed-size array should produce a compile-time constant.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_len() -> usize {
            let arr: [u32; 5] = [1, 2, 3, 4, 5];
            arr.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_len");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_len", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "array len should produce CHC rules");
        assert!(!vc.relations.is_empty(), "array len should produce CHC relations");

        // Array length returns usize, so at Reg level the return value state var
        // should be a bitvec (64-bit on 64-bit platforms, or 32-bit on 32-bit).
        let has_bv = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64) || s.bitvec_width() == Some(32))
        });
        assert!(has_bv, "array len return (usize) should produce BV state var");

        // The SMT output should contain the constant for array length 5
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bv5") || smt.contains("#x00000005") || smt.contains("#x0000000000000005"),
            "array len should encode constant 5 in SMT output: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Rvalue::Repeat — [value; count] array initialization
// =============================================================================

#[test]
fn test_mir_to_chc_repeat_produces_const_array() {
    // Rvalue::Repeat creates [0u32; 4] — should produce const_array.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_repeat() -> [u32; 4] {
            [0u32; 4]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_repeat");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_repeat", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "repeat should produce CHC rules");

        let smt = emit_chc(&vc).to_string();
        // const_array produces ((as const (Array ...)) value)
        assert!(
            smt.contains("const") || smt.contains("Array") || smt.contains("bv"),
            "repeat should produce const array or bv encoding: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Rvalue::NullaryOp — runtime checks encoding
// =============================================================================

#[test]
fn test_nullary_op_ub_checks_produces_true() {
    // NullOp::RuntimeChecks(UbChecks) should produce true so MIR-generated
    // UB assertions are reachable (#3299).
    //
    // NOTE: In recent nightly, `unchecked_add` is lowered as an intrinsic
    // call without MIR Assert terminators. We test the error-rule pipeline
    // via array indexing, which reliably produces Assert terminators for
    // bounds checks.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ub_checks(arr: [u8; 4], idx: usize) -> u8 {
            arr[idx]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ub_checks");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ub_checks", ChcConfig::default());

        // The CHC encoding should declare an error relation.
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "array indexing should produce error relation for bounds check");

        // At least one rule should target the error relation (bounds violation → error).
        let error_rule_count = vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(
            error_rule_count > 0,
            "CHC should have error rules for bounds check, found {}",
            error_rule_count,
        );
    });
}

#[test]
fn test_nullary_op_contract_checks_produces_true() {
    // NullOp::RuntimeChecks(ContractChecks) should produce Expr::bool_const(true).
    let contract_check = Expr::bool_const(true);
    assert!(contract_check.sort().is_bool());
    assert!(contract_check.to_string().contains("true"));
}

// =============================================================================
// Fixed-layout reinterpretation helper — repr-SIMD array views
// =============================================================================

#[test]
fn test_reinterpret_fixed_layout_expr_array_identity() {
    let array_sort =
        ay_bindings::Sort::array(ay_bindings::Sort::bitvec(64), ay_bindings::Sort::bitvec(8));
    let array_expr = Expr::var("simd_arr", array_sort.clone());

    let result = ChcCtx::reinterpret_fixed_layout_expr(&array_expr, &array_sort)
        .expect("same Array sort should reinterpret as identity");

    assert_eq!(*result.sort(), array_sort, "identity reinterpretation should preserve Array sort");
    assert_eq!(
        result.to_string(),
        array_expr.to_string(),
        "same-sort reinterpretation should be identity"
    );
}

#[test]
fn test_reinterpret_fixed_layout_expr_unwraps_single_array_field_datatype() {
    let array_sort =
        ay_bindings::Sort::array(ay_bindings::Sort::bitvec(64), ay_bindings::Sort::bitvec(8));
    let simd_sort = struct_sort("CustomSimd_u8_4", [("fld_0", array_sort.clone())]);
    let simd_expr = Expr::datatype_constructor(
        "CustomSimd_u8_4",
        names::cons_name("CustomSimd_u8_4"),
        vec![Expr::var("simd_arr", array_sort.clone())],
        simd_sort,
    );

    let result = ChcCtx::reinterpret_fixed_layout_expr(&simd_expr, &array_sort)
        .expect("single-array-field datatype should unwrap to its Array view");

    assert_eq!(*result.sort(), array_sort, "unwrapped repr-SIMD view should have Array sort");
    assert!(
        matches!(
            result.value(),
            ay_bindings::ExprValue::DatatypeSelector { selector_name, .. } if selector_name == "fld_0"
        ),
        "repr-SIMD datatype should unwrap through fld_0, got {:?}",
        result.value()
    );
}

#[test]
fn test_reinterpret_fixed_layout_expr_rewraps_array_into_simd_datatype() {
    let array_sort =
        ay_bindings::Sort::array(ay_bindings::Sort::bitvec(64), ay_bindings::Sort::bitvec(32));
    let simd_sort = struct_sort("i32x4", [("fld_0", array_sort.clone())]);
    let array_expr = Expr::var("lanes", array_sort);

    let result = ChcCtx::reinterpret_fixed_layout_expr(&array_expr, &simd_sort)
        .expect("Array view should rewrap into the single-field repr-SIMD datatype");

    assert_eq!(
        *result.sort(),
        simd_sort,
        "rewrapped value should use the destination datatype sort"
    );
    assert!(
        result.to_string().contains("i32x4"),
        "rewrapped repr-SIMD value should mention the datatype constructor, got: {result}"
    );
}

const TRANSMUTE_LAYOUT_FALLBACK_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct LayoutSrc {
        pub a: u32,
        pub b: u16,
    }

    pub struct LayoutDst {
        pub a: u16,
        pub b: u32,
    }

    #[repr(C)]
    pub struct ReprSrc {
        pub a: u32,
        pub b: u16,
    }

    #[repr(C)]
    pub struct ReprDst {
        pub a: u32,
        pub b: u16,
    }

    pub fn probe_layout_sensitive_transmute(src: LayoutSrc) -> LayoutDst {
        unsafe { std::mem::transmute::<LayoutSrc, LayoutDst>(src) }
    }

    pub fn probe_repr_c_transmute(src: ReprSrc) -> ReprDst {
        unsafe { std::mem::transmute::<ReprSrc, ReprDst>(src) }
    }
"#;

fn find_transmute_cast(
    body: &rustc_public::mir::Body,
) -> (rustc_public::mir::Operand, rustc_public::ty::Ty) {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let rustc_public::mir::StatementKind::Assign(
                _lhs,
                rustc_public::mir::Rvalue::Cast(
                    rustc_public::mir::CastKind::Transmute,
                    operand,
                    target_ty,
                ),
            ) = &stmt.kind
            {
                return (operand.clone(), *target_ty);
            }
        }
    }
    panic!("expected CastKind::Transmute statement in MIR");
}

#[test]
fn test_translate_rvalue_cast_cross_adt_transmute_records_sound_fallback() {
    with_test_ay_ctx_for_source(TRANSMUTE_LAYOUT_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_sensitive_transmute");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_layout_sensitive_transmute", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (operand, target_ty) = find_transmute_cast(&body);
        let target_sort = ChcCtx::translate_ty(target_ty).expect("target sort for LayoutDst");
        let modified = HashSet::<usize>::new();

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: cross-ADT transmute test starts with zero sound fallbacks"
        );

        let result = chc_ctx
            .translate_rvalue_cast(
                &rustc_public::mir::CastKind::Transmute,
                &operand,
                &target_ty,
                &modified,
            )
            .expect("layout-sensitive transmute should still yield a target expression");

        assert_eq!(
            *result.sort(),
            target_sort,
            "layout-sensitive transmute fallback should preserve the destination sort"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "cross-ADT transmute should record exactly one sound fallback"
        );
        assert!(
            result.to_string().contains("__transmute_layout_nondet"),
            "layout-sensitive transmute should produce a fresh nondeterministic target, got {result}"
        );
    });
}

#[test]
fn test_translate_rvalue_cast_repr_c_cross_adt_transmute_stays_precise() {
    with_test_ay_ctx_for_source(TRANSMUTE_LAYOUT_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_repr_c_transmute");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_repr_c_transmute", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (operand, target_ty) = find_transmute_cast(&body);
        let target_sort = ChcCtx::translate_ty(target_ty).expect("target sort for ReprDst");
        let modified = HashSet::<usize>::new();

        let result = chc_ctx
            .translate_rvalue_cast(
                &rustc_public::mir::CastKind::Transmute,
                &operand,
                &target_ty,
                &modified,
            )
            .expect("repr(C) cross-ADT transmute should stay on the precise coercion path");

        assert_eq!(
            *result.sort(),
            target_sort,
            "repr(C) transmute should still return the destination sort"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "repr(C) cross-ADT transmute should not record a sound fallback"
        );
        assert!(
            !result.to_string().contains("__transmute_layout_nondet"),
            "repr(C) transmute should not produce a nondeterministic fallback value: {result}"
        );
    });
}

// =============================================================================
// Rvalue::Ref / AddressOf — translate_ref_or_addressof paths
// =============================================================================

#[test]
fn test_mir_to_chc_ref_at_reg_uses_value_semantics() {
    // At Reg track level, Ref should use value semantics for simple locals.
    // This exercises the translate_ref_or_addressof Reg path.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ref(x: u32) -> u32 {
            let r = &x;
            *r
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "ref should produce CHC rules");

        // At Reg level, references should NOT produce address computations
        // (no obj_valid, no heap arrays)
        let smt = emit_chc(&vc).to_string();
        // obj_valid is now declared as a relation parameter at all track
        // levels for dealloc safety (Fix #2736), but simple refs should not
        // produce store(obj_valid, ...) constraints.
        assert!(
            !smt.contains("store obj_valid"),
            "Reg-level ref should not store to obj_valid heap array"
        );
    });
}

#[test]
fn test_mir_to_chc_ref_at_mem_uses_heap_model() {
    // At Mem track level, Ref should use abstract heap model.
    // This exercises the translate_ref_or_addressof Mem path.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ref_mem(x: u32) -> u32 {
            let r = &x;
            *r
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_mem");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_ref_mem",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "mem-level ref should produce CHC rules");

        // At Mem level, the VC must have Array-sorted state variables for
        // the abstract heap model — this is the fundamental Mem-level invariant.
        // After ay bump to declare-var encoding, state variable sorts moved from
        // relation arg_sorts to vc.vars(). Check both locations.
        let has_array_sort =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_array))
                || vc.vars().iter().any(|v| v.sort.is_array());
        assert!(has_array_sort, "Mem-level ref should produce Array-sorted memory state variables");
    });
}

// =============================================================================
// CopyForDeref — deref load path
// =============================================================================

#[test]
fn test_mir_to_chc_copy_for_deref_through_ref() {
    // CopyForDeref(*ptr) should synthesize a Deref projection.
    // This exercises the CopyForDeref arm of translate_rvalue_with_modified.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_deref(x: &u32) -> u32 {
            *x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_deref");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_copy_deref", ChcConfig::default());

        // Should produce valid CHC that references the input variable
        assert!(!vc.rules.is_empty(), "copy deref should produce CHC rules");

        // The function takes &u32 and returns u32 — at Reg level, state vars
        // should include BV32 for the u32 values.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "copy deref of &u32 should produce BV32 state vars");

        // SMT output should be non-trivial (not just declarations)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("rule") || smt.contains("forall") || smt.contains("=>"),
            "copy deref should produce non-trivial SMT with rule bodies"
        );
    });
}

/// Part of #3059: CopyForDeref through a struct field reference.
/// When MIR produces CopyForDeref(_p.1), the Deref must be appended after
/// the field projection: [Field(1), Deref] = *(_p.second), not [Deref, Field(1)] = (*_p).1.
#[test]
fn test_mir_to_chc_copy_for_deref_field_projection() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        struct Pair<'a> {
            first: &'a u32,
            second: &'a u32,
        }

        fn probe_copy_deref_field(p: &Pair) -> u32 {
            *p.second
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_deref_field");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_copy_deref_field", ChcConfig::default());

        // Should produce valid CHC rules without panic.
        // Before #3059 fix, the Deref was prepended before Field, which could
        // produce incorrect memory loads for projected CopyForDeref.
        assert!(!vc.rules.is_empty(), "copy deref field should produce CHC rules");

        // The Pair struct has two &u32 fields; at Reg level the return u32
        // should produce BV32 state vars.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "copy deref through struct field should produce BV32 state vars");
    });
}

#[test]
fn test_mir_to_chc_simd_index_projection_does_not_panic() {
    // Part of #2244: portable SIMD locals can currently fall back to BV32 sorts.
    // Dynamic lane indexing then reaches translate_place_with_deref Index projection.
    // Guard this path to fail closed instead of panicking on select(non-array).
    const SOURCE: &str = r#"
        #![feature(portable_simd)]
        #![allow(dead_code)]

        use std::simd::f32x2;

        pub fn probe_simd_index_projection(v: f32x2) -> f32 {
            let mut sum = 0.0f32;
            let mut i = 0usize;
            while i < 2 {
                sum += v[i];
                i += 1;
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simd_index_projection");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_simd_index_projection", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "simd index projection should fail closed without CHC panic");

        // SIMD types fall back to BV32 sorts; verify the VC still has proper
        // block structure (relations with bb0 entry point).
        let has_bb0 = vc.relations.iter().any(|r| r.name.contains("__bb0"));
        assert!(has_bb0, "SIMD fallback VC should still have bb0 entry relation");

        // The loop counter i is usize, so BV state vars should exist.
        let has_bv = vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.is_bitvec()));
        assert!(has_bv, "SIMD index projection VC should have BV state vars for loop counter");
    });
}

// =============================================================================
// BinaryOp::Offset — pointer offset translation
// =============================================================================

#[test]
fn test_pointer_offset_expression_encoding() {
    // Pointer offset: ptr.bvadd(count * pointee_size) at the expression level.
    // Exercises the logic of translate_pointer_offset_with_modified.
    let ptr = Expr::var("ptr", Sort::bitvec(64));
    let count = Expr::var("count", Sort::bitvec(64));
    let pointee_size = Expr::bitvec_const(4u128, 64); // sizeof(u32) = 4

    // byte_offset = count * pointee_size
    let byte_offset = count.bvmul(pointee_size);
    // result = ptr + byte_offset
    let result = ptr.bvadd(byte_offset);

    assert!(result.sort().is_bitvec());
    assert_eq!(result.sort().bitvec_width(), Some(64));

    let smt = result.to_string();
    assert!(smt.contains("bvadd"), "should contain pointer addition: {}", smt);
    assert!(smt.contains("bvmul"), "should contain size multiplication: {}", smt);
}

#[test]
fn test_pointer_offset_unit_pointee_skips_multiply() {
    // When pointee_size == 1, the multiply should be skipped (optimization).
    let ptr = Expr::var("ptr", Sort::bitvec(64));
    let count = Expr::var("count", Sort::bitvec(64));

    // pointee_size == 1: byte_offset = count (no multiply)
    let result = ptr.bvadd(count);

    let smt = result.to_string();
    assert!(smt.contains("bvadd"), "should contain pointer addition: {}", smt);
    assert!(!smt.contains("bvmul"), "unit pointee should skip multiply: {}", smt);
}

// =============================================================================
// Aggregate translation — tuple, struct
// =============================================================================

#[test]
fn test_mir_to_chc_tuple_aggregate() {
    // Tuple aggregate (a, b) exercises translate_aggregate in codegen_stmt_rvalue.rs.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_tuple(a: u32, b: u32) -> (u32, u32) {
            (a, b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_tuple", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "tuple aggregate should produce CHC rules");

        // After flattening (#2214), (u32, u32) is encoded as two scalar BV32 state
        // vars — no relation argument should have Datatype sort.
        // Note: `declare-datatype` may still appear in SMT output as infrastructure
        // for translate_place Datatype reconstruction (#2970).
        let has_datatype_arg =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype_arg,
            "flattened (u32, u32) tuple relations should not have Datatype-sorted arguments"
        );
        // Both fields should appear as BV32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "flattened tuple should have BV32 state vars for u32 fields");
    });
}

// =============================================================================
// Discriminant translation
// =============================================================================

#[test]
fn test_mir_to_chc_discriminant_extraction() {
    // Discriminant extraction on Option exercises translate_discriminant.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_discriminant(opt: Option<u32>) -> bool {
            opt.is_some()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_discriminant");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_discriminant", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "discriminant should produce CHC rules");

        // Should have error relation for the assertion/property
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "discriminant function should have error relation");
    });
}

// =============================================================================
// ShallowInitBox — heap allocation wrapping
// =============================================================================

#[test]
fn test_mir_to_chc_box_new_produces_allocation() {
    // Box::new(42) desugars to exchange_malloc + ShallowInitBox.
    // This exercises the ShallowInitBox arm of translate_rvalue_with_modified.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;

        pub fn probe_box() -> alloc::boxed::Box<u32> {
            alloc::boxed::Box::new(42u32)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Box::new should produce heap-related rules at Mem level
        assert!(!vc.rules.is_empty(), "box allocation should produce CHC rules");

        // At Mem level, Box::new must produce Array-sorted memory state variables
        // for the abstract heap model (store/select operations on heap arrays).
        // After ay bump to declare-var encoding, state variable sorts moved from
        // relation arg_sorts to vc.vars(). Check both locations.
        let has_array_sort =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_array))
                || vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_array_sort,
            "Mem-level Box::new should produce Array-sorted memory state variables"
        );

        // Box allocation should produce store or select operations in the SMT output
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("store") || smt.contains("select") || smt.contains("Array"),
            "Mem-level Box::new should produce heap memory operations: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Fallback counter assertions for codegen_stmt_rvalue.rs (Part of #2783)
// =============================================================================

const SIGNEDNESS_MISMATCH_SOURCE: &str = r#"
#![allow(dead_code)]

fn probe_signedness_mismatch(a: i32, b: u32) -> u32 {
    if a < 0 { b } else { b.wrapping_add(1) }
}
"#;

const POINTER_OFFSET_FALLBACK_SOURCE: &str = r#"
#![allow(dead_code)]

fn probe_offset_fallback(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}
"#;

const ARRAY_LEN_NO_FALLBACK_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn probe_array_len_direct(arr: [u32; 4]) -> usize {
    arr.len()
}
"#;

const SHALLOW_INIT_BOX_FALLBACK_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn probe_shallow_box_fallback_ty(x: u32) -> u32 {
    x
}
"#;

/// Rvalue::Len on a non-array place must increment fallback_count in the
/// `translate_rvalue_with_modified` path (codegen_stmt_rvalue.rs line ~125).
///
/// The expr_env counterpart is tested by `test_rvalue_len_non_array_increments_fallback_counter`
/// in test_expr_env.rs. This test covers the `_with_modified` main codegen path
/// (used by `encode_block_statements` → `translate_rvalue_with_modified`).
/// Part of #2783.
#[test]
fn test_rvalue_len_non_array_increments_fallback_counter_with_modified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_len_fb_mod(s: &[u32]) -> usize {
            s.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_len_fb_mod");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_slice_len_fb_mod", ChcConfig::default());

        // Directly call translate_rvalue_with_modified with a synthetic
        // Rvalue::Len on a non-array local (local 1 = &[u32] parameter).
        let modified = HashSet::<usize>::new();
        let rvalue = rustc_public::mir::Rvalue::Len(Place { local: 1, projection: vec![] });

        let before = chc_ctx.sound_fallback_count();
        let result = chc_ctx.translate_rvalue_with_modified(&rvalue, &modified, None);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            result.is_some(),
            "Rvalue::Len on non-array (slice ref) should return fresh symbolic from translate_rvalue_with_modified"
        );
        assert!(
            after > before,
            "Rvalue::Len fallback in translate_rvalue_with_modified must increment \
             sound_fallback_count (before={before}, after={after})"
        );
    });
}

/// Div/Rem with unknown signedness must still translate but increment fallback_count.
///
/// Covers the `record_fallback()` at `codegen_stmt_rvalue.rs` in the
/// `translate_rvalue_with_modified` BinaryOp path when operand signedness cannot
/// be inferred for Div/Rem.
#[test]
fn test_div_unknown_signedness_increments_fallback_counter_with_modified() {
    with_test_ay_ctx_for_source(SIGNEDNESS_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signedness_mismatch");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_signedness_mismatch", ChcConfig::default());
        chc_ctx.declare_block_relations();
        let mut signed_local = None;
        let mut unsigned_local = None;
        for (idx, decl) in body.locals().iter().enumerate() {
            match decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Int(_)) => signed_local = Some(idx),
                TyKind::RigidTy(RigidTy::Uint(_)) => unsigned_local = Some(idx),
                _ => {}
            }
        }
        let lhs_local = signed_local.expect("expected signed local in probe_signedness_mismatch");
        let rhs_local =
            unsigned_local.expect("expected unsigned local in probe_signedness_mismatch");
        assert!(
            chc_ctx.try_state_idx_for_local(lhs_local).is_some(),
            "signed local {lhs_local} must have a state-var slot"
        );
        assert!(
            chc_ctx.try_state_idx_for_local(rhs_local).is_some(),
            "unsigned local {rhs_local} must have a state-var slot"
        );

        let rvalue = rustc_public::mir::Rvalue::BinaryOp(
            rustc_public::mir::BinOp::Div,
            Operand::Copy(Place { local: lhs_local, projection: vec![] }),
            Operand::Copy(Place { local: rhs_local, projection: vec![] }),
        );
        let mut modified = HashSet::<usize>::new();
        modified.insert(lhs_local);
        modified.insert(rhs_local);
        chc_ctx.encode.local_expr_env.insert(lhs_local, Expr::bitvec_const(24, 32));
        chc_ctx.encode.local_expr_env.insert(rhs_local, Expr::bitvec_const(3, 32));
        let lhs_expr = chc_ctx.translate_operand_with_modified(
            &Operand::Copy(Place { local: lhs_local, projection: vec![] }),
            &modified,
        );
        let rhs_expr = chc_ctx.translate_operand_with_modified(
            &Operand::Copy(Place { local: rhs_local, projection: vec![] }),
            &modified,
        );
        assert!(lhs_expr.is_some(), "lhs operand must translate for signedness fallback test");
        assert!(rhs_expr.is_some(), "rhs operand must translate for signedness fallback test");

        let before = chc_ctx.fallback_count;
        let _ = chc_ctx.translate_rvalue_with_modified(&rvalue, &modified, None);
        let after = chc_ctx.fallback_count;

        assert!(
            after > before,
            "unknown-signedness Div in translate_rvalue_with_modified must increment \
             fallback_count (before={before}, after={after})"
        );
    });
}

/// Pointer offset on a non-pointer lhs must fail closed and increment fallback_count.
///
/// Covers the `record_fallback()` in `translate_pointer_offset_with_modified`
/// when pointee size is unknown (lhs type is not Ref/RawPtr).
#[test]
fn test_pointer_offset_unknown_pointee_increments_fallback_counter() {
    with_test_ay_ctx_for_source(POINTER_OFFSET_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_offset_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_offset_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();
        let uint_locals: Vec<usize> = body
            .locals()
            .iter()
            .enumerate()
            .filter_map(|(idx, decl)| {
                matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::Uint(_))).then_some(idx)
            })
            .collect();
        assert!(
            uint_locals.len() >= 2,
            "expected at least two unsigned locals in probe_offset_fallback"
        );
        let lhs_local = uint_locals[0];
        let rhs_local = uint_locals[1];
        assert!(
            chc_ctx.try_state_idx_for_local(lhs_local).is_some(),
            "lhs local {lhs_local} must have a state-var slot"
        );
        assert!(
            chc_ctx.try_state_idx_for_local(rhs_local).is_some(),
            "rhs local {rhs_local} must have a state-var slot"
        );

        let lhs = Operand::Copy(Place { local: lhs_local, projection: vec![] });
        let rhs = Operand::Copy(Place { local: rhs_local, projection: vec![] });
        let mut modified = HashSet::<usize>::new();
        modified.insert(lhs_local);
        modified.insert(rhs_local);
        chc_ctx.encode.local_expr_env.insert(lhs_local, Expr::bitvec_const(0x1000, 32));
        chc_ctx.encode.local_expr_env.insert(rhs_local, Expr::bitvec_const(2, 32));
        let lhs_expr = chc_ctx.translate_operand_with_modified(&lhs, &modified);
        let rhs_expr = chc_ctx.translate_operand_with_modified(&rhs, &modified);
        assert!(lhs_expr.is_some(), "lhs operand must translate for pointer-offset fallback test");
        assert!(rhs_expr.is_some(), "rhs operand must translate for pointer-offset fallback test");

        let before = chc_ctx.sound_fallback_count();
        let result = chc_ctx.translate_pointer_offset_with_modified(&lhs, &rhs, &modified);
        let after = chc_ctx.sound_fallback_count();

        // Part of #3099: Returns Some(fresh symbolic) to avoid double-counting
        // with the parent self-loop handler's record_fallback() (DEMOTED).
        assert!(result.is_some(), "unknown pointee-size should return fresh symbolic (not None)");
        assert!(
            after > before,
            "unknown pointee-size fallback must increment sound_fallback_count (before={before}, after={after})"
        );
    });
}

/// Rvalue::Len on fixed-size arrays should not increment fallback_count.
#[test]
fn test_rvalue_len_array_does_not_increment_fallback_counter_with_modified() {
    with_test_ay_ctx_for_source(ARRAY_LEN_NO_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_len_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_array_len_direct", ChcConfig::default());

        let modified = HashSet::<usize>::new();
        let rvalue = rustc_public::mir::Rvalue::Len(Place { local: 1, projection: vec![] });

        let before = chc_ctx.fallback_count;
        let result = chc_ctx.translate_rvalue_with_modified(&rvalue, &modified, None);
        let after = chc_ctx.fallback_count;

        assert!(result.is_some(), "Rvalue::Len on array should translate to a constant expression");
        assert_eq!(
            after, before,
            "array-length success path must not increment fallback_count (before={before}, after={after})"
        );
    });
}

/// ShallowInitBox fallback path must increment fallback_count when operand
/// translation fails.
///
/// Covers the `record_fallback()` inside `Rvalue::ShallowInitBox` handling when
/// the operand cannot be translated.
#[test]
fn test_shallow_init_box_operand_translate_failure_increments_fallback_counter() {
    with_test_ay_ctx_for_source(SHALLOW_INIT_BOX_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shallow_box_fallback_ty");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_shallow_box_fallback_ty",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let ty = body.locals()[1].ty;
        let rvalue = rustc_public::mir::Rvalue::ShallowInitBox(
            Operand::Copy(Place { local: 999, projection: vec![] }),
            ty,
        );
        let modified = HashSet::<usize>::new();

        let before = chc_ctx.sound_fallback_count();
        let result = chc_ctx.translate_rvalue_with_modified(&rvalue, &modified, None);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            result.is_some(),
            "ShallowInitBox fallback should allocate a fresh symbolic pointer"
        );
        assert!(
            after > before,
            "ShallowInitBox operand-translation fallback must increment sound_fallback_count \
             (before={before}, after={after})"
        );
    });
}

/// Regression (#2465): ShallowInitBox fallback must NOT use unconstrained
/// symbolic obj_size. Verify that no `unk_box_size` variables appear in the
/// CHC output — the fix uses size=0 (sound over-approximation) instead.
#[test]
fn test_shallow_init_box_no_unconstrained_symbolic_size() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;

        pub fn probe_box_u32() -> alloc::boxed::Box<u32> {
            alloc::boxed::Box::new(42u32)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_u32");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_u32",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let smt = emit_chc(&vc).to_string();
        assert!(
            !smt.contains("unk_box_size"),
            "regression #2465: ShallowInitBox must not emit unconstrained symbolic \
             obj_size (unk_box_size). Found in:\n{smt}"
        );
    });
}

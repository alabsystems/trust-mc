// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven unit tests for sort_inference.rs — ADT special-case paths and
//! compound types.
//!
//! Trivial tests that only constructed AY Sort/Expr values (Vec/String fld_data
//! array sort, IndexRange/PolymorphicIter struct construction, unit enum
//! discriminant width, RawVec two-field struct, global allocator bool sort,
//! BTreeMap Entry/VacantEntry/OccupiedEntry/Layout struct construction) were
//! removed per rule #2312 and #2482 because they did not exercise production
//! codegen paths.
//!
//! Part of #2016.

use super::*;
use crate::codegen_ay::names::{RUST_STRING_SORT, struct_sort};

// =============================================================================
// MIR-based Vec/String/RawVec sort inference
// =============================================================================

const VEC_STRING_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn vec_string_probe(v: Vec<i32>, s: String, v64: Vec<u64>) {}
"#;

/// Test infer_sort_from_ty for Vec<i32> — should produce Vec_bv32 struct sort
/// with (fld_ptr, fld_len, fld_cap, fld_data) fields.
#[test]
fn test_infer_sort_vec_i32_via_mir() {
    with_test_ay_ctx_for_source(VEC_STRING_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "vec_string_probe");
        let body = instance.body().expect("body");

        // Find Vec<i32> local
        let vec_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
                    let name = def.trimmed_name();
                    (name == "Vec" || name.ends_with("::Vec"))
                        && args
                            .0
                            .first()
                            .is_some_and(|a| {
                                matches!(a, rustc_public::ty::GenericArgKind::Type(t)
                                    if matches!(t.kind(), TyKind::RigidTy(RigidTy::Int(rustc_public::ty::IntTy::I32))))
                            })
                } else {
                    false
                }
            })
            .expect("missing Vec<i32> local");

        let sort = StatementCodegen::infer_sort_from_ty(vec_ty)
            .expect("infer_sort_from_ty should succeed for Vec<i32>");
        assert!(sort.is_datatype(), "Vec<i32> should be datatype, got {:?}", sort);

        let name = sort.datatype_name().unwrap().to_string();
        assert!(name.contains("Vec"), "Vec sort name should contain 'Vec', got {name}");

        // Should have fld_ptr, fld_len, fld_cap, fld_data fields
        let v = Expr::var("v", sort);
        let ptr = v.clone().field_select(&name, "fld_ptr", Sort::bitvec(POINTER_WIDTH));
        let len = v.clone().field_select(&name, "fld_len", Sort::bitvec(POINTER_WIDTH));
        let cap = v.field_select(&name, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(len.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(cap.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test infer_sort_from_ty for String — should produce String struct sort.
#[test]
fn test_infer_sort_string_via_mir() {
    with_test_ay_ctx_for_source(VEC_STRING_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "vec_string_probe");
        let body = instance.body().expect("body");

        let string_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    let name = def.trimmed_name();
                    name == "String" || name.ends_with("::String")
                } else {
                    false
                }
            })
            .expect("missing String local");

        let sort = StatementCodegen::infer_sort_from_ty(string_ty)
            .expect("infer_sort_from_ty should succeed for String");
        assert!(sort.is_datatype(), "String should be datatype, got {:?}", sort);
        assert_eq!(sort.datatype_name(), Some(RUST_STRING_SORT));

        // String has same 4-field layout as Vec<u8>
        let s = Expr::var("s", sort);
        let ptr = s.clone().field_select(RUST_STRING_SORT, "fld_ptr", Sort::bitvec(POINTER_WIDTH));
        let len = s.clone().field_select(RUST_STRING_SORT, "fld_len", Sort::bitvec(POINTER_WIDTH));
        let cap = s.field_select(RUST_STRING_SORT, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(len.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(cap.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test that Vec<i32> and Vec<u64> produce different sort names.
#[test]
fn test_vec_sort_name_varies_by_element_type() {
    with_test_ay_ctx_for_source(VEC_STRING_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "vec_string_probe");
        let body = instance.body().expect("body");

        let mut vec_sorts: Vec<String> = Vec::new();
        for local in body.locals() {
            if let TyKind::RigidTy(RigidTy::Adt(def, _)) = local.ty.kind() {
                let name = def.trimmed_name();
                if (name == "Vec" || name.ends_with("::Vec"))
                    && let Some(sort) = StatementCodegen::infer_sort_from_ty(local.ty)
                    && let Some(dt_name) = sort.datatype_name()
                {
                    vec_sorts.push(dt_name.to_string());
                }
            }
        }

        assert!(vec_sorts.len() >= 2, "should find at least 2 Vec locals");
        // Names should differ (Vec_bv32 vs Vec_bv64)
        let unique: std::collections::HashSet<_> = vec_sorts.iter().collect();
        assert!(unique.len() >= 2, "Vec sort names should differ: {:?}", vec_sorts);
    });
}

// =============================================================================
// CheckedBinaryOp compound type inference
// =============================================================================

const CHECKED_OP_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn checked_add_probe(a: u32, b: u32) -> (u32, bool) {
    a.checked_add(b).map_or((0, true), |v| (v, false))
}

pub fn checked_add_u8(a: u8, b: u8) -> (u8, bool) {
    a.checked_add(b).map_or((0, true), |v| (v, false))
}

pub fn triple_probe() -> (u32, u64, bool) {
    (1u32, 2u64, true)
}
"#;

/// Test try_infer_sort_from_compound_ty for (u32, bool) — CheckedBinaryOp pattern.
/// Should pack into bitvec(33) = bitvec(32 + 1).
#[test]
fn test_compound_checked_u32_bool_packs_to_bv33() {
    with_test_ay_ctx_for_source(CHECKED_OP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_add_probe");
        let body = instance.body().expect("body");

        // The return type is (u32, bool) — find it
        let ret_ty = body.locals()[0].ty; // local 0 is return
        let sort = StatementCodegen::try_infer_sort_from_compound_ty(ret_ty)
            .expect("(u32, bool) should produce a sort");
        // (u32, bool) should pack to bitvec(33) for CheckedBinaryOp
        assert!(sort.is_bitvec(), "(u32, bool) should pack to bitvec, got {:?}", sort);
        assert_eq!(sort.bitvec_width(), Some(33));
    });
}

/// Test try_infer_sort_from_compound_ty for (u8, bool) — packs to bitvec(9).
#[test]
fn test_compound_checked_u8_bool_packs_to_bv9() {
    with_test_ay_ctx_for_source(CHECKED_OP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_add_u8");
        let body = instance.body().expect("body");

        let ret_ty = body.locals()[0].ty;
        let sort = StatementCodegen::try_infer_sort_from_compound_ty(ret_ty)
            .expect("(u8, bool) should produce a sort");
        // (u8, bool) should pack to bitvec(9) for CheckedBinaryOp
        assert!(sort.is_bitvec(), "(u8, bool) should pack to bitvec, got {:?}", sort);
        assert_eq!(sort.bitvec_width(), Some(9));
    });
}

/// Test try_infer_sort_from_compound_ty for (u32, u64, bool) — NOT a checked op pattern.
/// Should fall through to normal tuple sort.
#[test]
fn test_compound_triple_falls_through_to_tuple() {
    with_test_ay_ctx_for_source(CHECKED_OP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "triple_probe");
        let body = instance.body().expect("body");

        let ret_ty = body.locals()[0].ty;
        let sort = StatementCodegen::try_infer_sort_from_compound_ty(ret_ty)
            .expect("(u32, u64, bool) should produce a sort");
        // 3-element tuple is not a CheckedBinaryOp pattern
        assert!(sort.is_datatype(), "triple should be tuple struct, got {:?}", sort);
    });
}

// =============================================================================
// resolve_generic_ty edge cases (standalone tests via MIR context)
// =============================================================================

const GENERIC_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn generic_probe(x: u32) -> u32 { x }
"#;

/// Test resolve_generic_ty passes non-generic types through unchanged.
#[test]
fn test_resolve_generic_ty_passthrough_for_concrete() {
    with_test_ay_ctx_for_source(GENERIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "generic_probe");
        let body = instance.body().expect("body");

        // Local 1 is the parameter x: u32
        let ty = body.locals()[1].ty;
        assert!(matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::U32))));

        // Empty args — concrete type should pass through resolve_generic_ty
        let args = rustc_public::ty::GenericArgs(vec![]);
        let resolved = StatementCodegen::resolve_generic_ty(ty, &args);
        assert!(resolved.is_some(), "concrete type should pass through");
        assert_eq!(resolved.unwrap().kind(), ty.kind());
    });
}

// =============================================================================
// Standalone sort construction tests (no MIR context)
// =============================================================================

/// Test slice_sort element sort is correctly embedded in name.
#[test]
fn test_slice_sort_int_element() {
    let int_slice = StatementCodegen::slice_sort(Sort::int());
    assert!(int_slice.is_datatype());
    assert_eq!(int_slice.datatype_name(), Some("Slice_int"));
}

/// Test dyn_sort with different trait names.
#[test]
fn test_dyn_sort_different_traits() {
    let display = StatementCodegen::dyn_sort("Display");
    let debug = StatementCodegen::dyn_sort("Debug");
    let any = StatementCodegen::dyn_sort("Any");

    assert_eq!(display.datatype_name(), Some("Dyn_Display"));
    assert_eq!(debug.datatype_name(), Some("Dyn_Debug"));
    assert_eq!(any.datatype_name(), Some("Dyn_Any"));

    // All should have the same structure (ptr + vtable)
    for sort in [&display, &debug, &any] {
        assert!(sort.is_datatype());
    }
}

/// Test tuple_sort_name with multiple fields of different sorts.
#[test]
fn test_tuple_sort_name_mixed_sorts() {
    let fields = vec![("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bool()), ("fld_2", Sort::int())];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_bv32_bool_int");
}

/// Test tuple_sort_name with array and datatype elements.
#[test]
fn test_tuple_sort_name_with_array() {
    let arr = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let fields = vec![("fld_0", arr), ("fld_1", Sort::bitvec(64))];
    let name = StatementCodegen::tuple_sort_name(&fields);
    // Array sort should appear in the tuple name
    assert!(name.starts_with("Tuple_"));
    assert!(name.contains("bv64"));
}

// =============================================================================
// infer_sort_from_ty: array and slice bare types (via MIR)
// =============================================================================

const ARRAY_SLICE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn array_slice_probe(arr: [u16; 4], slice: &[u64]) {}
"#;

/// Test infer_sort_from_ty for [u16; 4] → Array(bitvec(POINTER_WIDTH), bitvec(16)).
#[test]
fn test_infer_sort_array_u16() {
    with_test_ay_ctx_for_source(ARRAY_SLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_slice_probe");
        let body = instance.body().expect("body");

        // Local 1: arr: [u16; 4]
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("array sort");
        assert!(sort.is_array(), "array type should produce array sort, got {:?}", sort);
    });
}

/// Test infer_sort_from_ty for bare slice type [u64] → Slice_bv64.
#[test]
fn test_infer_sort_slice_ref_u64() {
    with_test_ay_ctx_for_source(ARRAY_SLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_slice_probe");
        let body = instance.body().expect("body");

        // Local 2: slice: &[u64] — reference to slice
        let ty = body.locals()[2].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("slice ref sort");
        assert!(sort.is_datatype(), "slice ref should be fat pointer datatype");
        assert_eq!(sort.datatype_name(), Some("Slice_bv64"));
    });
}

// =============================================================================
// infer_sort_from_ty: float types (via MIR)
// =============================================================================

const FLOAT_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn float_probe(f32_val: f32, f64_val: f64) {}
"#;

/// Test infer_sort_from_ty for f32 → bitvec(32).
#[test]
fn test_infer_sort_f32() {
    with_test_ay_ctx_for_source(FLOAT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "float_probe");
        let body = instance.body().expect("body");

        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("f32 sort");
        assert!(sort.is_bitvec());
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

/// Test infer_sort_from_ty for f64 → bitvec(64).
#[test]
fn test_infer_sort_f64() {
    with_test_ay_ctx_for_source(FLOAT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "float_probe");
        let body = instance.body().expect("body");

        let ty = body.locals()[2].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("f64 sort");
        assert!(sort.is_bitvec());
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

// =============================================================================
// view_sort_from_ty: None cases (via MIR)
// =============================================================================

const VIEW_SORT_NONE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn view_sort_none_probe(f: f64, ptr: *const u32) {}
"#;

/// Test view_sort_from_ty returns None for f64 (not a "viewable" type).
#[test]
fn test_view_sort_f64_returns_none() {
    with_test_ay_ctx_for_source(VIEW_SORT_NONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_none_probe");
        let body = instance.body().expect("body");

        let ty = body.locals()[1].ty;
        assert!(
            StatementCodegen::view_sort_from_ty(ty).is_none(),
            "f64 should not have a view sort"
        );
    });
}

/// Test view_sort_from_ty returns None for raw pointer.
#[test]
fn test_view_sort_raw_ptr_returns_none() {
    with_test_ay_ctx_for_source(VIEW_SORT_NONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_none_probe");
        let body = instance.body().expect("body");

        let ty = body.locals()[2].ty;
        assert!(
            StatementCodegen::view_sort_from_ty(ty).is_none(),
            "raw pointer should not have a view sort"
        );
    });
}

// =============================================================================
// infer_sort_from_ty: char type (via MIR)
// =============================================================================

const CHAR_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn char_probe(c: char) {}
"#;

/// Test infer_sort_from_ty for char → bitvec(32).
#[test]
fn test_infer_sort_char() {
    with_test_ay_ctx_for_source(CHAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "char_probe");
        let body = instance.body().expect("body");

        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("char sort");
        assert!(sort.is_bitvec());
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

// =============================================================================
// codegen_sort.rs: unwrap_tuple_first_field (#1582)
// =============================================================================

/// Single-field datatype with bitvec field is unwrapped to the inner bitvec.
#[test]
fn test_unwrap_tuple_single_bv_field() {
    let sort = struct_sort("Closure_env", [("fld_0", Sort::bitvec(32))]);
    let expr = Expr::var("closure_env", sort);
    let unwrapped = StatementCodegen::unwrap_tuple_first_field(expr);
    assert_eq!(
        unwrapped.sort().bitvec_width(),
        Some(32),
        "single-field closure env should unwrap to bv32"
    );
}

/// Multi-field datatype is NOT unwrapped (#1590).
#[test]
fn test_unwrap_tuple_multi_field_not_unwrapped() {
    let sort =
        struct_sort("Tuple_bv32_bv32", [("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bitvec(32))]);
    let expr = Expr::var("tuple_var", sort.clone());
    let unwrapped = StatementCodegen::unwrap_tuple_first_field(expr);
    assert_eq!(*unwrapped.sort(), sort, "multi-field tuple must not be unwrapped");
}

/// Non-datatype expressions pass through unchanged.
#[test]
fn test_unwrap_tuple_bitvec_passthrough() {
    let expr = Expr::var("x", Sort::bitvec(64));
    let unwrapped = StatementCodegen::unwrap_tuple_first_field(expr);
    assert_eq!(unwrapped.sort().bitvec_width(), Some(64));
}

/// Single-field datatype with bool field is NOT unwrapped (only bitvec triggers).
#[test]
fn test_unwrap_tuple_single_bool_field_unchanged() {
    let sort = struct_sort("Closure_bool", [("fld_0", Sort::bool())]);
    let expr = Expr::var("closure_bool", sort.clone());
    let unwrapped = StatementCodegen::unwrap_tuple_first_field(expr);
    assert_eq!(*unwrapped.sort(), sort);
}

/// Single-field datatype with Int field is NOT unwrapped (only bitvec triggers).
#[test]
fn test_unwrap_tuple_single_int_field_unchanged() {
    let sort = struct_sort("Wrapper_int", [("fld_0", Sort::int())]);
    let expr = Expr::var("wrapper_int", sort.clone());
    let unwrapped = StatementCodegen::unwrap_tuple_first_field(expr);
    assert_eq!(*unwrapped.sort(), sort);
}

// =============================================================================
// codegen_sort.rs: coerce_to_match_widths_typed
// =============================================================================

/// Same-width bitvecs: no coercion needed.
#[test]
fn test_coerce_typed_same_width() {
    let lhs = Expr::var("a", Sort::bitvec(32));
    let rhs = Expr::var("b", Sort::bitvec(32));
    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert_eq!(l.sort().bitvec_width(), Some(32));
    assert_eq!(r.sort().bitvec_width(), Some(32));
}

/// Unsigned widening: 8-bit zero-extended to 32-bit.
#[test]
fn test_coerce_typed_unsigned_widen() {
    let lhs = Expr::var("narrow", Sort::bitvec(8));
    let rhs = Expr::var("wide", Sort::bitvec(32));
    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert_eq!(l.sort().bitvec_width(), Some(32), "narrow should widen to 32");
    assert_eq!(r.sort().bitvec_width(), Some(32));
}

/// Signed widening: 16-bit sign-extended to 64-bit.
#[test]
fn test_coerce_typed_signed_widen() {
    let lhs = Expr::var("narrow", Sort::bitvec(16));
    let rhs = Expr::var("wide", Sort::bitvec(64));
    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, true);
    assert_eq!(l.sort().bitvec_width(), Some(64), "narrow should sign-extend to 64");
    assert_eq!(r.sort().bitvec_width(), Some(64));
}

/// Int + BitVec mixed: both convert to Int (#1043).
#[test]
fn test_coerce_typed_int_bv_to_int() {
    let lhs = Expr::int_const(42);
    let rhs = Expr::var("bv_val", Sort::bitvec(32));
    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert!(l.sort().is_int(), "lhs should stay Int");
    assert!(r.sort().is_int(), "bv should convert to Int via bv2int");
}

/// Both Int: returned unchanged.
#[test]
fn test_coerce_typed_both_int_unchanged() {
    let lhs = Expr::int_const(1);
    let rhs = Expr::int_const(2);
    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
}

/// Single-field tuple + bitvec: tuple unwrapped then widths matched (#1582).
#[test]
fn test_coerce_typed_closure_env_unwrap() {
    let closure_sort = struct_sort("Closure_env", [("fld_0", Sort::bitvec(8))]);
    let lhs = Expr::var("env", closure_sort);
    let rhs = Expr::var("wide", Sort::bitvec(32));
    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    // After unwrapping: bv8 vs bv32, then coerce to 32
    assert_eq!(l.sort().bitvec_width(), Some(32));
    assert_eq!(r.sort().bitvec_width(), Some(32));
}

// =============================================================================
// codegen_sort.rs: MIR-driven checked binary op dispatch
// =============================================================================

/// Probe source: tuple return values that exercise codegen_sort.rs tuple handling.
const TUPLE_CODEGEN_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn pair_u32_bool(a: u32, b: bool) -> (u32, bool) {
    (a, b)
}

pub fn triple_u32(a: u32, b: u32, c: u32) -> (u32, u32, u32) {
    (a, b, c)
}

pub fn unit_fn() -> () {}
"#;

/// Count Aggregate rvalues and run full codegen.
fn run_tuple_codegen(ctx: &mut AYCtx<'_, 'static>, fn_name: &str) -> usize {
    let instance = find_instance_by_suffix(ctx, fn_name);
    let body = instance.body().expect("body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    let mut aggregate_count = 0;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(_, Rvalue::Aggregate(..)) = &stmt.kind {
                aggregate_count += 1;
            }
            codegen.codegen_statement(stmt);
        }
        let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
    }
    aggregate_count
}

/// (u32, bool) tuple generates Aggregate rvalue and codegen completes.
#[test]
fn test_mir_pair_u32_bool_aggregate() {
    with_test_ay_ctx_for_source(TUPLE_CODEGEN_SOURCE, |mut ctx| {
        let count = run_tuple_codegen(&mut ctx, "pair_u32_bool");
        assert!(count >= 1, "pair (u32, bool) should have Aggregate rvalue, got {count}");
    });
}

/// (u32, u32, u32) triple generates Aggregate rvalue and codegen completes.
#[test]
fn test_mir_triple_u32_aggregate() {
    with_test_ay_ctx_for_source(TUPLE_CODEGEN_SOURCE, |mut ctx| {
        let count = run_tuple_codegen(&mut ctx, "triple_u32");
        assert!(count >= 1, "triple (u32,u32,u32) should have Aggregate, got {count}");
    });
}

/// Unit function codegen completes without Aggregate rvalues.
#[test]
fn test_mir_unit_fn_no_aggregate() {
    with_test_ay_ctx_for_source(TUPLE_CODEGEN_SOURCE, |mut ctx| {
        let count = run_tuple_codegen(&mut ctx, "unit_fn");
        assert_eq!(count, 0, "unit fn should have no Aggregate, got {count}");
    });
}

// =============================================================================
// view_sort_from_ty: positive cases (via MIR)
// =============================================================================

const VIEW_SORT_POS_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn view_sort_probe(i: i32, u: u64, c: char, b: bool, s: i8, z: usize) {}
"#;

/// Test view_sort_from_ty for signed integer → (Int, true).
#[test]
fn test_view_sort_i32_returns_int_signed() {
    with_test_ay_ctx_for_source(VIEW_SORT_POS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_probe");
        let body = instance.body().expect("body");

        // Local 1: i: i32
        let ty = body.locals()[1].ty;
        let (sort, is_signed) =
            StatementCodegen::view_sort_from_ty(ty).expect("i32 should have view sort");
        assert!(sort.is_int(), "i32 view sort should be Int");
        assert!(is_signed, "i32 should be signed");
    });
}

/// Test view_sort_from_ty for unsigned integer → (Int, false).
#[test]
fn test_view_sort_u64_returns_int_unsigned() {
    with_test_ay_ctx_for_source(VIEW_SORT_POS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_probe");
        let body = instance.body().expect("body");

        // Local 2: u: u64
        let ty = body.locals()[2].ty;
        let (sort, is_signed) =
            StatementCodegen::view_sort_from_ty(ty).expect("u64 should have view sort");
        assert!(sort.is_int(), "u64 view sort should be Int");
        assert!(!is_signed, "u64 should be unsigned");
    });
}

/// Test view_sort_from_ty for char → (Int, false).
#[test]
fn test_view_sort_char_returns_int_unsigned() {
    with_test_ay_ctx_for_source(VIEW_SORT_POS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_probe");
        let body = instance.body().expect("body");

        // Local 3: c: char
        let ty = body.locals()[3].ty;
        let (sort, is_signed) =
            StatementCodegen::view_sort_from_ty(ty).expect("char should have view sort");
        assert!(sort.is_int(), "char view sort should be Int");
        assert!(!is_signed, "char should be unsigned");
    });
}

/// Test view_sort_from_ty for bool → (Bool, false).
#[test]
fn test_view_sort_bool_returns_bool_unsigned() {
    with_test_ay_ctx_for_source(VIEW_SORT_POS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_probe");
        let body = instance.body().expect("body");

        // Local 4: b: bool
        let ty = body.locals()[4].ty;
        let (sort, is_signed) =
            StatementCodegen::view_sort_from_ty(ty).expect("bool should have view sort");
        assert!(sort.is_bool(), "bool view sort should be Bool");
        assert!(!is_signed, "bool should be unsigned");
    });
}

/// Test view_sort_from_ty for i8 → (Int, true) — covers small signed.
#[test]
fn test_view_sort_i8_returns_int_signed() {
    with_test_ay_ctx_for_source(VIEW_SORT_POS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_probe");
        let body = instance.body().expect("body");

        // Local 5: s: i8
        let ty = body.locals()[5].ty;
        let (sort, is_signed) =
            StatementCodegen::view_sort_from_ty(ty).expect("i8 should have view sort");
        assert!(sort.is_int(), "i8 view sort should be Int");
        assert!(is_signed, "i8 should be signed");
    });
}

/// Test view_sort_from_ty for usize → (Int, false) — covers pointer-width unsigned.
#[test]
fn test_view_sort_usize_returns_int_unsigned() {
    with_test_ay_ctx_for_source(VIEW_SORT_POS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_probe");
        let body = instance.body().expect("body");

        // Local 6: z: usize
        let ty = body.locals()[6].ty;
        let (sort, is_signed) =
            StatementCodegen::view_sort_from_ty(ty).expect("usize should have view sort");
        assert!(sort.is_int(), "usize view sort should be Int");
        assert!(!is_signed, "usize should be unsigned");
    });
}

// =============================================================================
// Option-like enum sort inference (via MIR)
// =============================================================================

const OPTION_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn option_probe(x: Option<u32>, y: Option<bool>) {}
"#;

/// Test infer_sort_from_ty for Option<u32> — should produce enum_type with
/// None (no fields) and Some (value: bv32) constructors.
#[test]
fn test_infer_sort_option_u32_via_mir() {
    with_test_ay_ctx_for_source(OPTION_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_probe");
        let body = instance.body().expect("body");

        // Local 1: x: Option<u32>
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Option<u32>");
        assert!(sort.is_datatype(), "Option<u32> should be datatype, got {:?}", sort);

        // Option-like enum: should be an enum_type, not struct_type
        let dt_name = sort.datatype_name().unwrap();
        assert!(
            dt_name.contains("Option"),
            "Option sort name should contain 'Option', got {dt_name}"
        );
    });
}

/// Test infer_sort_from_ty for Option<bool> — different payload sort.
#[test]
fn test_infer_sort_option_bool_via_mir() {
    with_test_ay_ctx_for_source(OPTION_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_probe");
        let body = instance.body().expect("body");

        // Local 2: y: Option<bool>
        let ty = body.locals()[2].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Option<bool>");
        assert!(sort.is_datatype(), "Option<bool> should be datatype, got {:?}", sort);
    });
}

// =============================================================================
// User-defined struct sort inference (via MIR)
// =============================================================================

const STRUCT_SOURCE: &str = r#"
#![allow(dead_code)]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

pub struct Pair<T> {
    pub first: T,
    pub second: T,
}

pub fn struct_probe(p: Point, pair: Pair<u64>) {}
"#;

/// Test infer_sort_from_ty for user-defined struct with named fields.
#[test]
fn test_infer_sort_struct_named_fields_via_mir() {
    with_test_ay_ctx_for_source(STRUCT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "struct_probe");
        let body = instance.body().expect("body");

        // Local 1: p: Point
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Point");
        assert!(sort.is_datatype(), "Point should be datatype, got {:?}", sort);

        let dt_name = sort.datatype_name().unwrap().to_string();
        assert!(
            dt_name.contains("Point"),
            "struct sort name should contain 'Point', got {dt_name}"
        );

        // Should have fld_x, fld_y fields with bv32
        let p = Expr::var("p", sort);
        let fld_x = p.clone().field_select(&dt_name, "fld_x", Sort::bitvec(32));
        let fld_y = p.field_select(&dt_name, "fld_y", Sort::bitvec(32));
        assert_eq!(fld_x.sort().bitvec_width(), Some(32));
        assert_eq!(fld_y.sort().bitvec_width(), Some(32));
    });
}

/// Test infer_sort_from_ty for generic struct Pair<u64>.
#[test]
fn test_infer_sort_generic_struct_via_mir() {
    with_test_ay_ctx_for_source(STRUCT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "struct_probe");
        let body = instance.body().expect("body");

        // Local 2: pair: Pair<u64>
        let ty = body.locals()[2].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Pair<u64>");
        assert!(sort.is_datatype(), "Pair<u64> should be datatype, got {:?}", sort);

        let dt_name = sort.datatype_name().unwrap().to_string();
        // Fields should be fld_first and fld_second with bv64
        let p = Expr::var("pair", sort);
        let first = p.clone().field_select(&dt_name, "fld_first", Sort::bitvec(64));
        let second = p.field_select(&dt_name, "fld_second", Sort::bitvec(64));
        assert_eq!(first.sort().bitvec_width(), Some(64));
        assert_eq!(second.sort().bitvec_width(), Some(64));
    });
}

// =============================================================================
// General enum with fields (Result-like) sort inference (via MIR)
// =============================================================================

const RESULT_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn result_probe(r: Result<u32, bool>) {}
"#;

/// Test infer_sort_from_ty for Result<u32, bool> — general enum with fields
/// in multiple variants.
#[test]
fn test_infer_sort_result_enum_via_mir() {
    with_test_ay_ctx_for_source(RESULT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_probe");
        let body = instance.body().expect("body");

        // Local 1: r: Result<u32, bool>
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Result<u32, bool>");
        assert!(sort.is_datatype(), "Result should be datatype, got {:?}", sort);

        let dt_name = sort.datatype_name().unwrap().to_string();
        assert!(
            dt_name.contains("Result"),
            "Result sort name should contain 'Result', got {dt_name}"
        );
    });
}

// =============================================================================
// Unit enum sort inference (via MIR)
// =============================================================================

const UNIT_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
pub enum Direction {
    North,
    South,
    East,
    West,
}

pub fn unit_enum_probe(d: Direction) {}
"#;

/// Test infer_sort_from_ty for user-defined unit enum — should produce bitvec(32).
#[test]
fn test_infer_sort_unit_enum_via_mir() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "unit_enum_probe");
        let body = instance.body().expect("body");

        // Local 1: d: Direction
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Direction");
        assert!(sort.is_bitvec(), "unit enum should be bitvec, got {:?}", sort);
        assert_eq!(sort.bitvec_width(), Some(32), "unit enum discriminant should be 32-bit");
    });
}

// =============================================================================
// Empty tuple → Unit struct (via MIR)
// =============================================================================

const EMPTY_TUPLE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn empty_tuple_probe() -> () {}
"#;

/// Test infer_tuple_sort for empty tuple → Unit struct type.
#[test]
fn test_infer_sort_empty_tuple_via_mir() {
    with_test_ay_ctx_for_source(EMPTY_TUPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "empty_tuple_probe");
        let body = instance.body().expect("body");

        // Local 0: return type ()
        let ret_ty = body.locals()[0].ty;
        if let TyKind::RigidTy(RigidTy::Tuple(tys)) = ret_ty.kind() {
            let sort =
                StatementCodegen::infer_tuple_sort(&tys).expect("empty tuple should produce Unit");
            assert!(sort.is_datatype(), "Unit should be datatype, got {:?}", sort);
            assert_eq!(sort.datatype_name(), Some("Unit"));
        }
        // rustc may optimize away the unit return; both paths are valid
    });
}

// =============================================================================
// &str and &dyn Trait sort inference (via MIR)
// =============================================================================

const STR_DYN_SOURCE: &str = r#"
#![allow(dead_code)]

pub trait MyTrait {
    fn dummy(&self);
}

pub fn str_probe(s: &str) {}
pub fn dyn_probe(d: &dyn MyTrait) {}
"#;

/// Test infer_sort_from_ty for &str → Slice_bv8 fat pointer.
#[test]
fn test_infer_sort_str_ref_via_mir() {
    with_test_ay_ctx_for_source(STR_DYN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "str_probe");
        let body = instance.body().expect("body");

        // Local 1: s: &str
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for &str");
        assert!(sort.is_datatype(), "&str should be fat pointer datatype, got {:?}", sort);
        assert_eq!(sort.datatype_name(), Some("Slice_bv8"), "&str should produce Slice_bv8 sort");
    });
}

/// Test infer_sort_from_ty for &dyn Trait → Dyn_Trait fat pointer.
#[test]
fn test_infer_sort_dyn_trait_ref_via_mir() {
    with_test_ay_ctx_for_source(STR_DYN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "dyn_probe");
        let body = instance.body().expect("body");

        // Local 1: d: &dyn MyTrait
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for &dyn Trait");
        assert!(sort.is_datatype(), "&dyn Trait should be fat pointer datatype, got {:?}", sort);
        assert_eq!(
            sort.datatype_name(),
            Some("Dyn_Trait"),
            "&dyn Trait should produce Dyn_Trait sort"
        );
    });
}

// =============================================================================
// try_infer_sort_from_compound_ty edge cases (via MIR)
// =============================================================================

const COMPOUND_EDGE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn pair_no_bool_probe() -> (u32, u64) { (1, 2) }
"#;

/// Test try_infer_sort_from_compound_ty for (u32, u64) — 2-element tuple
/// where second element is NOT bool. Should fall through to tuple sort.
#[test]
fn test_compound_pair_non_bool_falls_through() {
    with_test_ay_ctx_for_source(COMPOUND_EDGE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "pair_no_bool_probe");
        let body = instance.body().expect("body");

        let ret_ty = body.locals()[0].ty;
        let sort = StatementCodegen::try_infer_sort_from_compound_ty(ret_ty)
            .expect("(u32, u64) should produce a sort");
        // Should NOT pack to bitvec since second element is u64, not bool
        assert!(
            sort.is_datatype(),
            "(u32, u64) should produce tuple struct, not bitvec; got {:?}",
            sort
        );
    });
}

// =============================================================================
// MaybeUninit transparent unwrapping (via MIR)
// =============================================================================

const MAYBE_UNINIT_SOURCE: &str = r#"
#![allow(dead_code)]
use std::mem::MaybeUninit;
pub fn maybe_uninit_probe(x: MaybeUninit<u32>) {}
"#;

/// Test infer_sort_from_ty for MaybeUninit<u32> — should unwrap to bv32.
#[test]
fn test_infer_sort_maybe_uninit_unwraps_via_mir() {
    with_test_ay_ctx_for_source(MAYBE_UNINIT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "maybe_uninit_probe");
        let body = instance.body().expect("body");

        // Local 1: x: MaybeUninit<u32>
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for MaybeUninit<u32>");
        assert!(sort.is_bitvec(), "MaybeUninit<u32> should unwrap to bitvec, got {:?}", sort);
        assert_eq!(sort.bitvec_width(), Some(32), "MaybeUninit<u32> should unwrap to bv32");
    });
}

// =============================================================================
// ManuallyDrop transparent unwrapping (via MIR)
// =============================================================================

const MANUALLY_DROP_SOURCE: &str = r#"
#![allow(dead_code)]
use std::mem::ManuallyDrop;
pub fn manually_drop_probe(x: ManuallyDrop<u64>) {}
"#;

/// Test infer_sort_from_ty for ManuallyDrop<u64> — should unwrap to bv64.
#[test]
fn test_infer_sort_manually_drop_unwraps_via_mir() {
    with_test_ay_ctx_for_source(MANUALLY_DROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "manually_drop_probe");
        let body = instance.body().expect("body");

        // Local 1: x: ManuallyDrop<u64>
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for ManuallyDrop<u64>");
        assert!(sort.is_bitvec(), "ManuallyDrop<u64> should unwrap to bitvec, got {:?}", sort);
        assert_eq!(sort.bitvec_width(), Some(64), "ManuallyDrop<u64> should unwrap to bv64");
    });
}

// =============================================================================
// Part of #2255: Vec IntoIter sort dispatch (via MIR)
// =============================================================================

const VEC_INTO_ITER_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn vec_into_iter_probe(_x: std::vec::IntoIter<u32>) {}
"#;

/// Test infer_sort_from_ty for Vec IntoIter<u32> — should produce VecIntoIter_bv32
/// with {fld_vec: Vec_bv32, fld_pos: bvN} shape.
#[test]
fn test_infer_sort_vec_into_iter_via_mir() {
    with_test_ay_ctx_for_source(VEC_INTO_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "vec_into_iter_probe");
        let body = instance.body().expect("body");

        // Local 1: x: std::vec::IntoIter<u32>
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Vec IntoIter<u32>");

        // Vec IntoIter should be a datatype with VecIntoIter_ prefix
        assert!(sort.is_datatype(), "Vec IntoIter<u32> should be a datatype sort, got {:?}", sort);
        let name = sort.datatype_name().expect("datatype should have name");
        assert!(
            name.contains("VecIntoIter"),
            "Vec IntoIter sort name should contain 'VecIntoIter', got '{}'",
            name
        );

        // Part of #2912: BMC 6-field model matching MIR IntoIter<T> layout
        assert!(sort.datatype_has_field("fld_buf"), "VecIntoIter should have fld_buf");
        assert!(sort.datatype_has_field("fld_end"), "VecIntoIter should have fld_end");
    });
}

/// Test direct infer_adt_sort on Vec IntoIter matches infer_sort_from_ty.
///
/// This guards the centralized ADT dispatch path used by direct call sites.
#[test]
fn test_infer_adt_sort_direct_vec_into_iter_matches_infer_sort_from_ty() {
    with_test_ay_ctx_for_source(VEC_INTO_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "vec_into_iter_probe");
        let body = instance.body().expect("body");

        let ty = body.locals()[1].ty;
        let inferred = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Vec IntoIter<u32>");

        let direct = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => StatementCodegen::infer_adt_sort(def, args)
                .expect("infer_adt_sort should succeed for Vec IntoIter<u32>"),
            _ => panic!("expected ADT type for Vec IntoIter probe"),
        };

        assert_eq!(
            direct.datatype_name(),
            inferred.datatype_name(),
            "direct infer_adt_sort should produce the same datatype name as infer_sort_from_ty",
        );
        assert!(direct.datatype_has_field("fld_buf"), "direct VecIntoIter must have fld_buf");
        assert!(direct.datatype_has_field("fld_end"), "direct VecIntoIter must have fld_end");
    });
}

// =============================================================================
// Part of #2255: Array IntoIter sort dispatch (via MIR)
// =============================================================================

const ARRAY_INTO_ITER_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn array_into_iter_probe(_x: std::array::IntoIter<u32, 4>) {}
"#;

/// Test infer_sort_from_ty for Array IntoIter<u32, 4> — should produce IntoIter_bv32
/// with {fld_alive: IndexRange, fld_data: Array} shape.
#[test]
fn test_infer_sort_array_into_iter_via_mir() {
    with_test_ay_ctx_for_source(ARRAY_INTO_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_into_iter_probe");
        let body = instance.body().expect("body");

        // Local 1: x: std::array::IntoIter<u32, 4>
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty)
            .expect("infer_sort_from_ty should succeed for Array IntoIter<u32, 4>");

        // Array IntoIter should be a datatype with IntoIter_ prefix (not VecIntoIter_)
        assert!(
            sort.is_datatype(),
            "Array IntoIter<u32, 4> should be a datatype sort, got {:?}",
            sort
        );
        let name = sort.datatype_name().expect("datatype should have name");
        assert!(
            name.contains("IntoIter") && !name.contains("VecIntoIter"),
            "Array IntoIter sort name should contain 'IntoIter' but NOT 'VecIntoIter', got '{}'",
            name
        );

        // Should have fld_alive and fld_data fields
        assert!(sort.datatype_has_field("fld_alive"), "Array IntoIter should have fld_alive field");
        assert!(sort.datatype_has_field("fld_data"), "Array IntoIter should have fld_data field");
    });
}

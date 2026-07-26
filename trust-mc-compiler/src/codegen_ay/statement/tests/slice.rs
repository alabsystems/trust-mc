// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven unit tests for slice.rs — wide pointer type utilities.
//!
//! Trivial tests that only constructed AY Sort/Expr values (slice sort
//! construction, index coercion expressions, bounds check expressions,
//! ZST sort/equality) were removed per rule #2312 and #2482 because they
//! did not exercise production codegen paths.
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

// ─── Fat pointer metadata extraction ────────────────────────────────

#[test]
fn test_fat_ptr_with_fld_len_metadata() {
    // Fat pointer datatype with fld_ptr and fld_len

    let fat_sort = struct_sort(
        "FatPtr_slice_u32",
        [("fld_ptr", Sort::bitvec(POINTER_WIDTH)), ("fld_len", Sort::bitvec(POINTER_WIDTH))],
    );
    let ptr = Expr::bitvec_const(0x1000u128, POINTER_WIDTH);
    let len = Expr::bitvec_const(5u128, POINTER_WIDTH);
    let fat_expr = Expr::datatype_constructor(
        "FatPtr_slice_u32",
        "FatPtr_slice_u32_mk",
        vec![ptr, len],
        fat_sort,
    );

    let metadata = extract_fat_ptr_metadata(&fat_expr);
    assert!(metadata.is_some(), "should extract fld_len metadata");
    assert_eq!(metadata.unwrap().sort().bitvec_width(), Some(POINTER_WIDTH));
}

#[test]
fn test_fat_ptr_without_metadata_field() {
    // A thin pointer datatype (no fld_len/fld_vtable/fld_meta) returns None

    let thin_sort = struct_sort("ThinPtr", [("fld_ptr", Sort::bitvec(POINTER_WIDTH))]);
    let ptr = Expr::bitvec_const(0x2000u128, POINTER_WIDTH);
    let thin_expr = Expr::datatype_constructor("ThinPtr", "ThinPtr_mk", vec![ptr], thin_sort);

    let metadata = extract_fat_ptr_metadata(&thin_expr);
    assert!(metadata.is_none(), "thin pointer should have no metadata");
}

#[test]
fn test_fat_ptr_vtable_metadata() {
    // Trait object fat pointer has fld_vtable instead of fld_len

    let dyn_sort = struct_sort(
        "FatPtr_dyn_Trait",
        [("fld_ptr", Sort::bitvec(POINTER_WIDTH)), ("fld_vtable", Sort::bitvec(POINTER_WIDTH))],
    );
    let ptr = Expr::bitvec_const(0x3000u128, POINTER_WIDTH);
    let vtable = Expr::bitvec_const(0x4000u128, POINTER_WIDTH);
    let dyn_expr = Expr::datatype_constructor(
        "FatPtr_dyn_Trait",
        "FatPtr_dyn_Trait_mk",
        vec![ptr, vtable],
        dyn_sort,
    );

    let metadata = extract_fat_ptr_metadata(&dyn_expr);
    assert!(metadata.is_some(), "should extract fld_vtable metadata");
}

// ─── Type checking with MIR context ────────────────────────────────

#[test]
fn test_wide_pointer_detection_for_slice_ref() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn slice_ref_test(s: &[u32]) -> usize { s.len() }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "slice_ref_test");
            let body = instance.body().expect("body");

            // First local (_1) should be the &[u32] parameter
            let param_ty = body.locals()[1].ty;
            assert!(
                StatementCodegen::is_wide_pointer_ty(param_ty),
                "&[u32] should be detected as wide pointer"
            );
            assert!(
                StatementCodegen::is_slice_pointer_ty(param_ty),
                "&[u32] should be detected as slice pointer"
            );
            assert!(
                StatementCodegen::is_slice_or_array_ref_ty(param_ty),
                "&[u32] should be detected as slice or array ref"
            );
        },
    );
}

#[test]
fn test_thin_pointer_for_sized_type() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn thin_ptr_test(p: &u32) -> u32 { *p }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "thin_ptr_test");
            let body = instance.body().expect("body");

            // Parameter &u32 is thin pointer
            let param_ty = body.locals()[1].ty;
            assert!(
                !StatementCodegen::is_wide_pointer_ty(param_ty),
                "&u32 should NOT be wide pointer"
            );
            assert!(
                !StatementCodegen::is_slice_pointer_ty(param_ty),
                "&u32 should NOT be slice pointer"
            );
        },
    );
}

#[test]
fn test_thin_pointer_for_pointee_sized() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn pointee_test(p: &u64) -> u64 { *p }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "pointee_test");
            let body = instance.body().expect("body");

            // Get the pointee type from &u64
            let ref_ty = body.locals()[1].ty;
            if let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ref_ty.kind() {
                assert!(
                    StatementCodegen::use_thin_pointer_for_pointee(pointee),
                    "u64 pointee should use thin pointer"
                );
            } else {
                panic!("expected reference type for parameter");
            }
        },
    );
}

#[test]
fn test_array_ref_detected() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn array_ref_test(a: &[u32; 4]) -> u32 { a[0] }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "array_ref_test");
            let body = instance.body().expect("body");

            let param_ty = body.locals()[1].ty;
            assert!(
                StatementCodegen::is_slice_or_array_ref_ty(param_ty),
                "&[u32; 4] should be detected as slice or array ref"
            );
            // Not a wide pointer — arrays have known length
            assert!(
                !StatementCodegen::is_wide_pointer_ty(param_ty),
                "&[u32; 4] should NOT be wide pointer"
            );
        },
    );
}

#[test]
fn test_array_len_extraction() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn array_len_test(a: &[u8; 16]) -> u8 { a[0] }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "array_len_test");
            let body = instance.body().expect("body");

            let param_ty = body.locals()[1].ty;
            let len = StatementCodegen::array_len_from_pointer_ty(param_ty);
            assert_eq!(len, Some(16), "should extract array length 16 from &[u8; 16]");
        },
    );
}

#[test]
fn test_array_len_returns_none_for_slice() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn no_array_len_test(s: &[u32]) -> usize { s.len() }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "no_array_len_test");
            let body = instance.body().expect("body");

            let param_ty = body.locals()[1].ty;
            let len = StatementCodegen::array_len_from_pointer_ty(param_ty);
            assert_eq!(len, None, "slices don't have static array length");
        },
    );
}

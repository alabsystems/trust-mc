// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// codegen_types.rs — is_opaque_alloc_infra unit tests (Part of #2188)
// =============================================================================

#[test]
fn test_translate_ty_bool() {
    // (#2188) Unit test for translate_ty: Bool -> Sort::bool()
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bool_ty(x: bool) -> bool { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_bool_ty");
        let ret_ty = sig.output();
        let sort = ChcCtx::translate_ty(ret_ty);
        assert!(sort.is_some(), "Bool should translate to a sort");
        assert!(sort.unwrap().is_bool(), "Bool should translate to SMT Bool sort");
    });
}

#[test]
fn test_translate_ty_array_produces_smt_array() {
    // (#2188) Unit test for translate_ty: [u8; N] -> Array<BV64, BV8>
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_ty(arr: [u8; 4]) -> u8 { arr[0] }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_array_ty");
        let arr_ty = sig.inputs()[0];
        let sort = ChcCtx::translate_ty(arr_ty);
        assert!(sort.is_some(), "[u8; 4] should translate to a sort");
        let sort = sort.unwrap();
        assert!(sort.is_array(), "[u8; 4] should translate to Array sort");
    });
}

#[test]
fn test_translate_ty_unit_is_bool() {
    // (#2188) Unit test: () -> Bool (placeholder for unit type)
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_unit_ty() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_unit_ty");
        let ret_ty = sig.output();
        let sort = ChcCtx::translate_ty(ret_ty);
        assert!(sort.is_some(), "Unit should translate to a sort");
        assert!(sort.unwrap().is_bool(), "Unit should translate to Bool sort");
    });
}

#[test]
fn test_translate_ty_raw_pointer_is_bitvec() {
    // (#2188) Unit test: *const u8 -> BV(POINTER_WIDTH)
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_ty(p: *const u8) -> *const u8 { p }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_ptr_ty");
        let ptr_ty = sig.inputs()[0];
        let sort = ChcCtx::translate_ty(ptr_ty);
        assert!(sort.is_some(), "Raw pointer should translate to a sort");
        let sort = sort.unwrap();
        assert!(sort.is_bitvec(), "Raw pointer should translate to bitvec sort");
    });
}

#[test]
fn test_translate_ty_reference_is_bitvec() {
    // (#2188) Unit test: &u32 -> BV(POINTER_WIDTH)
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ref_ty(r: &u32) -> &u32 { r }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_ref_ty");
        let ref_ty = sig.inputs()[0];
        let sort = ChcCtx::translate_ty(ref_ty);
        assert!(sort.is_some(), "Reference should translate to a sort");
        let sort = sort.unwrap();
        assert!(sort.is_bitvec(), "Reference should translate to bitvec sort");
    });
}

#[test]
fn test_translate_ty_tuple_pair() {
    // (#2188) Unit test: (u32, u64) -> struct with two fields
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_tuple_ty(t: (u32, u64)) -> u32 { t.0 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_tuple_ty");
        let tuple_ty = sig.inputs()[0];
        let sort = ChcCtx::translate_ty(tuple_ty);
        assert!(sort.is_some(), "(u32, u64) should translate to a sort");
        let sort = sort.unwrap();
        assert!(sort.is_datatype(), "(u32, u64) should translate to datatype (struct) sort");
    });
}

#[test]
fn test_translate_ty_single_element_tuple_unwraps() {
    // (#2188) Unit test: (u128,) -> unwrapped to inner sort (not wrapped in struct)
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_single_tuple(t: (u128,)) -> u128 { t.0 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_single_tuple");
        let tuple_ty = sig.inputs()[0];
        let sort = ChcCtx::translate_ty(tuple_ty);
        assert!(sort.is_some(), "(u128,) should translate to a sort");
        let sort = sort.unwrap();
        // Single-element tuples unwrap to inner type (#1979)
        assert!(sort.is_bitvec(), "(u128,) should unwrap to BV128, got: {:?}", sort);
        assert_eq!(sort.bitvec_width(), Some(128));
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC memory_impl_layout.rs — get_type_size, get_type_align,
//! get_array_element_ty, get_array_length for primitive and compound types.
//!
//! Part of #2303 (test coverage for decomposed CHC modules).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_middle::ty::TypingEnv;

const MONOMORPHIZED_LAYOUT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct ScalarWrap<T> {
        pub value: T,
        pub flag: bool,
    }

    pub fn probe_scalar_wrap<T: Copy>(wrap: ScalarWrap<T>) -> T {
        wrap.value
    }

    pub fn probe_u32_anchor(v: u32) -> u32 {
        v
    }
"#;

const UNSIZED_TAIL_LAYOUT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Inner {
        pub inner: [u8],
    }

    pub struct MyStr {
        pub header_0: u8,
        pub header_1: u8,
        pub data: str,
    }

    pub fn probe_inner_ptr(ptr: *const Inner) {
        let _ = ptr;
    }

    pub fn probe_mystr_ptr(ptr: *const MyStr) {
        let _ = ptr;
    }
"#;

const TRANSPARENT_WRAPPER_LAYOUT_SOURCE: &str = r#"
    #![allow(dead_code)]
    use core::cell::{Cell, UnsafeCell};
    use core::mem::{ManuallyDrop, MaybeUninit};

    pub fn probe_wrapper_layouts(
        a: UnsafeCell<*mut i32>,
        b: Cell<*mut i32>,
        c: MaybeUninit<*mut i32>,
        d: ManuallyDrop<*mut i32>,
    ) {
        let _ = (a, b, c, d);
    }
"#;

const LIFETIME_ONLY_PARAM_LAYOUT_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[repr(C)]
    pub struct LifetimeWrap<'a> {
        pub ptr: &'a u8,
        pub flag: bool,
    }

    pub fn probe_lifetime_wrap<'a>(wrap: LifetimeWrap<'a>) -> bool {
        wrap.flag
    }
"#;

// =============================================================================
// get_type_size — primitive types
// =============================================================================

/// Verify size and alignment for all primitive integer types.
#[test]
fn test_layout_primitive_integer_sizes() {
    const SOURCE: &str = r#"
        #![allow(dead_code, unused_variables)]

        pub fn probe_primitives(
            a: i8, b: i16, c: i32, d: i64, e: i128,
            f: u8, g: u16, h: u32, i: u64, j: u128,
            k: isize, l: usize,
        ) -> u32 { 0 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_primitives");
        let inputs = fn_sig.inputs();
        let instance = find_instance_by_suffix(ctx.tcx, "probe_primitives");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_primitives", ChcConfig::default());

        // (type, expected_size, expected_align)
        let expected: &[(usize, usize, u64)] = &[
            (0, 1, 1),   // i8
            (1, 2, 2),   // i16
            (2, 4, 4),   // i32
            (3, 8, 8),   // i64
            (4, 16, 16), // i128
            (5, 1, 1),   // u8
            (6, 2, 2),   // u16
            (7, 4, 4),   // u32
            (8, 8, 8),   // u64
            (9, 16, 16), // u128
            (10, 8, 8),  // isize
            (11, 8, 8),  // usize
        ];

        for &(idx, exp_size, exp_align) in expected {
            let ty = inputs[idx];
            assert_eq!(
                chc_ctx.get_type_size(ty),
                Some(exp_size),
                "size mismatch for input[{idx}] ({ty:?})"
            );
            assert_eq!(
                chc_ctx.get_type_align(ty),
                Some(exp_align),
                "align mismatch for input[{idx}] ({ty:?})"
            );
        }
    });
}

/// Verify size and alignment for bool, char, and float types.
#[test]
fn test_layout_bool_char_float_sizes() {
    const SOURCE: &str = r#"
        #![allow(dead_code, unused_variables)]

        pub fn probe_misc_types(a: bool, b: char, c: f32, d: f64) -> u32 { 0 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_misc_types");
        let inputs = fn_sig.inputs();
        let instance = find_instance_by_suffix(ctx.tcx, "probe_misc_types");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_misc_types", ChcConfig::default());

        // bool: 1 byte, align 1
        assert_eq!(chc_ctx.get_type_size(inputs[0]), Some(1));
        assert_eq!(chc_ctx.get_type_align(inputs[0]), Some(1));

        // char: 4 bytes, align 4
        assert_eq!(chc_ctx.get_type_size(inputs[1]), Some(4));
        assert_eq!(chc_ctx.get_type_align(inputs[1]), Some(4));

        // f32: 4 bytes, align 4
        assert_eq!(chc_ctx.get_type_size(inputs[2]), Some(4));
        assert_eq!(chc_ctx.get_type_align(inputs[2]), Some(4));

        // f64: 8 bytes, align 8
        assert_eq!(chc_ctx.get_type_size(inputs[3]), Some(8));
        assert_eq!(chc_ctx.get_type_align(inputs[3]), Some(8));
    });
}

/// Verify size for pointer and reference types (64-bit pointers).
#[test]
fn test_layout_pointer_and_ref_sizes() {
    const SOURCE: &str = r#"
        #![allow(dead_code, unused_variables)]

        pub fn probe_ptr_types(a: &u32, b: *const u32, c: *mut u8) -> u32 { 0 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_ptr_types");
        let inputs = fn_sig.inputs();
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_types");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_types", ChcConfig::default());

        // All pointer-width types are 8 bytes on 64-bit
        for (idx, label) in [(0, "&u32"), (1, "*const u32"), (2, "*mut u8")] {
            assert_eq!(chc_ctx.get_type_size(inputs[idx]), Some(8), "size mismatch for {label}");
            assert_eq!(chc_ctx.get_type_align(inputs[idx]), Some(8), "align mismatch for {label}");
        }
    });
}

#[test]
fn test_layout_transparent_pointer_wrappers_use_inner_pointer_layout() {
    with_test_ay_ctx_for_source(TRANSPARENT_WRAPPER_LAYOUT_SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_wrapper_layouts");
        let inputs = fn_sig.inputs();
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapper_layouts");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrapper_layouts", ChcConfig::default());

        for (idx, label) in [
            (0, "UnsafeCell<*mut i32>"),
            (1, "Cell<*mut i32>"),
            (2, "MaybeUninit<*mut i32>"),
            (3, "ManuallyDrop<*mut i32>"),
        ] {
            assert_eq!(
                chc_ctx.get_type_size(inputs[idx]),
                Some(8),
                "{label} should use pointer-sized layout"
            );
            assert_eq!(
                chc_ctx.get_type_align(inputs[idx]),
                Some(8),
                "{label} should use pointer alignment"
            );
        }
    });
}

#[test]
fn test_layout_resolves_monomorphized_generic_field_type() {
    with_test_ay_ctx_for_source(MONOMORPHIZED_LAYOUT_SOURCE, |ctx| {
        let concrete_ty = fn_sig_by_suffix(ctx.tcx, "probe_u32_anchor").inputs()[0];
        let instance = resolve_single_type_generic_instance_by_suffix(
            ctx.tcx,
            "probe_scalar_wrap",
            concrete_ty,
        );
        let body = instance.body().expect("resolved generic function body");
        let raw_sig = fn_sig_by_suffix(ctx.tcx, "probe_scalar_wrap");
        let wrap_ty = raw_sig.inputs()[0];
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = wrap_ty.kind() else {
            panic!("expected ScalarWrap<T> input, got {:?}", wrap_ty.kind());
        };
        let field_ty = def.variants()[0].fields()[0].ty();
        let chc_ctx = ChcCtx::new_with_instance(
            ctx.tcx,
            &body,
            instance,
            "probe_scalar_wrap",
            ChcConfig::default(),
        );

        assert!(matches!(field_ty.kind(), TyKind::Param(_)));
        assert_eq!(chc_ctx.get_type_size(field_ty), Some(4));
        assert_eq!(chc_ctx.get_type_align(field_ty), Some(4));
    });
}

#[test]
fn test_layout_unsized_wrapper_slice_and_str_tails_use_tail_element_layout() {
    with_test_ay_ctx_for_source(UNSIZED_TAIL_LAYOUT_SOURCE, |ctx| {
        let inner_ptr_sig = fn_sig_by_suffix(ctx.tcx, "probe_inner_ptr");
        let mystr_ptr_sig = fn_sig_by_suffix(ctx.tcx, "probe_mystr_ptr");
        let inner_ty = match inner_ptr_sig.inputs()[0].kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => panic!("expected *const Inner argument"),
        };
        let mystr_ty = match mystr_ptr_sig.inputs()[0].kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => panic!("expected *const MyStr argument"),
        };

        let instance = find_instance_by_suffix(ctx.tcx, "probe_mystr_ptr");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_mystr_ptr", ChcConfig::default());

        assert_eq!(chc_ctx.get_type_size(inner_ty), Some(1), "Inner tail element size should be 1");
        assert_eq!(
            chc_ctx.get_type_align(inner_ty),
            Some(1),
            "Inner tail element align should be 1"
        );
        assert_eq!(chc_ctx.get_type_size(mystr_ty), Some(1), "MyStr tail element size should be 1");
        assert_eq!(
            chc_ctx.get_type_align(mystr_ty),
            Some(1),
            "MyStr tail element align should be 1"
        );
    });
}

#[test]
fn test_layout_unsized_wrapper_field_offsets_use_internal_layout_query() {
    with_test_ay_ctx_for_source(UNSIZED_TAIL_LAYOUT_SOURCE, |ctx| {
        let mystr_ptr_sig = fn_sig_by_suffix(ctx.tcx, "probe_mystr_ptr");
        let inner_ptr_sig = fn_sig_by_suffix(ctx.tcx, "probe_inner_ptr");
        let mystr_ty = match mystr_ptr_sig.inputs()[0].kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => panic!("expected *const MyStr argument"),
        };
        let inner_ty = match inner_ptr_sig.inputs()[0].kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => panic!("expected *const Inner argument"),
        };

        let instance = find_instance_by_suffix(ctx.tcx, "probe_inner_ptr");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_inner_ptr", ChcConfig::default());

        assert_eq!(
            chc_ctx.get_field_offset(inner_ty, 0),
            Some(0),
            "Inner::inner should start at byte 0"
        );
        assert_eq!(
            chc_ctx.get_field_offset(mystr_ty, 0),
            Some(0),
            "MyStr::header_0 should start at byte 0"
        );
        assert_eq!(
            chc_ctx.get_field_offset(mystr_ty, 1),
            Some(1),
            "MyStr::header_1 should start at byte 1"
        );
        assert_eq!(
            chc_ctx.get_field_offset(mystr_ty, 2),
            Some(2),
            "MyStr::data should start after the 2-byte head"
        );
    });
}

// =============================================================================
// get_array_element_ty and get_array_length
// =============================================================================

/// Array type: get_array_element_ty returns the element type,
/// get_array_length returns the compile-time length.
#[test]
fn test_array_element_ty_and_length() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array(arr: [u32; 5]) -> u32 {
            arr[0]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_array");
        let arr_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_array", ChcConfig::default());

        // Element type should be u32
        let elem_ty = chc_ctx.get_array_element_ty(arr_ty);
        assert!(elem_ty.is_some(), "should extract element type from [u32; 5]");
        let elem = elem_ty.unwrap();
        assert_eq!(chc_ctx.get_type_size(elem), Some(4), "element type should be u32 (4 bytes)");

        // Length should be 5
        assert_eq!(
            chc_ctx.get_array_length(arr_ty),
            Some(5),
            "compile-time array length should be 5"
        );
    });
}

/// Slice type: get_array_element_ty works, but get_array_length returns None.
#[test]
fn test_slice_element_ty_no_length() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice(s: &[u8]) -> u8 {
            s[0]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_slice");
        let ref_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_slice", ChcConfig::default());

        // The parameter type is &[u8], which is a reference to a slice.
        // We need to unwrap the reference to get the slice type.
        if let TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _)) = ref_ty.kind() {
            let elem_ty = chc_ctx.get_array_element_ty(inner_ty);
            assert!(elem_ty.is_some(), "should extract element type from &[u8] inner slice");

            // Slices have no compile-time length
            assert_eq!(
                chc_ctx.get_array_length(inner_ty),
                None,
                "slice should have no compile-time length"
            );
        } else {
            panic!("expected reference type for &[u8], got: {ref_ty:?}");
        }
    });
}

/// Non-array type: get_array_element_ty returns None.
#[test]
fn test_non_array_element_ty_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_non_array(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_non_array");
        let u32_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_array");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_array", ChcConfig::default());

        assert_eq!(chc_ctx.get_array_element_ty(u32_ty), None, "u32 should not be an array type");
        assert_eq!(chc_ctx.get_array_length(u32_ty), None, "u32 should not have an array length");
    });
}

/// Non-aggregate type: get_field_offset must fail closed (no heuristic offset).
#[test]
fn test_non_aggregate_field_offset_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_scalar(x: bool) -> bool { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_scalar");
        let bool_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_scalar");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_scalar", ChcConfig::default());

        assert_eq!(
            chc_ctx.get_field_offset(bool_ty, 0),
            None,
            "scalar types must not synthesize field offsets"
        );
    });
}

// =============================================================================
// Fallback counter assertions for get_field_offset (Part of #2783)
// =============================================================================

/// get_field_offset on a non-aggregate (bool) must increment sound_fallback_count().
///
/// This is the catch-all `_ =>` branch in get_field_offset (memory_impl_layout.rs).
/// Part of #2783: 3 untested record_fallback() sites in memory_impl_layout.rs.
#[test]
fn test_field_offset_unknown_type_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_scalar_fallback(x: bool) -> bool { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_scalar_fallback");
        let bool_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_scalar_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_scalar_fallback", ChcConfig::default());

        // Part of #3369: Reclassified to DEMOTED — returning None causes
        // callers to skip stores (identity), not sound over-approximation.
        let before = chc_ctx.fallback_count;
        let result = chc_ctx.get_field_offset(bool_ty, 0);
        let after = chc_ctx.fallback_count;

        assert!(result.is_none(), "scalar field offset should be None");
        assert!(
            after > before,
            "get_field_offset on unknown type must increment fallback_count \
             (before={before}, after={after})"
        );
    });
}

/// get_field_offset on an ADT with out-of-bounds field index must increment sound_fallback_count().
///
/// When `ty.layout()` succeeds but `offsets.get(field_idx)` returns None (out-of-bounds),
/// the function falls through to the ADT match arm which calls record_fallback().
/// Part of #2783.
#[test]
fn test_field_offset_adt_oob_index_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct TwoFields {
            pub a: u32,
            pub b: u64,
        }

        pub fn probe_adt_oob(s: TwoFields) -> u32 { s.a }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_adt_oob");
        let struct_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_adt_oob");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_adt_oob", ChcConfig::default());

        // Valid index should succeed without fallback
        let before_valid = chc_ctx.sound_fallback_count();
        let valid = chc_ctx.get_field_offset(struct_ty, 0);
        assert!(valid.is_some(), "valid field index should return Some");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_valid,
            "valid field offset should not increment sound_fallback_count()"
        );

        // Out-of-bounds index: struct has 2 fields, requesting index 99
        // Part of #3369: Reclassified to DEMOTED — returning None causes
        // callers to skip stores (identity).
        let before = chc_ctx.fallback_count;
        let result = chc_ctx.get_field_offset(struct_ty, 99);
        let after = chc_ctx.fallback_count;

        assert!(result.is_none(), "OOB field index should return None");
        assert!(
            after > before,
            "get_field_offset on ADT with OOB index must increment fallback_count \
             (before={before}, after={after})"
        );
    });
}

/// get_field_offset on a tuple with out-of-bounds field index must increment sound_fallback_count().
///
/// Part of #2783.
#[test]
fn test_field_offset_tuple_oob_index_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_tuple_oob(t: (u8, u32)) -> u32 { t.1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_tuple_oob");
        let tuple_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_oob");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_oob", ChcConfig::default());

        // Valid index should succeed without fallback
        let before_valid = chc_ctx.sound_fallback_count();
        let valid = chc_ctx.get_field_offset(tuple_ty, 0);
        assert!(valid.is_some(), "valid tuple field index should return Some");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_valid,
            "valid tuple field offset should not increment sound_fallback_count()"
        );

        // Out-of-bounds: tuple has 2 fields, requesting index 50
        // Part of #3369: Reclassified to DEMOTED.
        let before = chc_ctx.fallback_count;
        let result = chc_ctx.get_field_offset(tuple_ty, 50);
        let after = chc_ctx.fallback_count;

        assert!(result.is_none(), "OOB tuple field index should return None");
        assert!(
            after > before,
            "get_field_offset on tuple with OOB index must increment fallback_count \
             (before={before}, after={after})"
        );
    });
}

// =============================================================================
// get_field_offset — tuple types
// =============================================================================

/// Tuple field offsets are available and have non-overlapping values.
/// Note: Rust may reorder tuple fields for alignment, so we verify
/// structural properties rather than exact offsets.
#[test]
fn test_layout_tuple_field_offsets() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_tuple(t: (u8, u32, u64)) -> u64 {
            t.2
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_tuple");
        let tuple_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple", ChcConfig::default());

        // All field offsets should be available
        let off0 = chc_ctx.get_field_offset(tuple_ty, 0);
        let off1 = chc_ctx.get_field_offset(tuple_ty, 1);
        let off2 = chc_ctx.get_field_offset(tuple_ty, 2);
        assert!(off0.is_some(), "tuple field 0 offset should be available");
        assert!(off1.is_some(), "tuple field 1 offset should be available");
        assert!(off2.is_some(), "tuple field 2 offset should be available");

        // All three offsets should be distinct (fields don't overlap)
        let offsets = [off0.unwrap(), off1.unwrap(), off2.unwrap()];
        assert_ne!(offsets[0], offsets[1], "field 0 and 1 should have different offsets");
        assert_ne!(offsets[1], offsets[2], "field 1 and 2 should have different offsets");
        assert_ne!(offsets[0], offsets[2], "field 0 and 2 should have different offsets");

        // Total size should be computable
        let size = chc_ctx.get_type_size(tuple_ty);
        assert!(size.is_some(), "tuple size should be computable");
        // (u8, u32, u64) = 16 bytes with alignment padding
        assert_eq!(size, Some(16), "tuple (u8, u32, u64) should be 16 bytes");
    });
}

// =============================================================================
// get_type_size / get_type_align — struct types (layout-derived, not hardcoded)
// =============================================================================

/// Struct with a single u8 field must report size=1, not a hardcoded 8.
///
/// Regression guard: before this fix, get_type_size had `_ => Some(8)` which
/// returned 8 for ALL types not explicitly matched. Struct types go through
/// rustc layout (which succeeds for concrete types), so this test guards
/// that the layout path works and the fallback is never used for known types.
#[test]
fn test_layout_struct_single_u8_field_not_hardcoded_8() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct TinyStruct {
            pub val: u8,
        }

        pub fn probe_struct(s: TinyStruct) -> u8 {
            s.val
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_struct");
        let struct_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_struct", ChcConfig::default());

        // TinyStruct { val: u8 } should be 1 byte, not 8
        let size = chc_ctx.get_type_size(struct_ty);
        assert_eq!(size, Some(1), "struct with single u8 field must be 1 byte (not hardcoded 8)");

        let align = chc_ctx.get_type_align(struct_ty);
        assert_eq!(align, Some(1), "struct with single u8 field must have 1-byte alignment");
    });
}

/// Struct with mixed-size fields verifies layout includes padding.
///
/// Guards against heuristic: field_count * 8 would give 24 but actual
/// layout for (u8, u64, u8) is 24 with padding (or 10 packed).
/// The point is: the size comes from rustc layout, not a formula.
#[test]
fn test_layout_struct_mixed_fields_uses_rustc_layout() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MixedStruct {
            pub a: u8,
            pub b: u64,
            pub c: u8,
        }

        pub fn probe_mixed(s: MixedStruct) -> u64 {
            s.b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_mixed");
        let struct_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mixed");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_mixed", ChcConfig::default());

        // rustc layout for { u8, u64, u8 } is typically 24 bytes (with alignment padding).
        // The exact value depends on field reordering (Rust may reorder for alignment).
        // What matters: size comes from rustc layout, not field_count * 8.
        let size = chc_ctx.get_type_size(struct_ty);
        assert!(size.is_some(), "struct size should be available from rustc layout");
        let s = size.unwrap();
        // Must be >= 10 (1 + 8 + 1 minimum) and <= 24 (with maximum padding)
        assert!((10..=24).contains(&s), "struct size {s} out of expected range [10, 24]");

        // Alignment should be 8 (driven by the u64 field)
        let align = chc_ctx.get_type_align(struct_ty);
        assert_eq!(align, Some(8), "struct alignment should be driven by largest field (u64)");

        // Field offsets should be available and correct
        let off_a = chc_ctx.get_field_offset(struct_ty, 0);
        let off_b = chc_ctx.get_field_offset(struct_ty, 1);
        let off_c = chc_ctx.get_field_offset(struct_ty, 2);
        assert!(
            off_a.is_some() && off_b.is_some() && off_c.is_some(),
            "all field offsets should be available"
        );
    });
}

#[test]
fn test_layout_lifetime_only_generic_adt_uses_rustc_layout() {
    with_test_ay_ctx_for_source(LIFETIME_ONLY_PARAM_LAYOUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_lifetime_wrap");
        let body = instance.body().expect("function body");
        let arg_ty = body.locals()[1].ty;
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_lifetime_wrap", ChcConfig::default());

        let TyKind::RigidTy(RigidTy::Adt(_, args)) = arg_ty.kind() else {
            panic!("probe_lifetime_wrap arg should stay an ADT, got {:?}", arg_ty.kind());
        };
        assert!(
            args.0.iter().any(|arg| matches!(arg, rustc_public::ty::GenericArgKind::Lifetime(_)))
                && args
                    .0
                    .iter()
                    .all(|arg| matches!(arg, rustc_public::ty::GenericArgKind::Lifetime(_))),
            "probe_lifetime_wrap arg should keep only lifetime generics so this test exercises the #3942 guard"
        );
        assert_eq!(
            chc_ctx.get_type_size(arg_ty),
            Some(16),
            "lifetime-only params should not suppress rustc layout size queries"
        );
        assert_eq!(
            chc_ctx.get_type_align(arg_ty),
            Some(8),
            "lifetime-only params should not suppress rustc layout align queries"
        );
        assert_eq!(
            chc_ctx.get_field_offset(arg_ty, 0),
            Some(0),
            "first repr(C) field should stay at offset 0"
        );
        assert_eq!(
            chc_ctx.get_field_offset(arg_ty, 1),
            Some(8),
            "second repr(C) field should use rustc-computed offset despite lifetime params"
        );
    });
}

// =============================================================================
// get_type_size — ADT types (Box, newtype wrappers) — Part of #3083
// =============================================================================

/// Box<T> should have a known type size via rustc layout.
///
/// Part of #3083: verify that common std ADTs resolve through ty.layout()
/// rather than hitting the unknown-type fallback.
#[test]
fn test_layout_box_type_size() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box(b: Box<u32>) -> u32 { *b }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_box");
        let box_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_box", ChcConfig::default());

        // Box<u32> is a thin pointer: 8 bytes on 64-bit
        let size = chc_ctx.get_type_size(box_ty);
        assert_eq!(size, Some(8), "Box<u32> should be 8 bytes (thin pointer)");
    });
}

/// Newtype wrapper should have same size as inner type via rustc layout.
///
/// Part of #3083: single-field newtype wrappers.
#[test]
fn test_layout_newtype_wrapper_size() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Wrapper(pub u64);

        pub fn probe_newtype(w: Wrapper) -> u64 { w.0 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_newtype");
        let wrapper_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_newtype");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_newtype", ChcConfig::default());

        // Wrapper(u64) should be 8 bytes, same as u64
        let size = chc_ctx.get_type_size(wrapper_ty);
        assert_eq!(size, Some(8), "Wrapper(u64) should be 8 bytes (same as inner u64)");
    });
}

/// repr-SIMD ADTs should recover their exact vector ABI layout even when the
/// stable `ty.layout()` helper rejects the type.
///
/// Regression for #3675: `heap_access_checks` needs concrete size+align for
/// repr-SIMD pointers. Falling back to the inner array field is unsound because
/// repr-SIMD rounds to the target vector ABI, so this test compares the CHC
/// helper against rustc's internal layout query instead of hardcoding array
/// field values.
#[test]
fn test_layout_repr_simd_matches_internal_layout_query() {
    const SOURCE: &str = r#"
        #![allow(dead_code, non_camel_case_types)]
        #![feature(repr_simd)]

        #[repr(simd)]
        pub struct CustomSimd([u8; 10]);

        pub fn probe_simd(v: CustomSimd) -> CustomSimd { v }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_simd");
        let simd_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simd");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simd", ChcConfig::default());

        let internal_ty = rustc_internal::internal(ctx.tcx, simd_ty);
        let expected = ctx
            .tcx
            .layout_of(TypingEnv::fully_monomorphized().as_query_input(internal_ty))
            .expect("repr-SIMD layout should be available from internal rustc query");
        let expected_size =
            usize::try_from(expected.size.bytes()).expect("repr-SIMD size should fit usize");

        assert_eq!(
            chc_ctx.get_type_size(simd_ty),
            Some(expected_size),
            "repr-SIMD size should match rustc vector ABI layout"
        );
        assert_eq!(
            chc_ctx.get_type_align(simd_ty),
            Some(expected.align.abi.bytes()),
            "repr-SIMD alignment should match rustc vector ABI layout"
        );
    });
}

/// Array type [u32; 5] should have a known size via rustc layout.
///
/// Part of #3083: verify array type size resolution.
#[test]
fn test_layout_array_type_size() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_size(arr: [u32; 5]) -> u32 { arr[0] }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_array_size");
        let arr_ty = fn_sig.inputs()[0];
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_size");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_array_size", ChcConfig::default());

        // [u32; 5] = 5 * 4 = 20 bytes
        let size = chc_ctx.get_type_size(arr_ty);
        assert_eq!(size, Some(20), "[u32; 5] should be 20 bytes");
    });
}

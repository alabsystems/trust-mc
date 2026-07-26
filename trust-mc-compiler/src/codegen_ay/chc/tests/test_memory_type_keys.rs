// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused tests for memory_impl type-key mapping logic.
//!
//! Part of #2188: additional edge coverage for:
//! - `sort_from_type_key`
//! - `type_key_for_ty`

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::memory_type_key_tables;

const TYPE_KEY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct GenericWrap<T>(pub T);
    pub struct Plain;

    pub fn probe_type_keys(
        r: &u32,
        p: *const i16,
        arr: [u8; 3],
        s: &[u8],
        tup: (u8, bool),
        unit: (),
        generic: GenericWrap<u16>,
        plain: Plain,
    ) {
        let _ = (r, p, arr, s, tup, unit, generic, plain);
    }
"#;

const HUGE_TYPE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct HugeBlob {
        pub bytes: [u8; 536_870_912],
    }

    pub fn probe_huge_blob_ptr(ptr: *const HugeBlob) {
        let _ = ptr;
    }
"#;

const UNION_TYPE_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[repr(C)]
    pub union WordOrBytes {
        pub word: u32,
        pub bytes: [u8; 4],
    }

    pub fn probe_union_arg(v: WordOrBytes) {
        let _ = v;
    }
"#;

const STR_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_str_ptr(v: *const str) {
        let _ = v;
    }
"#;

const GENERIC_SIMD_TYPE_KEY_SOURCE: &str = r#"
    #![allow(dead_code, non_camel_case_types)]
    #![feature(repr_simd)]

    #[repr(simd)]
    struct CustomSimd<T, const LANES: usize>([T; LANES]);

    pub fn probe_generic_keys<T: Copy, const LANES: usize>(
        simd: CustomSimd<T, LANES>,
        expected: [T; LANES],
    ) -> T {
        let _ = simd;
        expected[0]
    }
"#;

const MONOMORPHIZED_GENERIC_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct ArrayWrap<T> {
        pub lanes: [T; 4],
        pub tail: T,
    }

    pub fn probe_array_wrap<T: Copy>(wrap: ArrayWrap<T>) -> T {
        wrap.lanes[0]
    }

    pub fn probe_u16_anchor(v: u16) -> u16 {
        v
    }
"#;

const TRANSPARENT_WRAPPER_TYPE_KEY_SOURCE: &str = r#"
    #![allow(dead_code)]
    use core::cell::{Cell, UnsafeCell};
    use core::mem::{ManuallyDrop, MaybeUninit};

    pub fn probe_transparent_wrapper_keys(
        a: UnsafeCell<*mut i32>,
        b: Cell<*mut i32>,
        c: MaybeUninit<*mut i32>,
        d: ManuallyDrop<*mut i32>,
    ) {
        let _ = (a, b, c, d);
    }
"#;

// ============================================================================
// sort_from_type_key edge coverage
// ============================================================================

#[test]
fn test_sort_from_type_key_bool_maps_to_bool() {
    assert_eq!(ChcCtx::sort_from_type_key("bool"), Sort::bool());
}

#[test]
fn test_sort_from_type_key_char_maps_to_bv32() {
    assert_eq!(ChcCtx::sort_from_type_key("char"), Sort::bitvec(32));
}

#[test]
fn test_sort_from_type_key_unit_maps_to_bool() {
    assert_eq!(ChcCtx::sort_from_type_key("unit"), Sort::bool());
}

#[test]
fn test_sort_from_type_key_isize_and_usize_use_pointer_width() {
    let pointer_sort = Sort::bitvec(POINTER_WIDTH);
    assert_eq!(ChcCtx::sort_from_type_key("isize"), pointer_sort);
    assert_eq!(ChcCtx::sort_from_type_key("usize"), pointer_sort);
}

#[test]
fn test_sort_from_type_key_float_extremes() {
    assert_eq!(ChcCtx::sort_from_type_key("f16"), Sort::bitvec(16));
    assert_eq!(ChcCtx::sort_from_type_key("f128"), Sort::bitvec(128));
}

#[test]
fn test_sort_from_type_key_compact_simd_key_flattens_to_vector_width() {
    assert_eq!(ChcCtx::sort_from_type_key("i64x4"), Sort::bitvec(256));
    assert_eq!(ChcCtx::sort_from_type_key("u8x16"), Sort::bitvec(128));
}

#[test]
fn test_sort_from_type_key_ref_prefix_maps_to_pointer() {
    assert_eq!(ChcCtx::sort_from_type_key("ref_u8"), Sort::bitvec(POINTER_WIDTH));
}

#[test]
fn test_sort_from_type_key_ptr_prefix_maps_to_pointer() {
    assert_eq!(ChcCtx::sort_from_type_key("ptr_i32"), Sort::bitvec(POINTER_WIDTH));
}

// Part of #2244: tuple type keys now recursively resolve element sort instead
// of blindly mapping to Sort::int(). Single-element tuples unwrap (matching
// translate_ty). Multi-element tuples parse ambiguously, producing the bv32 default.
#[test]
fn test_sort_from_type_key_tuple_multi_element_maps_to_bv32_default() {
    // "tuple_u8_bool" has ambiguous element parsing → falls to bv32 default
    assert_eq!(ChcCtx::sort_from_type_key("tuple_u8_bool"), Sort::bitvec(32));
}

#[test]
fn test_sort_from_type_key_tuple_single_ptr_unwraps_to_pointer_width() {
    // "tuple_ptr_u8" → single element "ptr_u8" → BV(POINTER_WIDTH)
    // This is the B2 fix: (*mut u8,) tuples in alloc paths must not map to Int
    assert_eq!(ChcCtx::sort_from_type_key("tuple_ptr_u8"), Sort::bitvec(POINTER_WIDTH));
}

#[test]
fn test_sort_from_type_key_tuple_single_scalar_unwraps() {
    assert_eq!(ChcCtx::sort_from_type_key("tuple_i32"), Sort::bitvec(32));
    assert_eq!(ChcCtx::sort_from_type_key("tuple_bool"), Sort::bool());
    assert_eq!(ChcCtx::sort_from_type_key("tuple_u64"), Sort::bitvec(64));
}

#[test]
fn test_sort_from_type_key_tuple_bigint_preserves_int_sort() {
    // BigInt tuples should still resolve to Int (correct behavior)
    assert_eq!(ChcCtx::sort_from_type_key("tuple_BigInt"), Sort::int());
}

#[test]
fn test_sort_from_type_key_tuple_empty_suffix_maps_to_bv32() {
    assert_eq!(ChcCtx::sort_from_type_key("tuple_"), Sort::bitvec(32));
}

#[test]
fn test_sort_from_type_key_nested_array_reconstructs_recursive_sort() {
    let expected = Sort::array(
        Sort::bitvec(POINTER_WIDTH),
        Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bool()),
    );
    assert_eq!(ChcCtx::sort_from_type_key("arr_arr_bool"), expected);
}

#[test]
fn test_sort_from_type_key_nested_slice_reconstructs_recursive_sort() {
    let expected = Sort::array(
        Sort::bitvec(POINTER_WIDTH),
        Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8)),
    );
    assert_eq!(ChcCtx::sort_from_type_key("slice_arr_u8"), expected);
}

#[test]
fn test_sort_from_type_key_unknown_uses_opaque_byte_array_fallback() {
    assert_eq!(
        ChcCtx::sort_from_type_key("totally_unknown_sort_key"),
        ChcCtx::unknown_type_key_fallback_sort()
    );
}

#[test]
fn test_sort_from_type_key_custom_uppercase_adt_keys_match_prefix_rule() {
    let opaque_sort = ChcCtx::unknown_type_key_fallback_sort();

    assert!(
        memory_type_key_tables::has_prefix_type_key_rule("MyStr"),
        "custom DST type keys should match the dedicated uppercase-ADT rule"
    );
    assert!(
        memory_type_key_tables::has_prefix_type_key_rule("Inner"),
        "custom unsized struct type keys should match the dedicated uppercase-ADT rule"
    );
    assert!(
        !memory_type_key_tables::has_prefix_type_key_rule("totally_unknown_sort_key"),
        "lowercase unknown keys should still fall through to the generic fallback path"
    );
    assert_eq!(ChcCtx::sort_from_type_key("MyStr"), opaque_sort);
    assert_eq!(ChcCtx::sort_from_type_key("Inner"), opaque_sort);
}

#[test]
fn test_elem_sort_for_memory_array_large_datatype_width_overflow_uses_type_key_fallback() {
    with_test_ay_ctx_for_source(HUGE_TYPE_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_huge_blob_ptr");
        let ptr_ty = sig.inputs()[0];
        let huge_ty = match ptr_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => panic!("expected *const HugeBlob argument, got {:?}", ptr_ty.kind()),
        };

        let instance = find_instance_by_suffix(ctx.tcx, "probe_huge_blob_ptr");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_huge_blob_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let sort = chc_ctx.elem_sort_for_memory_array(huge_ty);
        // Part of #4126: after #4152 unwrap, elem_sort_for_memory_array returns
        // the element sort (BV8) instead of Array(BV64, BV8).
        assert_eq!(
            sort,
            Sort::bitvec(8),
            "size*8 overflow should fall back to byte-level element sort after #4152 unwrap"
        );
    });
}

#[test]
fn test_elem_sort_for_memory_array_union_with_known_layout_uses_size_bitvec() {
    with_test_ay_ctx_for_source(UNION_TYPE_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_union_arg");
        let union_ty = sig.inputs()[0];

        // Part of #3669: translate_ty now handles unions directly as bitvec.
        // Previously unions hit the None-arm fallback; W5:3805 added AdtKind::Union.
        let direct_sort = ChcCtx::translate_ty(union_ty);
        assert_eq!(
            direct_sort,
            Some(Sort::bitvec(32)),
            "4-byte union should translate directly to BV32 (Part of #3669)"
        );

        let instance = find_instance_by_suffix(ctx.tcx, "probe_union_arg");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_union_arg",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_eq!(chc_ctx.get_type_size(union_ty), Some(4), "union layout should be 4 bytes");

        let sort = chc_ctx.elem_sort_for_memory_array(union_ty);
        assert_eq!(sort, Sort::bitvec(32), "known-size union should map to size-based bitvec");
        assert_ne!(
            sort,
            ChcCtx::unknown_type_key_fallback_sort(),
            "union must not use opaque unknown fallback"
        );
    });
}

#[test]
fn test_elem_sort_for_memory_array_str_uses_element_size_bv8() {
    with_test_ay_ctx_for_source(STR_PTR_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_str_ptr");
        let ptr_ty = sig.inputs()[0];
        let str_ty = match ptr_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => panic!("expected *const str argument, got {:?}", ptr_ty.kind()),
        };

        // Part of #4251: translate_ty now handles bare `str` directly as
        // Array(ptr_sort, bv8_sort). The old None-arm assertion is obsolete —
        // keep the rest of the test intact since it still exercises the
        // get_type_size / type_key_for_ty / elem_sort_for_memory_array path
        // that unblocks Box<str> operations (#3655).
        assert!(
            ChcCtx::translate_ty(str_ty).is_some(),
            "str should translate to an explicit sort (#4251), not the None-arm"
        );

        let instance = find_instance_by_suffix(ctx.tcx, "probe_str_ptr");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_str_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Part of #3655: str element size is 1 (same as u8). This was previously
        // None, causing str to use the debug-format type key fallback path and
        // creating disconnected memory arrays for Box<str> operations.
        assert_eq!(
            chc_ctx.get_type_size(str_ty),
            Some(1),
            "str element size should be 1 (same as u8)"
        );

        // Part of #3655: type key for str maps to "slice_u8" (same as [u8]),
        // ensuring stores via [u8] and loads via str use the same partition.
        let type_key = ChcCtx::type_key_for_ty(str_ty);
        assert_eq!(type_key.as_ref(), "slice_u8", "str type key should be slice_u8");

        // With element size known (1), elem_sort_for_memory_array returns BV8
        // via the get_type_size path (1 * 8 = 8 bits) instead of the old
        // Slice_bv8 fat-pointer sort from sort_from_type_key fallback.
        let sort = chc_ctx.elem_sort_for_memory_array(str_ty);
        assert_eq!(sort, Sort::bitvec(8), "str elem sort should be BV8 (byte-level access)");
        assert_ne!(
            sort,
            ChcCtx::unknown_type_key_fallback_sort(),
            "str should not degrade to opaque unknown byte-array sort"
        );
    });
}

// ============================================================================
// type_key_for_ty edge coverage
// ============================================================================

#[test]
fn test_type_key_for_ty_ref_ptr_array_tuple_unit() {
    with_test_ay_ctx_for_source(TYPE_KEY_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_type_keys");
        let args = sig.inputs();

        assert_eq!(ChcCtx::type_key_for_ty(args[0]), "ref_u32");
        assert_eq!(ChcCtx::type_key_for_ty(args[1]), "ptr_i16");
        // Part of #3318: arrays now share type key with slices.
        assert_eq!(ChcCtx::type_key_for_ty(args[2]), "slice_u8");
        assert_eq!(ChcCtx::type_key_for_ty(args[4]), "tuple_u8_bool");
        assert_eq!(ChcCtx::type_key_for_ty(args[5]), "unit");
    });
}

#[test]
fn test_type_key_for_ty_slice_and_adt_names() {
    with_test_ay_ctx_for_source(TYPE_KEY_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_type_keys");
        let args = sig.inputs();

        // &[u8] should include both the outer ref and inner slice in the key.
        assert_eq!(ChcCtx::type_key_for_ty(args[3]), "ref_slice_u8");
        let inner_slice = match args[3].kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => panic!("expected &[u8] argument"),
        };
        assert_eq!(ChcCtx::type_key_for_ty(inner_slice), "slice_u8");

        let generic_key = ChcCtx::type_key_for_ty(args[6]);
        let plain_key = ChcCtx::type_key_for_ty(args[7]);
        assert!(generic_key.contains("GenericWrap"), "unexpected generic key: {generic_key}");
        assert!(generic_key.ends_with("_u16"), "generic arg key missing in: {generic_key}");
        assert!(plain_key.contains("Plain"), "unexpected plain key: {plain_key}");
        assert!(
            !plain_key.ends_with("_u16"),
            "plain key should not encode generic arg: {plain_key}"
        );
    });
}

#[test]
fn test_type_key_for_ty_transparent_pointer_wrappers_normalize_to_inner_pointer_key() {
    with_test_ay_ctx_for_source(TRANSPARENT_WRAPPER_TYPE_KEY_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_transparent_wrapper_keys");
        let args = sig.inputs();
        let instance = find_instance_by_suffix(ctx.tcx, "probe_transparent_wrapper_keys");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_transparent_wrapper_keys",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        for (idx, label) in [
            (0, "UnsafeCell<*mut i32>"),
            (1, "Cell<*mut i32>"),
            (2, "MaybeUninit<*mut i32>"),
            (3, "ManuallyDrop<*mut i32>"),
        ] {
            assert_eq!(
                ChcCtx::type_key_for_ty(args[idx]).as_ref(),
                "ptr_i32",
                "{label} should normalize to the inner pointer key"
            );
            assert_eq!(
                chc_ctx.type_key_for_body_ty(args[idx]).as_ref(),
                "ptr_i32",
                "{label} body type key should stay normalized"
            );
        }
    });
}

#[test]
fn test_type_key_for_ty_unresolved_param_uses_reconstructible_param_key() {
    with_test_ay_ctx_for_source(GENERIC_SIMD_TYPE_KEY_SOURCE, |ctx| {
        // Use CrateItem::body() for pre-monomorphization body (generic functions
        // cannot be converted to Instance via Instance::try_from).
        let item = find_crate_item_by_suffix(ctx.tcx, "probe_generic_keys");
        let body = item.body().expect("function body");
        let array_ty = body.locals()[2].ty;
        let elem_ty = match array_ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => elem_ty,
            _ => panic!("expected generic [T; LANES] argument, got {:?}", array_ty.kind()),
        };

        let elem_key = ChcCtx::type_key_for_ty(elem_ty);
        assert_eq!(elem_key, "param_0");
        assert_eq!(ChcCtx::sort_from_type_key(&elem_key), Sort::bitvec(POINTER_WIDTH));
    });
}

#[test]
fn test_sort_from_type_key_generic_array_param_reconstructs_pointer_array() {
    with_test_ay_ctx_for_source(GENERIC_SIMD_TYPE_KEY_SOURCE, |ctx| {
        // Use CrateItem::body() for pre-monomorphization body (generic functions
        // cannot be converted to Instance via Instance::try_from).
        let item = find_crate_item_by_suffix(ctx.tcx, "probe_generic_keys");
        let body = item.body().expect("function body");
        let array_ty = body.locals()[2].ty;
        let array_key = ChcCtx::type_key_for_ty(array_ty);
        let expected_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(POINTER_WIDTH));

        assert_eq!(array_key, "slice_param_0");
        assert_eq!(ChcCtx::sort_from_type_key(&array_key), expected_sort);
        assert_ne!(
            ChcCtx::sort_from_type_key(&array_key),
            ChcCtx::unknown_type_key_fallback_sort(),
            "generic array type key should stay reconstructible instead of falling to opaque sort"
        );
    });
}

#[test]
fn test_type_key_for_body_ty_resolves_monomorphized_generic_array_field() {
    with_test_ay_ctx_for_source(MONOMORPHIZED_GENERIC_FIELD_SOURCE, |ctx| {
        let concrete_ty = fn_sig_by_suffix(ctx.tcx, "probe_u16_anchor").inputs()[0];
        let instance = resolve_single_type_generic_instance_by_suffix(
            ctx.tcx,
            "probe_array_wrap",
            concrete_ty,
        );
        let body = instance.body().expect("resolved generic function body");
        let raw_sig = fn_sig_by_suffix(ctx.tcx, "probe_array_wrap");
        let wrap_ty = raw_sig.inputs()[0];
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = wrap_ty.kind() else {
            panic!("expected ArrayWrap<T> input, got {:?}", wrap_ty.kind());
        };
        let field_ty = def.variants()[0].fields()[0].ty();
        let chc_ctx = ChcCtx::new_with_instance(
            ctx.tcx,
            &body,
            instance,
            "probe_array_wrap",
            ChcConfig::default(),
        );

        assert_eq!(
            ChcCtx::type_key_for_ty(field_ty),
            "slice_param_0",
            "raw field type should stay generic without instance-aware resolution"
        );
        assert_eq!(chc_ctx.type_key_for_body_ty(field_ty), "slice_u16");
        // Part of #4126: after #4152 unwrap, elem_sort_for_memory_array returns
        // the element sort (BV16) instead of Array(BV64, BV16).
        assert_eq!(chc_ctx.elem_sort_for_memory_array(field_ty), Sort::bitvec(16));
    });
}

// ============================================================================
// Range<T> and Option<T> sort resolution (Part of #2323)
// ============================================================================

#[test]
fn test_sort_from_type_key_range_usize_structure() {
    let sort = ChcCtx::sort_from_type_key("std_ops_Range_usize");
    let dt = sort.datatype_sort().expect("Range sort should be a datatype");
    assert!(dt.name.contains("Range"), "sort name should contain 'Range', got: {}", dt.name);
    // Range is a struct: single constructor with 2 fields (fld_start, fld_end)
    assert_eq!(dt.constructors.len(), 1, "Range should have 1 constructor (struct)");
    let fields = &dt.constructors[0].fields;
    assert_eq!(fields.len(), 2, "Range should have 2 fields (start, end), got {}", fields.len());
    assert_eq!(fields[0].name, "fld_start");
    assert_eq!(fields[1].name, "fld_end");
    // Both fields should be bv64 (usize on 64-bit)
    assert_eq!(fields[0].sort, fields[1].sort, "start and end should have same sort");
}

#[test]
fn test_sort_from_type_key_range_i32_structure() {
    let sort = ChcCtx::sort_from_type_key("Range_i32");
    let dt = sort.datatype_sort().expect("Range<i32> sort should be a datatype");
    assert!(dt.name.contains("Range"), "sort name should contain 'Range', got: {}", dt.name);
    assert_eq!(dt.constructors.len(), 1, "Range should have 1 constructor (struct)");
    assert_eq!(dt.constructors[0].fields.len(), 2, "Range should have 2 fields");
}

#[test]
fn test_sort_from_type_key_option_usize_structure() {
    let sort = ChcCtx::sort_from_type_key("std_option_Option_usize");
    let dt = sort.datatype_sort().expect("Option sort should be a datatype");
    assert!(dt.name.contains("Option"), "sort name should contain 'Option', got: {}", dt.name);
    // Option is an enum: 2 constructors (None, Some)
    assert_eq!(dt.constructors.len(), 2, "Option should have 2 constructors (None, Some)");
    let none_ctor = dt.constructors.iter().find(|c| c.name.contains("None"));
    let some_ctor = dt.constructors.iter().find(|c| c.name.contains("Some"));
    assert!(none_ctor.is_some(), "Option should have a None constructor");
    assert!(some_ctor.is_some(), "Option should have a Some constructor");
    assert_eq!(none_ctor.unwrap().fields.len(), 0, "None constructor should have 0 fields");
    assert_eq!(some_ctor.unwrap().fields.len(), 1, "Some constructor should have 1 field");
}

#[test]
fn test_sort_from_type_key_option_i32_structure() {
    let sort = ChcCtx::sort_from_type_key("Option_i32");
    let dt = sort.datatype_sort().expect("Option<i32> sort should be a datatype");
    assert!(dt.name.contains("Option"), "sort name should contain 'Option', got: {}", dt.name);
    assert_eq!(dt.constructors.len(), 2, "Option should have 2 constructors (None, Some)");
}

#[test]
fn test_sort_from_type_key_range_not_opaque_fallback() {
    let opaque = ChcCtx::unknown_type_key_fallback_sort();
    let range_sort = ChcCtx::sort_from_type_key("std_ops_Range_usize");
    assert_ne!(range_sort, opaque, "Range sort must not be the opaque fallback");
}

#[test]
fn test_sort_from_type_key_option_not_opaque_fallback() {
    let opaque = ChcCtx::unknown_type_key_fallback_sort();
    let option_sort = ChcCtx::sort_from_type_key("std_option_Option_usize");
    assert_ne!(option_sort, opaque, "Option sort must not be the opaque fallback");
}

// ============================================================================
// sum_datatype_field_bits (Part of #2323: struct sort-size fallback)
// ============================================================================

#[test]
fn test_sum_datatype_field_bits_two_bv32_fields() {
    // Point-like struct: two bv32 fields → 64 bits
    let sort = struct_sort("Point", vec![("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))]);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&sort), Some(64));
}

#[test]
fn test_sum_datatype_field_bits_mixed_widths() {
    let sort = struct_sort(
        "Mixed",
        vec![("fld_a", Sort::bitvec(8)), ("fld_b", Sort::bitvec(32)), ("fld_c", Sort::bitvec(64))],
    );
    assert_eq!(ChcCtx::sum_datatype_field_bits(&sort), Some(104));
}

#[test]
fn test_sum_datatype_field_bits_bool_field_counts_as_byte() {
    let sort = struct_sort("BoolPair", vec![("fld_a", Sort::bool()), ("fld_b", Sort::bitvec(32))]);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&sort), Some(40));
}

#[test]
fn test_sum_datatype_field_bits_returns_none_for_non_scalar_field() {
    let sort =
        struct_sort("HasArray", vec![("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(8)))]);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&sort), None);
}

#[test]
fn test_sum_datatype_field_bits_recurses_into_nested_datatype_field() {
    // Part of #2516: nested structs now recurse instead of returning None
    let inner = struct_sort("Inner", vec![("fld_x", Sort::bitvec(32))]);
    let outer = struct_sort("Outer", vec![("fld_inner", inner)]);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&outer), Some(32));
}

#[test]
fn test_sum_datatype_field_bits_recurses_mixed_scalar_and_nested() {
    // Part of #2516: struct with both scalar and nested struct fields
    let inner =
        struct_sort("Inner", vec![("fld_a", Sort::bitvec(16)), ("fld_b", Sort::bitvec(16))]);
    let outer = struct_sort("Outer", vec![("fld_id", Sort::bitvec(64)), ("fld_inner", inner)]);
    // 64 + (16 + 16) = 96
    assert_eq!(ChcCtx::sum_datatype_field_bits(&outer), Some(96));
}

#[test]
fn test_sum_datatype_field_bits_recurses_deeply_nested() {
    // Part of #2516: three levels of nesting
    let level2 = struct_sort("L2", vec![("fld_v", Sort::bitvec(8))]);
    let level1 = struct_sort("L1", vec![("fld_nested", level2)]);
    let level0 = struct_sort("L0", vec![("fld_nested", level1)]);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&level0), Some(8));
}

#[test]
fn test_sum_datatype_field_bits_nested_with_array_field_returns_none() {
    // Nested struct containing an Array field still returns None
    let inner =
        struct_sort("InnerArr", vec![("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(8)))]);
    let outer = struct_sort("OuterArr", vec![("fld_inner", inner)]);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&outer), None);
}

#[test]
fn test_sum_datatype_field_bits_returns_none_for_non_datatype() {
    assert_eq!(ChcCtx::sum_datatype_field_bits(&Sort::bitvec(32)), None);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&Sort::bool()), None);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&Sort::int()), None);
}

#[test]
fn test_sum_datatype_field_bits_empty_struct_is_zero() {
    let fields: Vec<(&str, Sort)> = vec![];
    let sort = struct_sort("Empty", fields);
    assert_eq!(ChcCtx::sum_datatype_field_bits(&sort), Some(0));
}

/// Demonstrates that `sum_datatype_field_bits` returns raw field-width sums
/// without alignment padding. For `{ bool, i32 }`, Rust layout is 8 bytes
/// (64 bits) due to 3 bytes padding between the bool and i32 fields, but
/// `sum_datatype_field_bits` returns 40 bits (8 + 32).
///
/// This is a known limitation (documented in the function's doc comment).
/// When this fallback is used for memory array element sorts, the undersized
/// bitvec causes store values to be replaced with unconstrained symbolics
/// (sound over-approximation, but loses field-value precision).
///
/// Part of #2323: regression test documenting the padding gap.
#[test]
fn test_sum_datatype_field_bits_undercounts_padded_struct() {
    // Rust struct { flag: bool, value: i32 } has layout:
    //   offset 0: flag (1 byte)
    //   offset 1-3: padding (3 bytes)
    //   offset 4-7: value (4 bytes)
    //   total: 8 bytes = 64 bits
    //
    // But AY Datatype fields only record the logical sorts (Bool + bv32),
    // so sum_datatype_field_bits computes 8 + 32 = 40, not 64.
    let sort = struct_sort(
        "PaddedStruct",
        vec![("fld_flag", Sort::bool()), ("fld_value", Sort::bitvec(32))],
    );
    let result = ChcCtx::sum_datatype_field_bits(&sort);
    // This documents the current behavior (40 bits, not 64).
    // If this test fails because the function was fixed to account for
    // padding, that's an improvement — update the expected value to 64.
    assert_eq!(result, Some(40), "raw field sum without padding");
    // The correct padded size would be 64 bits (8 bytes).
    // assert_eq!(result, Some(64), "with padding — future improvement");
}

// ============================================================================
// Iterator/collection type key resolution (Part of #2516 Step 3)
// ============================================================================

#[test]
fn test_sort_from_type_key_slice_iter_is_fat_pointer() {
    let sort = ChcCtx::sort_from_type_key("std_slice_Iter_i32");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_slice_iter_mut_is_fat_pointer() {
    let sort = ChcCtx::sort_from_type_key("std_slice_IterMut_i32");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_vec_into_iter_is_triple_pointer() {
    let sort = ChcCtx::sort_from_type_key("std_vec_IntoIter_i32_std_alloc_Global");
    assert_eq!(sort, Sort::bitvec(3 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_hashbrown_bucket_is_thin_pointer() {
    let sort = ChcCtx::sort_from_type_key("hashbrown_raw_Bucket_tuple_i32_i32");
    assert_eq!(sort, Sort::bitvec(POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_hashbrown_into_iter_is_pointer_pair() {
    let sort = ChcCtx::sort_from_type_key("hashbrown_map_IntoIter_i32_i32_std_alloc_Global");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_hashbrown_raw_iter_is_pointer_pair() {
    let sort = ChcCtx::sort_from_type_key("hashbrown_raw_RawIter_tuple_i32_i32");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_hashbrown_raw_into_iter_is_pointer_pair() {
    let sort =
        ChcCtx::sort_from_type_key("hashbrown_raw_RawIntoIter_tuple_i32_i32_std_alloc_Global");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_hashbrown_raw_iter_range_is_pointer_pair() {
    let sort = ChcCtx::sort_from_type_key("hashbrown_raw_RawIterRange_tuple_i32_i32");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_std_collections_hash_set_into_iter() {
    let sort = ChcCtx::sort_from_type_key("std_collections_hash_set_IntoIter_i32");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_std_collections_hash_map_into_iter() {
    let sort = ChcCtx::sort_from_type_key("std_collections_hash_map_IntoIter_i32_i32");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_hashbrown_set_into_iter() {
    let sort = ChcCtx::sort_from_type_key("hashbrown_set_IntoIter_i32_std_alloc_Global");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_kani_map_into_iter() {
    let sort = ChcCtx::sort_from_type_key("kani_hashmap_TrustMcMapIntoIter_u32_u32");
    assert_eq!(sort, Sort::bitvec(2 * POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_niche_type_is_pointer_width() {
    let sort = ChcCtx::sort_from_type_key("core_num_niche_types_UsizeNoHighBit");
    assert_eq!(sort, Sort::bitvec(POINTER_WIDTH));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_sort_from_type_key_result_try_reserve_error() {
    let sort = ChcCtx::sort_from_type_key("std_result_Result_unit_std_collections_TryReserveError");
    assert_eq!(sort, Sort::bitvec(128));
    assert_ne!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

// Part of #3738 D3: negative regression — non-TryReserveError Result keys must NOT
// hit the BV128 special-case. They should fall through to the opaque fallback sort.
#[test]
fn test_sort_from_type_key_result_non_try_reserve_error_uses_opaque_fallback() {
    let sort = ChcCtx::sort_from_type_key("std_result_Result_u32_u8");
    assert_ne!(sort, Sort::bitvec(128), "Result<u32, u8> must not collapse to BV128");
    assert_eq!(
        sort,
        ChcCtx::unknown_type_key_fallback_sort(),
        "unrecognized Result key should use opaque byte-array fallback"
    );
}

#[test]
fn test_sort_from_type_key_result_bool_error_uses_opaque_fallback() {
    let sort = ChcCtx::sort_from_type_key("std_result_Result_bool_std_io_Error");
    assert_ne!(sort, Sort::bitvec(128), "Result<bool, io::Error> must not collapse to BV128");
    assert_eq!(sort, ChcCtx::unknown_type_key_fallback_sort());
}

#[test]
fn test_elem_sort_struct_fallback_uses_field_sum_when_layout_unavailable() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]

        pub struct Point {
            pub x: i32,
            pub y: i32,
        }

        pub fn probe_point(p: Point) {
            let _ = p;
        }
        "#,
        |ctx| {
            let sig = fn_sig_by_suffix(ctx.tcx, "probe_point");
            let point_ty = sig.inputs()[0];

            let translated = ChcCtx::translate_ty(point_ty);
            assert!(
                translated.as_ref().is_some_and(ay_bindings::Sort::is_datatype),
                "translate_ty(Point) should return a Datatype sort"
            );

            if let Some(dt_sort) = &translated {
                assert_eq!(
                    ChcCtx::sum_datatype_field_bits(dt_sort),
                    Some(64),
                    "Point should sum to 64 bits"
                );
            }

            let instance = find_instance_by_suffix(ctx.tcx, "probe_point");
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                "probe_point",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let sort = chc_ctx.elem_sort_for_memory_array(point_ty);
            assert_ne!(
                sort,
                ChcCtx::unknown_type_key_fallback_sort(),
                "Point should not get opaque byte-array fallback"
            );
            assert!(sort.is_bitvec(), "Point elem sort should be a bitvec");
        },
    );
}

// ============================================================================
// Sort consistency: sort_from_type_key vs sort_inference.rs (Fix #2379)
// ============================================================================

/// Verify Str type key produces "Slice_bv8" sort name matching sort_inference.rs.
#[test]
fn test_sort_from_type_key_str_matches_sort_inference_name() {
    let sort = ChcCtx::sort_from_type_key("ty_RigidTy_Str");
    let dt = sort.datatype_sort().expect("Str sort should be a datatype");
    assert_eq!(dt.name, "Slice_bv8", "Str type key sort name must match sort_inference.rs");
    assert_eq!(dt.constructors.len(), 1, "Slice_bv8 should have 1 constructor");
    let fields = &dt.constructors[0].fields;
    assert_eq!(fields.len(), 3, "Slice_bv8 should have 3 fields (fld_ptr, fld_len, fld_data)");
    assert_eq!(fields[0].name, "fld_ptr");
    assert_eq!(fields[1].name, "fld_len");
    assert_eq!(fields[2].name, "fld_data");
}

/// Verify Dynamic type key produces "Dyn_Trait" struct sort matching sort_inference.rs.
#[test]
fn test_sort_from_type_key_dynamic_matches_sort_inference_structure() {
    let sort = ChcCtx::sort_from_type_key("ty_RigidTy_Dynamic_Binder");
    let dt = sort.datatype_sort().expect("Dynamic sort should be a datatype");
    assert_eq!(dt.name, "Dyn_Trait", "Dynamic type key sort name must match sort_inference.rs");
    assert_eq!(dt.constructors.len(), 1, "Dyn_Trait should have 1 constructor");
    let fields = &dt.constructors[0].fields;
    assert_eq!(fields.len(), 2, "Dyn_Trait should have 2 fields (fld_ptr, fld_vtable)");
    assert_eq!(fields[0].name, "fld_ptr");
    assert_eq!(fields[1].name, "fld_vtable");
}

/// Verify Dynamic sort is NOT a flat bitvec (regression for #2379 finding 3).
#[test]
fn test_sort_from_type_key_dynamic_is_not_flat_bitvec() {
    let sort = ChcCtx::sort_from_type_key("ty_RigidTy_Dynamic_Binder");
    assert!(!sort.is_bitvec(), "Dynamic sort must be a struct, not a flat bitvec");
    assert!(sort.is_datatype(), "Dynamic sort must be a datatype (struct)");
}

/// Verify non-capturing closure type key still maps to Bool.
#[test]
fn test_sort_from_type_key_closure_non_capturing_is_bool() {
    let sort = ChcCtx::sort_from_type_key("ty_RigidTy_Closure_DefId_123");
    assert_eq!(sort, Sort::bool(), "non-capturing closure fallback should be Bool");
}

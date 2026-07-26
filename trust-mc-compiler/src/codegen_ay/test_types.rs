// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `codegen_ay::types` — type coercion utilities for AY expressions.
//!
//! Extracted from inline tests in `types.rs` per designs/2026-02-24-types-rs-decomposition.md.

#![allow(clippy::unwrap_used)]

use super::names::{enum_sort, struct_sort};
use super::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width, coerce_bitvec_width_safe, coerce_int_real,
    datatype_field_select, datatype_field_select_by_name, flatten_datatype_to_bitvec,
    flattenable_datatype_sort_width, float_ty_to_bitvec_width, int_ty_to_bitvec_width,
    uint_ty_to_bitvec_width, unflatten_bitvec_to_datatype, unwrap_single_field_datatype,
    unwrap_single_field_datatype_to_sort,
};
use ay_bindings::Expr;
use rustc_public::ty::{FloatTy, IntTy, UintTy};

#[test]
fn int_ty_widths_are_correct() {
    assert_eq!(int_ty_to_bitvec_width(IntTy::I8), 8);
    assert_eq!(int_ty_to_bitvec_width(IntTy::I16), 16);
    assert_eq!(int_ty_to_bitvec_width(IntTy::I32), 32);
    assert_eq!(int_ty_to_bitvec_width(IntTy::I64), 64);
    assert_eq!(int_ty_to_bitvec_width(IntTy::I128), 128);
    assert_eq!(int_ty_to_bitvec_width(IntTy::Isize), POINTER_WIDTH);
}

#[test]
fn uint_ty_widths_are_correct() {
    assert_eq!(uint_ty_to_bitvec_width(UintTy::U8), 8);
    assert_eq!(uint_ty_to_bitvec_width(UintTy::U16), 16);
    assert_eq!(uint_ty_to_bitvec_width(UintTy::U32), 32);
    assert_eq!(uint_ty_to_bitvec_width(UintTy::U64), 64);
    assert_eq!(uint_ty_to_bitvec_width(UintTy::U128), 128);
    assert_eq!(uint_ty_to_bitvec_width(UintTy::Usize), POINTER_WIDTH);
}

#[test]
fn float_ty_widths_are_correct() {
    assert_eq!(float_ty_to_bitvec_width(FloatTy::F16), 16);
    assert_eq!(float_ty_to_bitvec_width(FloatTy::F32), 32);
    assert_eq!(float_ty_to_bitvec_width(FloatTy::F64), 64);
    assert_eq!(float_ty_to_bitvec_width(FloatTy::F128), 128);
}

#[test]
fn coerce_bitvec_width_widen_and_narrow() {
    let expr = Expr::bitvec_const(1u8, 8);
    let widened = coerce_bitvec_width(expr.clone(), 16, SignExtension::ZeroExtend);
    assert_eq!(widened, expr.clone().zero_extend(8));

    let signed_widened = coerce_bitvec_width(expr.clone(), 16, SignExtension::SignExtend);
    assert_eq!(signed_widened, expr.clone().sign_extend(8));

    let narrowed = coerce_bitvec_width(expr.clone(), 4, SignExtension::ZeroExtend);
    assert_eq!(narrowed, expr.extract(3, 0));
}

#[test]
fn sign_extension_for_signedness_maps_bool_to_named_mode() {
    assert_eq!(SignExtension::for_signedness(true), SignExtension::SignExtend);
    assert_eq!(SignExtension::for_signedness(false), SignExtension::ZeroExtend);
}

#[test]
#[should_panic(expected = "coerce_bitvec_width requires target_width > 0")]
fn coerce_bitvec_width_rejects_zero_target_width() {
    let _ = coerce_bitvec_width(Expr::bitvec_const(1u8, 8), 0, SignExtension::ZeroExtend);
}

#[test]
fn coerce_bitvec_width_safe_non_bitvec() {
    let int_expr = Expr::int_const(7);
    let coerced = coerce_bitvec_width_safe(int_expr.clone(), 32, SignExtension::ZeroExtend);
    assert_eq!(coerced, int_expr);
}

#[test]
fn coerce_bitvec_width_safe_bool_to_bv() {
    // Part of #2244: Bool→BV coercion for sort mismatch prevention
    let bool_expr = Expr::bool_const(true);
    let coerced = coerce_bitvec_width_safe(bool_expr, 64, SignExtension::ZeroExtend);
    assert!(coerced.sort().is_bitvec());
    assert_eq!(coerced.sort().bitvec_width(), Some(64));
    // Should produce ite(true, BV64(1), BV64(0))
    let expected = Expr::ite(
        Expr::bool_const(true),
        Expr::bitvec_const(1u64, 64),
        Expr::bitvec_const(0u64, 64),
    );
    assert_eq!(coerced, expected);
}

#[test]
#[should_panic(expected = "coerce_bitvec_width_safe requires target_width > 0")]
fn coerce_bitvec_width_safe_rejects_zero_target_width() {
    let _ = coerce_bitvec_width_safe(Expr::bool_const(false), 0, SignExtension::ZeroExtend);
}

#[test]
fn coerce_int_real_int_to_real() {
    let int_expr = Expr::int_const(3);
    let real_expr = Expr::int_const(4).int_to_real();
    let (lhs, rhs) = coerce_int_real(int_expr.clone(), real_expr.clone());
    assert_eq!(lhs, int_expr.int_to_real());
    assert_eq!(rhs, real_expr);
}

#[test]
fn coerce_int_real_noop_on_same_sort() {
    let int_expr = Expr::int_const(11);
    let (lhs, rhs) = coerce_int_real(int_expr.clone(), Expr::int_const(12));
    assert_eq!(lhs, int_expr);
    assert_eq!(rhs, Expr::int_const(12));

    let real_expr = Expr::int_const(5).int_to_real();
    let (lhs, rhs) = coerce_int_real(real_expr.clone(), Expr::int_const(6).int_to_real());
    assert_eq!(lhs, real_expr);
    assert_eq!(rhs, Expr::int_const(6).int_to_real());
}

#[test]
fn unwrap_single_field_datatype_extracts_inner_field() {
    let tuple_sort = struct_sort("Tuple_bv64", vec![("fld_0", ay_bindings::Sort::bitvec(64))]);
    let tuple = Expr::var("_tuple", tuple_sort);

    let unwrapped = unwrap_single_field_datatype(&tuple)
        .expect("single-field datatype should unwrap to its inner field");
    assert_eq!(unwrapped.sort().bitvec_width(), Some(64));
}

#[test]
fn unwrap_single_field_datatype_to_sort_matches_target() {
    let tuple_sort = struct_sort("Tuple_bv32", vec![("fld_0", ay_bindings::Sort::bitvec(32))]);
    let tuple = Expr::var("_tuple", tuple_sort);

    assert!(
        unwrap_single_field_datatype_to_sort(&tuple, &ay_bindings::Sort::bitvec(32)).is_some(),
        "single-field datatype should unwrap when target sort matches field sort"
    );
    assert!(
        unwrap_single_field_datatype_to_sort(&tuple, &ay_bindings::Sort::bitvec(64)).is_none(),
        "single-field datatype should not unwrap when target sort differs"
    );
}

#[test]
fn datatype_field_select_extracts_field_by_index() {
    let sort = struct_sort(
        "Point",
        vec![("x", ay_bindings::Sort::bitvec(32)), ("y", ay_bindings::Sort::bitvec(64))],
    );
    let expr = Expr::var("_pt", sort);

    let x = datatype_field_select(expr.clone(), 0, 0).expect("field 0 should be selectable");
    assert_eq!(x.sort().bitvec_width(), Some(32));

    let y = datatype_field_select(expr.clone(), 0, 1).expect("field 1 should be selectable");
    assert_eq!(y.sort().bitvec_width(), Some(64));

    assert!(datatype_field_select(expr.clone(), 0, 2).is_none(), "out of range");
    assert!(datatype_field_select(expr, 1, 0).is_none(), "bad cons idx");
}

#[test]
fn datatype_field_select_returns_none_for_non_datatype() {
    let bv = Expr::bitvec_const(42u64, 64);
    assert!(datatype_field_select(bv, 0, 0).is_none());
}

#[test]
fn datatype_field_select_by_name_extracts_named_field() {
    let sort = struct_sort(
        "Vec_bv32",
        vec![
            (
                "fld_data",
                ay_bindings::Sort::array(
                    ay_bindings::Sort::bitvec(64),
                    ay_bindings::Sort::bitvec(32),
                ),
            ),
            ("fld_len", ay_bindings::Sort::bitvec(64)),
        ],
    );
    let expr = Expr::var("_vec", sort);

    let len = datatype_field_select_by_name(expr.clone(), 0, "fld_len")
        .expect("fld_len should be selectable");
    assert_eq!(len.sort().bitvec_width(), Some(64));

    assert!(datatype_field_select_by_name(expr, 0, "fld_missing").is_none());
}

#[test]
fn flatten_flat_struct_to_bitvec() {
    // Point { x: bv32, y: bv32 } -> bv64
    let point_sort = struct_sort(
        "Point",
        vec![("fld_x", ay_bindings::Sort::bitvec(32)), ("fld_y", ay_bindings::Sort::bitvec(32))],
    );
    let point = Expr::var("_pt", point_sort);
    let flat = flatten_datatype_to_bitvec(&point, 64)
        .expect("flat struct with matching width should flatten");
    assert!(flat.sort().is_bitvec());
    assert_eq!(flat.sort().bitvec_width(), Some(64));
}

#[test]
fn flatten_nested_struct_to_bitvec() {
    // Outer { inner: Point { x: bv32, y: bv32 }, value: bv32 } -> bv96
    let point_sort = struct_sort(
        "Point",
        vec![("fld_x", ay_bindings::Sort::bitvec(32)), ("fld_y", ay_bindings::Sort::bitvec(32))],
    );
    let outer_sort = struct_sort(
        "Outer",
        vec![("fld_inner", point_sort), ("fld_value", ay_bindings::Sort::bitvec(32))],
    );
    let outer = Expr::var("_outer", outer_sort);
    let flat = flatten_datatype_to_bitvec(&outer, 96)
        .expect("nested struct with matching width should flatten");
    assert!(flat.sort().is_bitvec());
    assert_eq!(flat.sort().bitvec_width(), Some(96));
}

#[test]
fn flatten_width_over_target_returns_none() {
    // Leaves sum (64) > target (32) → None
    let point_sort = struct_sort(
        "Point",
        vec![("fld_x", ay_bindings::Sort::bitvec(32)), ("fld_y", ay_bindings::Sort::bitvec(32))],
    );
    let point = Expr::var("_pt", point_sort);
    assert!(flatten_datatype_to_bitvec(&point, 32).is_none());
}

#[test]
fn flatten_width_under_target_zero_pads() {
    // Part of #2915: leaves sum (64) < target (128) → zero-padded to 128
    let point_sort = struct_sort(
        "Point",
        vec![("fld_x", ay_bindings::Sort::bitvec(32)), ("fld_y", ay_bindings::Sort::bitvec(32))],
    );
    let point = Expr::var("_pt", point_sort);
    let flat = flatten_datatype_to_bitvec(&point, 128).expect("under-target width should zero-pad");
    assert!(flat.sort().is_bitvec());
    assert_eq!(flat.sort().bitvec_width(), Some(128));
}

#[test]
fn flatten_bool_leaf_to_bv8() {
    // Part of #2915: Tuple(bv32, Bool) → bv8(bool) + bv32 + padding
    // Simulates ((u32, bool)) stored to memory
    let inner_sort = struct_sort(
        "Tuple_bv32_bool",
        vec![("fld_0", ay_bindings::Sort::bitvec(32)), ("fld_1", ay_bindings::Sort::bool())],
    );
    let inner = Expr::var("_tup", inner_sort);
    // Leaves: bv32 + bv8(from Bool) = 40 bits. Target: 64 (8 bytes with padding)
    let flat = flatten_datatype_to_bitvec(&inner, 64)
        .expect("Bool leaf should be converted to bv8 and zero-padded");
    assert!(flat.sort().is_bitvec());
    assert_eq!(flat.sort().bitvec_width(), Some(64));
}

#[test]
fn flatten_nested_with_bool_and_padding() {
    // Part of #2915: Tuple_Tuple_bv32_bool_bv8 → target bv96
    // This is the exact pattern from test_nested_tuple_field_mutation_smoke
    let inner_sort = struct_sort(
        "Tuple_bv32_bool",
        vec![("fld_0", ay_bindings::Sort::bitvec(32)), ("fld_1", ay_bindings::Sort::bool())],
    );
    let outer_sort = struct_sort(
        "Tuple_Tuple_bv32_bool_bv8",
        vec![("fld_0", inner_sort), ("fld_1", ay_bindings::Sort::bitvec(8))],
    );
    let outer = Expr::var("_nested", outer_sort);
    // Leaves: bv32 + bv8(Bool) + bv8 = 48 bits. Target: 96 (12 bytes with padding)
    let flat = flatten_datatype_to_bitvec(&outer, 96)
        .expect("nested struct with Bool should flatten with padding");
    assert!(flat.sort().is_bitvec());
    assert_eq!(flat.sort().bitvec_width(), Some(96));
}

#[test]
fn flatten_struct_with_array_field_skips_array_and_pads() {
    // Part of #2915: Struct with an Array field — the Array is a CHC
    // abstraction for variable-length data. collect_bv_leaves skips it
    // (0 bits), and flatten_datatype_to_bitvec zero-pads to target width.
    let sort = struct_sort(
        "WithArray",
        vec![
            ("fld_len", ay_bindings::Sort::bitvec(64)),
            (
                "fld_data",
                ay_bindings::Sort::array(
                    ay_bindings::Sort::bitvec(64),
                    ay_bindings::Sort::bitvec(32),
                ),
            ),
        ],
    );
    let expr = Expr::var("_wa", sort);
    let result = flatten_datatype_to_bitvec(&expr, 96);
    assert!(result.is_some(), "Array fields should be skipped, not block flattening");
    // Result is fld_len(64) concat pad(32) = BV(96)
    assert_eq!(
        result.as_ref().expect("result should be Some").sort().bitvec_width(),
        Some(96),
        "flattened width should match target"
    );
}

#[test]
fn flatten_nested_iter_datatype_with_array_to_bitvec() {
    // Part of #2915: IntoIter-like nested datatype with Array field.
    // Models the exact pattern that caused store drops:
    //   IntoIter { inner: PolymorphicIter { alive: IndexRange { start:64, end:64 }, data: Array } }
    let index_range = struct_sort(
        "IndexRange",
        [("fld_start", ay_bindings::Sort::bitvec(64)), ("fld_end", ay_bindings::Sort::bitvec(64))],
    );
    let poly_iter = struct_sort(
        "PolymorphicIter",
        [
            ("fld_alive", index_range),
            (
                "fld_data",
                ay_bindings::Sort::array(
                    ay_bindings::Sort::bitvec(64),
                    ay_bindings::Sort::bitvec(8),
                ),
            ),
        ],
    );
    let into_iter = struct_sort("IntoIter", [("fld_inner", poly_iter)]);
    let expr = Expr::var("_iter", into_iter);
    let result = flatten_datatype_to_bitvec(&expr, 128);
    assert!(result.is_some(), "nested IntoIter with Array should flatten via Array skip");
    assert_eq!(result.as_ref().expect("result should be Some").sort().bitvec_width(), Some(128));
}

#[test]
fn flatten_non_datatype_returns_none() {
    let bv = Expr::bitvec_const(42u64, 64);
    assert!(flatten_datatype_to_bitvec(&bv, 64).is_none());
}

#[test]
fn flatten_option_like_enum_to_bitvec_is_supported() {
    let option_sort = enum_sort(
        "Option_u8",
        vec![
            ("None_Option_u8", vec![]),
            ("Some_Option_u8", vec![("value", ay_bindings::Sort::bitvec(8))]),
        ],
    );
    let option_expr = Expr::var("_opt", option_sort);
    let flattened = flatten_datatype_to_bitvec(&option_expr, 16)
        .expect("2-constructor option-like enum should flatten to bv16");
    assert_eq!(flattened.sort(), &ay_bindings::Sort::bitvec(16));
}

#[test]
fn flatten_two_payload_enum_returns_bitvec() {
    // Part of #3041: generalized from option-only to all 2-constructor enums.
    // Result<u8,u8> has two 8-bit payload variants → [tag:8 | payload:8] = 16 bits.
    let result_like_sort = enum_sort(
        "Result_u8_u8",
        vec![
            ("Ok_Result_u8_u8", vec![("ok", ay_bindings::Sort::bitvec(8))]),
            ("Err_Result_u8_u8", vec![("err", ay_bindings::Sort::bitvec(8))]),
        ],
    );
    let expr = Expr::var("_result", result_like_sort);
    let flattened = flatten_datatype_to_bitvec(&expr, 16)
        .expect("2-constructor enum with matching payload should flatten");
    assert_eq!(flattened.sort(), &ay_bindings::Sort::bitvec(16));
}

#[test]
fn unflatten_bitvec_to_option_like_datatype_returns_datatype_expr() {
    let option_sort = enum_sort(
        "Option_u8",
        vec![
            ("None_Option_u8", vec![]),
            ("Some_Option_u8", vec![("value", ay_bindings::Sort::bitvec(8))]),
        ],
    );
    let encoded = Expr::bitvec_const(0x0104u64, 16);
    let rebuilt = unflatten_bitvec_to_datatype(&encoded, &option_sort)
        .expect("option-like bv16 encoding should decode to datatype");
    assert_eq!(rebuilt.sort(), &option_sort);
}

#[test]
fn unflatten_bitvec_to_single_constructor_struct_returns_datatype_expr() {
    // Part of #2969: Single-constructor struct round-trip (BoxPair-like).
    // flatten: Point { x: bv32, y: bv32 } → bv64 (MSB-first, no padding)
    // unflatten: bv64 → Point { x: bv32, y: bv32 }
    let point_sort = struct_sort(
        "Point",
        vec![("fld_x", ay_bindings::Sort::bitvec(32)), ("fld_y", ay_bindings::Sort::bitvec(32))],
    );
    let point = Expr::var("_pt", point_sort.clone());
    let flat = flatten_datatype_to_bitvec(&point, 64).expect("flat struct should flatten to bv64");
    assert_eq!(flat.sort().bitvec_width(), Some(64));
    let rebuilt = unflatten_bitvec_to_datatype(&flat, &point_sort)
        .expect("bv64 should unflatten back to Point struct");
    assert_eq!(rebuilt.sort(), &point_sort);
}

#[test]
fn unflatten_bitvec_to_padded_struct_returns_datatype_expr() {
    // Part of #2969: Struct with alignment padding (TestStruct-like).
    // TestStruct { x: u32, y: u64 } → total_field_bits = 96, target = 128 (with padding)
    // Fields at HIGH end, padding at LOW end (matching flatten encoding).
    let ts_sort = struct_sort(
        "TestStruct",
        vec![("fld_x", ay_bindings::Sort::bitvec(32)), ("fld_y", ay_bindings::Sort::bitvec(64))],
    );
    let ts = Expr::var("_ts", ts_sort.clone());
    let flat = flatten_datatype_to_bitvec(&ts, 128)
        .expect("mixed-width struct should flatten to bv128 with padding");
    assert_eq!(flat.sort().bitvec_width(), Some(128));
    let rebuilt = unflatten_bitvec_to_datatype(&flat, &ts_sort)
        .expect("bv128 should unflatten back to TestStruct with padding extraction");
    assert_eq!(rebuilt.sort(), &ts_sort);
}

// Part of #3328: sort-level width must use min_tag_bits + enum_leaf_width,
// matching expression-level flatten encoding.

#[test]
fn sort_width_option_bool_uses_min_tag_bits() {
    // Option<bool>: 1-bit tag + 1-bit Bool payload = 2 bits (not 8+8=16).
    let option_bool = enum_sort(
        "Option_bool",
        vec![
            ("None_Option_bool", vec![]),
            ("Some_Option_bool", vec![("value", ay_bindings::Sort::bool())]),
        ],
    );
    assert_eq!(flattenable_datatype_sort_width(&option_bool), Some(2));
}

#[test]
fn sort_width_option_u8_uses_min_tag_bits() {
    // Option<u8>: 1-bit tag + 8-bit payload = 9 bits (not 8+8=16).
    let option_u8 = enum_sort(
        "Option_u8",
        vec![
            ("None_Option_u8", vec![]),
            ("Some_Option_u8", vec![("value", ay_bindings::Sort::bitvec(8))]),
        ],
    );
    assert_eq!(flattenable_datatype_sort_width(&option_u8), Some(9));
}

#[test]
fn sort_width_result_u8_u16_uses_min_tag_bits() {
    // Result<u8, u16>: 1-bit tag + max(8, 16) = 17 bits (not 8+16=24).
    let result_sort = enum_sort(
        "Result_u8_u16",
        vec![
            ("Ok_Result_u8_u16", vec![("ok", ay_bindings::Sort::bitvec(8))]),
            ("Err_Result_u8_u16", vec![("err", ay_bindings::Sort::bitvec(16))]),
        ],
    );
    assert_eq!(flattenable_datatype_sort_width(&result_sort), Some(17));
}

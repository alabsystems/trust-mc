// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// Tests for switchint_case_guard

#[test]
fn test_switchint_case_guard_bool_false() {
    // Bool discriminant, case value 0 means "false" branch
    let discr = Expr::var("b", Sort::bool());
    let guard = ChcCtx::switchint_case_guard(&discr, 0, 0);
    assert!(guard.is_some());
    // Guard should be "not b" (b == false)
    let g = guard.unwrap();
    assert!(g.sort().is_bool());
    // Verify the guard is actually (not b), not some other Bool expression
    let smt = g.to_string();
    assert!(smt.contains("not"), "Bool case=0 guard should be (not b), got: {smt}");
}

#[test]
fn test_switchint_case_guard_bool_true() {
    // Bool discriminant, case value 1 means "true" branch
    let discr = Expr::var("b", Sort::bool());
    let guard = ChcCtx::switchint_case_guard(&discr, 1, 0);
    assert!(guard.is_some());
    // Guard should be "b" (b == true) — the discriminant itself, not (not b)
    let g = guard.unwrap();
    assert!(g.sort().is_bool());
    let smt = g.to_string();
    assert!(!smt.contains("not"), "Bool case=1 guard should be b (no negation), got: {smt}");
}

#[test]
fn test_switchint_case_guard_bool_invalid() {
    // Bool discriminant, case value outside 0/1 returns false constant (unreachable branch)
    let discr = Expr::var("b", Sort::bool());
    let guard = ChcCtx::switchint_case_guard(&discr, 42, 0);
    // Implementation returns Some(false) for invalid bool cases to mark unreachable branches
    assert!(guard.is_some(), "Invalid bool case returns false constant for unreachable branch");
    let g = guard.unwrap();
    assert!(g.sort().is_bool());
    // Verify the guard is the constant `false`, marking the branch as unreachable
    let smt = g.to_string();
    assert!(smt.contains("false"), "Invalid bool case guard should be constant false, got: {smt}");
}

#[test]
fn test_switchint_case_guard_bitvec() {
    // Bitvector discriminant: guard should be (= x #x0000002a)
    let discr = Expr::var("x", Sort::bitvec(32));
    let guard = ChcCtx::switchint_case_guard(&discr, 42, 0);
    assert!(guard.is_some());
    let g = guard.unwrap();
    assert!(g.sort().is_bool());
    // Verify the guard checks equality with the case value 42
    let smt = g.to_string();
    assert!(
        smt.contains('=') && smt.contains('x'),
        "BV guard should be equality check on x, got: {smt}"
    );
}

#[test]
fn test_switchint_case_guard_int() {
    // Int discriminant: guard should be (= x 100)
    let discr = Expr::var("x", Sort::int());
    let guard = ChcCtx::switchint_case_guard(&discr, 100, 0);
    assert!(guard.is_some());
    let g = guard.unwrap();
    assert!(g.sort().is_bool());
    // Verify the guard checks equality with the case value 100
    let smt = g.to_string();
    assert!(
        smt.contains('=') && smt.contains("100"),
        "Int guard should be equality check with 100, got: {smt}"
    );
}

#[test]
fn test_switchint_case_guard_int_large_value() {
    // Int discriminant with large value - BigInt handles arbitrary precision
    let discr = Expr::var("x", Sort::int());
    let guard = ChcCtx::switchint_case_guard(&discr, u128::MAX, 0);
    assert!(guard.is_some(), "BigInt handles u128::MAX");
    let g = guard.unwrap();
    assert!(g.sort().is_bool());
    let smt = g.to_string();
    assert!(smt.contains('x'), "Guard should reference discriminant var, got: {smt}");
    assert!(smt.contains('='), "Guard should be an equality check, got: {smt}");
}

#[test]
fn test_switchint_case_guard_unsupported_sort() {
    // Unsupported sort (Real) should return None
    let discr = Expr::var("r", Sort::real());
    let guard = ChcCtx::switchint_case_guard(&discr, 0, 0);
    assert!(guard.is_none(), "Unsupported sort should return None");
}

// Tests for ADT type encoding (Range, Option)

#[test]
fn test_adt_struct_sort_encoding() {
    // Range<u32> should encode as a struct with start/end fields
    let range_sort =
        struct_sort("Range", [("fld_start", Sort::bitvec(32)), ("fld_end", Sort::bitvec(32))]);

    assert_eq!(range_sort.datatype_name(), Some("Range"));
    // Verify field selection works — proves the struct is properly constructed
    let range_var = Expr::var("r", range_sort);
    let start = select_field_val(&range_var, 0, None);
    assert!(start.is_some(), "Field 0 (start) should be selectable");
    assert_eq!(start.unwrap().sort().bitvec_width(), Some(32));
    let end = select_field_val(&range_var, 1, None);
    assert!(end.is_some(), "Field 1 (end) should be selectable");
}

#[test]
fn test_adt_option_sort_encoding() {
    // (#686) Option<u32> encodes as struct (is_some: Bool, value: bv32) for CHC compatibility
    let option_sort =
        struct_sort("Option", [("is_some", Sort::bool()), ("value", Sort::bitvec(32))]);

    assert_eq!(option_sort.datatype_name(), Some("Option"));
    // Verify both fields are accessible with correct sorts
    let opt_var = Expr::var("o", option_sort);
    let is_some = select_field_val(&opt_var, 0, None);
    assert!(is_some.is_some());
    assert!(is_some.unwrap().sort().is_bool(), "Field 0 should be Bool (is_some)");
    let value = select_field_val(&opt_var, 1, None);
    assert!(value.is_some());
    assert_eq!(value.unwrap().sort().bitvec_width(), Some(32), "Field 1 should be bv32 (value)");
}

#[test]
fn test_adt_result_like_enum_encoding() {
    // Result<T, E> encodes as enum with Ok/Err constructors.
    // Accessor names must be globally unique across constructors (#776).
    let result_sort = enum_sort(
        "Result",
        vec![
            ("Ok", vec![("Ok_field_0", Sort::bitvec(32))]),
            ("Err", vec![("Err_field_0", Sort::bitvec(64))]),
        ],
    );

    assert_eq!(result_sort.datatype_name(), Some("Result"));
    // Verify field selection with constructor downcasts
    let res_var = Expr::var("res", result_sort);
    let ok_val = select_field_val(&res_var, 0, Some(0));
    assert!(ok_val.is_some(), "Ok variant field should be selectable");
    assert_eq!(ok_val.unwrap().sort().bitvec_width(), Some(32));
    let err_val = select_field_val(&res_var, 0, Some(1));
    assert!(err_val.is_some(), "Err variant field should be selectable");
    assert_eq!(err_val.unwrap().sort().bitvec_width(), Some(64));
}

#[test]
fn test_adt_nested_struct_encoding() {
    // IndexRange (used in iterator encoding) is a struct with two bv64 fields
    let index_range_sort =
        struct_sort("IndexRange", [("fld_start", Sort::bitvec(64)), ("fld_end", Sort::bitvec(64))]);

    assert_eq!(index_range_sort.datatype_name(), Some("IndexRange"));
    // Verify the sort can be used in expressions and fields are accessible
    let range_var = Expr::var("range", index_range_sort);
    let start = select_field_val(&range_var, 0, None);
    assert!(start.is_some());
    assert_eq!(start.unwrap().sort().bitvec_width(), Some(64));
}

#[test]
fn test_option_value_sort_extracts_some_field() {
    // Test fix for #821: option_value_sort should find the Some variant's first field
    // regardless of field name (not just "value")
    let option_sort =
        enum_sort("Option", vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let inner = option_value_sort(&option_sort);
    assert!(inner.is_some());
    assert_eq!(inner.unwrap().bitvec_width(), Some(32));
}

#[test]
fn test_option_value_sort_with_custom_field_name() {
    // Test fix for #821: option_value_sort works even with custom field names
    let option_sort = enum_sort(
        "CustomOption",
        vec![("None", vec![]), ("Some", vec![("payload", Sort::bitvec(64))])],
    );
    let inner = option_value_sort(&option_sort);
    assert!(inner.is_some());
    assert_eq!(inner.unwrap().bitvec_width(), Some(64));
}

#[test]
fn test_option_value_sort_fallback_for_non_some() {
    // Test fallback: if no "Some" constructor, find any single-field constructor
    let custom_option = enum_sort(
        "MaybeValue",
        vec![("Empty", vec![]), ("HasValue", vec![("data", Sort::bool())])],
    );
    let inner = option_value_sort(&custom_option);
    // Fallback should find HasValue's field since it's a single-field non-None constructor
    assert!(inner.is_some());
    assert!(inner.unwrap().is_bool());
}

#[test]
fn test_option_payload_variant_name_standard() {
    // Test helper finds "Some" for standard Option
    let option_sort =
        enum_sort("Option", vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let name = option_payload_variant_name(&option_sort);
    assert_eq!(name, Some("Some"));
}

#[test]
fn test_option_payload_variant_name_custom() {
    // Test helper finds custom payload variant name
    let custom_option = enum_sort(
        "MaybeValue",
        vec![("Empty", vec![]), ("HasValue", vec![("data", Sort::bool())])],
    );
    let name = option_payload_variant_name(&custom_option);
    assert_eq!(name, Some("HasValue"));
}

#[test]
fn test_option_empty_variant_name_standard() {
    // Test helper finds "None" for standard Option
    let option_sort =
        enum_sort("Option", vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let name = option_empty_variant_name(&option_sort);
    assert_eq!(name, Some("None"));
}

#[test]
fn test_option_empty_variant_name_custom() {
    // Test helper finds custom empty variant name
    let custom_option = enum_sort(
        "MaybeValue",
        vec![("Empty", vec![]), ("HasValue", vec![("data", Sort::bool())])],
    );
    let name = option_empty_variant_name(&custom_option);
    assert_eq!(name, Some("Empty"));
}

#[test]
fn test_option_helpers_return_none_for_invalid_structure() {
    // Test edge case: all constructors have multiple fields (no Option-like pattern)
    let not_option = enum_sort(
        "NotOption",
        vec![
            ("First", vec![("a", Sort::bool()), ("b", Sort::int())]),
            ("Second", vec![("c", Sort::bool()), ("d", Sort::int())]),
        ],
    );
    // option_value_sort should return None - no single-field constructor
    assert!(option_value_sort(&not_option).is_none());
    // option_payload_variant_name should return None
    assert!(option_payload_variant_name(&not_option).is_none());
    // option_empty_variant_name should return None - no zero-field constructor
    assert!(option_empty_variant_name(&not_option).is_none());
}

#[test]
fn test_option_value_sort_returns_none_for_non_datatype() {
    // Test edge case: non-datatype sort
    let bv_sort = Sort::bitvec(32);
    assert!(option_value_sort(&bv_sort).is_none());
    assert!(option_payload_variant_name(&bv_sort).is_none());
    assert!(option_empty_variant_name(&bv_sort).is_none());
}

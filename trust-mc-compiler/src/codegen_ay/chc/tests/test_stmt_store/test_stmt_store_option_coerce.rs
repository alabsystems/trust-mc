// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_coerce_store_value_option_storage_marker_array_payload_preserves_discriminant() {
    let _ = take_pending_fresh_var_decls();
    let payload_array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let target_option_sort = enum_sort(
        "Option_arr_bv64_bv8",
        [
            ("None_Option_arr_bv64_bv8", vec![]),
            ("Some_Option_arr_bv64_bv8", vec![("value_Option_arr_bv64_bv8", payload_array_sort)]),
        ],
    );
    let node_ref_sort = struct_sort(
        "NodeRef_marker_Dying_marker_Leaf",
        [
            ("fld_height", Sort::bitvec(64)),
            ("fld_node", Sort::bitvec(64)),
            ("fld__marker", Sort::bool()),
        ],
    );
    let edge_handle_sort = struct_sort(
        "Handle_NodeRef_marker_Dying_marker_Leaf_marker_Edge",
        [
            ("fld_node", node_ref_sort.clone()),
            ("fld_idx", Sort::bitvec(64)),
            ("fld__marker", Sort::bool()),
        ],
    );
    let lazy_leaf_handle_sort = enum_sort(
        "LazyLeafHandle_marker_Dying",
        [
            ("Root_LazyLeafHandle_marker_Dying", vec![("Root_field_0", node_ref_sort)]),
            ("Edge_LazyLeafHandle_marker_Dying", vec![("Edge_field_0", edge_handle_sort)]),
        ],
    );
    let source_option_sort = enum_sort(
        "Option_LazyLeafHandle_marker_Dying",
        [
            ("None_Option_LazyLeafHandle_marker_Dying", vec![]),
            (
                "Some_Option_LazyLeafHandle_marker_Dying",
                vec![("value_Option_LazyLeafHandle_marker_Dying", lazy_leaf_handle_sort)],
            ),
        ],
    );
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), target_option_sort.clone());
    let value = Expr::var("_storage_marker_option", source_option_sort);
    let diagnostics = ChcDiagnostics::default();

    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);

    assert_eq!(
        *result.sort(),
        target_option_sort,
        "StorageMarkers-shaped Option store coercion should produce target Option sort"
    );
    assert_eq!(
        diagnostics.aggregate_encoding_gap.get(),
        0,
        "Option datatype coercion should avoid the fresh-symbolic fallback"
    );
    assert!(
        take_pending_fresh_var_decls().is_empty(),
        "Option datatype coercion should not declare __store_val fresh symbolics"
    );
    let result_s = result.to_string();
    assert!(
        result_s.contains("Some_Option_arr_bv64_bv8")
            && result_s.contains("None_Option_arr_bv64_bv8"),
        "coerced Option should preserve the source discriminant with target constructors: {result_s}"
    );
}

#[test]
fn test_coerce_store_value_option_payload_width_coercion_avoids_fresh_symbolic() {
    let _ = take_pending_fresh_var_decls();
    let target_option_sort = enum_sort(
        "Option_bv32",
        [
            ("None_Option_bv32", vec![]),
            ("Some_Option_bv32", vec![("value_Option_bv32", Sort::bitvec(32))]),
        ],
    );
    let source_option_sort = enum_sort(
        "Option_bv64",
        [
            ("None_Option_bv64", vec![]),
            ("Some_Option_bv64", vec![("value_Option_bv64", Sort::bitvec(64))]),
        ],
    );
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), target_option_sort.clone());
    let value = Expr::var("_wide_option", source_option_sort);
    let diagnostics = ChcDiagnostics::default();

    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);

    assert_eq!(*result.sort(), target_option_sort, "coerced Option should match target sort");
    assert_eq!(
        diagnostics.aggregate_encoding_gap.get(),
        0,
        "coercible Option payload mismatch should not use the fresh-symbolic fallback"
    );
    assert!(
        take_pending_fresh_var_decls().is_empty(),
        "coercible Option payload mismatch should not declare a fresh store value"
    );
}

#[test]
fn test_coerce_store_value_bv_to_option_uses_niche_encoding() {
    let _ = take_pending_fresh_var_decls();
    let target_option_sort = enum_sort(
        "Option_bv64",
        [
            ("None_Option_bv64", vec![]),
            ("Some_Option_bv64", vec![("value_Option_bv64", Sort::bitvec(64))]),
        ],
    );
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), target_option_sort.clone());
    let value = Expr::var("_nonnull_payload", Sort::bitvec(64));
    let diagnostics = ChcDiagnostics::default();

    let result = ChcCtx::coerce_store_value(&arr_sort, value, false, &diagnostics);

    assert_eq!(
        *result.sort(),
        target_option_sort,
        "BV payload stored into Option mirror should produce target Option sort"
    );
    assert_eq!(
        diagnostics.aggregate_encoding_gap.get(),
        0,
        "BV to Option niche coercion should not use the fresh-symbolic fallback"
    );
    assert!(
        take_pending_fresh_var_decls().is_empty(),
        "BV to Option niche coercion should not declare a fresh store value"
    );
    let result_s = result.to_string();
    assert!(
        result_s.contains("Some_Option_bv64")
            && result_s.contains("None_Option_bv64")
            && result_s.contains("_nonnull_payload"),
        "coerced Option should preserve payload and both niche constructors: {result_s}"
    );
}

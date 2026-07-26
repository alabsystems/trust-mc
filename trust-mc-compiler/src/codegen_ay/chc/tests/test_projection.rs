// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// ===== Projection Handling Tests (#600) =====

#[test]
fn test_datatype_field_select_struct() {
    // Test field selection on a struct type
    let p = Expr::var("p", point_sort_prefixed());

    // Select field 0 (x)
    let x = ChcCtx::datatype_field_select(&p, 0, None);
    assert!(x.is_some());
    let x = x.unwrap();
    assert_eq!(x.sort().bitvec_width(), Some(32));
    let smt = x.to_string();
    assert!(smt.contains("fld_x"), "Field 0 select should reference 'fld_x', got: {smt}");

    // Select field 1 (y) — distinct from field 0
    let y = ChcCtx::datatype_field_select(&p, 1, None);
    assert!(y.is_some());
    let y = y.unwrap();
    assert!(y.sort().is_bitvec());
    assert_ne!(x.to_string(), y.to_string(), "Different fields must produce different expressions");
}

#[test]
fn test_datatype_field_select_out_of_bounds() {
    // Test field selection with invalid field index
    let p = Expr::var("p", point_sort_prefixed());

    // Field index 5 is out of bounds
    let result = ChcCtx::datatype_field_select(&p, 5, None);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_select_non_datatype() {
    // Field selection on non-datatype should return None
    let x = Expr::var("x", Sort::bitvec(32));
    let result = ChcCtx::datatype_field_select(&x, 0, None);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_update_struct() {
    // Test field update on a struct type
    let sort = point_sort_prefixed();
    let p = Expr::var("p", sort.clone());
    let new_x = Expr::bitvec_const(42, 32);

    // Update field 0 (x) with new value
    let updated = ChcCtx::datatype_field_update(&p, 0, None, new_x);
    assert!(updated.is_some());
    let updated = updated.unwrap();
    assert!(updated.sort().is_datatype());
    assert_eq!(updated.sort(), &sort);
}

#[test]
fn test_datatype_field_update_sort_mismatch() {
    // Field update with wrong sort should return None
    let p = Expr::var("p", point_sort_prefixed());
    let wrong_sort = Expr::bool_const(true); // Bool instead of BV32

    let result = ChcCtx::datatype_field_update(&p, 0, None, wrong_sort);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_update_unwraps_single_field_rhs() {
    let p = Expr::var("p", point_sort_prefixed());
    let tuple_sort = struct_sort("Tuple_bv32", [("fld_0", Sort::bitvec(32))]);
    let wrapped = Expr::var("_wrapped", tuple_sort);

    let result = ChcCtx::datatype_field_update(&p, 0, None, wrapped.clone());
    assert!(result.is_some(), "single-field datatype rhs should be unwrapped for field update");

    let updated = result.expect("field update should succeed");
    let expected_x = wrapped.field_select("Tuple_bv32", "fld_0", Sort::bitvec(32));
    let ExprValue::DatatypeConstructor { args, .. } = updated.value() else {
        unreachable!("updated point should be a datatype constructor");
    };
    assert_eq!(
        args.first().expect("Point constructor should have fld_x"),
        &expected_x,
        "updated field should use unwrapped rhs value"
    );
}

#[test]
fn test_datatype_field_select_enum_with_downcast() {
    // Test field selection on enum type with constructor index
    let option_sort =
        enum_sort("Option", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let opt = Expr::var("opt", option_sort);

    // Select field 0 from constructor 1 (Some.value)
    let value = ChcCtx::datatype_field_select(&opt, 0, Some(1));
    assert!(value.is_some());
    let value = value.unwrap();
    assert_eq!(value.sort().bitvec_width(), Some(32));
    let smt = value.to_string();
    assert!(smt.contains("value"), "Enum field select should reference field 'value', got: {smt}");
}

#[test]
fn test_datatype_field_select_option_ite_reconstruction_returns_payload() {
    let option_sort = enum_sort(
        "Option_i16",
        [("None_Option_i16", vec![]), ("Some_Option_i16", vec![("value", Sort::bitvec(16))])],
    );
    let is_some = Expr::var("is_some", Sort::bool());
    let payload = Expr::var("payload", Sort::bitvec(16));
    let some = Expr::datatype_constructor(
        "Option_i16",
        "Some_Option_i16",
        vec![payload.clone()],
        option_sort.clone(),
    );
    let none = Expr::datatype_constructor("Option_i16", "None_Option_i16", vec![], option_sort);
    let reconstructed = Expr::ite(is_some, some, none);

    let value = ChcCtx::datatype_field_select(&reconstructed, 0, Some(1));
    assert!(value.is_some(), "expected payload extraction from reconstructed option ITE");
    assert_eq!(value.unwrap().to_string(), payload.to_string());
}

#[test]
fn test_datatype_field_select_option_nested_ite_avoids_selector_over_ite() {
    let option_sort = enum_sort(
        "Option_i16",
        [("None_Option_i16", vec![]), ("Some_Option_i16", vec![("value", Sort::bitvec(16))])],
    );
    let none =
        Expr::datatype_constructor("Option_i16", "None_Option_i16", vec![], option_sort.clone());
    let opt_a = Expr::var("opt_a", option_sort.clone());
    let opt_b = Expr::var("opt_b", option_sort);
    let nested = Expr::ite(Expr::var("cond_b", Sort::bool()), opt_a, opt_b);
    let reconstructed = Expr::ite(Expr::var("cond_a", Sort::bool()), none, nested);

    let value = ChcCtx::datatype_field_select(&reconstructed, 0, Some(1));
    assert!(value.is_some(), "expected payload extraction from nested option ITE");
    let value = value.unwrap();
    assert!(
        matches!(value.value(), ExprValue::Ite { .. }),
        "nested option field select should remain in ITE form"
    );
    assert!(
        !constraint_tree_contains(&value, &|expr| match expr.value() {
            ExprValue::DatatypeSelector { expr: inner, .. } => {
                matches!(inner.value(), ExprValue::Ite { .. })
            }
            _ => false,
        }),
        "field select must not emit DatatypeSelector over ITE: {value}"
    );
}

#[test]
fn test_datatype_field_select_ite_coerces_structurally_matching_constructor_arg() {
    let generic_range_sort = struct_sort(
        "RawIterRange_T",
        [("fld_current", Sort::bitvec(64)), ("fld_end", Sort::bitvec(64))],
    );
    let monomorphized_range_sort = struct_sort(
        "RawIterRange__u32_u32",
        [("fld_current", Sort::bitvec(64)), ("fld_end", Sort::bitvec(64))],
    );
    let wrapper_sort = struct_sort(
        "Wrapper_RawIterRange__u32_u32",
        [("fld_range", monomorphized_range_sort.clone())],
    );

    let mismatched_ctor = Expr::datatype_constructor(
        "Wrapper_RawIterRange__u32_u32",
        "Wrapper_RawIterRange__u32_u32_mk",
        vec![Expr::var("generic_range", generic_range_sort)],
        wrapper_sort.clone(),
    );
    let symbolic_wrapper = Expr::var("wrapper_sym", wrapper_sort);
    let container = Expr::ite(Expr::var("cond", Sort::bool()), mismatched_ctor, symbolic_wrapper);

    let selected = ChcCtx::datatype_field_select(&container, 0, None)
        .expect("ITE field select should coerce structurally matching constructor args");

    assert_eq!(
        selected.sort(),
        &monomorphized_range_sort,
        "field select should normalize branch results to the declared field sort"
    );
    let ExprValue::Ite { then_expr, else_expr, .. } = selected.value() else {
        panic!("selected field from wrapper ITE should remain an ITE");
    };
    assert_eq!(then_expr.sort(), &monomorphized_range_sort);
    assert_eq!(else_expr.sort(), &monomorphized_range_sort);
}

#[test]
fn test_datatype_field_select_enum_missing_downcast() {
    // Multi-constructor enum without Downcast should fail
    let option_sort =
        enum_sort("Option", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let opt = Expr::var("opt", option_sort);

    // Missing constructor index - should fail
    let result = ChcCtx::datatype_field_select(&opt, 0, None);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_select_bv64_transparent_wrapper() {
    // Transparent wrapper encoded as bv64 should return underlying value for Field(0)
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));

    let result = ChcCtx::datatype_field_select(&ptr, 0, None);
    assert!(result.is_some());
    let result = result.unwrap();
    assert!(result.sort().is_bitvec());
    assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(result.to_string(), ptr.to_string());
}

#[test]
fn test_datatype_field_select_bv64_with_cons_idx() {
    // Transparent wrapper should only apply when cons_idx is None
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));

    let result = ChcCtx::datatype_field_select(&ptr, 0, Some(0));
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_select_bv64_wrong_width() {
    // Non-pointer-width bitvec should not be treated as transparent wrapper
    let ptr = Expr::var("ptr32", Sort::bitvec(32));

    let result = ChcCtx::datatype_field_select(&ptr, 0, None);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_select_bv128_downcast_passthrough() {
    // Flattened enum payload select (Downcast+Field(0)) should pass through bv128 unchanged.
    let payload = Expr::var("payload", Sort::bitvec(128));
    let result = ChcCtx::datatype_field_select(&payload, 0, Some(1));
    assert!(result.is_some());
    assert_eq!(result.unwrap().to_string(), payload.to_string());
}

#[test]
fn test_datatype_field_select_bv128_layout_size_extracts_upper_half() {
    // Layout(size, align) is packed as concat(size:bv64, align:bv64).
    let layout = Expr::var("layout", Sort::bitvec(128));
    let result = ChcCtx::datatype_field_select(&layout, 0, None);
    assert!(result.is_some());
    let result = result.unwrap();
    assert_eq!(result.sort().bitvec_width(), Some(64));
    let expected = layout.extract(127, 64);
    assert_eq!(result.to_string(), expected.to_string());
}

#[test]
fn test_datatype_field_select_bv128_layout_align_extracts_lower_half() {
    // Layout(size, align) is packed as concat(size:bv64, align:bv64).
    let layout = Expr::var("layout", Sort::bitvec(128));
    let result = ChcCtx::datatype_field_select(&layout, 1, None);
    assert!(result.is_some());
    let result = result.unwrap();
    assert_eq!(result.sort().bitvec_width(), Some(64));
    let expected = layout.extract(63, 0);
    assert_eq!(result.to_string(), expected.to_string());
}

#[test]
fn test_datatype_field_select_bv128_layout_out_of_bounds() {
    let layout = Expr::var("layout", Sort::bitvec(128));
    let result = ChcCtx::datatype_field_select(&layout, 2, None);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_update_bv64_transparent_wrapper() {
    // Transparent wrapper update should return the new value directly
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));
    let new_val = Expr::bitvec_const(7, POINTER_WIDTH);

    let result = ChcCtx::datatype_field_update(&ptr, 0, None, new_val.clone());
    assert!(result.is_some());
    assert_eq!(result.unwrap().to_string(), new_val.to_string());
}

#[test]
fn test_datatype_field_update_bv64_with_cons_idx() {
    // Transparent wrapper update should not apply when cons_idx is provided
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));
    let new_val = Expr::bitvec_const(7, POINTER_WIDTH);

    let result = ChcCtx::datatype_field_update(&ptr, 0, Some(0), new_val);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_update_bv64_sort_mismatch() {
    // Updating with a non-pointer-width bitvec should fail
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));
    let new_val = Expr::bitvec_const(7, 32);

    let result = ChcCtx::datatype_field_update(&ptr, 0, None, new_val);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_update_bv128_layout_size_rebuilds_concat() {
    let layout = Expr::var("layout", Sort::bitvec(128));
    let new_size = Expr::bitvec_const(99, 64);
    let result = ChcCtx::datatype_field_update(&layout, 0, None, new_size.clone());
    assert!(result.is_some());
    let updated = result.unwrap();
    assert_eq!(updated.sort().bitvec_width(), Some(128));
    let expected = new_size.concat(layout.extract(63, 0));
    assert_eq!(updated.to_string(), expected.to_string());
}

#[test]
fn test_datatype_field_update_bv128_layout_align_rebuilds_concat() {
    let layout = Expr::var("layout", Sort::bitvec(128));
    let new_align = Expr::bitvec_const(8, 64);
    let result = ChcCtx::datatype_field_update(&layout, 1, None, new_align.clone());
    assert!(result.is_some());
    let updated = result.unwrap();
    assert_eq!(updated.sort().bitvec_width(), Some(128));
    let expected = layout.extract(127, 64).concat(new_align);
    assert_eq!(updated.to_string(), expected.to_string());
}

#[test]
fn test_datatype_field_update_bv128_layout_rejects_non_bv64_rhs() {
    let layout = Expr::var("layout", Sort::bitvec(128));
    let bad_width = Expr::bitvec_const(9, 32);
    let bad_sort = Expr::bool_const(true);

    assert!(
        ChcCtx::datatype_field_update(&layout, 0, None, bad_width).is_none(),
        "bv128 layout update must reject non-bv64 bitvec rhs"
    );
    assert!(
        ChcCtx::datatype_field_update(&layout, 1, None, bad_sort).is_none(),
        "bv128 layout update must reject non-bitvec rhs"
    );
}

#[test]
fn test_datatype_field_update_bv128_downcast_passthrough() {
    let flattened_variant = Expr::var("flattened_variant", Sort::bitvec(128));
    let new_payload = Expr::var("new_payload", Sort::bitvec(128));

    let result = ChcCtx::datatype_field_update(&flattened_variant, 0, Some(1), new_payload.clone());
    assert!(result.is_some(), "bv128 downcast payload update should succeed");
    assert_eq!(result.unwrap().to_string(), new_payload.to_string());
}

#[test]
fn test_datatype_field_update_bv128_downcast_rejects_mismatched_rhs() {
    let flattened_variant = Expr::var("flattened_variant", Sort::bitvec(128));
    let bad_payload = Expr::bitvec_const(7, 64);

    let result = ChcCtx::datatype_field_update(&flattened_variant, 0, Some(1), bad_payload);
    assert!(result.is_none(), "bv128 downcast payload update must reject non-bv128 rhs");
}

#[test]
fn test_datatype_field_select_bv64_nonzero_field() {
    // Field(>0) on bitvec should fall through and return None (not a datatype)
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));

    let result = ChcCtx::datatype_field_select(&ptr, 1, None);
    assert!(result.is_none());
}

#[test]
fn test_datatype_field_select_bv64_nonzero_field_with_cons_idx() {
    // Nonzero field with cons_idx should still fail for bitvec containers
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));

    let result = ChcCtx::datatype_field_select(&ptr, 1, Some(0));
    assert!(result.is_none());
}

#[test]
fn test_option_like_struct_field_remap() {
    // (#686 follow-up) Option-like struct encoding with field remapping
    // MIR uses Downcast(1) + Field(0) for Some payload, but struct has [is_some, value]
    let opt = Expr::var("opt", option_like_struct_sort(Sort::bitvec(32)));

    // MIR pattern for Some payload: cons_idx=1, field_idx=0
    // Should remap to struct field 1 (value), not field 0 (is_some)
    let value = ChcCtx::datatype_field_select(&opt, 0, Some(1));
    assert!(value.is_some());
    let value = value.unwrap();
    // Should get the bitvec value, not the bool is_some
    assert!(value.sort().is_bitvec());
    assert_eq!(value.sort().bitvec_width(), Some(32));
}

#[test]
fn test_apply_field_selections_chain() {
    // Test chained field selections (nested struct access)
    let inner_sort = struct_sort("Inner", [("fld_value", Sort::bitvec(32))]);
    let outer_sort = struct_sort("Outer", [("fld_inner", inner_sort)]);
    let outer = Expr::var("outer", outer_sort);
    // Select outer.inner.value: [Field(0), Field(0)]
    // field_ty: None skips ZST marker detection (avoids TLV.is_set panic in unit tests)
    let projections = vec![
        FieldProjection { field_idx: 0, cons_idx: None, field_ty: None },
        FieldProjection { field_idx: 0, cons_idx: None, field_ty: None },
    ];
    let result = ChcCtx::apply_field_selections(outer, &projections);
    assert!(result.is_some());
    let result = result.unwrap();
    assert!(result.sort().is_bitvec());
    assert_eq!(result.sort().bitvec_width(), Some(32));
}

#[test]
fn test_apply_projection_update_nested() {
    // Test nested field update: outer.inner.value = 99
    let inner_sort = struct_sort("Inner", [("fld_value", Sort::bitvec(32))]);
    let outer_sort = struct_sort("Outer", [("fld_inner", inner_sort)]);
    let outer = Expr::var("outer", outer_sort.clone());
    let new_val = Expr::bitvec_const(99, 32);
    // Update outer.inner.value: [Field(0), Field(0)]
    // field_ty: None skips ZST marker detection (avoids TLV.is_set panic in unit tests)
    let projections = vec![
        FieldProjection { field_idx: 0, cons_idx: None, field_ty: None },
        FieldProjection { field_idx: 0, cons_idx: None, field_ty: None },
    ];
    let result = ChcCtx::apply_projection_update(&outer, &projections, new_val);
    assert!(result.is_some());
    let result = result.unwrap();
    assert!(result.sort().is_datatype());
    assert_eq!(result.sort(), &outer_sort);
}

#[test]
fn test_apply_projection_update_bv128_downcast_passthrough() {
    let flattened_variant = Expr::var("flattened_variant", Sort::bitvec(128));
    let new_payload = Expr::var("new_payload", Sort::bitvec(128));
    let projections = vec![FieldProjection { field_idx: 0, cons_idx: Some(1), field_ty: None }];

    let result = ChcCtx::apply_projection_update(&flattened_variant, &projections, new_payload);
    assert!(result.is_some(), "apply_projection_update should reuse bv128 downcast passthrough");
    assert_eq!(result.unwrap().sort().bitvec_width(), Some(128));
}

#[test]
fn test_apply_projection_update_empty() {
    // Edge case: empty projections should return new_val directly
    let x = Expr::var("x", Sort::bitvec(32));
    let new_val = Expr::bitvec_const(42, 32);
    let projections: Vec<FieldProjection> = vec![];
    let result = ChcCtx::apply_projection_update(&x, &projections, new_val.clone());
    assert!(result.is_some());
    // Should return new_val unchanged
    assert_eq!(result.unwrap().to_string(), new_val.to_string());
}

#[test]
fn test_datatype_field_update_enum_with_downcast() {
    // Test field update on enum variant with constructor index
    let option_sort =
        enum_sort("Option", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let opt = Expr::var("opt", option_sort.clone());
    let new_val = Expr::bitvec_const(123, 32);

    // Update Some.value with constructor index 1
    let result = ChcCtx::datatype_field_update(&opt, 0, Some(1), new_val);
    assert!(result.is_some());
    let result = result.unwrap();
    assert!(result.sort().is_datatype());
    assert_eq!(result.sort(), &option_sort);
}

#[test]
fn test_option_like_struct_field_update_remap() {
    // (#686 follow-up) Option-like struct field update with remapping
    let option_struct = option_like_struct_sort(Sort::bitvec(32));
    let opt = Expr::var("opt", option_struct.clone());
    let new_val = Expr::bitvec_const(456, 32);

    // MIR pattern for updating Some payload: cons_idx=1, field_idx=0
    // Should remap to struct field 1 (value)
    let result = ChcCtx::datatype_field_update(&opt, 0, Some(1), new_val);
    assert!(result.is_some());
    let result = result.unwrap();
    assert!(result.sort().is_datatype());
    assert_eq!(result.sort(), &option_struct);
}

// ═══════════════════════════════════════════════════════════════════════
// Error-path tests: datatype_field_update returns None
// ═══════════════════════════════════════════════════════════════════════
//
// Part of #2627: error-path test coverage gaps.
// Mirrors existing select-side None tests for the update side.

#[test]
fn test_datatype_field_update_non_datatype_returns_none() {
    // Bool sort is neither bitvec nor datatype — update should fail
    let x = Expr::var("x", Sort::bool());
    let new_val = Expr::bitvec_const(1, 32);

    let result = ChcCtx::datatype_field_update(&x, 0, None, new_val);
    assert!(result.is_none(), "field update on Bool sort should return None");
}

#[test]
fn test_datatype_field_update_enum_missing_downcast_returns_none() {
    // Multi-constructor enum without cons_idx should fail (same as select-side test)
    let option_sort =
        enum_sort("Option", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let opt = Expr::var("opt", option_sort);
    let new_val = Expr::bitvec_const(42, 32);

    let result = ChcCtx::datatype_field_update(&opt, 0, None, new_val);
    assert!(result.is_none(), "enum update without cons_idx should return None");
}

#[test]
fn test_datatype_field_update_constructor_out_of_bounds_returns_none() {
    let option_sort =
        enum_sort("Option", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let opt = Expr::var("opt", option_sort);
    let new_val = Expr::bitvec_const(42, 32);

    // Constructor index 99 is out of bounds (only 0 and 1 exist)
    let result = ChcCtx::datatype_field_update(&opt, 0, Some(99), new_val);
    assert!(result.is_none(), "update with constructor OOB should return None");
}

#[test]
fn test_datatype_field_select_constructor_out_of_bounds_returns_none() {
    let option_sort =
        enum_sort("Option", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let opt = Expr::var("opt", option_sort);

    // Constructor index 99 is out of bounds
    let result = ChcCtx::datatype_field_select(&opt, 0, Some(99));
    assert!(result.is_none(), "select with constructor OOB should return None");
}

#[test]
fn test_datatype_field_update_field_out_of_bounds_returns_none() {
    let p = Expr::var("p", point_sort_prefixed());
    let new_val = Expr::bitvec_const(42, 32);

    // Field index 5 is out of bounds
    let result = ChcCtx::datatype_field_update(&p, 5, None, new_val);
    assert!(result.is_none(), "update with field OOB should return None");
}

#[test]
fn test_datatype_field_update_bv128_field_out_of_bounds_returns_none() {
    let layout = Expr::var("layout", Sort::bitvec(128));
    let new_val = Expr::bitvec_const(1, 64);

    // bv128 Layout has fields 0 (size) and 1 (align); field 2 is OOB
    let result = ChcCtx::datatype_field_update(&layout, 2, None, new_val);
    assert!(result.is_none(), "bv128 layout update with field >= 2 should return None");
}

#[test]
fn test_datatype_field_update_unsupported_bitvec_width_returns_none() {
    // bv16 is neither 64 (transparent wrapper) nor 128 (Layout) — should fail
    let x = Expr::var("x", Sort::bitvec(16));
    let new_val = Expr::bitvec_const(1, 16);

    let result = ChcCtx::datatype_field_update(&x, 0, None, new_val);
    assert!(result.is_none(), "field update on bv16 should return None (unsupported width)");
}

#[test]
fn test_apply_field_selections_bad_inner_field_returns_none() {
    // Chained selection where inner select fails due to bad field index
    let inner_sort = struct_sort("Inner", [("fld_value", Sort::bitvec(32))]);
    let outer_sort = struct_sort("Outer", [("fld_inner", inner_sort)]);
    let outer = Expr::var("outer", outer_sort);

    // First projection OK (field 0 of Outer), second fails (field 5 of Inner is OOB)
    let projections = vec![
        FieldProjection { field_idx: 0, cons_idx: None, field_ty: None },
        FieldProjection { field_idx: 5, cons_idx: None, field_ty: None },
    ];
    let result = ChcCtx::apply_field_selections(outer, &projections);
    assert!(result.is_none(), "chained selection with bad inner field should return None");
}

#[test]
fn test_apply_projection_update_bad_select_path_returns_none() {
    // Nested update where the path-building select fails
    let inner_sort = struct_sort("Inner", [("fld_value", Sort::bitvec(32))]);
    let outer_sort = struct_sort("Outer", [("fld_inner", inner_sort)]);
    let outer = Expr::var("outer", outer_sort);
    let new_val = Expr::bitvec_const(99, 32);

    // Second projection has OOB field index — path building will fail
    let projections = vec![
        FieldProjection { field_idx: 0, cons_idx: None, field_ty: None },
        FieldProjection { field_idx: 5, cons_idx: None, field_ty: None },
    ];
    let result = ChcCtx::apply_projection_update(&outer, &projections, new_val);
    assert!(result.is_none(), "nested update with bad select path should return None");
}

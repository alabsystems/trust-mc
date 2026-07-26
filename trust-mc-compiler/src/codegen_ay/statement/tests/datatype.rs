// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for production sort-construction helpers in sort_inference.rs:
//! slice_sort, dyn_sort, tuple_sort_name.
//!
//! Trivial AY-only expression tests (field_select, field_update,
//! is_constructor, Sort::struct_type assertions) deleted per rule #2312
//! and #2482 — they tested AY API, not production codegen.

use super::*;

// =============================================================================
// Slice sort (sort_inference.rs:98 — StatementCodegen::slice_sort)
// =============================================================================

#[test]
fn test_datatype_field_update_option_like_struct_some_remaps_payload_field() {
    with_test_ay_ctx_for_source("pub fn probe() {}", |mut ctx| {
        let payload_sort =
            struct_sort("Point", vec![("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))]);
        let option_like_sort = struct_sort(
            "OptionLikePoint",
            vec![("is_some", Sort::bool()), ("value", payload_sort.clone())],
        );
        let option_expr = Expr::var("_opt", option_like_sort.clone());
        let new_payload = Expr::var("_payload", payload_sort.clone());
        let place = local_place(0);

        let updated = StatementCodegen::datatype_field_update(
            &option_expr,
            0,
            Some(1),
            new_payload.clone(),
            &place,
            &mut ctx,
        )
        .expect("Option-like Some payload update should remap to field 1");

        assert_eq!(updated.sort(), &option_like_sort);

        let payload =
            StatementCodegen::datatype_field_select(&updated, 0, Some(1), &place, &mut ctx)
                .expect("updated Option-like value should expose Some payload");
        assert_eq!(payload.sort(), &payload_sort);
    });
}

/// Test slice sort has correct structure (ptr, len, data).
#[test]
fn test_datatype_slice_sort_structure() {
    let slice_sort = StatementCodegen::slice_sort(Sort::bitvec(32));

    assert!(slice_sort.is_datatype());
    assert_eq!(slice_sort.datatype_name(), Some("Slice_bv32"));
    assert!(slice_sort.datatype_has_field("fld_ptr"));
    assert!(slice_sort.datatype_has_field("fld_len"));
    assert!(slice_sort.datatype_has_field("fld_data"));
}

/// Test slice sort naming with different element sorts.
#[test]
fn test_datatype_slice_sort_naming() {
    let s8 = StatementCodegen::slice_sort(Sort::bitvec(8));
    let s64 = StatementCodegen::slice_sort(Sort::bitvec(64));
    let s_bool = StatementCodegen::slice_sort(Sort::bool());

    assert_eq!(s8.datatype_name(), Some("Slice_bv8"));
    assert_eq!(s64.datatype_name(), Some("Slice_bv64"));
    assert_eq!(s_bool.datatype_name(), Some("Slice_bool"));
}

/// Test slice construction and field selection.
#[test]
fn test_datatype_slice_construction_and_select() {
    let slice_sort = StatementCodegen::slice_sort(Sort::bitvec(32));
    let cons = slice_sort.datatype_default_constructor().unwrap().to_string();
    let ptr = Expr::bitvec_const(0x4000u128, POINTER_WIDTH);
    let len = Expr::bitvec_const(8u128, POINTER_WIDTH);
    let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u128, 32));
    let slice = Expr::datatype_constructor("Slice_bv32", &cons, vec![ptr, len, data], slice_sort);

    let sel_ptr = slice.clone().field_select("Slice_bv32", "fld_ptr", Sort::bitvec(POINTER_WIDTH));
    let sel_len = slice.field_select("Slice_bv32", "fld_len", Sort::bitvec(POINTER_WIDTH));

    assert_eq!(sel_ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(sel_len.sort().bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// Dyn sort (sort_inference.rs:111 — StatementCodegen::dyn_sort)
// =============================================================================

/// Test dyn sort (trait object fat pointer) structure.
#[test]
fn test_datatype_dyn_sort_structure() {
    let dyn_sort = StatementCodegen::dyn_sort("Trait");

    assert!(dyn_sort.is_datatype());
    assert_eq!(dyn_sort.datatype_name(), Some("Dyn_Trait"));
    assert!(dyn_sort.datatype_has_field("fld_ptr"));
    assert!(dyn_sort.datatype_has_field("fld_vtable"));
}

/// Test dyn sort with specific trait name.
#[test]
fn test_datatype_dyn_sort_custom_trait() {
    let dyn_sort = StatementCodegen::dyn_sort("Iterator");

    assert_eq!(dyn_sort.datatype_name(), Some("Dyn_Iterator"));
}

/// Test dyn sort construction and field selection.
#[test]
fn test_datatype_dyn_sort_construction() {
    let dyn_sort = StatementCodegen::dyn_sort("Debug");
    let cons = dyn_sort.datatype_default_constructor().unwrap().to_string();
    let ptr = Expr::bitvec_const(0x1000u128, POINTER_WIDTH);
    let vtable = Expr::bitvec_const(0x2000u128, POINTER_WIDTH);
    let dyn_val = Expr::datatype_constructor("Dyn_Debug", &cons, vec![ptr, vtable], dyn_sort);

    let sel_ptr = dyn_val.clone().field_select("Dyn_Debug", "fld_ptr", Sort::bitvec(POINTER_WIDTH));
    let sel_vtable = dyn_val.field_select("Dyn_Debug", "fld_vtable", Sort::bitvec(POINTER_WIDTH));

    assert_eq!(sel_ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(sel_vtable.sort().bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// Tuple sort name (sort_inference.rs:183 — StatementCodegen::tuple_sort_name)
// =============================================================================

/// Test tuple_sort_name for various field combinations.
#[test]
fn test_datatype_tuple_sort_name_basic() {
    let fields = vec![("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bool())];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_bv32_bool");
}

/// Test tuple_sort_name with single field.
#[test]
fn test_datatype_tuple_sort_name_single() {
    let fields = vec![("fld_0", Sort::bitvec(64))];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_bv64");
}

/// Test tuple_sort_name with three fields.
#[test]
fn test_datatype_tuple_sort_name_triple() {
    let fields =
        vec![("fld_0", Sort::bitvec(8)), ("fld_1", Sort::bitvec(16)), ("fld_2", Sort::bitvec(32))];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_bv8_bv16_bv32");
}

/// Test tuple_sort_name with Int sort.
#[test]
fn test_datatype_tuple_sort_name_with_int() {
    let fields = vec![("fld_0", Sort::int()), ("fld_1", Sort::bitvec(32))];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_int_bv32");
}

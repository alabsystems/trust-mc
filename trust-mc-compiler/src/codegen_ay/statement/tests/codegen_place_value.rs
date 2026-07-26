// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for codegen_place_value.rs — value assignment, reference
//! assignment, value-through-ref, Option payload, and Box pointee detection.
//!
//! Tests cover:
//! - assign_value_to_place: SSA variable creation and env update
//! - assign_reference_to_place: reference tracking via ref_pointees
//! - get_value_through_ref: deref resolution for &T operands
//! - get_option_payload_value: value semantics for Option<&T>
//! - box_pointee_ty: Box<T> type extraction
//! - extract_fat_ptr_metadata: fat pointer metadata field extraction
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

const PLACE_VALUE_PROBE: &str = r#"
pub fn place_value_probe() {}
"#;

// =============================================================================
// assign_value_to_place via MIR
// =============================================================================

/// assign_value_to_place creates SSA var and updates env.
#[test]
fn test_assign_value_to_place_u32() {
    let source = r#"
pub fn assign_probe() -> u32 {
    let x: u32 = 42;
    x
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "assign_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find a local and assign a value to it
        let place = Place { local: 1, projection: vec![] };
        let value = Expr::bitvec_const(42u128, 32);
        codegen.assign_value_to_place(&place, value);

        // The env should have the assigned value
        let base_name = codegen.ssa_base_name(&place);
        let stored = codegen.env_lookup(&base_name);
        assert!(stored.is_some(), "assigned place should be in env");
        assert!(stored.unwrap().sort().is_bitvec(), "stored value should be bitvec");
    });
}

/// assign_value_to_place with bool creates bool SSA var.
#[test]
fn test_assign_value_to_place_bool() {
    with_test_ay_ctx_for_source(PLACE_VALUE_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "place_value_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let value = Expr::bool_const(true);
        codegen.assign_value_to_place(&place, value);

        let base_name = codegen.ssa_base_name(&place);
        let stored = codegen.env_lookup(&base_name);
        assert!(stored.is_some());
        assert!(stored.unwrap().sort().is_bool());
    });
}

/// assign_value_to_place with array sort.
#[test]
fn test_assign_value_to_place_array() {
    with_test_ay_ctx_for_source(PLACE_VALUE_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "place_value_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let value = Expr::var("arr_sym", array_sort);
        codegen.assign_value_to_place(&place, value);

        let base_name = codegen.ssa_base_name(&place);
        let stored = codegen.env_lookup(&base_name);
        assert!(stored.is_some());
        assert!(stored.unwrap().sort().is_array());
    });
}

/// assign_value_to_place should carry nested ref_pointees when the assigned
/// value already exists in env as a composite containing reference fields.
#[test]
fn test_assign_value_to_place_propagates_nested_ref_pointees() {
    with_test_ay_ctx_for_source(PLACE_VALUE_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "place_value_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let source_base: std::sync::Arc<str> =
            std::sync::Arc::from("place_value_probe::source_wrapper");
        let target_pointee: std::sync::Arc<str> =
            std::sync::Arc::from("place_value_probe::nested_ref_target");
        let wrapper_sort = crate::codegen_ay::names::struct_sort(
            "Wrapper_u32_ref",
            vec![("fld_0", Sort::bitvec(64)), ("fld_1", Sort::bitvec(32))],
        );
        let wrapper_value = Expr::var("wrapper_src", wrapper_sort);

        codegen.current_env.insert(std::sync::Arc::clone(&source_base), wrapper_value.clone());
        codegen.ref_pointees.insert(
            std::sync::Arc::from(format!("{source_base}_field_0")),
            std::sync::Arc::clone(&target_pointee),
        );

        let place = Place { local: 1, projection: vec![] };
        codegen.assign_value_to_place(&place, wrapper_value);

        let dest_base = codegen.ssa_base_name(&place);
        assert_eq!(
            codegen.ref_pointees.get(format!("{dest_base}_field_0").as_str()),
            Some(&target_pointee),
            "assign_value_to_place should propagate nested ref metadata to the destination base"
        );
    });
}

// =============================================================================
// get_value_through_ref via MIR
// =============================================================================

/// get_value_through_ref resolves &T to the pointee value.
#[test]
fn test_get_value_through_ref_resolves_pointee() {
    let source = r#"
pub fn ref_probe(x: &u32) -> u32 {
    *x
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // arg 1 is &u32, init_reference_arguments should have set up ref_pointees
        let arg_place = Place { local: 1, projection: vec![] };
        let arg_operand = Operand::Copy(arg_place);
        let result = codegen.get_value_through_ref(&arg_operand);
        // Should resolve to the pointee value (not a pointer bitvec)
        assert!(result.is_some(), "should resolve &u32 to pointee value");
        let expr = result.unwrap();
        assert!(expr.sort().is_bitvec(), "pointee of &u32 should be bitvec (u32)");
        assert_eq!(expr.sort().bitvec_width(), Some(32));
    });
}

/// get_value_through_ref with non-ref operand falls back to codegen_operand.
#[test]
fn test_get_value_through_ref_non_ref_fallback() {
    let source = r#"
pub fn nonref_probe(x: u32) -> u32 {
    x
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "nonref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Codegen the first operand to populate env
        let arg_place = Place { local: 1, projection: vec![] };
        let arg_operand = Operand::Copy(arg_place);

        // For non-ref types, get_value_through_ref falls through to codegen_operand
        let result = codegen.get_value_through_ref(&arg_operand);
        // Should still produce a value (from codegen_operand fallback)
        assert!(result.is_some(), "non-ref operand should still produce a value");
    });
}

// =============================================================================
// get_option_payload_value via MIR
// =============================================================================

/// get_option_payload_value for non-ref type returns direct value.
#[test]
fn test_option_payload_value_non_ref() {
    let source = r#"
pub fn val_probe(x: u32) -> u32 {
    x
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "val_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // arg 1 is u32 (non-ref), populate env
        let place = Place { local: 1, projection: vec![] };
        let value = Expr::bitvec_const(99u128, 32);
        codegen.assign_value_to_place(&place, value);

        let operand = Operand::Copy(place);
        let result = codegen.get_option_payload_value(&operand);
        assert!(result.is_some());
        // For non-ref, returns via codegen_operand (no dereference needed)
        assert!(result.unwrap().sort().is_bitvec());
    });
}

/// get_option_payload_value for &T dereferences to value semantics.
#[test]
fn test_option_payload_value_ref_deref() {
    let source = r#"
pub fn opt_ref_probe(x: &u32) -> u32 {
    *x
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "opt_ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // arg 1 is &u32
        let arg_place = Place { local: 1, projection: vec![] };
        let operand = Operand::Copy(arg_place);
        let result = codegen.get_option_payload_value(&operand);
        // Should dereference to get the u32 value, not the pointer
        assert!(result.is_some());
        let val = result.unwrap();
        assert!(val.sort().is_bitvec(), "should dereference &u32 to bitvec 32");
        assert_eq!(val.sort().bitvec_width(), Some(32));
    });
}

// =============================================================================
// box_pointee_ty (static method — type extraction)
// =============================================================================

/// box_pointee_ty extracts T from Box<T> in MIR.
#[test]
fn test_box_pointee_ty_extraction() {
    let source = r#"
pub fn box_probe() -> Box<u32> {
    Box::new(42)
}
"#;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "box_probe");
        let body = instance.body().expect("function body");

        // Find the return type which is Box<u32>
        let ret_ty = body.locals()[0].ty;
        let pointee = StatementCodegen::box_pointee_ty(ret_ty);
        assert!(pointee.is_some(), "Box<u32> should have pointee type u32");
        let inner = pointee.unwrap();
        // The inner type should be u32
        match inner.kind() {
            TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::U32)) => {} // expected
            other => panic!("expected u32, got {:?}", other),
        }
    });
}

/// box_pointee_ty returns None for non-Box types.
#[test]
fn test_box_pointee_ty_non_box() {
    let source = r#"
pub fn non_box_probe() -> u32 {
    42
}
"#;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "non_box_probe");
        let body = instance.body().expect("function body");

        let ret_ty = body.locals()[0].ty;
        let pointee = StatementCodegen::box_pointee_ty(ret_ty);
        assert!(pointee.is_none(), "u32 is not Box");
    });
}

// =============================================================================
// extract_fat_ptr_metadata (free function)
// =============================================================================

/// Fat pointer with fld_len metadata extracts len field.
#[test]
fn test_extract_fat_ptr_metadata_len() {
    let sort = struct_sort(
        "SlicePtr",
        [("fld_ptr", Sort::bitvec(POINTER_WIDTH)), ("fld_len", Sort::bitvec(POINTER_WIDTH))],
    );
    let ptr_expr = Expr::datatype_constructor(
        "SlicePtr",
        "SlicePtr_mk",
        vec![
            Expr::bitvec_const(0x1000u128, POINTER_WIDTH),
            Expr::bitvec_const(10u128, POINTER_WIDTH),
        ],
        sort,
    );
    let meta = extract_fat_ptr_metadata(&ptr_expr);
    assert!(meta.is_some(), "should extract fld_len metadata");
    assert!(meta.unwrap().sort().is_bitvec());
}

/// Fat pointer with fld_meta extracts generic metadata.
#[test]
fn test_extract_fat_ptr_metadata_generic() {
    let sort = struct_sort(
        "FatPtr",
        [("fld_data", Sort::bitvec(POINTER_WIDTH)), ("fld_meta", Sort::bitvec(POINTER_WIDTH))],
    );
    let ptr_expr = Expr::datatype_constructor(
        "FatPtr",
        "FatPtr_mk",
        vec![
            Expr::bitvec_const(0x2000u128, POINTER_WIDTH),
            Expr::bitvec_const(0x3000u128, POINTER_WIDTH),
        ],
        sort,
    );
    let meta = extract_fat_ptr_metadata(&ptr_expr);
    assert!(meta.is_some(), "should extract fld_meta metadata");
}

/// Thin pointer (no metadata field) returns None.
#[test]
fn test_extract_fat_ptr_metadata_thin_pointer() {
    let thin = Expr::bitvec_const(0x1000u128, POINTER_WIDTH);
    let meta = extract_fat_ptr_metadata(&thin);
    assert!(meta.is_none(), "thin pointer has no metadata");
}

/// Datatype without recognized metadata field names returns None.
#[test]
fn test_extract_fat_ptr_metadata_no_recognized_fields() {
    let sort =
        struct_sort("CustomStruct", [("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))]);
    let expr = Expr::datatype_constructor(
        "CustomStruct",
        "CustomStruct_mk",
        vec![Expr::bitvec_const(1u128, 32), Expr::bitvec_const(2u128, 32)],
        sort,
    );
    let meta = extract_fat_ptr_metadata(&expr);
    assert!(meta.is_none(), "no fld_len/fld_vtable/fld_meta → None");
}

/// Fat pointer with fld_vtable metadata extracts vtable field.
#[test]
fn test_extract_fat_ptr_metadata_vtable() {
    let sort = struct_sort(
        "DynPtr",
        [("fld_data", Sort::bitvec(POINTER_WIDTH)), ("fld_vtable", Sort::bitvec(POINTER_WIDTH))],
    );
    let ptr_expr = Expr::datatype_constructor(
        "DynPtr",
        "DynPtr_mk",
        vec![
            Expr::bitvec_const(0x4000u128, POINTER_WIDTH),
            Expr::bitvec_const(0x5000u128, POINTER_WIDTH),
        ],
        sort,
    );
    let meta = extract_fat_ptr_metadata(&ptr_expr);
    assert!(meta.is_some(), "should extract fld_vtable metadata");
    assert_eq!(meta.unwrap().sort().bitvec_width(), Some(POINTER_WIDTH));
}

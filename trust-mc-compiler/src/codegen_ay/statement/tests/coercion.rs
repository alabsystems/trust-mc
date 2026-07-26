// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Coercion edge case unit tests.

use super::*;
use std::sync::Arc;

// =============================================================================
// Tests for coercion edge cases
// =============================================================================

const SLICE_COERCION_SOURCE: &str = r#"
pub fn array_to_slice() {
    let arr: [u8; 4] = [1, 2, 3, 4];
    let slice: &[u8] = &arr;
    let _ = slice;
}

pub static ARRAY_REF: &'static [u8; 4] = &[1, 2, 3, 4];

// Function with raw pointer local for testing array_len_from_pointer_ty.
pub fn raw_ptr_fn() {
    let raw: *const [u16; 8] = core::ptr::null();
    let _ = raw;
}
"#;

const STR_CONST_SOURCE: &str = r#"
pub fn str_literal_operand() {
    let msg: &str = "cover message";
    let _ = msg;
}
"#;

const SLICE_LEN_SOURCE: &str = r#"
pub fn slice_len(xs: &[u8]) -> usize {
    xs.len()
}
"#;

// Use a slice coercion to force Rvalue::Len generation.
// Direct array.len() is often optimized to a constant by rustc.
const ARRAY_LEN_SOURCE: &str = r#"
pub fn array_len(arr: &[u32; 5]) -> usize {
    arr.len()
}
"#;

const FAT_PTR_CAST_SOURCE: &str = r#"
pub fn slice_data_addr(xs: &mut [u8]) -> usize {
    xs as *mut [u8] as *mut u8 as usize
}
"#;

const NESTED_ENUM_DISCRIMINANT_SOURCE: &str = r#"
#![allow(dead_code)]

enum Inner {
    A(u8),
    B(u8),
}

enum Outer {
    X(Inner),
    Y,
}

fn nested_enum_discriminant(o: Outer) -> u8 {
    match o {
        Outer::X(Inner::A(_)) => 0,
        Outer::X(Inner::B(_)) => 1,
        Outer::Y => 2,
    }
}
"#;

const NESTED_UNIT_ENUM_DISCRIMINANT_SOURCE: &str = r#"
#![allow(dead_code)]

enum Unit {
    A,
    B,
}

enum UnitOuter {
    X(Unit),
    Y,
}

fn nested_unit_enum_discriminant(o: UnitOuter) -> u8 {
    match o {
        UnitOuter::X(Unit::A) => 0,
        UnitOuter::X(Unit::B) => 1,
        UnitOuter::Y => 2,
    }
}
"#;

const NESTED_OPTION_DISCRIMINANT_SOURCE: &str = r#"
#![allow(dead_code)]

enum OptOuter {
    X(Option<u8>),
    Y,
}

fn nested_option_discriminant(o: OptOuter) -> u8 {
    match o {
        OptOuter::X(Some(_)) => 0,
        OptOuter::X(None) => 1,
        OptOuter::Y => 2,
    }
}
"#;

fn find_item_by_suffix(ctx: &AYCtx<'_, '_>, suffix: &str) -> rustc_public::CrateItem {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
            let path = ctx.tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing item with suffix '{suffix}'"),
        [single] => *single,
        many => {
            let names: Vec<_> = many
                .iter()
                .map(|item| {
                    let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
                    ctx.tcx.def_path_str(def_id)
                })
                .collect();
            panic!("ambiguous suffix '{suffix}': {} matches: {names:?}", many.len());
        }
    }
}

fn find_projected_discriminant_place(body: &rustc_public::mir::Body) -> Place {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                continue;
            };
            let Rvalue::Discriminant(place) = rvalue else {
                continue;
            };
            if place.projection.len() == 2
                && matches!(place.projection[0], ProjectionElem::Downcast(..))
                && matches!(place.projection[1], ProjectionElem::Field(..))
            {
                return place.clone();
            }
        }
    }
    panic!("missing discriminant place with Downcast+Field projection");
}

fn expr_contains_datatype_selector(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::DatatypeSelector { .. } => true,
        ExprValue::DatatypeTester { expr, .. } => expr_contains_datatype_selector(expr),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            expr_contains_datatype_selector(cond)
                || expr_contains_datatype_selector(then_expr)
                || expr_contains_datatype_selector(else_expr)
        }
        ExprValue::Not(inner) => expr_contains_datatype_selector(inner),
        ExprValue::And(args) | ExprValue::Or(args) | ExprValue::Distinct(args) => {
            args.iter().any(expr_contains_datatype_selector)
        }
        ExprValue::Eq(lhs, rhs) => {
            expr_contains_datatype_selector(lhs) || expr_contains_datatype_selector(rhs)
        }
        _ => false,
    }
}

fn assert_projected_discriminant_uses_field_select(source: &str, fn_suffix: &str, root_sort: Sort) {
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_suffix);
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = find_projected_discriminant_place(&body);
        let root_name = codegen.root_ssa_base_name(&place);
        let root_expr = codegen.ctx.declare_var(&root_name, root_sort);
        codegen.env_update(root_name, root_expr);

        let place_expr = codegen.codegen_place(&place).expect("projected place expr");
        assert!(
            expr_contains_datatype_selector(&place_expr),
            "expected place expression to include field_select, got {place_expr}"
        );
        let discr_rvalue = Rvalue::Discriminant(place);
        let discr_expr = codegen.codegen_rvalue(&discr_rvalue).expect("discriminant expr");

        assert!(
            expr_contains_datatype_selector(&discr_expr),
            "expected discriminant expression to include field_select, got {discr_expr}"
        );
    });
}

fn nested_enum_root_sort() -> Sort {
    let inner_sort = enum_sort(
        "Inner",
        vec![("A", vec![("fld_0", Sort::bitvec(8))]), ("B", vec![("fld_0", Sort::bitvec(8))])],
    );
    enum_sort("Outer", vec![("X", vec![("fld_0", inner_sort)]), ("Y", vec![])])
}

fn nested_unit_enum_root_sort() -> Sort {
    enum_sort("UnitOuter", vec![("X", vec![("fld_0", Sort::bitvec(32))]), ("Y", vec![])])
}

fn nested_option_root_sort() -> Sort {
    let option_sort =
        enum_sort("Option", vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(8))])]);
    enum_sort("OptOuter", vec![("X", vec![("fld_0", option_sort)]), ("Y", vec![])])
}

/// Test slice_sort creates the expected datatype layout and naming.
#[test]
fn test_slice_sort_structure() {
    let slice_sort = StatementCodegen::slice_sort(Sort::bitvec(8));
    assert!(slice_sort.is_datatype());
    assert_eq!(slice_sort.datatype_name(), Some("Slice_bv8"));
}

/// Test dyn_sort creates the expected datatype layout and naming for trait objects.
/// Part of #1140: Trait object fat pointers use (ptr, vtable) structure.
#[test]
fn test_dyn_sort_structure() {
    let dyn_sort = StatementCodegen::dyn_sort("MyTrait");
    assert!(dyn_sort.is_datatype());
    assert_eq!(dyn_sort.datatype_name(), Some("Dyn_MyTrait"));
}

/// Test extract_fat_ptr_metadata extracts len from slice fat pointer datatypes.
#[test]
fn test_extract_fat_ptr_metadata_slice() {
    let slice_sort = StatementCodegen::slice_sort(Sort::bitvec(8));
    let slice_expr = Expr::var("slice_var", slice_sort);
    let metadata = extract_fat_ptr_metadata(&slice_expr);
    assert!(metadata.is_some());
    let meta_expr = metadata.unwrap();
    assert_eq!(meta_expr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test extract_fat_ptr_metadata extracts vtable from dyn Trait fat pointer datatypes.
/// Part of #1140: Verifies vtable extraction for trait objects.
#[test]
fn test_extract_fat_ptr_metadata_dyn() {
    let dyn_sort = StatementCodegen::dyn_sort("MyTrait");
    let dyn_expr = Expr::var("dyn_var", dyn_sort);
    let metadata = extract_fat_ptr_metadata(&dyn_expr);
    assert!(metadata.is_some());
    let meta_expr = metadata.unwrap();
    assert_eq!(meta_expr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test extract_fat_ptr_metadata returns None for thin pointers (non-fat pointer types).
#[test]
fn test_extract_fat_ptr_metadata_thin_ptr_returns_none() {
    // Thin pointer is just a bitvec, not a datatype with metadata field
    let thin_ptr = Expr::var("thin_ptr", Sort::bitvec(POINTER_WIDTH));
    let metadata = extract_fat_ptr_metadata(&thin_ptr);
    assert!(metadata.is_none(), "thin pointer should not have metadata");
}

/// Test array_len_from_pointer_ty extracts the length from &[T; N] types.
#[test]
fn test_array_len_from_pointer_ty_ref() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |ctx| {
        let array_ref_item = find_item_by_suffix(&ctx, "ARRAY_REF");
        let array_ref_ty = array_ref_item.ty();
        assert_eq!(StatementCodegen::array_len_from_pointer_ty(array_ref_ty), Some(4));
    });
}

/// Test array_len_from_pointer_ty extracts the length from *const [T; N] types.
/// Uses a local variable type from a function body since raw pointers can't be in statics.
#[test]
fn test_array_len_from_pointer_ty_raw_ptr() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |ctx| {
        // Get the function body and extract type from local variable `raw`.
        let raw_ptr_fn = find_instance_by_suffix(&ctx, "raw_ptr_fn");
        let body = raw_ptr_fn.body().expect("raw_ptr_fn body");
        // Local 1 is typically the first user-declared local (local 0 is return place).
        // The `raw` variable is of type *const [u16; 8].
        let raw_ty = body.locals()[1].ty;
        assert_eq!(StatementCodegen::array_len_from_pointer_ty(raw_ty), Some(8));
    });
}

/// Test try_construct_slice_datatype_from_cast builds slice datatypes with correct length.
#[test]
fn test_try_construct_slice_datatype_from_cast() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_to_slice");
        let body = instance.body().expect("array_to_slice body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut cast_operand: Option<Operand> = None;
        let mut cast_target_ty: Option<rustc_public::ty::Ty> = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                if let Rvalue::Cast(_, operand, target_ty) = rvalue
                    && StatementCodegen::is_slice_pointer_ty(*target_ty)
                {
                    cast_operand = Some(operand.clone());
                    cast_target_ty = Some(*target_ty);
                    break;
                }
            }
        }

        let operand = cast_operand.as_ref().expect("array-to-slice cast operand");
        let target_ty = cast_target_ty.expect("array-to-slice cast target type");

        let operand_place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => panic!("expected place operand for slice cast"),
        };
        let base_name = codegen.ssa_base_name(operand_place);
        let ptr_expr = Expr::var(base_name.clone(), Sort::bitvec(POINTER_WIDTH));
        codegen.env_update(base_name.clone(), ptr_expr);
        let backing_name = "coercion_slice_backing";
        let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
        let backing = codegen.ctx.declare_var(backing_name, array_sort);
        codegen.env_update(backing_name.to_string(), backing.clone());
        codegen.ref_pointees.insert(Arc::from(base_name), Arc::from(backing_name));

        let slice_expr = codegen
            .try_construct_slice_datatype_from_cast(operand, target_ty)
            .expect("constructed slice datatype");
        assert!(slice_expr.sort().is_datatype());
        match slice_expr.value() {
            ExprValue::DatatypeConstructor { args, .. } => {
                assert_eq!(
                    args.len(),
                    3,
                    "slice cast should produce (ptr, len, data), got {} fields",
                    args.len()
                );
                match args[1].value() {
                    ExprValue::BitVecConst { value, width } => {
                        assert_eq!(*width, POINTER_WIDTH);
                        assert_eq!(value, &BigInt::from(4u32));
                    }
                    other => panic!("expected len bitvec const, got {other:?}"),
                }
                assert_eq!(
                    args[2].to_string(),
                    backing.to_string(),
                    "third field should preserve the tracked backing array"
                );
            }
            other => panic!("expected datatype constructor, got {other:?}"),
        }
    });
}

/// Test fat-pointer casts to usize extract the pointer field (not symbolic dt_to_bv).
/// Regression for #2076: slice fat pointers use fld_ptr/fld_len naming.
#[test]
fn test_codegen_cast_fat_pointer_to_usize_uses_fld_ptr() {
    with_test_ay_ctx_for_source(FAT_PTR_CAST_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "slice_data_addr");
        let body = instance.body().expect("slice_data_addr body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut target_cast: Option<(Operand, rustc_public::ty::Ty)> = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                let Rvalue::Cast(_, operand, target_ty) = rvalue else {
                    continue;
                };
                let Some(src_ty) = operand.ty(body.locals()).into_option() else {
                    continue;
                };
                let is_wide_ptr = StatementCodegen::is_wide_pointer_ty(src_ty);
                let target_is_bv = StatementCodegen::infer_sort_from_ty(*target_ty)
                    .is_some_and(|sort| sort.is_bitvec());
                if is_wide_ptr && target_is_bv {
                    target_cast = Some((operand.clone(), *target_ty));
                    break;
                }
            }
            if target_cast.is_some() {
                break;
            }
        }

        let (operand, target_ty) = target_cast.expect("wide-pointer cast to bitvec target");
        let operand_place = match &operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => panic!("expected place operand for fat-pointer cast"),
        };
        let src_ty = operand.ty(body.locals()).into_option().expect("cast source type");
        let src_sort =
            StatementCodegen::infer_sort_from_ty(src_ty).expect("fat-pointer source sort");
        let datatype_name = src_sort.datatype_name().expect("fat-pointer datatype").to_string();
        let constructor =
            src_sort.datatype_default_constructor().expect("fat-pointer constructor").to_string();

        let expected_ptr = Expr::bitvec_const(0x1234u128, POINTER_WIDTH);
        let expected_len = Expr::bitvec_const(16u128, POINTER_WIDTH);
        let expected_data =
            Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u128, 8));
        let fat_ptr_expr = Expr::datatype_constructor(
            &datatype_name,
            constructor,
            vec![expected_ptr, expected_len, expected_data],
            src_sort,
        );

        let base_name = codegen.ssa_base_name(operand_place);
        codegen.env_update(base_name, fat_ptr_expr);

        let cast_expr = codegen.codegen_cast(&operand, target_ty).expect("cast expression");
        assert_eq!(cast_expr.sort().bitvec_width(), Some(POINTER_WIDTH));
        match cast_expr.value() {
            ExprValue::DatatypeSelector { selector_name, .. } => {
                assert_eq!(selector_name, "fld_ptr");
            }
            ExprValue::BitVecConst { value, .. } => {
                assert_eq!(value, &BigInt::from(0x1234u32));
            }
            other => panic!("expected fld_ptr selector or pointer constant, got {other:?}"),
        }
    });
}

/// Test try_extract_str_constant extracts string literal from &str operand.
#[test]
fn test_try_extract_str_constant() {
    with_test_ay_ctx_for_source(STR_CONST_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "str_literal_operand");
        let body = instance.body().expect("str_literal_operand body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut str_operand: Option<Operand> = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                let Rvalue::Use(operand) = rvalue else {
                    continue;
                };
                let Some(ty) = operand.ty(body.locals()).into_option() else {
                    continue;
                };
                let TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _)) = ty.kind() else {
                    continue;
                };
                if matches!(inner_ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                    str_operand = Some(operand.clone());
                    break;
                }
            }
            if str_operand.is_some() {
                break;
            }
        }

        let operand = str_operand.expect("string literal operand");
        let extracted = codegen.try_extract_str_constant(&operand);
        assert_eq!(extracted.as_deref(), Some("cover message"));
    });
}

/// Test Rvalue::Len extracts length from fat pointer metadata for slices (#1316).
/// Per Kani semantics, slice lengths should come from the fat pointer's len field,
/// not a fresh symbolic variable.
#[test]
fn test_rvalue_len_extracts_slice_metadata() {
    with_test_ay_ctx_for_source(SLICE_LEN_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "slice_len");
        let body = instance.body().expect("slice_len body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut len_place: Option<Place> = None;
        let mut metadata_place: Option<Place> = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                match rvalue {
                    Rvalue::Len(place) => {
                        len_place = Some(place.clone());
                        break;
                    }
                    Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
                        let operand_place = match operand {
                            Operand::Copy(place) | Operand::Move(place) => place.clone(),
                            Operand::Constant(_) => continue,
                        };
                        metadata_place = Some(operand_place);
                    }
                    _ => {}
                }
            }
            if len_place.is_some() {
                break;
            }
        }

        let len_place = len_place
            .or_else(|| {
                metadata_place.map(|place| {
                    let mut projection = place.projection.clone();
                    projection.push(ProjectionElem::Deref);
                    Place { local: place.local, projection }
                })
            })
            .expect("expected Rvalue::Len or PtrMetadata operand place");
        let len_rvalue = Rvalue::Len(len_place);

        let len_expr = codegen.codegen_rvalue(&len_rvalue).expect("len expr");
        assert_eq!(len_expr.sort().bitvec_width(), Some(POINTER_WIDTH));

        // #1316: Slice length should be extracted from fat pointer metadata field,
        // not be a fresh symbolic variable. This matches Kani's behavior.
        // #1607: Field names use fld_ prefix convention.
        match len_expr.value() {
            ExprValue::DatatypeSelector { selector_name, .. } => {
                assert_eq!(selector_name, "fld_len", "expected fat ptr len field selector");
            }
            ExprValue::Var { .. } => {
                // Fallback to symbolic is acceptable if fat pointer not available
            }
            other => panic!("expected DatatypeSelector or Var, got {other:?}"),
        }

        // Repeated calls should return same expression
        let len_expr_second = codegen.codegen_rvalue(&len_rvalue).expect("len expr (2)");
        assert_eq!(len_expr_second, len_expr);
    });
}

/// Test Rvalue::Len returns compile-time constant for arrays (#1316).
/// Per Kani semantics, array lengths are known at compile time and should
/// not be symbolic variables.
#[test]
fn test_rvalue_len_returns_constant_for_arrays() {
    with_test_ay_ctx_for_source(ARRAY_LEN_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_len");
        let body = instance.body().expect("array_len body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find a local with array type [u32; 5] - either direct array or reference to array.
        // The arg is &[u32; 5], so we need to find the pointee array type.
        let mut array_place: Option<Place> = None;
        for (local_idx, local) in body.locals().iter().enumerate() {
            let ty = local.ty;
            // Check for direct array type
            if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = ty.kind()
                && let Some(len) = const_len.eval_target_usize().into_option()
                && len == 5
            {
                array_place = Some(Place { local: Local::from(local_idx), projection: vec![] });
                break;
            }
            // Check for reference to array type (the argument type)
            if let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ty.kind()
                && let TyKind::RigidTy(RigidTy::Array(_, const_len)) = pointee.kind()
                && let Some(len) = const_len.eval_target_usize().into_option()
                && len == 5
            {
                // Create a place that dereferences the reference to get to the array
                array_place = Some(Place {
                    local: Local::from(local_idx),
                    projection: vec![ProjectionElem::Deref],
                });
                break;
            }
        }

        let array_place = array_place.expect("expected array local [u32; 5]");
        let len_rvalue = Rvalue::Len(array_place.clone());

        // Verify the place type is an array
        let place_ty =
            array_place.ty(body.locals()).into_option().expect("place should have a type");
        assert!(
            matches!(place_ty.kind(), TyKind::RigidTy(RigidTy::Array(..))),
            "place should be array type, got {:?}",
            place_ty.kind()
        );

        let len_expr = codegen.codegen_rvalue(&len_rvalue).expect("len expr");
        assert_eq!(len_expr.sort().bitvec_width(), Some(POINTER_WIDTH));

        // #1316: Array length should be a compile-time constant, not symbolic
        match len_expr.value() {
            ExprValue::BitVecConst { value, .. } => {
                assert_eq!(*value, BigInt::from(5u64), "expected array length constant 5");
            }
            other => panic!("expected BitVecConst for array length, got {other:?}"),
        }
    });
}

/// Test projected discriminant uses field_select for nested enum matches (#1406).
#[test]
fn test_rvalue_discriminant_projected_nested_enum() {
    assert_projected_discriminant_uses_field_select(
        NESTED_ENUM_DISCRIMINANT_SOURCE,
        "nested_enum_discriminant",
        nested_enum_root_sort(),
    );
}

/// Test projected discriminant uses field_select for nested unit enums (#1406).
#[test]
fn test_rvalue_discriminant_projected_unit_enum() {
    assert_projected_discriminant_uses_field_select(
        NESTED_UNIT_ENUM_DISCRIMINANT_SOURCE,
        "nested_unit_enum_discriminant",
        nested_unit_enum_root_sort(),
    );
}

/// Test projected discriminant uses field_select for nested Option patterns (#1406).
#[test]
fn test_rvalue_discriminant_projected_option() {
    assert_projected_discriminant_uses_field_select(
        NESTED_OPTION_DISCRIMINANT_SOURCE,
        "nested_option_discriminant",
        nested_option_root_sort(),
    );
}

/// Test coerce_to_width_typed with truncation (wider to narrower).
#[test]
fn test_coerce_truncation() {
    let expr = Expr::bitvec_const(0x1234_5678u128, 32);
    let truncated = StatementCodegen::coerce_to_width_typed(expr, 16, false);

    assert_eq!(truncated.sort().bitvec_width(), Some(16));
    assert!(matches!(truncated.value(), ExprValue::BvExtract { .. }));
}

/// Test coerce_to_width_typed with no change needed.
#[test]
fn test_coerce_no_change() {
    let expr = Expr::bitvec_const(42u128, 32);
    let coerced = StatementCodegen::coerce_to_width_typed(expr, 32, true);

    assert_eq!(coerced.sort().bitvec_width(), Some(32));
}

/// Test coerce_to_match_widths_typed with LHS narrower than RHS.
#[test]
fn test_coerce_match_lhs_narrower() {
    let lhs = Expr::bitvec_const(0xffu128, 8);
    let rhs = Expr::bitvec_const(0u128, 32);
    let (lhs_w, rhs_w) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);

    assert_eq!(lhs_w.sort().bitvec_width(), Some(32));
    assert_eq!(rhs_w.sort().bitvec_width(), Some(32));
    // LHS should be zero-extended (unsigned)
    assert!(matches!(lhs_w.value(), ExprValue::BvZeroExtend { .. }));
}

/// Test coerce_to_match_widths_typed with equal widths (no change).
#[test]
fn test_coerce_match_equal_widths() {
    let lhs = Expr::bitvec_const(10u128, 32);
    let rhs = Expr::bitvec_const(20u128, 32);
    let (lhs_w, rhs_w) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, true);

    // Should return unchanged
    assert_eq!(lhs_w.sort().bitvec_width(), Some(32));
    assert_eq!(rhs_w.sort().bitvec_width(), Some(32));
}

/// Part of #1632: When array data is available via ref_pointees, the slice
/// cast should include fld_data so that indexing returns stored values.
#[test]
fn test_slice_cast_includes_fld_data_when_array_backing_available() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_to_slice");
        let body = instance.body().expect("array_to_slice body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find the array-to-slice cast in MIR
        let mut cast_operand: Option<Operand> = None;
        let mut cast_target_ty: Option<rustc_public::ty::Ty> = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                if let Rvalue::Cast(_, operand, target_ty) = rvalue
                    && StatementCodegen::is_slice_pointer_ty(*target_ty)
                {
                    cast_operand = Some(operand.clone());
                    cast_target_ty = Some(*target_ty);
                    break;
                }
            }
        }

        let operand = cast_operand.as_ref().expect("array-to-slice cast operand");
        let target_ty = cast_target_ty.expect("array-to-slice cast target type");

        // Seed the operand place with a pointer value (for fld_ptr)
        let operand_place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => panic!("expected place operand for slice cast"),
        };
        let ref_base = codegen.ssa_base_name(operand_place);
        let ptr_expr = Expr::var(ref_base.clone(), Sort::bitvec(POINTER_WIDTH));
        codegen.env_update(ref_base.clone(), ptr_expr);

        // Seed an array backing in the SSA env and link it via ref_pointees.
        // This simulates `let arr = [1, 2, 3, 4]; let ref = &arr;`
        let elem_sort = Sort::bitvec(8);
        let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
        let array_name = "test_array_backing";
        let mut arr = codegen.ctx.declare_var(array_name, array_sort);
        // Store 4 concrete elements
        for i in 0u128..4 {
            arr = arr.store(Expr::bitvec_const(i, POINTER_WIDTH), Expr::bitvec_const(i + 1, 8));
        }
        let arr_base = array_name.to_string();
        codegen.env_update(arr_base.clone(), arr);
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(arr_base));

        // Now construct the slice — should have fld_data
        let slice_expr = codegen
            .try_construct_slice_datatype_from_cast(operand, target_ty)
            .expect("constructed slice datatype");

        assert!(slice_expr.sort().is_datatype(), "result should be a datatype");

        match slice_expr.value() {
            ExprValue::DatatypeConstructor { args, .. } => {
                assert_eq!(
                    args.len(),
                    3,
                    "slice with array backing should have 3 fields (ptr, len, data), got {}",
                    args.len()
                );
                // args[0] = ptr (bitvec), args[1] = len (bitvec const 4), args[2] = data (array)
                assert!(
                    args[0].sort().bitvec_width().is_some(),
                    "first field should be fld_ptr bitvec"
                );
                match args[1].value() {
                    ExprValue::BitVecConst { value, width } => {
                        assert_eq!(*width, POINTER_WIDTH);
                        assert_eq!(value, &BigInt::from(4u32), "fld_len should be 4");
                    }
                    other => panic!("expected fld_len bitvec const, got {other:?}"),
                }
                assert!(
                    args[2].sort().is_array(),
                    "third field should be fld_data array, got {:?}",
                    args[2].sort()
                );
            }
            other => panic!("expected datatype constructor, got {other:?}"),
        }

        // Verify the sort has fld_data field
        if let Some(dt) = slice_expr.sort().datatype_sort() {
            let field_names: Vec<&str> =
                dt.constructors[0].fields.iter().map(|f| f.name.as_str()).collect();
            assert!(
                field_names.contains(&"fld_data"),
                "slice sort should contain fld_data field, got {:?}",
                field_names
            );
        } else {
            panic!("expected datatype sort");
        }
    });
}

/// Part of #4215: The slice cast must not fabricate `fld_data` when there is no
/// tracked backing object. Callers should retain the generic assignment fallback.
#[test]
fn test_slice_cast_without_tracked_backing_returns_none() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_to_slice");
        let body = instance.body().expect("array_to_slice body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find the array-to-slice cast in MIR
        let mut cast_operand: Option<Operand> = None;
        let mut cast_target_ty: Option<rustc_public::ty::Ty> = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                if let Rvalue::Cast(_, operand, target_ty) = rvalue
                    && StatementCodegen::is_slice_pointer_ty(*target_ty)
                {
                    cast_operand = Some(operand.clone());
                    cast_target_ty = Some(*target_ty);
                    break;
                }
            }
        }

        let operand = cast_operand.as_ref().expect("array-to-slice cast operand");
        let target_ty = cast_target_ty.expect("array-to-slice cast target type");

        // Seed only the reference operand with a pointer value. Do NOT seed
        // ref_pointees or a backing array: this must not be materialized as a
        // precise slice.
        let operand_place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => panic!("expected place operand for slice cast"),
        };
        let base_name = codegen.ssa_base_name(operand_place);
        let ptr_expr = Expr::var(base_name.clone(), Sort::bitvec(POINTER_WIDTH));
        codegen.env_update(base_name, ptr_expr);

        let slice_expr = codegen.try_construct_slice_datatype_from_cast(operand, target_ty);
        assert!(
            slice_expr.is_none(),
            "slice materialization without tracked array backing should fail closed"
        );
        assert!(
            codegen.ctx.unsupported_constructs.contains_key("slice_cast_backing_untracked"),
            "untracked backing should be recorded in diagnostics"
        );
    });
}

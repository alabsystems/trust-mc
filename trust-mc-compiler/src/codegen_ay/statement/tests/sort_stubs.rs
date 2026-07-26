// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Collection stub sort inference tests.
//
// Extracted from regression.rs per #1734.

use super::*;
use crate::codegen_ay::names::{RUST_STRING_SORT, struct_sort};

const SORT_INFERENCE_SOURCE: &str = r#"
pub fn tuple_checked(a: u8) -> (u8, bool) {
    let pair: (u8, bool) = (a, a > 0);
    pair
}

pub fn tuple_regular() -> (u8, u16) {
    let pair: (u8, u16) = (1, 2);
    pair
}

pub fn view_sort_inputs() -> (i16, u32, bool, char) {
    let i: i16 = -1;
    let u: u32 = 1;
    let b: bool = true;
    let c: char = 'x';
    (i, u, b, c)
}
"#;

// Unit tests for sort_inference.rs collection stubs (Part of #1281)
// =============================================================================
// These tests verify the Sort structure returned by collection stub handlers
// in sort_inference.rs. The actual type matching requires full MIR context,
// but we can verify the Sort construction is correct.

/// Test Vec<T> stub returns correct struct sort with (ptr, len, cap, data) fields.
/// Part of #1281: sort_inference.rs lines 211-220.
/// Updated for #1628: Added fld_data array backing field.
#[test]
fn test_vec_stub_sort_structure() {
    // Vec is encoded as struct with 4 fields: ptr, len, cap, and data array
    // The data field is an Array<usize, Element> for element storage (#1628)
    let elem_sort = Sort::bitvec(32); // i32 elements for this test
    let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort.clone());

    let vec_sort = struct_sort(
        "Vec",
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
            ("fld_data", array_sort.clone()),
        ],
    );

    assert!(vec_sort.is_datatype());
    assert_eq!(vec_sort.datatype_name(), Some("Vec"));

    // Verify we can construct valid expressions with this sort
    let ptr = Expr::bitvec_const(0x1000, POINTER_WIDTH);
    let len = Expr::bitvec_const(10, POINTER_WIDTH);
    let cap = Expr::bitvec_const(16, POINTER_WIDTH);
    let default_elem = Expr::var("default", elem_sort);
    let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), default_elem);
    let vec_expr = Expr::datatype_constructor("Vec", "Vec_mk", vec![ptr, len, cap, data], vec_sort);

    assert!(vec_expr.sort().is_datatype());

    // Verify we can extract the data field
    let data_field = vec_expr.field_select("Vec", "fld_data", array_sort);
    assert!(data_field.sort().is_array());
}

/// Test String stub returns correct struct sort with (ptr, len, cap) fields.
/// Part of #1281: sort_inference.rs lines 224-233.
/// Note: String uses 3 fields (no fld_data) unlike Vec's 4 fields,
/// because String operations don't expose character-level indexing.
#[test]
fn test_string_stub_sort_structure() {
    // String is encoded as (ptr, len, cap) - simpler than Vec's 4-field model
    let string_sort = struct_sort(
        RUST_STRING_SORT,
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
        ],
    );

    assert!(string_sort.is_datatype());
    assert_eq!(string_sort.datatype_name(), Some(RUST_STRING_SORT));

    // Verify field extraction works
    let string_expr = Expr::var("s", string_sort);
    let len_expr =
        string_expr.field_select(RUST_STRING_SORT, "fld_len", Sort::bitvec(POINTER_WIDTH));
    assert_eq!(len_expr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test RawVec<T, A> stub returns correct struct sort with (ptr, cap) fields.
/// Part of #1281: sort_inference.rs lines 237-245.
#[test]
fn test_rawvec_stub_sort_structure() {
    // RawVec has 2 fields (no len - that's in Vec)
    let rawvec_sort = struct_sort(
        "RawVec",
        [("fld_ptr", Sort::bitvec(POINTER_WIDTH)), ("fld_cap", Sort::bitvec(POINTER_WIDTH))],
    );

    assert!(rawvec_sort.is_datatype());
    assert_eq!(rawvec_sort.datatype_name(), Some("RawVec"));

    // Verify we can construct expressions
    let ptr = Expr::bitvec_const(0x2000, POINTER_WIDTH);
    let cap = Expr::bitvec_const(32, POINTER_WIDTH);
    let rawvec_expr =
        Expr::datatype_constructor("RawVec", "RawVec_mk", vec![ptr, cap], rawvec_sort);

    assert!(rawvec_expr.sort().is_datatype());
}

/// Test Global (allocator) stub returns bool sort for ZST.
/// Part of #1281: sort_inference.rs lines 249-251.
#[test]
fn test_global_allocator_stub_sort() {
    // Global is a ZST allocator marker, encoded as bool
    let global_sort = Sort::bool();

    assert!(global_sort.is_bool());

    // ZST expressions can use bool values (typically true for "exists")
    let global_expr = Expr::bool_const(true);
    assert!(global_expr.sort().is_bool());
}

/// Test tuple sort naming uses concise sort short names from field sorts.
#[test]
fn test_tuple_sort_name_uses_sort_short_names() {
    let fields = vec![("fld_0", Sort::bitvec(8)), ("fld_1", Sort::bool()), ("fld_2", Sort::int())];
    assert_eq!(StatementCodegen::tuple_sort_name(&fields), "Tuple_bv8_bool_int");
}

/// Test checked-op tuple `(T, bool)` is compressed to a packed bitvector.
/// This exercises `try_infer_sort_from_compound_ty` special handling.
#[test]
fn test_try_infer_sort_from_compound_ty_checked_tuple() {
    with_test_ay_ctx_for_source(SORT_INFERENCE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_checked");
        let body = instance.body().expect("tuple_checked body");

        let tuple_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Tuple(tys)) = ty.kind() {
                    tys.len() == 2 && matches!(tys[1].kind(), TyKind::RigidTy(RigidTy::Bool))
                } else {
                    false
                }
            })
            .expect("missing (u8, bool) tuple local");

        let sort = StatementCodegen::try_infer_sort_from_compound_ty(tuple_ty)
            .expect("compound sort inference should succeed");
        assert_eq!(sort.bitvec_width(), Some(9));
    });
}

/// Test non-checked tuple uses tuple datatype encoding, not packed bitvector encoding.
#[test]
fn test_try_infer_sort_from_compound_ty_regular_tuple() {
    with_test_ay_ctx_for_source(SORT_INFERENCE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_regular");
        let body = instance.body().expect("tuple_regular body");

        let tuple_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Tuple(tys)) = ty.kind() {
                    tys.len() == 2 && matches!(tys[1].kind(), TyKind::RigidTy(RigidTy::Uint(..)))
                } else {
                    false
                }
            })
            .expect("missing (u8, u16) tuple local");

        let sort = StatementCodegen::try_infer_sort_from_compound_ty(tuple_ty)
            .expect("compound sort inference should succeed");
        assert_eq!(sort.datatype_name(), Some("Tuple_bv8_bv16"));
    });
}

/// Test view sort inference for primitive numeric/bool/char locals.
#[test]
fn test_view_sort_from_ty_for_primitives() {
    with_test_ay_ctx_for_source(SORT_INFERENCE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_sort_inputs");
        let body = instance.body().expect("view_sort_inputs body");

        let mut saw_int = false;
        let mut saw_uint = false;
        let mut saw_bool = false;
        let mut saw_char = false;

        for ty in body.locals().iter().map(|local| local.ty) {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Int(_)) if !saw_int => {
                    let (sort, is_signed) = StatementCodegen::view_sort_from_ty(ty)
                        .expect("view sort should exist for signed int");
                    assert!(sort.is_int());
                    assert!(is_signed);
                    saw_int = true;
                }
                TyKind::RigidTy(RigidTy::Uint(_)) if !saw_uint => {
                    let (sort, is_signed) = StatementCodegen::view_sort_from_ty(ty)
                        .expect("view sort should exist for unsigned int");
                    assert!(sort.is_int());
                    assert!(!is_signed);
                    saw_uint = true;
                }
                TyKind::RigidTy(RigidTy::Bool) if !saw_bool => {
                    let (sort, is_signed) = StatementCodegen::view_sort_from_ty(ty)
                        .expect("view sort should exist for bool");
                    assert!(sort.is_bool());
                    assert!(!is_signed);
                    saw_bool = true;
                }
                TyKind::RigidTy(RigidTy::Char) if !saw_char => {
                    let (sort, is_signed) = StatementCodegen::view_sort_from_ty(ty)
                        .expect("view sort should exist for char");
                    assert!(sort.is_int());
                    assert!(!is_signed);
                    saw_char = true;
                }
                _ => {}
            }
        }

        assert!(saw_int, "missing signed integer local");
        assert!(saw_uint, "missing unsigned integer local");
        assert!(saw_bool, "missing bool local");
        assert!(saw_char, "missing char local");
    });
}

// =============================================================================
// Standalone sort construction tests (no MIR context needed)
// =============================================================================

/// Test slice_sort produces a struct with (fld_ptr, fld_len, fld_data) fields.
#[test]
fn test_slice_sort_structure() {
    let elem = Sort::bitvec(32);
    let slice = StatementCodegen::slice_sort(elem);
    assert!(slice.is_datatype());
    assert_eq!(slice.datatype_name(), Some("Slice_bv32"));

    // Verify field sorts via expression construction
    let s = Expr::var("s", slice);
    let ptr = s.clone().field_select("Slice_bv32", "fld_ptr", Sort::bitvec(POINTER_WIDTH));
    let len = s.clone().field_select("Slice_bv32", "fld_len", Sort::bitvec(POINTER_WIDTH));
    let data = s.field_select(
        "Slice_bv32",
        "fld_data",
        Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32)),
    );
    assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(len.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert!(data.sort().is_array());
}

/// Test slice_sort naming varies with element sort.
#[test]
fn test_slice_sort_naming() {
    let s8 = StatementCodegen::slice_sort(Sort::bitvec(8));
    let s64 = StatementCodegen::slice_sort(Sort::bitvec(64));
    let s_bool = StatementCodegen::slice_sort(Sort::bool());
    assert_eq!(s8.datatype_name(), Some("Slice_bv8"));
    assert_eq!(s64.datatype_name(), Some("Slice_bv64"));
    assert_eq!(s_bool.datatype_name(), Some("Slice_bool"));
}

/// Test dyn_sort produces a fat pointer struct with (fld_ptr, fld_vtable).
#[test]
fn test_dyn_sort_structure() {
    let dyn_sort = StatementCodegen::dyn_sort("Display");
    assert!(dyn_sort.is_datatype());
    assert_eq!(dyn_sort.datatype_name(), Some("Dyn_Display"));

    let d = Expr::var("d", dyn_sort);
    let ptr = d.clone().field_select("Dyn_Display", "fld_ptr", Sort::bitvec(POINTER_WIDTH));
    let vtable = d.field_select("Dyn_Display", "fld_vtable", Sort::bitvec(POINTER_WIDTH));
    assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(vtable.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test tuple_sort_name with empty field list.
#[test]
fn test_tuple_sort_name_empty() {
    let fields: Vec<(String, Sort)> = vec![];
    assert_eq!(StatementCodegen::tuple_sort_name(&fields), "Tuple");
}

/// Test tuple_sort_name with single field.
#[test]
fn test_tuple_sort_name_single() {
    let fields = vec![("fld_0", Sort::bitvec(64))];
    assert_eq!(StatementCodegen::tuple_sort_name(&fields), "Tuple_bv64");
}

// =============================================================================
// MIR-based infer_sort_from_ty tests (Part of #2016)
// =============================================================================

const SORT_INFERENCE_EXTENDED_SOURCE: &str = r#"
#![allow(dead_code)]
pub struct Point { x: i32, y: i32 }
pub enum Color { Red, Green, Blue }
pub enum Maybe<T> { Nothing, Just(T) }

pub fn probe_sort_types() -> (Point, Color, Maybe<u8>) {
    let p = Point { x: 1, y: 2 };
    let c = Color::Green;
    let m = Maybe::Just(42u8);
    (p, c, m)
}
"#;

/// Test infer_sort_from_ty for a user-defined struct with i32 fields.
#[test]
fn test_infer_sort_from_ty_struct() {
    with_test_ay_ctx_for_source(SORT_INFERENCE_EXTENDED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_sort_types");
        let body = instance.body().expect("body");

        let struct_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Point"
                } else {
                    false
                }
            })
            .expect("missing Point local");

        let sort = StatementCodegen::infer_sort_from_ty(struct_ty)
            .expect("sort inference should succeed for Point struct");
        assert!(sort.is_datatype());
        // Point has two i32 fields → fld_x: bv32, fld_y: bv32
        let dt_name = sort.datatype_name().unwrap().to_string();
        let p = Expr::var("p", sort);
        let x = p.field_select(&dt_name, "fld_x", Sort::bitvec(32));
        assert_eq!(x.sort().bitvec_width(), Some(32));
    });
}

/// Test infer_sort_from_ty for a unit enum (all variants fieldless).
#[test]
fn test_infer_sort_from_ty_unit_enum() {
    with_test_ay_ctx_for_source(SORT_INFERENCE_EXTENDED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_sort_types");
        let body = instance.body().expect("body");

        let enum_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Color"
                } else {
                    false
                }
            })
            .expect("missing Color local");

        let sort = StatementCodegen::infer_sort_from_ty(enum_ty)
            .expect("sort inference should succeed for unit enum");
        // Unit enums → bitvec discriminant
        assert!(sort.is_bitvec(), "unit enum should be bitvec, got {:?}", sort);
        // 3 variants → fits in 32 bits (conservative default)
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

/// Test infer_sort_from_ty for an Option-like enum with one payload variant.
#[test]
fn test_infer_sort_from_ty_option_like_enum() {
    with_test_ay_ctx_for_source(SORT_INFERENCE_EXTENDED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_sort_types");
        let body = instance.body().expect("body");

        let maybe_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Maybe"
                } else {
                    false
                }
            })
            .expect("missing Maybe<u8> local");

        let sort = StatementCodegen::infer_sort_from_ty(maybe_ty)
            .expect("sort inference should succeed for Option-like enum");
        // Option-like enum → SMT datatype with Nothing/Just constructors
        assert!(sort.is_datatype(), "Option-like enum should be datatype, got {:?}", sort);
    });
}

// =============================================================================
// MIR-based infer_sort_from_ty: pointer/ref/slice/array types (Part of #2016)
// =============================================================================

const POINTER_REF_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn ptr_ref_probe(
    raw_ptr: *const u32,
    ref_val: &u64,
    slice_ref: &[i32],
    str_ref: &str,
    arr_ref: &[u8; 4],
    dyn_ref: &dyn core::fmt::Debug,
) {}
"#;

/// Test infer_sort_from_ty: *const u32 → bitvec(POINTER_WIDTH)
#[test]
fn test_infer_sort_raw_ptr() {
    with_test_ay_ctx_for_source(POINTER_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "ptr_ref_probe");
        let body = instance.body().expect("body");

        // Local 1: raw_ptr: *const u32
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("raw ptr sort");
        // *const u32 pointee is u32 (not slice/str/dyn), so it's a thin pointer
        assert!(sort.is_bitvec(), "raw ptr should be bitvec, got {:?}", sort);
        assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test infer_sort_from_ty: &u64 → bitvec(POINTER_WIDTH)
#[test]
fn test_infer_sort_ref() {
    with_test_ay_ctx_for_source(POINTER_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "ptr_ref_probe");
        let body = instance.body().expect("body");

        // Local 2: ref_val: &u64
        let ty = body.locals()[2].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("ref sort");
        assert!(sort.is_bitvec(), "ref to u64 should be thin pointer bitvec");
        assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test infer_sort_from_ty: &[i32] → Slice_bv32 fat pointer
#[test]
fn test_infer_sort_slice_ref() {
    with_test_ay_ctx_for_source(POINTER_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "ptr_ref_probe");
        let body = instance.body().expect("body");

        // Local 3: slice_ref: &[i32]
        let ty = body.locals()[3].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("slice ref sort");
        assert!(sort.is_datatype(), "slice ref should be fat pointer datatype");
        assert_eq!(sort.datatype_name(), Some("Slice_bv32"));
    });
}

/// Test infer_sort_from_ty: &str → Slice_bv8 fat pointer
#[test]
fn test_infer_sort_str_ref() {
    with_test_ay_ctx_for_source(POINTER_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "ptr_ref_probe");
        let body = instance.body().expect("body");

        // Local 4: str_ref: &str
        let ty = body.locals()[4].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("str ref sort");
        assert!(sort.is_datatype(), "str ref should be fat pointer datatype");
        assert_eq!(sort.datatype_name(), Some("Slice_bv8"));
    });
}

/// Test infer_sort_from_ty: &[u8; 4] → bitvec(POINTER_WIDTH) (thin pointer to array)
#[test]
fn test_infer_sort_array_ref() {
    with_test_ay_ctx_for_source(POINTER_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "ptr_ref_probe");
        let body = instance.body().expect("body");

        // Local 5: arr_ref: &[u8; 4]
        let ty = body.locals()[5].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("array ref sort");
        // &[u8; 4] is a thin pointer (not a slice)
        assert!(sort.is_bitvec(), "array ref should be thin pointer bitvec");
        assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test infer_sort_from_ty: &dyn Debug → Dyn_Trait fat pointer
#[test]
fn test_infer_sort_dyn_ref() {
    with_test_ay_ctx_for_source(POINTER_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "ptr_ref_probe");
        let body = instance.body().expect("body");

        // Local 6: dyn_ref: &dyn Debug
        let ty = body.locals()[6].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("dyn ref sort");
        assert!(sort.is_datatype(), "dyn ref should be fat pointer datatype");
        assert_eq!(sort.datatype_name(), Some("Dyn_Trait"));
    });
}

// =============================================================================
// MIR-based infer_sort_from_ty: numeric primitives and char (Part of #2016)
// =============================================================================

const PRIMITIVE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn prim_probe(
    b: bool,
    i8v: i8,
    i16v: i16,
    i32v: i32,
    i64v: i64,
    i128v: i128,
    u8v: u8,
    u16v: u16,
    u32v: u32,
    u64v: u64,
    u128v: u128,
    f32v: f32,
    f64v: f64,
    cv: char,
    isz: isize,
    usz: usize,
) {}
"#;

/// Test infer_sort_from_ty covers all primitive types with correct bitvec widths.
#[test]
fn test_infer_sort_all_primitives() {
    with_test_ay_ctx_for_source(PRIMITIVE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "prim_probe");
        let body = instance.body().expect("body");

        let locals = body.locals();
        // Local 0 is return place (unit), locals 1-16 are args

        // bool → Sort::bool()
        let sort = StatementCodegen::infer_sort_from_ty(locals[1].ty).unwrap();
        assert!(sort.is_bool(), "bool");

        // i8 → bv8
        let sort = StatementCodegen::infer_sort_from_ty(locals[2].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(8), "i8");

        // i16 → bv16
        let sort = StatementCodegen::infer_sort_from_ty(locals[3].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(16), "i16");

        // i32 → bv32
        let sort = StatementCodegen::infer_sort_from_ty(locals[4].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(32), "i32");

        // i64 → bv64
        let sort = StatementCodegen::infer_sort_from_ty(locals[5].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(64), "i64");

        // i128 → bv128
        let sort = StatementCodegen::infer_sort_from_ty(locals[6].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(128), "i128");

        // u8 → bv8
        let sort = StatementCodegen::infer_sort_from_ty(locals[7].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(8), "u8");

        // u16 → bv16
        let sort = StatementCodegen::infer_sort_from_ty(locals[8].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(16), "u16");

        // u32 → bv32
        let sort = StatementCodegen::infer_sort_from_ty(locals[9].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(32), "u32");

        // u64 → bv64
        let sort = StatementCodegen::infer_sort_from_ty(locals[10].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(64), "u64");

        // u128 → bv128
        let sort = StatementCodegen::infer_sort_from_ty(locals[11].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(128), "u128");

        // f32 → bv32
        let sort = StatementCodegen::infer_sort_from_ty(locals[12].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(32), "f32");

        // f64 → bv64
        let sort = StatementCodegen::infer_sort_from_ty(locals[13].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(64), "f64");

        // char → bv32
        let sort = StatementCodegen::infer_sort_from_ty(locals[14].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(32), "char");

        // isize → bv(POINTER_WIDTH)
        let sort = StatementCodegen::infer_sort_from_ty(locals[15].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH), "isize");

        // usize → bv(POINTER_WIDTH)
        let sort = StatementCodegen::infer_sort_from_ty(locals[16].ty).unwrap();
        assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH), "usize");
    });
}

// =============================================================================
// MIR-based infer_sort_from_ty: arrays and tuples (Part of #2016)
// =============================================================================

const ARRAY_TUPLE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn array_tuple_probe(
    arr: [u32; 5],
    empty_tuple: (),
    triple: (u8, u16, u32),
) {}
"#;

/// Test infer_sort_from_ty: [u32; 5] → Array(bv_ptr, bv32)
#[test]
fn test_infer_sort_array() {
    with_test_ay_ctx_for_source(ARRAY_TUPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_tuple_probe");
        let body = instance.body().expect("body");

        // Local 1: arr: [u32; 5]
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("array sort");
        assert!(sort.is_array(), "array should produce SMT array sort");
    });
}

/// Test infer_sort_from_ty: () → Unit struct
#[test]
fn test_infer_sort_unit_tuple() {
    with_test_ay_ctx_for_source(ARRAY_TUPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_tuple_probe");
        let body = instance.body().expect("body");

        // Local 2: empty_tuple: ()
        let ty = body.locals()[2].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("unit tuple sort");
        assert!(sort.is_datatype(), "unit tuple should be Unit struct datatype");
        assert_eq!(sort.datatype_name(), Some("Unit"));
    });
}

/// Test infer_sort_from_ty: (u8, u16, u32) → Tuple_bv8_bv16_bv32
#[test]
fn test_infer_sort_triple_tuple() {
    with_test_ay_ctx_for_source(ARRAY_TUPLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_tuple_probe");
        let body = instance.body().expect("body");

        // Local 3: triple: (u8, u16, u32)
        let ty = body.locals()[3].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("triple tuple sort");
        assert!(sort.is_datatype(), "tuple should be datatype");
        assert_eq!(sort.datatype_name(), Some("Tuple_bv8_bv16_bv32"));
    });
}

// =============================================================================
// MIR-based infer_sort_from_ty: special ADT types (Part of #2016)
// =============================================================================

const SPECIAL_ADT_SOURCE: &str = r#"
#![allow(dead_code)]
use std::mem::MaybeUninit;
use std::mem::ManuallyDrop;
use std::num::NonZero;
use std::ptr::NonNull;

pub fn special_adt_probe(
    mu: MaybeUninit<u32>,
    md: ManuallyDrop<i64>,
    nn: NonNull<u8>,
    nz: NonZero<u32>,
) {}
"#;

/// Test infer_sort_from_ty: MaybeUninit<u32> → bv32 (transparent wrapper)
#[test]
fn test_infer_sort_maybe_uninit() {
    with_test_ay_ctx_for_source(SPECIAL_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "special_adt_probe");
        let body = instance.body().expect("body");

        // Local 1: mu: MaybeUninit<u32>
        let ty = body.locals()[1].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("MaybeUninit sort");
        // MaybeUninit<u32> is transparent → unwraps to u32 → bv32
        assert_eq!(sort.bitvec_width(), Some(32), "MaybeUninit<u32> → bv32");
    });
}

/// Test infer_sort_from_ty: ManuallyDrop<i64> → bv64 (transparent wrapper)
#[test]
fn test_infer_sort_manually_drop() {
    with_test_ay_ctx_for_source(SPECIAL_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "special_adt_probe");
        let body = instance.body().expect("body");

        // Local 2: md: ManuallyDrop<i64>
        let ty = body.locals()[2].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("ManuallyDrop sort");
        assert_eq!(sort.bitvec_width(), Some(64), "ManuallyDrop<i64> → bv64");
    });
}

/// Test infer_sort_from_ty: NonNull<u8> → bitvec(POINTER_WIDTH)
#[test]
fn test_infer_sort_non_null() {
    with_test_ay_ctx_for_source(SPECIAL_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "special_adt_probe");
        let body = instance.body().expect("body");

        // Local 3: nn: NonNull<u8>
        let ty = body.locals()[3].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("NonNull sort");
        assert!(sort.is_bitvec(), "NonNull should be pointer bitvec");
        assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test infer_sort_from_ty: NonZero<u32> → bv32 (transparent wrapper)
#[test]
fn test_infer_sort_non_zero() {
    with_test_ay_ctx_for_source(SPECIAL_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "special_adt_probe");
        let body = instance.body().expect("body");

        // Local 4: nz: NonZero<u32>
        let ty = body.locals()[4].ty;
        let sort = StatementCodegen::infer_sort_from_ty(ty).expect("NonZero sort");
        assert_eq!(sort.bitvec_width(), Some(32), "NonZero<u32> → bv32");
    });
}

// =============================================================================
// MIR-based infer_adt_sort: general enum with payload fields (Part of #2016)
// =============================================================================

const GENERAL_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
pub enum MyResult<T, E> {
    Ok(T),
    Err(E),
}

pub struct Wrapper { inner: u32 }

pub fn general_enum_probe() -> (MyResult<u32, bool>, Wrapper) {
    (MyResult::Ok(42), Wrapper { inner: 1 })
}
"#;

/// Test infer_sort_from_ty: general enum with two payload variants → SMT datatype
#[test]
fn test_infer_sort_general_enum() {
    with_test_ay_ctx_for_source(GENERAL_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "general_enum_probe");
        let body = instance.body().expect("body");

        let result_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "MyResult"
                } else {
                    false
                }
            })
            .expect("missing MyResult local");

        let sort = StatementCodegen::infer_sort_from_ty(result_ty).expect("general enum sort");
        // Result-like enum → SMT datatype with Ok/Err constructors
        assert!(sort.is_datatype(), "general enum should be datatype, got {:?}", sort);
        let name = sort.datatype_name().unwrap();
        assert!(name.contains("MyResult"), "sort name should contain MyResult, got {}", name);
    });
}

/// Test infer_sort_from_ty: struct with named fields → SMT datatype with fld_ prefix
#[test]
fn test_infer_sort_struct_fields() {
    with_test_ay_ctx_for_source(GENERAL_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "general_enum_probe");
        let body = instance.body().expect("body");

        let wrapper_ty = body
            .locals()
            .iter()
            .map(|local| local.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Wrapper"
                } else {
                    false
                }
            })
            .expect("missing Wrapper local");

        let sort = StatementCodegen::infer_sort_from_ty(wrapper_ty).expect("struct sort");
        assert!(sort.is_datatype(), "struct should be datatype");
        let name = sort.datatype_name().unwrap().to_string();
        // Verify field extraction works: fld_inner should be bv32
        let expr = Expr::var("w", sort);
        let inner = expr.field_select(&name, "fld_inner", Sort::bitvec(32));
        assert_eq!(inner.sort().bitvec_width(), Some(32));
    });
}

// =============================================================================
// MIR-based view_sort_from_ty: unsupported types return None (Part of #2016)
// =============================================================================

const VIEW_SORT_EXTENDED_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn view_extended_probe(
    f: f64,
    arr: [u8; 3],
    ptr: *const i32,
) {}
"#;

/// Test view_sort_from_ty returns None for unsupported types (float, array, ptr)
#[test]
fn test_view_sort_unsupported_types() {
    with_test_ay_ctx_for_source(VIEW_SORT_EXTENDED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "view_extended_probe");
        let body = instance.body().expect("body");

        // f64 should NOT have a view sort (not a mathematical integer type)
        let f64_ty = body.locals()[1].ty;
        assert!(
            StatementCodegen::view_sort_from_ty(f64_ty).is_none(),
            "f64 should not have view sort"
        );

        // [u8; 3] should not have a view sort
        let arr_ty = body.locals()[2].ty;
        assert!(
            StatementCodegen::view_sort_from_ty(arr_ty).is_none(),
            "array should not have view sort"
        );

        // *const i32 should not have a view sort
        let ptr_ty = body.locals()[3].ty;
        assert!(
            StatementCodegen::view_sort_from_ty(ptr_ty).is_none(),
            "pointer should not have view sort"
        );
    });
}

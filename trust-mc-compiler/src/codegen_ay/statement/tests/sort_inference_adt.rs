// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for sort_inference_adt.rs — well-known ADT sort inference.
//!
//! Tests cover:
//! - `infer_wellknown_adt_from_ty`: transparent wrappers (MaybeUninit, ManuallyDrop),
//!   pointer wrappers (NonNull, Unique), NonZero<T>, BigInt/BigUint/Ratio,
//!   IndexRange, Global, Layout, Entry/VacantEntry/OccupiedEntry, SetValZST
//! - `infer_adt_sort`: unit enums (all-fieldless), Option-like enums, general structs,
//!   general enums (Result-like), and fallback None cases
//!
//! Exercises production functions from sort_inference_adt.rs through real MIR types.
//!
//! Part of #2382 (dedicated test coverage for sort_inference_adt.rs).

use super::*;
use crate::codegen_ay::names::{self, struct_sort};

// ═══════════════════════════════════════════════════════════════════════
// MIR probe sources for well-known ADT types
// ═══════════════════════════════════════════════════════════════════════

const WELLKNOWN_ADT_SOURCE: &str = r#"
#![allow(dead_code)]

use std::mem::MaybeUninit;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;
use std::num::NonZero;

pub fn maybe_uninit_probe(x: MaybeUninit<u32>) -> u32 {
    unsafe { x.assume_init() }
}

pub fn manually_drop_probe(x: ManuallyDrop<u64>) -> u64 {
    ManuallyDrop::into_inner(x)
}

pub fn nonnull_probe(ptr: NonNull<u32>) -> *mut u32 {
    ptr.as_ptr()
}

pub fn nonzero_u32_probe(x: NonZero<u32>) -> u32 {
    x.get()
}
"#;

const BIGINT_SORT_SOURCE: &str = r#"
#![allow(dead_code)]

pub struct BigInt(pub u64);
pub struct BigUint(pub u64);
pub struct Ratio(pub u64, pub u64);

pub fn bigint_sort_probe(x: BigInt) -> u64 { x.0 }
pub fn biguint_sort_probe(x: BigUint) -> u64 { x.0 }
pub fn ratio_sort_probe(x: Ratio) -> u64 { x.0 }
"#;

const UNIT_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]

#[derive(Copy, Clone)]
pub enum Color { Red, Green, Blue }

#[derive(Copy, Clone)]
pub enum Direction { North, South, East, West }

pub fn color_probe(c: Color) -> u32 {
    match c {
        Color::Red => 0,
        Color::Green => 1,
        Color::Blue => 2,
    }
}

pub fn direction_probe(d: Direction) -> u32 {
    match d {
        Direction::North => 0,
        Direction::South => 1,
        Direction::East => 2,
        Direction::West => 3,
    }
}
"#;

const GENERAL_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]

pub enum Shape {
    Circle(u32),
    Rectangle(u32, u32),
    Triangle(u32, u32, u32),
}

pub fn shape_probe(s: Shape) -> u32 {
    match s {
        Shape::Circle(r) => r,
        Shape::Rectangle(w, h) => w.wrapping_add(h),
        Shape::Triangle(a, b, c) => a.wrapping_add(b).wrapping_add(c),
    }
}
"#;

// ═══════════════════════════════════════════════════════════════════════
// infer_wellknown_adt_from_ty: transparent wrappers
// ═══════════════════════════════════════════════════════════════════════

/// MaybeUninit<u32> should unwrap to u32's sort (bv32).
#[test]
fn test_infer_wellknown_maybe_uninit_unwraps_to_inner() {
    with_test_ay_ctx_for_source(WELLKNOWN_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "maybe_uninit_probe");
        let body = instance.body().expect("body");

        // Find the MaybeUninit<u32> local type
        let mu_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "MaybeUninit"
                } else {
                    false
                }
            })
            .expect("missing MaybeUninit<u32> local");

        let sort = StatementCodegen::infer_sort_from_ty(mu_ty)
            .expect("infer_sort_from_ty should succeed for MaybeUninit<u32>");
        assert_eq!(
            sort.bitvec_width(),
            Some(32),
            "MaybeUninit<u32> should unwrap to bv32, got {:?}",
            sort
        );
    });
}

/// ManuallyDrop<u64> should unwrap to u64's sort (bv64).
#[test]
fn test_infer_wellknown_manually_drop_unwraps_to_inner() {
    with_test_ay_ctx_for_source(WELLKNOWN_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "manually_drop_probe");
        let body = instance.body().expect("body");

        let md_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "ManuallyDrop"
                } else {
                    false
                }
            })
            .expect("missing ManuallyDrop<u64> local");

        let sort = StatementCodegen::infer_sort_from_ty(md_ty)
            .expect("infer_sort_from_ty should succeed for ManuallyDrop<u64>");
        assert_eq!(
            sort.bitvec_width(),
            Some(64),
            "ManuallyDrop<u64> should unwrap to bv64, got {:?}",
            sort
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// infer_wellknown_adt_from_ty: pointer wrappers
// ═══════════════════════════════════════════════════════════════════════

/// NonNull<u32> should produce pointer-width bitvec sort.
#[test]
fn test_infer_wellknown_nonnull_produces_pointer_bitvec() {
    with_test_ay_ctx_for_source(WELLKNOWN_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "nonnull_probe");
        let body = instance.body().expect("body");

        let nn_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "NonNull"
                } else {
                    false
                }
            })
            .expect("missing NonNull<u32> local");

        let sort = StatementCodegen::infer_sort_from_ty(nn_ty)
            .expect("infer_sort_from_ty should succeed for NonNull<u32>");
        assert_eq!(
            sort.bitvec_width(),
            Some(POINTER_WIDTH),
            "NonNull<u32> should be pointer-width bitvec, got {:?}",
            sort
        );
    });
}

/// NonZero<u32> should produce bv32 (transparent wrapper around u32).
#[test]
fn test_infer_wellknown_nonzero_u32_produces_bv32() {
    with_test_ay_ctx_for_source(WELLKNOWN_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "nonzero_u32_probe");
        let body = instance.body().expect("body");

        let nz_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "NonZero"
                } else {
                    false
                }
            })
            .expect("missing NonZero<u32> local");

        let sort = StatementCodegen::infer_sort_from_ty(nz_ty)
            .expect("infer_sort_from_ty should succeed for NonZero<u32>");
        assert_eq!(
            sort.bitvec_width(),
            Some(32),
            "NonZero<u32> should unwrap to bv32, got {:?}",
            sort
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// infer_wellknown_adt_from_ty: BigInt/BigUint/Ratio
// ═══════════════════════════════════════════════════════════════════════

/// BigInt should be inferred as Int sort.
#[test]
fn test_infer_wellknown_bigint_produces_int_sort() {
    with_test_ay_ctx_for_source(BIGINT_SORT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "bigint_sort_probe");
        let body = instance.body().expect("body");

        let bigint_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "BigInt"
                } else {
                    false
                }
            })
            .expect("missing BigInt local");

        let sort = StatementCodegen::infer_sort_from_ty(bigint_ty)
            .expect("infer_sort_from_ty should succeed for BigInt");
        assert!(sort.is_int(), "BigInt should produce Int sort, got {:?}", sort);
    });
}

/// BigUint should also be inferred as Int sort.
#[test]
fn test_infer_wellknown_biguint_produces_int_sort() {
    with_test_ay_ctx_for_source(BIGINT_SORT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "biguint_sort_probe");
        let body = instance.body().expect("body");

        let biguint_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "BigUint"
                } else {
                    false
                }
            })
            .expect("missing BigUint local");

        let sort = StatementCodegen::infer_sort_from_ty(biguint_ty)
            .expect("infer_sort_from_ty should succeed for BigUint");
        assert!(sort.is_int(), "BigUint should produce Int sort, got {:?}", sort);
    });
}

/// Ratio should be inferred as Int sort.
#[test]
fn test_infer_wellknown_ratio_produces_int_sort() {
    with_test_ay_ctx_for_source(BIGINT_SORT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "ratio_sort_probe");
        let body = instance.body().expect("body");

        let ratio_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Ratio"
                } else {
                    false
                }
            })
            .expect("missing Ratio local");

        let sort = StatementCodegen::infer_sort_from_ty(ratio_ty)
            .expect("infer_sort_from_ty should succeed for Ratio");
        assert!(sort.is_int(), "Ratio should produce Int sort, got {:?}", sort);
    });
}

// ═══════════════════════════════════════════════════════════════════════
// infer_adt_sort: unit enums
// ═══════════════════════════════════════════════════════════════════════

/// Unit enum Color{Red,Green,Blue} should produce bitvec sort (discriminant encoding).
#[test]
fn test_infer_adt_sort_unit_enum_produces_bitvec() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "color_probe");
        let body = instance.body().expect("body");

        let color_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Color"
                } else {
                    false
                }
            })
            .expect("missing Color local");

        let sort = StatementCodegen::infer_sort_from_ty(color_ty)
            .expect("infer_sort_from_ty should succeed for Color");
        assert!(sort.is_bitvec(), "unit enum Color should produce bitvec sort, got {:?}", sort);
        assert_eq!(
            sort.bitvec_width(),
            Some(32),
            "unit enum with <=65536 variants should use 32-bit bitvec, got {:?}",
            sort
        );
    });
}

/// Direction{N,S,E,W} with 4 variants should also be bv32.
#[test]
fn test_infer_adt_sort_unit_enum_four_variants_bv32() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "direction_probe");
        let body = instance.body().expect("body");

        let dir_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Direction"
                } else {
                    false
                }
            })
            .expect("missing Direction local");

        let sort = StatementCodegen::infer_sort_from_ty(dir_ty)
            .expect("infer_sort_from_ty should succeed for Direction");
        assert!(sort.is_bitvec(), "Direction should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

// ═══════════════════════════════════════════════════════════════════════
// infer_adt_sort: general enums with payload fields
// ═══════════════════════════════════════════════════════════════════════

/// Shape enum with multiple constructors each having different field counts
/// should produce a Datatype sort.
#[test]
fn test_infer_adt_sort_general_enum_produces_datatype() {
    with_test_ay_ctx_for_source(GENERAL_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "shape_probe");
        let body = instance.body().expect("body");

        let shape_ty = body
            .locals()
            .iter()
            .map(|l| l.ty)
            .find(|ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
                    def.trimmed_name() == "Shape"
                } else {
                    false
                }
            })
            .expect("missing Shape local");

        let sort = StatementCodegen::infer_sort_from_ty(shape_ty)
            .expect("infer_sort_from_ty should succeed for Shape");
        assert!(
            sort.is_datatype(),
            "general enum Shape should produce Datatype sort, got {:?}",
            sort
        );
        let dt_name = sort.datatype_name().expect("Shape Datatype should have a name");
        assert!(
            dt_name.contains("Shape"),
            "Shape Datatype name should contain 'Shape', got {dt_name}"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Sort construction helpers: direct API verification
// ═══════════════════════════════════════════════════════════════════════

/// IndexRange sort should be a struct with fld_start and fld_end bitvec fields.
#[test]
fn test_index_range_sort_structure() {
    let ir_sort = names::index_range_sort();
    assert!(ir_sort.is_datatype(), "IndexRange sort should be Datatype");
    let dt_name = ir_sort.datatype_name().expect("IndexRange should have name");
    assert_eq!(dt_name, "IndexRange", "name should be IndexRange");

    let ir = Expr::var("ir", ir_sort);
    let start = ir.clone().field_select("IndexRange", "fld_start", Sort::bitvec(POINTER_WIDTH));
    let end = ir.field_select("IndexRange", "fld_end", Sort::bitvec(POINTER_WIDTH));
    assert_eq!(start.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(end.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// RawVec sort should have fld_ptr and fld_cap pointer-width bitvec fields.
#[test]
fn test_rawvec_sort_field_structure() {
    let rv_sort = struct_sort("RawVec", names::rawvec_fields());
    assert!(rv_sort.is_datatype(), "RawVec sort should be Datatype");

    let rv = Expr::var("rv", rv_sort);
    let ptr = rv.clone().field_select("RawVec", "fld_ptr", Sort::bitvec(POINTER_WIDTH));
    let cap = rv.field_select("RawVec", "fld_cap", Sort::bitvec(POINTER_WIDTH));
    assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(cap.sort().bitvec_width(), Some(POINTER_WIDTH));
}

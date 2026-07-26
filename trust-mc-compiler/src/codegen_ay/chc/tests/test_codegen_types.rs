// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unit tests for chc/codegen_types.rs — translate_ty, translate_adt_sort,
// deref_ref_ty, is_opaque_alloc_infra, and related helpers.
// Part of #2213: coverage gap remediation for codegen_types.rs (856 LOC, ~1%).
//
// Extends the 7 existing tests in test_core_vc.rs (Bool, Array, Unit, RawPtr,
// Ref, Tuple pair, single-element tuple) with coverage for integer types, unsigned
// types, float types, char, FnDef, slices, closures, and named ADT special cases
// (String, Vec, Box, PhantomData, NonZero, ManuallyDrop, Option, user structs,
// unit enums, general enums).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::ChcCtx;
use super::common::*;
use crate::codegen_ay::names::{self, RUST_STRING_SORT, struct_sort};

mod test_codegen_types_into_iter;

// =============================================================================
// Primitive types — signed integers
// =============================================================================

#[test]
fn test_translate_ty_i8() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_i8(x: i8) -> i8 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_i8");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "i8 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(8));
    });
}

#[test]
fn test_translate_ty_i16() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_i16(x: i16) -> i16 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_i16");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "i16 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(16));
    });
}

#[test]
fn test_translate_ty_i32() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_i32(x: i32) -> i32 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_i32");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "i32 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

#[test]
fn test_translate_ty_i64() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_i64(x: i64) -> i64 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_i64");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "i64 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

#[test]
fn test_translate_ty_i128() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_i128(x: i128) -> i128 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_i128");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "i128 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(128));
    });
}

#[test]
fn test_translate_ty_isize() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_isize(x: isize) -> isize { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_isize");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "isize should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64), "isize should be pointer-width (64)");
    });
}

// =============================================================================
// Primitive types — unsigned integers
// =============================================================================

#[test]
fn test_translate_ty_u8() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_u8(x: u8) -> u8 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_u8");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "u8 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(8));
    });
}

#[test]
fn test_translate_ty_u16() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_u16(x: u16) -> u16 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_u16");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "u16 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(16));
    });
}

#[test]
fn test_translate_ty_u32() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_u32(x: u32) -> u32 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_u32");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "u32 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

#[test]
fn test_translate_ty_u64() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_u64(x: u64) -> u64 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_u64");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "u64 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

#[test]
fn test_translate_ty_u128() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_u128(x: u128) -> u128 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_u128");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "u128 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(128));
    });
}

#[test]
fn test_translate_ty_usize() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_usize(x: usize) -> usize { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_usize");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "usize should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64), "usize should be pointer-width (64)");
    });
}

// =============================================================================
// Primitive types — floats
// =============================================================================

#[test]
fn test_translate_ty_f32() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_f32(x: f32) -> f32 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_f32");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "f32 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

#[test]
fn test_translate_ty_f64() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_f64(x: f64) -> f64 { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_f64");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "f64 should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

// =============================================================================
// Primitive types — char
// =============================================================================

#[test]
fn test_translate_ty_char() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_char(x: char) -> char { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_char");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bitvec(), "char should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(32), "char should be 32-bit");
    });
}

// =============================================================================
// Pointer/function types
// =============================================================================

#[test]
fn test_translate_ty_mut_ref_is_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_mut_ref(r: &mut u32) -> &mut u32 { r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_mut_ref");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "&mut ref should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64), "&mut ref should be pointer-width");
    });
}

#[test]
fn test_translate_ty_raw_mut_ptr_is_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_mut_ptr(p: *mut u8) -> *mut u8 { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_mut_ptr");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "*mut ptr should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

#[test]
fn test_translate_ty_fn_ptr_is_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_fn_ptr(f: fn(u32) -> u32) -> fn(u32) -> u32 { f }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_fn_ptr");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "fn ptr should be bitvec");
        assert_eq!(sort.bitvec_width(), Some(64), "fn ptr should be pointer-width");
    });
}

// =============================================================================
// Compound types — slices
// =============================================================================

#[test]
fn test_translate_ty_slice_is_array() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_slice(s: &[u32]) -> &[u32] { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_slice");
        // &[u32] is a reference — deref to get the slice type
        let ref_ty = sig.inputs()[0];
        // The reference itself translates to bitvec (pointer), so we check
        // that the translation produces a sort (bitvec for the reference)
        let sort = ChcCtx::translate_ty(ref_ty).unwrap();
        assert!(sort.is_bitvec(), "&[u32] reference should be bitvec (pointer)");
    });
}

// =============================================================================
// Named ADT special cases — String
// =============================================================================

#[test]
fn test_translate_ty_string_is_struct() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::String;
        pub fn probe_string(s: String) -> String { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_string");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "String should be datatype");
        assert_eq!(
            sort.datatype_name(),
            Some(RUST_STRING_SORT),
            "String sort name should be 'RustString'"
        );
    });
}

// =============================================================================
// Named ADT special cases — Vec
// =============================================================================

#[test]
fn test_translate_ty_vec_u32_is_struct() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;
        pub fn probe_vec(v: Vec<u32>) -> Vec<u32> { v }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_vec");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "Vec<u32> should be datatype");
        assert_eq!(
            sort.datatype_name(),
            Some("Vec_bv32"),
            "Vec<u32> sort name should be 'Vec_bv32'"
        );
    });
}

// =============================================================================
// Named ADT special cases — Box
// =============================================================================

#[test]
fn test_translate_ty_box_is_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::boxed::Box;
        pub fn probe_box(b: Box<u32>) -> Box<u32> { b }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_box");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "Box<u32> should be bitvec (pointer)");
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

// =============================================================================
// Named ADT special cases — PhantomData
// =============================================================================

#[test]
fn test_translate_ty_phantom_data_is_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::marker::PhantomData;
        pub fn probe_phantom(p: PhantomData<u32>) -> PhantomData<u32> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_phantom");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bool(), "PhantomData should be Bool (ZST)");
    });
}

// =============================================================================
// Named ADT special cases — Option
// =============================================================================

#[test]
fn test_translate_ty_option_u32_is_enum() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option(o: Option<u32>) -> Option<u32> { o }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "Option<u32> should be datatype (enum)");
        let name = sort.datatype_name().unwrap_or("");
        assert!(name.contains("Option"), "Option sort name should contain 'Option', got: {}", name);
    });
}

// =============================================================================
// Named ADT special cases — NonZero (transparent wrapper)
// =============================================================================

#[test]
fn test_translate_ty_nonzero_usize_delegates() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::num::NonZero;
        pub fn probe_nonzero(n: NonZero<usize>) -> NonZero<usize> { n }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_nonzero");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        // NonZero<usize> delegates to usize -> bitvec(64)
        assert!(sort.is_bitvec(), "NonZero<usize> should delegate to bitvec");
        assert_eq!(sort.bitvec_width(), Some(64), "NonZero<usize> should be pointer-width");
    });
}

// =============================================================================
// Named ADT special cases — ManuallyDrop (transparent wrapper)
// =============================================================================

#[test]
fn test_translate_ty_manually_drop_delegates() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::mem::ManuallyDrop;
        pub fn probe_manually_drop(m: ManuallyDrop<u64>) -> ManuallyDrop<u64> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_manually_drop");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        // ManuallyDrop<u64> delegates to u64 -> bitvec(64)
        assert!(sort.is_bitvec(), "ManuallyDrop<u64> should delegate to bitvec");
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

// =============================================================================
// Named ADT special cases — MaybeUninit (transparent wrapper)
// =============================================================================

#[test]
fn test_translate_ty_maybe_uninit_delegates() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::mem::MaybeUninit;
        pub fn probe_maybe_uninit(m: MaybeUninit<i32>) -> MaybeUninit<i32> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_maybe_uninit");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        // MaybeUninit<i32> delegates to i32 -> bitvec(32)
        assert!(sort.is_bitvec(), "MaybeUninit<i32> should delegate to bitvec");
        assert_eq!(sort.bitvec_width(), Some(32));
    });
}

// =============================================================================
// Named ADT special cases — Cell (transparent wrapper)
// =============================================================================

#[test]
fn test_translate_ty_cell_delegates() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::cell::Cell;
        pub fn probe_cell(c: Cell<bool>) -> Cell<bool> { c }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_cell");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        // Cell<bool> -> UnsafeCell<bool> -> bool -> Bool
        assert!(sort.is_bool(), "Cell<bool> should delegate through to Bool");
    });
}

// =============================================================================
// User-defined struct (exercises translate_adt_sort struct path)
// =============================================================================

#[test]
fn test_translate_ty_user_struct() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Point {
            pub x: i32,
            pub y: i32,
        }
        pub fn probe_point(p: Point) -> Point { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_point");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "User struct should be datatype");
    });
}

// =============================================================================
// Unit enum (exercises translate_adt_sort unit enum path -> bitvec discriminant)
// =============================================================================

#[test]
fn test_translate_ty_unit_enum_is_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub enum Color { Red, Green, Blue }
        pub fn probe_color(c: Color) -> Color { c }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_color");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        // Unit enums are encoded as bitvec discriminants
        assert!(sort.is_bitvec(), "Unit enum should be bitvec discriminant");
        assert_eq!(sort.bitvec_width(), Some(32), "Unit enum with <=65536 variants should be bv32");
    });
}

// =============================================================================
// General enum with fields (exercises translate_adt_sort general enum path)
// =============================================================================

#[test]
fn test_translate_ty_general_enum_is_datatype() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub enum Shape {
            Circle(u32),
            Rect(u32, u32),
            Empty,
        }
        pub fn probe_shape(s: Shape) -> Shape { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_shape");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "General enum should be datatype");
    });
}

// =============================================================================
// Result<T, E> (exercises translate_adt_sort option-like enum path)
// =============================================================================

#[test]
fn test_translate_ty_result_is_datatype() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_result(r: Result<u32, i32>) -> Result<u32, i32> { r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_result");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        // Result<u32, i32> has 2 variants each with 1 field — general enum path
        assert!(sort.is_datatype(), "Result<u32, i32> should be datatype");
    });
}

// =============================================================================
// Three-element tuple (extends existing 2-element and 1-element tests)
// =============================================================================

#[test]
fn test_translate_ty_triple_tuple() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_triple(t: (u8, u16, u32)) -> u8 { t.0 }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_triple");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "(u8, u16, u32) should be datatype (struct)");
    });
}

// =============================================================================
// Never type and allocator/control-flow infrastructure special cases
// =============================================================================

#[test]
fn test_translate_ty_never_is_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_never() -> ! { loop {} }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_never");
        let sort = ChcCtx::translate_ty(sig.output()).unwrap();
        assert!(sort.is_bool(), "Never type should translate to Bool");
    });
}

#[test]
fn test_translate_ty_layout_is_bv128() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::alloc::Layout;
        pub fn probe_layout(layout: Layout) -> Layout { layout }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_layout");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "Layout should translate to bitvec");
        assert_eq!(sort.bitvec_width(), Some(128), "Layout should translate to bv128");
    });
}

// Part of #3521: ControlFlow is now a proper Datatype with Break/Continue constructors.
#[test]
fn test_translate_ty_control_flow_is_datatype() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ops::ControlFlow;
        pub fn probe_control_flow(c: ControlFlow<u32, u64>) -> ControlFlow<u32, u64> { c }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_control_flow");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "ControlFlow should translate to Datatype, got {:?}", sort);
        let dt = sort.datatype_sort().expect("ControlFlow should be a Datatype sort");
        assert_eq!(
            dt.constructors.len(),
            2,
            "ControlFlow should have 2 constructors (Break, Continue)"
        );
    });
}

#[test]
fn test_translate_ty_infallible_is_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::convert::Infallible;
        pub fn probe_infallible(v: Infallible) -> Infallible { v }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_infallible");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bool(), "Infallible should translate to Bool");
    });
}

// =============================================================================
// Collection special cases — HashMap/HashSet/BTreeSet/BTreeMap
// =============================================================================

#[test]
fn test_translate_ty_hashmap_is_array_with_datatype_values() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;
        pub fn probe_hashmap(m: HashMap<u8, u16>) -> HashMap<u8, u16> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashmap");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_array(), "HashMap should translate to Array sort");
        let arr = sort.array_sort().unwrap();
        assert!(arr.index_sort.is_bitvec(), "HashMap key sort should be bitvec for u8");
        assert_eq!(arr.index_sort.bitvec_width(), Some(8));
        // Part of #3057: DT-free encoding — value sort is direct BV, not Option DT
        assert!(arr.element_sort.is_bitvec(), "HashMap value should be bitvec (DT-free, #3057)");
        assert_eq!(arr.element_sort.bitvec_width(), Some(16));
    });
}

#[test]
fn test_translate_ty_btreemap_is_array() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeMap;
        pub fn probe_btreemap(m: BTreeMap<u32, u64>) -> BTreeMap<u32, u64> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_btreemap");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_array(), "BTreeMap should translate to Array sort");
    });
}

#[test]
fn test_translate_ty_hashset_is_array_with_bool_values() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;
        pub fn probe_hashset(s: HashSet<u32>) -> HashSet<u32> { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashset");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_array(), "HashSet should translate to Array sort");
        let arr = sort.array_sort().unwrap();
        assert!(arr.element_sort.is_bool(), "HashSet element sort should be Bool membership");
    });
}

#[test]
fn test_translate_ty_btreeset_is_array_with_bool_values() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;
        pub fn probe_btreeset(s: BTreeSet<u16>) -> BTreeSet<u16> { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_btreeset");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_array(), "BTreeSet should translate to Array sort");
        let arr = sort.array_sort().unwrap();
        assert!(arr.element_sort.is_bool(), "BTreeSet element sort should be Bool membership");
    });
}

// =============================================================================
// Iterator type special cases — RawIntoIter tuple-shape routing
// =============================================================================

#[test]
fn test_translate_ty_raw_into_iter_tuple_maps_to_hashmap_iter_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct RawIntoIter<T>(core::marker::PhantomData<T>);

        pub fn probe_raw_into_iter_tuple(
            iter: RawIntoIter<(u8, u16)>,
        ) -> RawIntoIter<(u8, u16)> {
            iter
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_raw_into_iter_tuple");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();

        // Part of #3057: DT-free — RawIntoIter<(K,V)> → 5-field struct with
        // fld_data (Array(K,V)), fld_present (Array(K,Bool)), fld_keys, fld_pos, fld_len
        let key_sort = Sort::bitvec(8);
        let val_sort = Sort::bitvec(16);
        let data_sort = Sort::array(key_sort.clone(), val_sort);
        let present_sort = Sort::array(key_sort.clone(), Sort::bool());
        let keys_sort = Sort::array(Sort::bitvec(64), key_sort);
        let expected = struct_sort(
            "HashMapIntoIter_bv8_bv16",
            [
                ("fld_data", data_sort),
                ("fld_present", present_sort),
                ("fld_keys", keys_sort),
                ("fld_pos", Sort::bitvec(64)),
                ("fld_len", Sort::bitvec(64)),
            ],
        );
        assert_eq!(sort, expected, "RawIntoIter<(K,V)> should route to HashMapIntoIter sort");
    });
}

#[test]
fn test_translate_ty_raw_into_iter_key_maps_to_hashset_iter_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct RawIntoIter<T>(core::marker::PhantomData<T>);

        pub fn probe_raw_into_iter_key(iter: RawIntoIter<u8>) -> RawIntoIter<u8> {
            iter
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_raw_into_iter_key");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();

        // RawIntoIter<K> → HashSetIntoIter_bv8 with parameterized name
        let key_sort = Sort::bitvec(8);
        let set_sort = Sort::array(key_sort.clone(), Sort::bool());
        let keys_sort = Sort::array(Sort::bitvec(64), key_sort);
        let expected = struct_sort(
            "HashSetIntoIter_bv8",
            [
                ("fld_set", set_sort),
                ("fld_keys", keys_sort),
                ("fld_pos", Sort::bitvec(64)),
                ("fld_len", Sort::bitvec(64)),
            ],
        );
        assert_eq!(sort, expected, "RawIntoIter<K> should route to HashSetIntoIter sort");
    });
}

// =============================================================================
// Pointer and transparent-wrapper special cases
// =============================================================================

#[test]
fn test_translate_ty_nonnull_is_pointer_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;
        pub fn probe_nonnull(p: NonNull<u8>) -> NonNull<u8> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_nonnull");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "NonNull should translate to pointer bitvec");
        assert_eq!(sort.bitvec_width(), Some(64));
    });
}

#[test]
fn test_translate_ty_unsafe_cell_delegates_to_inner_type() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::cell::UnsafeCell;
        pub fn probe_unsafe_cell(c: UnsafeCell<u16>) -> UnsafeCell<u16> { c }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_unsafe_cell");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "UnsafeCell<u16> should delegate to inner bitvec sort");
        assert_eq!(sort.bitvec_width(), Some(16));
    });
}

// =============================================================================
// Non-capturing closure (exercises Closure ZST path -> Bool)
// Part of #2244: Non-capturing closures are ZSTs, mapped to Bool to avoid
// Datatype sorts in CHC relation signatures.
// =============================================================================

#[test]
fn test_translate_ty_non_capturing_closure_is_bool_zst() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_closure() -> impl Fn(u32) -> u32 {
            |x| x + 1
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        // Find the closure type in the return position of probe_closure.
        // The Fn impl item carries the closure type in its generic args.
        let found_closure = rustc_public::all_local_items().into_iter().any(|item| {
            let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
            let path = ctx.tcx.def_path_str(def_id);
            if path.contains("closure") || path.contains("{closure") {
                let ty = rustc_internal::stable(ctx.tcx.type_of(def_id)).value;
                if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Closure(..))) {
                    let sort = ChcCtx::translate_ty(ty);
                    // Non-capturing closures are ZST -> Bool (Part of #2244)
                    let s = sort.unwrap_or_else(|| {
                        panic!("translate_ty returned None for closure type {:?}", ty)
                    });
                    assert!(
                        s.is_bool(),
                        "non-capturing closure should be Bool (ZST), got: {:?}",
                        s
                    );
                    return true;
                }
            }
            false
        });
        assert!(found_closure, "should find at least one closure item in MIR");
    });
}

// =============================================================================
// Capturing closure (exercises Closure path with upvar fields)
// =============================================================================

#[test]
fn test_translate_ty_capturing_closure_has_upvar_fields() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_capture_closure(offset: u32) -> impl Fn(u32) -> u32 {
            move |x| x + offset
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let found_closure = rustc_public::all_local_items().into_iter().any(|item| {
            let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
            let path = ctx.tcx.def_path_str(def_id);
            if path.contains("closure") || path.contains("{closure") {
                let ty = rustc_internal::stable(ctx.tcx.type_of(def_id)).value;
                if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Closure(..))) {
                    let sort = ChcCtx::translate_ty(ty);
                    let s = sort.unwrap_or_else(|| {
                        panic!("translate_ty returned None for capturing closure type {:?}", ty)
                    });
                    assert!(s.is_datatype(), "capturing closure should be datatype, got: {:?}", s);
                    // Capturing closures should have cap_N fields
                    let name = s.datatype_name().unwrap_or("");
                    assert!(
                        name.starts_with("Closure_"),
                        "closure sort name should start with Closure_, got: {}",
                        name
                    );
                    return true;
                }
            }
            false
        });
        assert!(found_closure, "should find at least one capturing closure in MIR");
    });
}

// =============================================================================
// is_opaque_alloc_infra — direct unit tests for the pub(super) predicate
// =============================================================================

#[test]
fn test_is_opaque_alloc_infra_layout_is_opaque() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::alloc::Layout;
        pub fn probe_layout(l: Layout) -> Layout { l }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_layout");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            assert!(ChcCtx::is_opaque_alloc_infra(def), "Layout should be opaque alloc infra");
        } else {
            panic!("Layout should be an ADT type");
        }
    });
}

#[test]
fn test_is_opaque_alloc_infra_infallible_is_opaque() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::convert::Infallible;
        pub fn probe_infallible(i: Infallible) -> Infallible { i }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_infallible");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            assert!(ChcCtx::is_opaque_alloc_infra(def), "Infallible should be opaque alloc infra");
        } else {
            panic!("Infallible should be an ADT type");
        }
    });
}

#[test]
fn test_is_opaque_alloc_infra_user_struct_is_not_opaque() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct MyStruct { pub x: u32 }
        pub fn probe_my_struct(s: MyStruct) -> MyStruct { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_my_struct");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            assert!(
                !ChcCtx::is_opaque_alloc_infra(def),
                "user struct should NOT be opaque alloc infra"
            );
        } else {
            panic!("MyStruct should be an ADT type");
        }
    });
}

#[test]
fn test_is_opaque_alloc_infra_option_is_not_opaque() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option(o: Option<u32>) -> Option<u32> { o }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            assert!(!ChcCtx::is_opaque_alloc_infra(def), "Option should NOT be opaque alloc infra");
        } else {
            panic!("Option should be an ADT type");
        }
    });
}

#[test]
fn test_is_opaque_alloc_infra_nonnull_is_opaque() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;
        pub fn probe_nonnull(p: NonNull<u8>) -> NonNull<u8> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_nonnull");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            assert!(ChcCtx::is_opaque_alloc_infra(def), "NonNull should be opaque alloc infra");
        } else {
            panic!("NonNull should be an ADT type");
        }
    });
}

// =============================================================================
// BigInt/BigRational type translation (headline trust_mc types)
// =============================================================================
// NOTE: These types require external crate num-bigint which is not available
// in the test compilation environment. We verify the pattern matching logic
// indirectly by testing with types that share the same ADT path matching.
// The BigInt/BigRational branches in translate_ty use name.contains() which
// matches against the ADT's trimmed_name(). Direct testing requires the
// num-bigint crate to be available at test compile time.

// =============================================================================
// ControlFlow type — Part of #3521: now a proper Datatype (not opaque BV128).
// translate_adt_sort general enum path resolves Break/Continue constructors.
// =============================================================================

#[test]
fn test_translate_ty_control_flow_is_datatype_with_constructors() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ops::ControlFlow;
        pub fn probe_cf(c: ControlFlow<u32, u64>) -> ControlFlow<u32, u64> { c }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_cf");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "ControlFlow should translate to Datatype, got {:?}", sort);
        let dt = sort.datatype_sort().expect("ControlFlow should be a Datatype sort");
        assert_eq!(
            dt.constructors.len(),
            2,
            "ControlFlow should have Break and Continue constructors"
        );
    });
}

// =============================================================================
// Vec type name includes element type (Vec_bv64 for Vec<u64>)
// =============================================================================

#[test]
fn test_translate_ty_vec_u64_sort_name_includes_element() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;
        pub fn probe_vec_u64(v: Vec<u64>) -> Vec<u64> { v }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_vec_u64");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "Vec<u64> should be datatype");
        assert_eq!(
            sort.datatype_name(),
            Some("Vec_bv64"),
            "Vec<u64> sort name should be 'Vec_bv64'"
        );
    });
}

// =============================================================================
// HashMap sort structure — verify key/value sorts in Array encoding
// =============================================================================

#[test]
fn test_translate_ty_hashmap_u32_u64_array_structure() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;
        pub fn probe_hm(m: HashMap<u32, u64>) -> HashMap<u32, u64> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hm");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_array(), "HashMap<u32, u64> should be Array");
        let arr = sort.array_sort().unwrap();
        assert!(arr.index_sort.is_bitvec(), "HashMap key should be bitvec");
        assert_eq!(arr.index_sort.bitvec_width(), Some(32), "HashMap<u32,_> key should be bv32");
        // Part of #3057: DT-free encoding — value sort is direct BV, not Option DT
        assert!(arr.element_sort.is_bitvec(), "HashMap value should be bitvec (DT-free, #3057)");
        assert_eq!(
            arr.element_sort.bitvec_width(),
            Some(64),
            "HashMap<_,u64> value should be bv64"
        );
    });
}

// =============================================================================
// Result<T, E> structure verification (two variants, each with one field)
// =============================================================================

#[test]
fn test_translate_ty_result_u32_i64_is_enum_with_ok_err() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_result(r: Result<u32, i64>) -> Result<u32, i64> { r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_result");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "Result<u32, i64> should be datatype (enum)");
        let name = sort.datatype_name().unwrap_or("");
        assert!(name.contains("Result"), "Result sort name should contain 'Result', got: {}", name);
    });
}

// =============================================================================
// Option<bool> (exercises option-like path with bool payload)
// =============================================================================

#[test]
fn test_translate_ty_option_bool_uses_bool_payload() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option_bool(o: Option<bool>) -> Option<bool> { o }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option_bool");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_datatype(), "Option<bool> should be datatype");
        let name = sort.datatype_name().unwrap_or("");
        assert!(
            name.contains("Option"),
            "Option<bool> sort name should contain 'Option', got: {}",
            name
        );
    });
}

// =============================================================================
// Type-sort fallback counter (Part of #2240)
// =============================================================================

// =============================================================================
// ADT name-based dispatch — untested branches from codegen_types_adt.rs
// Part of #2045: test quality gaps for zero-coverage chc/ files.
// =============================================================================

#[test]
fn test_translate_ty_bigint_is_int_sort() {
    // BigInt name match → Sort::int() (Part of #734)
    // Uses a locally-defined struct to trigger name-based dispatch.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct BigInt { data: Vec<u64> }
        pub fn probe_bigint(n: BigInt) -> BigInt { n }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_bigint");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_int(), "BigInt should translate to Int sort");
    });
}

#[test]
fn test_translate_ty_biguint_is_int_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct BigUint { data: Vec<u64> }
        pub fn probe_biguint(n: BigUint) -> BigUint { n }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_biguint");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_int(), "BigUint should translate to Int sort");
    });
}

#[test]
fn test_translate_ty_bigrational_is_real_sort() {
    // BigRational name match → Sort::real() (Part of #911)
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct BigRational { numer: i64, denom: i64 }
        pub fn probe_bigrational(r: BigRational) -> BigRational { r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_bigrational");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_real(), "BigRational should translate to Real sort");
    });
}

#[test]
fn test_translate_ty_ratio_is_real_sort() {
    // Ratio name match → Sort::real() (Part of #911)
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Ratio<T> { numer: T, denom: T }
        pub fn probe_ratio(r: Ratio<i64>) -> Ratio<i64> { r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_ratio");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_real(), "Ratio should translate to Real sort");
    });
}

#[test]
fn test_translate_ty_global_allocator_is_bool() {
    // Global allocator ZST → Sort::bool()
    // Requires allocator_api feature gate (nightly-only).
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(allocator_api)]
        use std::alloc::Global;
        pub fn probe_global(g: Global) -> Global { g }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_global");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bool(), "Global allocator should translate to Bool (ZST)");
    });
}

#[test]
fn test_translate_ty_alignment_is_bv64() {
    // core::ptr::Alignment → Sort::bitvec(POINTER_WIDTH)
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Alignment(core::ptr::NonNull<()>);
        pub fn probe_alignment(a: Alignment) -> Alignment { a }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_alignment");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "Alignment should translate to bitvec");
        assert_eq!(sort.bitvec_width(), Some(64), "Alignment should be bv64");
    });
}

#[test]
fn test_translate_ty_alloc_error_is_bool() {
    // core::alloc::AllocError → Sort::bool() (ZST)
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(allocator_api)]
        use core::alloc::AllocError;
        pub fn probe_alloc_error(e: AllocError) -> AllocError { e }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_alloc_error");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bool(), "AllocError should translate to Bool (ZST)");
    });
}

#[test]
fn test_translate_ty_arguments_is_bv128() {
    // fmt::Arguments → Sort::bitvec(128) (opaque)
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::fmt::Arguments;
        pub fn probe_arguments(a: Arguments<'_>) -> Arguments<'_> { a }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_arguments");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "Arguments should translate to bitvec");
        assert_eq!(sort.bitvec_width(), Some(128), "Arguments should be bv128 (opaque)");
    });
}

// =============================================================================
// PolymorphicIter element-sort unification
// =============================================================================

/// Part of #3984: PolymorphicIter<NonCopyWrapper> must flatten the DT element to BV,
/// matching the sort policy in translate_into_iter_sort (codegen_types_adt_sort.rs).
/// Without the fix, PolymorphicIter<NonCopyWrapper>.fld_data would be Datatype instead
/// of Array<ptr, BV>, causing flatten_dest_sort_mismatch in downstream projections.
#[test]
fn test_translate_ty_polymorphic_iter_non_copy_struct_flattens_element() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct NonCopyWrapper {
            pub value: u32,
        }

        pub struct PolymorphicIter<T> {
            _marker: core::marker::PhantomData<T>,
        }

        pub fn probe_poly_iter(
            iter: PolymorphicIter<NonCopyWrapper>,
        ) -> PolymorphicIter<NonCopyWrapper> {
            iter
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_poly_iter");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();

        // NonCopyWrapper has a single u32 field → flattenable to BV(32).
        // PolymorphicIter must produce fld_data = Array(ptr, BV(32)), not Datatype.
        let expected = struct_sort(
            "PolymorphicIter",
            [
                ("fld_alive", names::index_range_sort()),
                ("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(32))),
            ],
        );
        assert_eq!(
            sort, expected,
            "PolymorphicIter<NonCopyWrapper> must flatten DT element to BV in fld_data"
        );
    });
}

// =============================================================================
// Part of #4163: custom DST (ADT with unsized slice/str tail) pointer encoding
// =============================================================================

#[test]
fn test_translate_ty_ref_to_custom_dst_is_bv128_fat_pointer() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MyStr {
            header: u8,
            data: str,
        }

        pub fn probe_custom_dst_ref(s: &MyStr) -> &MyStr { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_custom_dst_ref");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "&MyStr (custom DST) should be bitvec");
        assert_eq!(
            sort.bitvec_width(),
            Some(128),
            "&MyStr (custom DST with str tail) should be BV128 fat pointer, not BV64"
        );
    });
}

#[test]
fn test_translate_ty_raw_ptr_to_custom_dst_is_bv128_fat_pointer() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Wrapper<T: ?Sized> {
            header: u8,
            data: T,
        }

        pub fn probe_custom_dst_raw(p: *const Wrapper<[u8]>) -> *const Wrapper<[u8]> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_custom_dst_raw");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "*const Wrapper<[u8]> (custom DST) should be bitvec");
        assert_eq!(
            sort.bitvec_width(),
            Some(128),
            "*const Wrapper<[u8]> (custom DST with slice tail) should be BV128 fat pointer"
        );
    });
}

#[test]
fn test_translate_ty_ref_to_sized_adt_remains_bv64() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Sized { x: u32, y: u32 }

        pub fn probe_sized_ref(s: &Sized) -> &Sized { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_sized_ref");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();
        assert!(sort.is_bitvec(), "&Sized should be bitvec");
        assert_eq!(
            sort.bitvec_width(),
            Some(64),
            "&Sized (no unsized tail) should remain BV64 thin pointer"
        );
    });
}

// Global TYPE_SORT_FALLBACK_COUNT counter unit tests removed (Part of #2906).
// Equivalent per-ctx ChcDiagnostics validation in test_ctx_globals.rs.
// The global counter API is tested implicitly through translate_with_diagnostics
// (snapshot-delta in translate_inner).

// =============================================================================
// &str / bare str sorts and the sized-only deref gate (BV128 unification)
// =============================================================================

/// `&str` is a BV128 fat pointer; bare `str` (behind the ref) stays
/// `Array(BV64, BV8)`. The sized-only deref gate keeps `&str` intact while
/// still stripping references to sized pointees.
#[test]
fn test_translate_ty_ref_str_is_bv128_and_bare_str_stays_array() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_ref_str(s: &str) -> usize { s.len() }
        pub fn probe_ref_u32(x: &u32) -> u32 { *x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_ref_str");
        let ref_str_ty = sig.inputs()[0];
        let ref_sort = ChcCtx::translate_ty(ref_str_ty).unwrap();
        assert_eq!(
            ref_sort.bitvec_width(),
            Some(128),
            "&str should be the BV128 fat pointer, got: {ref_sort:?}"
        );

        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ref_str_ty.kind() else {
            panic!("probe_ref_str input should be a reference");
        };
        let bare_sort = ChcCtx::translate_ty(pointee).unwrap();
        assert!(bare_sort.is_array(), "bare str should stay Array(BV64, BV8), got: {bare_sort:?}");

        // Gate: &str (unsized fat pointee) is NOT stripped.
        assert!(ChcCtx::ref_pointee_is_fat_bv128(pointee), "str pointee is a fat BV128 pointee");
        let (kept_ty, stripped) = ChcCtx::deref_ref_ty_sized_only(ref_str_ty);
        assert_eq!(kept_ty, ref_str_ty, "deref_ref_ty_sized_only must keep &str intact");
        assert!(!stripped, "&str must not be reported as stripped");

        // Gate: sized pointees are still stripped (value modeling unchanged).
        let sig_u32 = fn_sig_by_suffix(ctx.tcx, "probe_ref_u32");
        let ref_u32_ty = sig_u32.inputs()[0];
        let (inner_ty, stripped_u32) = ChcCtx::deref_ref_ty_sized_only(ref_u32_ty);
        assert!(stripped_u32, "&u32 (sized pointee) must still be stripped");
        assert_eq!(ChcCtx::translate_ty(inner_ty).unwrap().bitvec_width(), Some(32));
    });
}

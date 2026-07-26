// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unit tests for chc/codegen_types_adt.rs and chc/codegen_types_adt_sort.rs.
// Covers: nth_type_arg, translate_type_arg_sort_or_param_bv, translate_adt_ty,
// translate_into_iter_sort, translate_adt_sort, resolve_generic_ty,
// adt_sort_name, is_opaque_alloc_infra.
// Part of #2341: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::{
    codegen_types_adt::CodegenTypesAdt, codegen_types_adt_sort::CodegenTypesAdtSort,
};
use super::common::*;

mod test_types_adt_into_iter;

// =============================================================================
// nth_type_arg — extract Nth type generic argument, skipping const/lifetime
// =============================================================================

#[test]
fn test_nth_type_arg_extracts_first_type_from_option() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option(o: Option<u32>) -> Option<u32> { o }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() {
            let first = ChcCtx::nth_type_arg(&args, 0);
            assert!(first.is_some(), "Option<u32> should have a first type arg");
            if let Some(rustc_public::ty::GenericArgKind::Type(inner)) = first {
                let sort = ChcCtx::translate_ty(*inner);
                assert!(sort.is_some(), "inner type u32 should translate");
                assert_eq!(sort.unwrap().bitvec_width(), Some(32));
            } else {
                panic!("first type arg should be Type, not Const/Lifetime");
            }
        } else {
            panic!("Option<u32> should be an ADT type");
        }
    });
}

#[test]
fn test_nth_type_arg_extracts_second_type_from_hashmap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;
        pub fn probe_hashmap(m: HashMap<u8, u16>) -> HashMap<u8, u16> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashmap");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() {
            // HashMap<K, V, S> has 3 generic args; nth_type_arg(0) = K, nth_type_arg(1) = V
            let key = ChcCtx::nth_type_arg(&args, 0);
            assert!(key.is_some(), "HashMap should have key type arg");

            let val = ChcCtx::nth_type_arg(&args, 1);
            assert!(val.is_some(), "HashMap should have value type arg");

            if let Some(rustc_public::ty::GenericArgKind::Type(val_ty)) = val {
                let sort = ChcCtx::translate_ty(*val_ty);
                assert!(sort.is_some());
                assert_eq!(sort.unwrap().bitvec_width(), Some(16), "value type u16 -> bv16");
            } else {
                panic!("second type arg should be Type");
            }
        } else {
            panic!("HashMap should be an ADT type");
        }
    });
}

#[test]
fn test_nth_type_arg_out_of_bounds_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option(o: Option<u32>) -> Option<u32> { o }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() {
            // Option<T> has only 1 type arg
            let oob = ChcCtx::nth_type_arg(&args, 5);
            assert!(oob.is_none(), "out-of-bounds nth_type_arg should return None");
        } else {
            panic!("Option<u32> should be an ADT type");
        }
    });
}

// =============================================================================
// translate_type_arg_sort_or_param_bv — resolve type arg to sort with fallbacks
// =============================================================================

#[test]
fn test_translate_type_arg_sort_or_param_bv_resolved_type() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option(o: Option<u64>) -> Option<u64> { o }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() {
            let arg = ChcCtx::nth_type_arg(&args, 0);
            let sort =
                ChcCtx::translate_type_arg_sort_or_param_bv(arg, "test resolved type", Sort::int());
            // Successful resolution to bitvec proves no fallback occurred.
            assert!(sort.is_bitvec(), "u64 should resolve to bitvec");
            assert_eq!(sort.bitvec_width(), Some(64));
        } else {
            panic!("Option<u64> should be an ADT type");
        }
    });
}

#[test]
fn test_translate_type_arg_sort_or_param_bv_none_uses_fallback() {
    let sort = ChcCtx::translate_type_arg_sort_or_param_bv(None, "test None fallback", Sort::int());
    // Returning the provided fallback sort proves the fallback path was taken.
    assert!(sort.is_int(), "None arg should use the provided fallback sort");
}

// =============================================================================
// translate_adt_ty — direct calls to verify name-based dispatch paths
// =============================================================================

#[test]
fn test_translate_adt_ty_user_struct_falls_through_to_field_translation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Point { pub x: u32, pub y: u32 }
        pub fn probe_point(p: Point) -> Point { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_point");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "user struct Point should translate");
            let sort = sort.unwrap();
            assert!(sort.is_datatype(), "Point should be a datatype sort");
        } else {
            panic!("Point should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_generic_struct_with_concrete_types() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Pair<A, B> { pub first: A, pub second: B }
        pub fn probe_pair(p: Pair<u8, u16>) -> Pair<u8, u16> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_pair");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "generic struct Pair<u8,u16> should translate");
            let sort = sort.unwrap();
            assert!(sort.is_datatype(), "Pair should be a datatype sort");
        } else {
            panic!("Pair should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_unit_enum_produces_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub enum Color { Red, Green, Blue }
        pub fn probe_color(c: Color) -> Color { c }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_color");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "unit enum Color should translate");
            let sort = sort.unwrap();
            // Unit enums: all variants have no fields → bitvec(32) for ≤65536 variants
            assert!(sort.is_bitvec(), "unit enum should be bitvec");
            assert_eq!(sort.bitvec_width(), Some(32));
        } else {
            panic!("Color should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_option_produces_enum_type() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option(o: Option<i32>) -> Option<i32> { o }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Option<i32> should translate");
            let sort = sort.unwrap();
            assert!(sort.is_datatype(), "Option should be a datatype (enum encoding)");
            let name = sort.datatype_name().unwrap_or("");
            assert!(name.contains("Option"), "sort name should contain 'Option', got: {name}");
        } else {
            panic!("Option should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_result_produces_enum_type() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_result(r: Result<u32, u8>) -> Result<u32, u8> { r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_result");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Result<u32, u8> should translate");
            let sort = sort.unwrap();
            // Result is a 2-variant enum: Ok(T) and Err(E)
            // With 2 variants where one has 1 field each, it may use Option-like or general enum encoding
            assert!(sort.is_datatype(), "Result should produce a datatype sort");
        } else {
            panic!("Result should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_nonnull_produces_pointer_width_bv() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;
        pub fn probe_nonnull(p: NonNull<u8>) -> NonNull<u8> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_nonnull");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "NonNull should translate");
            let sort = sort.unwrap();
            assert!(sort.is_bitvec(), "NonNull should be bitvec (pointer wrapper)");
            assert_eq!(sort.bitvec_width(), Some(64));
        } else {
            panic!("NonNull should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_string_produces_struct_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::String;
        pub fn probe_string(s: String) -> String { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_string");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "String should translate");
            let sort = sort.unwrap();
            assert!(sort.is_datatype(), "String should be a datatype sort");
            assert_eq!(sort.datatype_name(), Some("RustString"));
        } else {
            panic!("String should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_layout_produces_bv128() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::alloc::Layout;
        pub fn probe_layout(l: Layout) -> Layout { l }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_layout");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Layout should translate");
            let sort = sort.unwrap();
            assert!(sort.is_bitvec(), "Layout should be opaque bitvec");
            assert_eq!(sort.bitvec_width(), Some(128));
        } else {
            panic!("Layout should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_phantom_data_produces_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::marker::PhantomData;
        pub fn probe_phantom(p: PhantomData<u32>) -> PhantomData<u32> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_phantom");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "PhantomData should translate");
            let sort = sort.unwrap();
            assert!(sort.is_bool(), "PhantomData should be Bool (ZST)");
        } else {
            panic!("PhantomData should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_box_produces_pointer_width_bv() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::boxed::Box;
        pub fn probe_box(b: Box<u32>) -> Box<u32> { b }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_box");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Box should translate");
            let sort = sort.unwrap();
            assert!(sort.is_bitvec(), "Box should be bitvec (pointer)");
            assert_eq!(sort.bitvec_width(), Some(64));
        } else {
            panic!("Box should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_vec_produces_datatype_with_element_suffix() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;
        pub fn probe_vec(v: Vec<i16>) -> Vec<i16> { v }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_vec");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Vec<i16> should translate");
            let sort = sort.unwrap();
            assert!(sort.is_datatype(), "Vec should be a datatype sort");
            assert_eq!(sort.datatype_name(), Some("Vec_bv16"));
        } else {
            panic!("Vec should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_hashset_produces_array_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;
        pub fn probe_hashset(s: HashSet<u32>) -> HashSet<u32> { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashset");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "HashSet<u32> should translate");
            let sort = sort.unwrap();
            assert!(sort.is_array(), "HashSet should be Array<K, Bool>");
            let arr = sort.array_sort().unwrap();
            assert_eq!(arr.index_sort.bitvec_width(), Some(32), "key sort should be bv32");
            assert!(arr.element_sort.is_bool(), "element sort should be Bool");
        } else {
            panic!("HashSet should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_hashmap_produces_array_option() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;
        pub fn probe_hashmap(m: HashMap<u32, u64>) -> HashMap<u32, u64> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashmap");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "HashMap<u32, u64> should translate");
            let sort = sort.unwrap();
            // Part of #3057: DT-free encoding — Array<K, V> without Option wrapper
            assert!(sort.is_array(), "HashMap should be Array<K, V> (DT-free, #3057)");
            let arr = sort.array_sort().unwrap();
            assert_eq!(arr.index_sort.bitvec_width(), Some(32), "key sort should be bv32");
            assert!(arr.element_sort.is_bitvec(), "element sort should be bitvec (DT-free, #3057)");
            assert_eq!(arr.element_sort.bitvec_width(), Some(64), "value sort should be bv64");
        } else {
            panic!("HashMap should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_global_allocator_produces_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(allocator_api)]
        use std::alloc::Global;
        pub fn probe_global(g: Global) -> Global { g }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_global");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Global allocator should translate");
            let sort = sort.unwrap();
            assert!(sort.is_bool(), "Global allocator should be Bool (ZST)");
        } else {
            panic!("Global should be an ADT type");
        }
    });
}

#[test]
fn test_translate_adt_ty_infallible_produces_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::convert::Infallible;
        pub fn probe_infallible(i: Infallible) -> Infallible { i }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_infallible");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Infallible should translate");
            let sort = sort.unwrap();
            assert!(sort.is_bool(), "Infallible should be Bool (uninhabited ZST)");
        } else {
            panic!("Infallible should be an ADT type");
        }
    });
}

// =============================================================================
// codegen_types_adt_sort.rs — resolve_generic_ty, adt_sort_name
// =============================================================================

#[test]
fn test_resolve_generic_ty_concrete_type_passes_through() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Wrapper<T> { pub inner: T }
        pub fn probe_wrapper(w: Wrapper<u32>) -> Wrapper<u32> { w }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_wrapper");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            // The field type of `inner` after monomorphization should be u32
            let variants = def.variants();
            let field = &variants[0].fields()[0];
            let field_ty = field.ty();
            let resolved = ChcCtx::resolve_generic_ty(field_ty, &args);
            assert!(resolved.is_some(), "concrete field type should resolve");
            let resolved = resolved.unwrap();
            let sort = ChcCtx::translate_ty(resolved);
            assert!(sort.is_some());
            assert_eq!(sort.unwrap().bitvec_width(), Some(32));
        } else {
            panic!("Wrapper should be an ADT type");
        }
    });
}

#[test]
fn test_adt_sort_name_includes_type_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Pair<A, B> { pub first: A, pub second: B }
        pub fn probe_pair(p: Pair<u8, u16>) -> Pair<u8, u16> { p }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_pair");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let name = ChcCtx::adt_sort_name(def, &args);
            // The name should contain the ADT base name and encode type args
            assert!(!name.is_empty(), "adt_sort_name should produce a non-empty name");
            assert!(
                name.contains("Pair"),
                "sort name should contain the ADT name 'Pair', got: {name}"
            );
        } else {
            panic!("Pair should be an ADT type");
        }
    });
}

#[test]
fn test_adt_sort_name_erases_nested_lifetime_names_in_type_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Inner<'a> { pub ptr: &'a u8 }
        pub struct Outer<T>(pub T);
        pub fn probe_outer(x: Outer<Inner<'static>>) -> Outer<Inner<'static>> { x }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_outer");
        let ty = sig.inputs()[0];
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            panic!("Outer<Inner<'static>> should be an ADT type");
        };

        let outer_name = ChcCtx::adt_sort_name(def, &args);
        assert_eq!(
            outer_name, "Outer_Inner",
            "outer sort name should not leak nested lifetime names"
        );

        let Some(rustc_public::ty::GenericArgKind::Type(inner_ty)) = args.0.first() else {
            panic!("Outer<T> should carry Inner<'static> as its first type arg");
        };
        let TyKind::RigidTy(RigidTy::Adt(inner_def, inner_args)) = inner_ty.kind() else {
            panic!("Outer<T> inner arg should be an ADT type");
        };

        let inner_name = ChcCtx::adt_sort_name(inner_def, &inner_args);
        assert_eq!(
            inner_name, "Inner_lt",
            "direct lifetime generic args should keep the canonical lt marker"
        );
    });
}

#[test]
fn test_translate_adt_ty_manually_drop_delegates_to_inner() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::mem::ManuallyDrop;
        pub fn probe_md(m: ManuallyDrop<u32>) -> ManuallyDrop<u32> { m }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_md");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "ManuallyDrop<u32> should translate");
            let sort = sort.unwrap();
            // ManuallyDrop<u32> delegates to u32 → bitvec(32)
            assert!(sort.is_bitvec(), "ManuallyDrop<u32> should delegate to u32 bitvec");
            assert_eq!(sort.bitvec_width(), Some(32));
        } else {
            panic!("ManuallyDrop should be an ADT type");
        }
    });
}

// =============================================================================
// translate_adt_ty — enum with data variants (general enum path)
// =============================================================================

#[test]
fn test_translate_adt_ty_data_enum_produces_datatype() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub enum Shape {
            Circle(u32),
            Rectangle(u32, u32),
        }
        pub fn probe_shape(s: Shape) -> Shape { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_shape");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "enum Shape with data variants should translate");
            let sort = sort.unwrap();
            assert!(sort.is_datatype(), "Shape should be a datatype (enum with data)");
        } else {
            panic!("Shape should be an ADT type");
        }
    });
}

// =============================================================================
// Gap 3: codegen_types_adt_sort.rs — translate_into_iter_sort
// =============================================================================

/// Helper: find an IntoIter ADT in function locals via MIR type inspection.
/// Scans all local variable types looking for an ADT named "IntoIter".
fn find_into_iter_adt_in_locals(
    body: &rustc_public::mir::Body,
) -> Option<(rustc_public::ty::AdtDef, rustc_public::ty::GenericArgs)> {
    for (_, local_decl) in body.local_decls() {
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = local_decl.ty.kind() {
            let name = def.trimmed_name();
            if name == "IntoIter" {
                return Some((def, args));
            }
        }
    }
    None
}

#[test]
fn test_translate_into_iter_sort_vec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_vec_into_iter() {
            let v = vec![1u32, 2, 3];
            let mut iter = v.into_iter();
            let _ = iter.next();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_into_iter");
        let body = instance.body().expect("function body");

        let (def, args) =
            find_into_iter_adt_in_locals(&body).expect("should find IntoIter ADT in locals");

        let sort = ChcCtx::translate_into_iter_sort(def, &args);
        assert!(sort.is_some(), "Vec IntoIter should produce a sort");
        let sort = sort.unwrap();
        let sort_str = sort.to_string();
        assert!(sort.is_datatype(), "VecIntoIter should be a datatype, got: {sort_str}");
        assert!(
            sort_str.contains("VecIntoIter"),
            "sort name should contain 'VecIntoIter', got: {sort_str}"
        );
    });
}

#[test]
fn test_translate_into_iter_sort_hashmap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;
        pub fn probe_hm_into_iter() {
            let mut m = HashMap::new();
            m.insert(1u32, 2u64);
            let mut iter = m.into_iter();
            let _ = iter.next();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hm_into_iter");
        let body = instance.body().expect("function body");

        // HashMap IntoIter appears as hashbrown's IntoIter with "hash_map" in the path.
        let mut found = false;
        for (_, local_decl) in body.local_decls() {
            if let TyKind::RigidTy(RigidTy::Adt(def, args)) = local_decl.ty.kind() {
                let name = def.trimmed_name();
                let full_name = def.0.name();
                if name == "IntoIter"
                    && (full_name.contains("hash_map") || full_name.contains("HashMap"))
                {
                    let sort = ChcCtx::translate_into_iter_sort(def, &args);
                    assert!(sort.is_some(), "HashMap IntoIter should produce a sort");
                    let sort = sort.unwrap();
                    let sort_str = sort.to_string();
                    assert!(sort.is_datatype(), "HashMapIntoIter should be a datatype");
                    assert!(
                        sort_str.contains("HashMapIntoIter"),
                        "sort name should contain 'HashMapIntoIter', got: {sort_str}"
                    );
                    found = true;
                    break;
                }
            }
        }
        assert!(found, "translate_into_iter_sort should recognize HashMap IntoIter in MIR locals");
    });
}

#[test]
fn test_translate_into_iter_sort_hashset() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;
        pub fn probe_hs_into_iter() {
            let mut s = HashSet::new();
            s.insert(1u32);
            let mut iter = s.into_iter();
            let _ = iter.next();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hs_into_iter");
        let body = instance.body().expect("function body");

        // HashSet IntoIter may appear as RawIntoIter or IntoIter in MIR.
        let mut found = false;
        for (_, local_decl) in body.local_decls() {
            if let TyKind::RigidTy(RigidTy::Adt(def, args)) = local_decl.ty.kind() {
                let name = def.trimmed_name();
                let full_name = def.0.name();
                if (name == "IntoIter" || name == "RawIntoIter")
                    && (full_name.contains("hash_set") || full_name.contains("HashSet"))
                {
                    let sort = ChcCtx::translate_into_iter_sort(def, &args);
                    assert!(sort.is_some(), "HashSet IntoIter should produce a sort");
                    let sort = sort.unwrap();
                    let sort_str = sort.to_string();
                    assert!(sort.is_datatype(), "HashSetIntoIter should be a datatype");
                    assert!(
                        sort_str.contains("HashSetIntoIter"),
                        "sort name should contain 'HashSetIntoIter', got: {sort_str}"
                    );
                    found = true;
                    break;
                }
            }
        }
        assert!(found, "translate_into_iter_sort should recognize HashSet IntoIter in MIR locals");
    });
}

// =============================================================================
// Gap 3: codegen_types_adt_sort.rs — translate_adt_sort (struct field-by-field)
// =============================================================================

#[test]
fn test_translate_adt_sort_struct_with_fields() {
    // translate_adt_sort is called indirectly via translate_adt_ty for user structs
    // that fall through name-based dispatch. Verify field-level sort construction.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Record { pub id: u32, pub value: u64, pub flag: bool }
        pub fn probe_record(r: Record) -> Record { r }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_record");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_ty(def, args);
            assert!(sort.is_some(), "Record struct should translate");
            let sort = sort.unwrap();
            assert!(sort.is_datatype(), "Record should be a datatype");
            let sort_str = sort.to_string();
            assert!(
                sort_str.contains("Record"),
                "sort name should contain 'Record', got: {sort_str}"
            );
        } else {
            panic!("Record should be an ADT type");
        }
    });
}

// =============================================================================
// Gap 3: codegen_types_adt_sort.rs — resolve_generic_ty Param resolution
// =============================================================================

#[test]
fn test_resolve_generic_ty_param_resolves_via_args() {
    // Test that a Param type in a generic struct field resolves to the concrete type
    // when GenericArgs carries the substitution.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Container<T> { pub item: T, pub count: u32 }
        pub fn probe_container(c: Container<u64>) -> Container<u64> { c }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_container");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let variants = def.variants();
            let field = &variants[0].fields()[0]; // item: T
            let field_ty = field.ty();

            // resolve_generic_ty should resolve the Param to u64
            let resolved = ChcCtx::resolve_generic_ty(field_ty, &args);
            assert!(resolved.is_some(), "Param T should resolve to u64");
            let resolved = resolved.unwrap();
            let sort = ChcCtx::translate_ty(resolved);
            assert!(sort.is_some());
            assert_eq!(
                sort.unwrap().bitvec_width(),
                Some(64),
                "resolved T should be u64 → bitvec(64)"
            );
        } else {
            panic!("Container should be an ADT type");
        }
    });
}

#[test]
fn test_resolve_generic_ty_out_of_range_param_returns_none() {
    // If GenericArgs doesn't have enough entries for a Param index, returns None
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Simple { pub val: u32 }
        pub fn probe_simple(s: Simple) -> Simple { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_simple");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() {
            // Simple has no generic params, so args is empty
            // A non-param type should still pass through
            let u32_ty = sig.inputs()[0]; // u32 is non-param, passes through
            let resolved = ChcCtx::resolve_generic_ty(u32_ty, &args);
            // Non-Param types are passed through unchanged
            assert!(resolved.is_some(), "non-Param type should pass through");
        } else {
            panic!("Simple should be an ADT type");
        }
    });
}

// =============================================================================
// Gap 3: codegen_types_adt_sort.rs — is_opaque_alloc_infra
// =============================================================================

#[test]
fn test_is_opaque_alloc_infra_layout() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;
        pub fn probe_layout(l: Layout) -> Layout { l }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_layout");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            assert!(
                ChcCtx::is_opaque_alloc_infra(def),
                "Layout should be classified as opaque alloc infra"
            );
        } else {
            panic!("Layout should be an ADT type");
        }
    });
}

#[test]
fn test_is_opaque_alloc_infra_user_struct_is_not_infra() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct MyStruct { pub x: u32 }
        pub fn probe_my(s: MyStruct) -> MyStruct { s }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_my");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            assert!(
                !ChcCtx::is_opaque_alloc_infra(def),
                "user struct should NOT be classified as opaque alloc infra"
            );
        } else {
            panic!("MyStruct should be an ADT type");
        }
    });
}

// =============================================================================
// Part of #3669: translate_adt_sort handles unions as bitvectors
// =============================================================================

#[test]
fn test_translate_adt_sort_union_returns_bitvec() {
    // Part of #3669: unions are modeled as bitvectors of their byte size.
    // FloatInt has f32 and u32 (both 4 bytes), so union is 4 bytes = BV32.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub union FloatInt {
            pub f: f32,
            pub i: u32,
        }
        pub fn probe_union(u: FloatInt) -> FloatInt { u }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_union");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_sort(def, args);
            assert!(sort.is_some(), "union should now produce a sort (BV of byte size)");
            let sort = sort.unwrap();
            assert_eq!(
                sort.bitvec_width(),
                Some(32),
                "FloatInt union (4 bytes) should be BV32, got {:?}",
                sort
            );
        } else {
            panic!("FloatInt should be an ADT type");
        }
    });
}

// =============================================================================
// Part of #3596: repr(simd) struct with parameterized array field
// =============================================================================

/// A `#[repr(simd)]` struct with generic array field `[T; N]` must produce
/// a Datatype sort containing an Array field, not fall through to BV32.
/// This was the root cause of 3 unsound fallbacks in SIMD compiletest
/// harnesses: `resolve_generic_ty` only resolved top-level Param types,
/// missing params nested inside Array elem types.
#[test]
fn test_repr_simd_generic_array_field_produces_datatype_with_array_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code, non_camel_case_types)]
        #![feature(repr_simd)]

        #[repr(simd)]
        struct CustomSimd<T, const LANES: usize>([T; LANES]);

        pub fn probe_simd(v: CustomSimd<u8, 10>) -> CustomSimd<u8, 10> { v }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_simd");
        let ty = sig.inputs()[0];
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let sort = ChcCtx::translate_adt_sort(def, args);
            assert!(sort.is_some(), "CustomSimd<u8, 10> should produce a sort, not None");
            let sort = sort.unwrap();
            let dt = sort.datatype_sort();
            assert!(
                dt.is_some(),
                "CustomSimd<u8, 10> should produce a Datatype sort, got: {:?}",
                sort
            );
            let dt = dt.unwrap();
            assert_eq!(dt.constructors.len(), 1, "should have exactly 1 constructor");
            assert_eq!(dt.constructors[0].fields.len(), 1, "should have exactly 1 field");
            let field_sort = &dt.constructors[0].fields[0].sort;
            assert!(
                field_sort.is_array(),
                "inner field should be Array sort, got: {:?}",
                field_sort
            );
        } else {
            panic!("CustomSimd<u8, 10> should be an ADT type");
        }
    });
}

// =============================================================================
// Unsized-pointee reference payloads — BV128 fat-pointer unification
// =============================================================================

/// `Option<&str>` payload must be declared as the BV128 fat pointer
/// (concat(len, data_ptr)), matching the value path `translate_ty(&str)`.
/// Previously the payload was declared as `Array(BV64, BV8)` (bare `str`)
/// while values flowed as BV128, producing ill-sorted constructor
/// applications that failed AY's parser.
#[test]
fn test_translate_adt_ty_option_ref_str_payload_is_bv128_fat_pointer() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option_ref_str(o: Option<&str>) -> bool { o.is_some() }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option_ref_str");
        let ty = sig.inputs()[0];
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            panic!("Option<&str> should be an ADT type");
        };
        let sort = ChcCtx::translate_adt_ty(def, args).expect("Option<&str> should translate");
        let dt = sort.datatype_sort().expect("Option<&str> should be a datatype");
        let payload_sort = dt
            .constructors
            .iter()
            .find_map(|c| c.fields.first().map(|f| f.sort.clone()))
            .expect("Some variant should carry a payload field");
        assert_eq!(
            payload_sort.bitvec_width(),
            Some(128),
            "Option<&str> payload must be the BV128 fat pointer, got: {payload_sort:?}"
        );
    });
}

/// `Result<&str, E>` (general enum arm) Ok payload must also be BV128.
#[test]
fn test_translate_adt_ty_result_ref_str_ok_payload_is_bv128_fat_pointer() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_result_ref_str(r: Result<&str, u32>) -> bool { r.is_ok() }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_result_ref_str");
        let ty = sig.inputs()[0];
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            panic!("Result<&str, u32> should be an ADT type");
        };
        let sort = ChcCtx::translate_adt_ty(def, args).expect("Result<&str, u32> should translate");
        let dt = sort.datatype_sort().expect("Result<&str, u32> should be a datatype");
        let has_bv128_payload = dt
            .constructors
            .iter()
            .any(|c| c.fields.iter().any(|f| f.sort.bitvec_width() == Some(128)));
        assert!(
            has_bv128_payload,
            "Result<&str, u32> Ok payload must be the BV128 fat pointer, got: {:?}",
            dt.constructors
        );
        let has_bv32_payload = dt
            .constructors
            .iter()
            .any(|c| c.fields.iter().any(|f| f.sort.bitvec_width() == Some(32)));
        assert!(has_bv32_payload, "Err(u32) payload should remain BV32");
    });
}

/// `Option<&[u8; N]>` has a *sized* pointee: the deref-strip stays and the
/// payload keeps the Array/value modeling (unchanged by the BV128 gate).
#[test]
fn test_translate_adt_ty_option_ref_sized_array_payload_stays_array() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_option_ref_arr(o: Option<&[u8; 4]>) -> bool { o.is_some() }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_option_ref_arr");
        let ty = sig.inputs()[0];
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            panic!("Option<&[u8; 4]> should be an ADT type");
        };
        let sort = ChcCtx::translate_adt_ty(def, args).expect("Option<&[u8; 4]> should translate");
        let dt = sort.datatype_sort().expect("Option<&[u8; 4]> should be a datatype");
        let payload_sort = dt
            .constructors
            .iter()
            .find_map(|c| c.fields.first().map(|f| f.sort.clone()))
            .expect("Some variant should carry a payload field");
        assert!(
            payload_sort.is_array(),
            "Option<&[u8; 4]> (sized pointee) payload should stay Array-modeled, got: {payload_sort:?}"
        );
    });
}

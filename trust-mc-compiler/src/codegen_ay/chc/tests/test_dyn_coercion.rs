// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `dyn_coercion.rs` — shared dyn-coercion type extraction.
//!
//! Part of #3604 — zero test coverage for dyn_coercion.rs (449 lines).
//!
//! Coverage areas:
//! - `extract_pointer_expr`: thin pointer extraction from wrapper datatypes
//! - `peel_pointer_like_wrapper_ty` / `find_dyn_trait_tail_ty`: wrapper vs dyn-tail intent split
//! - End-to-end dyn dispatch: MIR probes exercising the full coercion pipeline

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, Sort};

use super::super::codegen_call_closure::resolve_unique_dyn_callable_body;
use super::super::dyn_coercion::{
    extract_concrete_tail_for_dyn, extract_pointer_expr, find_dyn_trait_tail_ty,
    peel_pointer_like_wrapper_ty,
};

// =============================================================================
// extract_pointer_expr: pure unit tests
// =============================================================================

/// A bare bitvec expression (already a thin pointer) passes through unchanged.
#[test]
fn test_extract_pointer_expr_bv_passthrough() {
    let ptr = Expr::bitvec_const(0x1000u64, 64);
    let result = extract_pointer_expr(&ptr);
    assert!(result.is_some(), "BV expression should pass through");
    assert_eq!(*result.unwrap().sort(), Sort::bitvec(64));
}

/// A Bool expression (not a pointer, not a datatype) returns None.
#[test]
fn test_extract_pointer_expr_bool_returns_none() {
    let expr = Expr::bool_const(true);
    let result = extract_pointer_expr(&expr);
    assert!(result.is_none(), "Bool is not a pointer or datatype with fld_ptr");
}

/// An Int expression returns None (no bitvec, no datatype).
#[test]
fn test_extract_pointer_expr_int_returns_none() {
    let expr = Expr::int_const(42);
    let result = extract_pointer_expr(&expr);
    assert!(result.is_none(), "Int is not a pointer or datatype with fld_ptr");
}

/// A datatype with `fld_ptr` field extracts the pointer via field_select.
#[test]
fn test_extract_pointer_expr_datatype_with_fld_ptr() {
    let ptr_sort = Sort::bitvec(64);
    let wrapper_sort = Sort::struct_type("DynWrapper", [("fld_ptr", ptr_sort.clone())]);

    // Construct a variable with the wrapper sort
    let wrapper_var = Expr::var("wrapper_val", wrapper_sort);
    let result = extract_pointer_expr(&wrapper_var);
    assert!(result.is_some(), "Datatype with fld_ptr should extract pointer");
    assert_eq!(*result.unwrap().sort(), ptr_sort, "Extracted pointer should have BV64 sort");
}

/// A datatype with `fld_ptr` and additional fields still extracts the pointer.
#[test]
fn test_extract_pointer_expr_datatype_multi_field() {
    let ptr_sort = Sort::bitvec(64);
    let wrapper_sort = Sort::struct_type(
        "FatPtr",
        [("fld_ptr", ptr_sort.clone()), ("fld_vtable", Sort::bitvec(64))],
    );

    let fat_ptr = Expr::var("fat_ptr_val", wrapper_sort);
    let result = extract_pointer_expr(&fat_ptr);
    assert!(result.is_some(), "Multi-field datatype with fld_ptr should extract");
    assert_eq!(*result.unwrap().sort(), ptr_sort);
}

/// A datatype WITHOUT `fld_ptr` and no pointer-width BV field returns None.
#[test]
fn test_extract_pointer_expr_datatype_no_fld_ptr() {
    let other_sort = Sort::struct_type("Point", [("x", Sort::bitvec(32)), ("y", Sort::bitvec(32))]);

    let point = Expr::var("point_val", other_sort);
    let result = extract_pointer_expr(&point);
    assert!(result.is_none(), "Datatype without fld_ptr or BV64 field should return None");
}

/// A generic ADT fat pointer using positional field names (`field_0`, `field_1`)
/// instead of `fld_ptr` should still extract the first BV64 field as the data pointer.
/// Part of #3953: fat-pointer deref_non_bitvec_field_load recovery.
#[test]
fn test_extract_pointer_expr_generic_adt_fat_pointer() {
    let ptr_sort = Sort::bitvec(64);
    let generic_fat_ptr = Sort::struct_type(
        "GenericFatPtr",
        [("field_0", ptr_sort.clone()), ("field_1", Sort::bitvec(64))],
    );

    let fat_ptr = Expr::var("generic_fat_ptr_val", generic_fat_ptr);
    let result = extract_pointer_expr(&fat_ptr);
    assert!(result.is_some(), "Generic ADT fat pointer with BV64 field_0 should extract pointer");
    assert_eq!(*result.unwrap().sort(), ptr_sort, "Extracted pointer should have BV64 sort");
}

/// A generic ADT fat pointer where the BV64 field is not the first field but is
/// the first *pointer-width* BV field should still be extracted.
#[test]
fn test_extract_pointer_expr_generic_adt_mixed_fields() {
    let ptr_sort = Sort::bitvec(64);
    let mixed_sort = Sort::struct_type(
        "MixedFatPtr",
        [("tag", Sort::bitvec(8)), ("data_ptr", ptr_sort.clone()), ("metadata", Sort::bitvec(64))],
    );

    let mixed_ptr = Expr::var("mixed_fat_ptr_val", mixed_sort);
    let result = extract_pointer_expr(&mixed_ptr);
    assert!(result.is_some(), "Should extract first BV64 field even if preceded by BV8");
    assert_eq!(*result.unwrap().sort(), ptr_sort);
}

/// A many-field user ADT with BV64 fields must NOT have a field extracted as a
/// pointer. The fallback heuristic is restricted to ≤ 4 fields. Part of #4099:
/// DtSolver(11 fields) had scope_len (first BV64) mistaken for a pointer.
#[test]
fn test_extract_pointer_expr_many_field_adt_no_extract() {
    let many_field_sort = Sort::struct_type(
        "DtSolver",
        [
            ("fld_parent0", Sort::bitvec(32)),
            ("fld_parent1", Sort::bitvec(32)),
            ("fld_parent2", Sort::bitvec(32)),
            ("fld_ctor0", Sort::bitvec(32)),
            ("fld_ctor1", Sort::bitvec(32)),
            ("fld_ctor2", Sort::bitvec(32)),
            ("fld_scope_len", Sort::bitvec(64)),
            ("fld_scope0_ctor_count", Sort::bitvec(64)),
            ("fld_scope1_ctor_count", Sort::bitvec(64)),
            ("fld_ctor_count", Sort::bitvec(64)),
            ("fld_has_datatype", Sort::bool()),
        ],
    );
    let solver = Expr::var("solver_val", many_field_sort);
    let result = extract_pointer_expr(&solver);
    assert!(
        result.is_none(),
        "Many-field ADT (>4 fields) without fld_ptr should return None, not extract scope_len"
    );
}

/// A 5-field ADT at the boundary (>4) should NOT extract. Part of #4099.
#[test]
fn test_extract_pointer_expr_five_field_adt_no_extract() {
    let five_field = Sort::struct_type(
        "FiveFields",
        [
            ("a", Sort::bitvec(32)),
            ("b", Sort::bitvec(32)),
            ("c", Sort::bitvec(64)),
            ("d", Sort::bitvec(64)),
            ("e", Sort::bitvec(64)),
        ],
    );
    let val = Expr::var("five_val", five_field);
    let result = extract_pointer_expr(&val);
    assert!(result.is_none(), "5-field ADT should not extract a field as pointer");
}

// =============================================================================
// MIR-backed probes: dyn trait dispatch pipeline
// =============================================================================

/// Probe: simple dyn trait with a single concrete implementor.
/// Exercises pointer-wrapper peeling, candidate collection, and the full
/// coercion pipeline.
const DYN_TRAIT_SIMPLE_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Greet {
        fn greet(&self) -> u32;
    }

    struct Dog;
    impl Greet for Dog {
        fn greet(&self) -> u32 { 1 }
    }

    fn probe_dyn_dispatch(x: &dyn Greet) -> u32 {
        x.greet()
    }
"#;

/// A function calling a method on `&dyn Greet` should produce a valid VC.
/// The dyn coercion pipeline must detect the concrete implementor (Dog) and
/// generate dispatch rules.
#[test]
fn test_dyn_dispatch_simple_produces_valid_vc() {
    with_test_ay_ctx_for_source(DYN_TRAIT_SIMPLE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dyn_dispatch");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_dyn_dispatch", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "dyn dispatch function should produce relations");
        assert!(!vc.rules.is_empty(), "dyn dispatch function should produce rules");

        // Should have bv32 for the u32 return
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "dyn dispatch should have bv32 for u32 return");
    });
}

/// Probe: Box<dyn Trait> exercises the pointer-wrapper peeling path.
const BOX_DYN_TRAIT_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Compute {
        fn compute(&self) -> u32;
    }

    struct Adder { value: u32 }
    impl Compute for Adder {
        fn compute(&self) -> u32 { self.value + 1 }
    }

    fn probe_box_dyn_dispatch(x: Box<dyn Compute>) -> u32 {
        x.compute()
    }
"#;

/// Probe: boxed dyn FnOnce call that must recover the concrete closure body
/// from the shared dyn-coercion pipeline rather than a direct Closure arg.
const BOXED_DYN_FN_ONCE_PROBE: &str = r#"
    #![allow(dead_code)]

    fn probe_boxed_dyn_fn_once() {
        let f: Box<dyn FnOnce(f32, i32)> = Box::new(|x, y| {
            assert!(x == 1.0);
            assert!(y == 2);
        });
        f(1.0, 2);
    }
"#;

/// Probe: multiple dyn-callable closures with distinct signatures.
/// The resolver must match the current call signature instead of rejecting the
/// whole call site because unrelated closure candidates also exist in the body.
const MULTI_SIGNATURE_DYN_CALLABLE_PROBE: &str = r#"
    #![allow(dead_code)]

    fn probe_multi_signature_dyn_callable() {
        let f: Box<Box<dyn FnOnce(i32)>> = Box::new(Box::new(|x| assert!(x == 1)));
        f(1);

        let g = |x: f32, y: i32| {
            assert!(x == 1.0);
            assert!(y == 2);
        };
        let p: &dyn Fn(f32, i32) = &g;
        p(1.0, 2);

        let r: Box<&dyn Fn(f32, i32, bool)> = Box::new(&|x: f32, y: i32, z: bool| {
            assert!(x == 1.0);
            assert!(y == 2);
            assert!(z);
        });
        r(1.0, 2, true);
    }
"#;

/// Box<dyn Trait> dispatch exercises pointer-wrapper peeling (Box → dyn Compute).
#[test]
fn test_box_dyn_dispatch_produces_valid_vc() {
    with_test_ay_ctx_for_source(BOX_DYN_TRAIT_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_dyn_dispatch");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_box_dyn_dispatch", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "Box<dyn> dispatch should produce relations");
        assert!(!vc.rules.is_empty(), "Box<dyn> dispatch should produce rules");
    });
}

/// Box<dyn FnOnce(... )> should resolve to the unique closure body through the
/// shared dyn-coercion candidate/body pipeline.
#[test]
fn test_boxed_dyn_fn_once_resolves_unique_callable_body() {
    with_test_ay_ctx_for_source(BOXED_DYN_FN_ONCE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_boxed_dyn_fn_once");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_boxed_dyn_fn_once", ChcConfig::default());

        let (fn_def, fn_args) = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, .. } => {
                    let path = chc_ctx.resolve_callee_path(func)?;
                    if !path.ends_with("::call_once") {
                        return None;
                    }
                    let func_ty = func.ty(body.locals()).ok()?;
                    match func_ty.kind() {
                        TyKind::RigidTy(RigidTy::FnDef(def, args)) => Some((def, args)),
                        _ => None,
                    }
                }
                _ => None,
            })
            .expect("expected boxed dyn FnOnce call");

        let resolved_body = resolve_unique_dyn_callable_body(&chc_ctx, fn_def, &fn_args)
            .expect("boxed dyn FnOnce call should resolve a unique callable body");
        let resolved_ctx = ChcCtx::new(
            ctx.tcx,
            &resolved_body,
            "resolved_boxed_dyn_fn_once",
            ChcConfig::default(),
        );
        let forwards_to_call_once = resolved_body.blocks.iter().any(|block| {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                return false;
            };
            resolved_ctx
                .resolve_callee_path(&func)
                .is_some_and(|path| path.ends_with("::call_once"))
        });

        assert!(
            !resolved_body.blocks.is_empty(),
            "resolved boxed dyn FnOnce body should have MIR blocks"
        );
        assert!(
            !forwards_to_call_once,
            "boxed dyn FnOnce resolver should return the closure body, not a call_once shim"
        );
    });
}

/// Multiple dyn-callable closures in the same function should still resolve the
/// unique body for each concrete call signature instead of bailing out.
#[test]
fn test_multi_signature_dyn_callable_resolves_unique_body_per_signature() {
    with_test_ay_ctx_for_source(MULTI_SIGNATURE_DYN_CALLABLE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_signature_dyn_callable");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_multi_signature_dyn_callable", ChcConfig::default());

        let mut arities = Vec::new();
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if !path.ends_with("::call") && !path.ends_with("::call_once") {
                continue;
            }

            let func_ty = func.ty(body.locals()).expect("call terminator type");
            let (fn_def, fn_args) = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
                _ => panic!("expected FnDef for dyn-callable terminator"),
            };

            let resolved_body = resolve_unique_dyn_callable_body(&chc_ctx, fn_def, &fn_args)
                .unwrap_or_else(|| panic!("dyn-callable resolver should match path={path}"));
            arities.push(resolved_body.arg_locals().len() - 1);
        }

        arities.sort_unstable();
        assert_eq!(
            arities,
            vec![1, 2, 3],
            "resolver should recover the 1-arg, 2-arg, and 3-arg callable bodies"
        );
    });
}

/// Probe: multiple concrete implementors of the same trait.
/// Tests collect_dyn_trait_candidates with >1 candidate.
const MULTI_IMPL_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Shape {
        fn area(&self) -> u32;
    }

    struct Circle;
    impl Shape for Circle {
        fn area(&self) -> u32 { 314 }
    }

    struct Square;
    impl Shape for Square {
        fn area(&self) -> u32 { 400 }
    }

    fn probe_multi_impl(s: &dyn Shape) -> u32 {
        s.area()
    }
"#;

/// Multiple implementors should still produce a valid VC. The dispatch pipeline
/// builds an ITE chain over the vtable ID to route to the correct implementation.
#[test]
fn test_multi_impl_dyn_dispatch_produces_valid_vc() {
    with_test_ay_ctx_for_source(MULTI_IMPL_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_impl");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_multi_impl", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "multi-impl dispatch should produce relations");
        assert!(!vc.rules.is_empty(), "multi-impl dispatch should produce rules");
    });
}

/// Probe: dyn trait coercion site (Unsize cast from concrete to dyn).
/// Exercises collect_dyn_trait_candidates Phase 2 (MIR coercion scan).
const COERCION_SITE_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Printable {
        fn label(&self) -> u32;
    }

    struct Item { id: u32 }
    impl Printable for Item {
        fn label(&self) -> u32 { self.id }
    }

    fn probe_coercion_site() -> u32 {
        let item = Item { id: 42 };
        let dyn_ref: &dyn Printable = &item;
        dyn_ref.label()
    }
"#;

/// A function that creates a dyn trait reference from a concrete type exercises
/// both the coercion assignment (stmt side) and the dispatch (call side).
#[test]
fn test_coercion_site_produces_valid_vc() {
    with_test_ay_ctx_for_source(COERCION_SITE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coercion_site");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_coercion_site", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "coercion site should produce relations");
        assert!(!vc.rules.is_empty(), "coercion site should produce rules");

        // Should have bv32 for the u32 return value and Item.id field
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "coercion site should include bv32 for u32");
    });
}

// =============================================================================
// Struct-with-dyn-tail: resolve_unique_concrete_dyn_tail_ty + type_contains_dyn_tail
// =============================================================================
// These are pub(super)/private functions added by W3 (#3589) for unsized struct
// coercion recovery. type_contains_dyn_tail is private so must be tested indirectly
// through the full pipeline. resolve_unique_concrete_dyn_tail_ty is exercised when
// memory_impl_layout.rs does layout computation on a dyn-tailed struct.

/// Probe: struct with an unsized dyn tail field, coerced from concrete.
/// Exercises resolve_unique_concrete_dyn_tail_ty (scans MIR for Unsize coercion),
/// type_contains_dyn_tail (checks if type structurally contains dyn), and
/// replace_dyn_tail_with_concrete (substitutes concrete tail for layout).
const STRUCT_DYN_TAIL_PROBE: &str = r#"
    #![allow(dead_code)]

    use core::fmt::Debug;

    struct Wrapper<T: ?Sized> {
        tag: u32,
        inner: T,
    }

    fn probe_struct_dyn_tail() -> u32 {
        let w = Wrapper { tag: 42, inner: 7u32 };
        let dyn_ref: &Wrapper<dyn Debug> = &w;
        dyn_ref.tag
    }
"#;

/// Struct-with-dyn-tail unsizing exercises the three dyn_coercion.rs functions
/// that W3 added for #3589. The coercion `&Wrapper<u32>` → `&Wrapper<dyn Debug>`
/// triggers resolve_unique_concrete_dyn_tail_ty during layout computation for
/// the unsized `Wrapper<dyn Debug>` type.
#[test]
fn test_struct_dyn_tail_coercion_produces_valid_vc() {
    with_test_ay_ctx_for_source(STRUCT_DYN_TAIL_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_dyn_tail");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_dyn_tail", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "struct-dyn-tail should produce relations");
        assert!(!vc.rules.is_empty(), "struct-dyn-tail should produce rules");

        // Should have bv32 for the u32 tag field and inner
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "struct-dyn-tail should include bv32 for u32 fields");
    });
}

/// Probe: nested wrapper with dyn tail — tests type_contains_dyn_tail recursion
/// through ADT and Ref layers.
const NESTED_WRAPPER_DYN_TAIL_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn sound(&self) -> u32;
    }

    struct Cat;
    impl Animal for Cat {
        fn sound(&self) -> u32 { 1 }
    }

    struct Cage<T: ?Sized> {
        id: u32,
        occupant: T,
    }

    fn probe_nested_dyn_tail() -> u32 {
        let cage = Cage { id: 5, occupant: Cat };
        let dyn_ref: &Cage<dyn Animal> = &cage;
        dyn_ref.id
    }
"#;

const POINTER_WRAPPER_INTENT_SPLIT_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(coerce_unsized)]
    #![feature(unsize)]

    use std::marker::Unsize;
    use std::ops::CoerceUnsized;

    trait Identity {
        fn id(&self) -> u8;
    }

    struct Inner {
        id: u8,
    }

    impl Identity for Inner {
        fn id(&self) -> u8 {
            self.id
        }
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    struct Cage<T: ?Sized>(T);

    struct MyPtr<'a, T: ?Sized> {
        ptr: &'a T,
    }

    impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<'a, U>> for MyPtr<'a, T> {}

    fn probe_pointer_wrapper_intent_split<'a>(
        ptr: MyPtr<'a, dyn Identity>,
        outer: &'a Outer<dyn Identity>,
        cage: &'a Cage<dyn Identity>,
    ) -> u8 {
        let _ = ptr;
        let _ = outer;
        let _ = cage;
        0
    }
"#;

/// Nested custom trait unsizing: similar to Debug but with user-defined trait.
/// Ensures type_contains_dyn_tail correctly traverses ADT generic args.
#[test]
fn test_nested_dyn_tail_custom_trait_produces_valid_vc() {
    with_test_ay_ctx_for_source(NESTED_WRAPPER_DYN_TAIL_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_dyn_tail");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_nested_dyn_tail", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "nested dyn tail should produce relations");
        assert!(!vc.rules.is_empty(), "nested dyn tail should produce rules");
    });
}

#[test]
fn test_peel_pointer_like_wrapper_ty_stops_at_dyn_tail_adts() {
    with_test_ay_ctx_for_source(POINTER_WRAPPER_INTENT_SPLIT_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pointer_wrapper_intent_split");
        let sig = instance.ty().kind().fn_sig().unwrap().skip_binder();

        let ptr_ty = sig.inputs()[0];
        let outer_ty = sig.inputs()[1];
        let cage_ty = sig.inputs()[2];

        let peeled_ptr = peel_pointer_like_wrapper_ty(ptr_ty);
        let peeled_outer = peel_pointer_like_wrapper_ty(outer_ty);
        let peeled_cage = peel_pointer_like_wrapper_ty(cage_ty);

        assert!(
            matches!(peeled_ptr.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))),
            "custom pointer wrapper should peel to dyn tail, got {peeled_ptr:?}"
        );
        assert!(
            matches!(peeled_outer.kind(), TyKind::RigidTy(RigidTy::Adt(..))),
            "Outer<dyn Trait> should keep its DST shell, got {peeled_outer:?}"
        );
        assert!(
            matches!(peeled_cage.kind(), TyKind::RigidTy(RigidTy::Adt(..))),
            "Cage<dyn Trait> should keep its DST shell, got {peeled_cage:?}"
        );
    });
}

#[test]
fn test_find_dyn_trait_tail_ty_reports_tail_without_erasing_outer_shell() {
    with_test_ay_ctx_for_source(POINTER_WRAPPER_INTENT_SPLIT_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pointer_wrapper_intent_split");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_pointer_wrapper_intent_split", ChcConfig::default());
        let sig = instance.ty().kind().fn_sig().unwrap().skip_binder();

        for ty in sig.inputs() {
            let dyn_tail =
                find_dyn_trait_tail_ty(&chc_ctx, *ty).expect("wrapper should report dyn tail");
            assert!(
                matches!(dyn_tail.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))),
                "expected dyn tail for {ty:?}, got {dyn_tail:?}"
            );
        }
    });
}

// =============================================================================
// extract_concrete_tail_for_dyn: unit test via MIR types
// =============================================================================

/// Direct dyn coercion (target is Dynamic) returns src_inner unchanged.
#[test]
fn test_extract_concrete_tail_direct_dyn() {
    with_test_ay_ctx_for_source(DYN_TRAIT_SIMPLE_PROBE, |ctx| {
        // Find any dyn type and concrete type in the program
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dyn_dispatch");
        let sig = instance.ty().kind().fn_sig().unwrap().skip_binder();
        let param_ty = sig.inputs()[0]; // &dyn Greet

        // Peel the reference to get dyn Greet.
        let inner = peel_pointer_like_wrapper_ty(param_ty);

        // For direct dyn coercion where target is Dynamic, extract_concrete_tail_for_dyn
        // should return src_inner unchanged (since Dog is not an ADT wrapping anything).
        let result = extract_concrete_tail_for_dyn(inner, inner);
        assert_eq!(result, inner, "direct dyn target should return src unchanged");
    });
}

// =============================================================================
// Unsize alias store: per-field scatter instead of silent truncation (#4225)
// =============================================================================

/// Probe: `&Outer<Inner>` → `&dyn Identity` coercion where the concrete struct
/// flattens to BV16 (two u8 fields) but the dyn-tail type key is the u8 byte
/// view (BV8). Mirrors tests/kani/UnsizedCoercion/{box,custom,rc}_outer_coercion.
///
/// The source is a fn param reference (NOT an in-body aggregate) so the only
/// writer of the u8 byte view is the Unsize-coercion alias bridge itself —
/// in-body construction would emit its own correct per-field mirror stores and
/// mask the alias path under test.
const OUTER_ALIAS_SCATTER_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Inner {
        id: u8,
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id as u16
        }
    }

    impl<T: ?Sized + Identity> Identity for Outer<T> {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + self.inner.id()
        }
    }

    fn probe_outer_alias_scatter(outer: &Outer<Inner>) -> u16 {
        let dyn_ref: &dyn Identity = outer;
        dyn_ref.id()
    }
"#;

/// UnsizedCoercion FP regression: the #4225 alias bridge must NOT re-store the
/// loaded whole-struct BV16 value into the dyn-tail u8 array (coerce_store_value
/// would silently truncate it to the LOW byte = the LAST field, clobbering the
/// correct byte-0 cell via store forwarding and fabricating a Genuine CTREX on
/// safe programs). Instead it must scatter per field: field 0 (`outer_id`, the
/// MSB half of the flattened struct, `(_ extract 15 8)`) to ptr+0 and field 1
/// (`inner.id`, low byte) to ptr+1.
///
/// Discriminator: the truncating path only ever produced `(_ extract 7 0)` of
/// the loaded struct; `(_ extract 15 8)` appears exactly when the per-field
/// scatter fires (no in-body aggregate exists to emit competing mirrors).
#[test]
fn test_unsize_alias_scatters_struct_per_field_not_truncated() {
    with_test_ay_ctx_for_source(OUTER_ALIAS_SCATTER_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_outer_alias_scatter");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_outer_alias_scatter", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "outer alias probe should produce relations");
        assert!(!vc.rules.is_empty(), "outer alias probe should produce rules");

        let mut texts: Vec<String> = Vec::new();
        for rule in &vc.rules {
            texts.extend(rule.body.constraints.iter().map(ToString::to_string));
            texts.extend(rule.head.args.iter().map(ToString::to_string));
        }
        let all = texts.join("\n");

        assert!(
            all.contains("(_ extract 15 8)"),
            "Unsize alias bridge must scatter field 0 (outer_id, MSB half of the \
             flattened BV16 struct) into the dyn-tail byte view via \
             ((_ extract 15 8) ...) — a silently truncating whole-struct store \
             keeps only the low byte and fabricates a false CTREX \
             (UnsizedCoercion cluster). Constraints:\n{all}"
        );
    });
}

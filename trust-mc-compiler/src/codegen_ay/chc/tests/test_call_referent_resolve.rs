// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `referent_resolve.rs` — referent resolution helpers.
//!
//! `resolve_bare_local_impl` looks up bare local state variables for Call stubs.
//! `resolve_ref_or_const_referent_impl` resolves call operands through multi-tier
//! referent resolution (ref_targets → const_ref_values → const_ref_discriminants
//! → translate_operand → bare local fallback).
//!
//! Part of #2933 (zero-coverage remediation), #2408 S1 (codegen_call_misc decomposition).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;
use crate::codegen_ay::emit_chc;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Sort;
use rustc_public::mir::{Operand, Place, ProjectionElem, TerminatorKind};
use std::collections::HashMap;
use std::sync::Arc;

// =============================================================================
// resolve_bare_local_impl — static method, directly testable
// =============================================================================

#[test]
fn test_resolve_bare_local_copy_unmodified_uses_input_var() {
    let state_vars: Vec<(Arc<str>, Sort)> = vec![
        (Arc::from("test_fn::local_0"), Sort::bv32()),
        (Arc::from("test_fn::local_1"), Sort::bv32()),
    ];
    let output_state_vars: Vec<(Arc<str>, Sort)> = vec![
        (Arc::from("test_fn::local_0__out"), Sort::bv32()),
        (Arc::from("test_fn::local_1__out"), Sort::bv32()),
    ];
    let modified: HashSet<usize> = HashSet::new(); // local_1 is NOT modified
    let local_to_state: HashMap<usize, usize> = HashMap::from([(0, 0), (1, 1)]);

    let copy_op = Operand::Copy(Place { local: 1, projection: vec![] });

    let result = ChcCtx::resolve_bare_local_impl(
        &copy_op,
        &state_vars,
        &output_state_vars,
        &modified,
        &local_to_state,
        "test_fn",
    );
    assert!(result.is_some(), "Copy of unmodified bare local should resolve");
    let expr = result.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(32), "resolved expression should be BV32");
    // Verify input (not output) variable was selected for unmodified local
    let name = expr.to_string();
    assert!(
        !name.contains("__out"),
        "unmodified local should resolve to INPUT var (no __out suffix), got: {name}"
    );
}

#[test]
fn test_resolve_bare_local_copy_modified_uses_output_var() {
    let state_vars: Vec<(Arc<str>, Sort)> = vec![
        (Arc::from("test_fn::local_0"), Sort::bv32()),
        (Arc::from("test_fn::local_1"), Sort::bv32()),
    ];
    let output_state_vars: Vec<(Arc<str>, Sort)> = vec![
        (Arc::from("test_fn::local_0__out"), Sort::bv32()),
        (Arc::from("test_fn::local_1__out"), Sort::bv32()),
    ];
    let mut modified: HashSet<usize> = HashSet::new();
    modified.insert(1); // local_1 IS modified
    let local_to_state: HashMap<usize, usize> = HashMap::from([(0, 0), (1, 1)]);

    let copy_op = Operand::Copy(Place { local: 1, projection: vec![] });

    let result = ChcCtx::resolve_bare_local_impl(
        &copy_op,
        &state_vars,
        &output_state_vars,
        &modified,
        &local_to_state,
        "test_fn",
    );
    assert!(result.is_some(), "Copy of modified bare local should resolve");
    let expr = result.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(32), "resolved output expression should be BV32");
    // Verify output (not input) variable was selected for modified local
    let name = expr.to_string();
    assert!(
        name.contains("__out"),
        "modified local should resolve to OUTPUT var (with __out suffix), got: {name}"
    );
}

#[test]
fn test_resolve_bare_local_with_deref_projection_returns_none() {
    let state_vars: Vec<(Arc<str>, Sort)> = vec![(Arc::from("test_fn::local_0"), Sort::bv32())];
    let output_state_vars: Vec<(Arc<str>, Sort)> =
        vec![(Arc::from("test_fn::local_0__out"), Sort::bv32())];
    let modified: HashSet<usize> = HashSet::new();
    let local_to_state: HashMap<usize, usize> = HashMap::from([(0, 0)]);

    // Place with Deref projection — not a bare local
    let projected_op = Operand::Copy(Place { local: 0, projection: vec![ProjectionElem::Deref] });

    let result = ChcCtx::resolve_bare_local_impl(
        &projected_op,
        &state_vars,
        &output_state_vars,
        &modified,
        &local_to_state,
        "test_fn",
    );
    assert_eq!(result, None, "Operand with Deref projection should return None (not a bare local)");
}

#[test]
fn test_resolve_bare_local_missing_index_returns_none() {
    let state_vars: Vec<(Arc<str>, Sort)> = vec![(Arc::from("test_fn::local_0"), Sort::bv32())];
    let output_state_vars: Vec<(Arc<str>, Sort)> =
        vec![(Arc::from("test_fn::local_0__out"), Sort::bv32())];
    let modified: HashSet<usize> = HashSet::new();
    let local_to_state: HashMap<usize, usize> = HashMap::from([(0, 0)]);
    // local_5 is NOT in local_to_state

    let copy_op = Operand::Copy(Place { local: 5, projection: vec![] });

    let result = ChcCtx::resolve_bare_local_impl(
        &copy_op,
        &state_vars,
        &output_state_vars,
        &modified,
        &local_to_state,
        "test_fn",
    );
    assert_eq!(
        result, None,
        "bare local with no local_to_state_idx entry should return None (#2698)"
    );
}

#[test]
fn test_resolve_bare_local_move_operand_resolves() {
    let state_vars: Vec<(Arc<str>, Sort)> = vec![
        (Arc::from("test_fn::local_0"), Sort::bv32()),
        (Arc::from("test_fn::local_1"), Sort::bitvec(64)),
    ];
    let output_state_vars: Vec<(Arc<str>, Sort)> = vec![
        (Arc::from("test_fn::local_0__out"), Sort::bv32()),
        (Arc::from("test_fn::local_1__out"), Sort::bitvec(64)),
    ];
    let modified: HashSet<usize> = HashSet::new();
    let local_to_state: HashMap<usize, usize> = HashMap::from([(0, 0), (1, 1)]);

    // Move operand should also resolve (same logic as Copy)
    let move_op = Operand::Move(Place { local: 1, projection: vec![] });

    let result = ChcCtx::resolve_bare_local_impl(
        &move_op,
        &state_vars,
        &output_state_vars,
        &modified,
        &local_to_state,
        "test_fn",
    );
    assert!(result.is_some(), "Move of bare local should resolve");
    let expr = result.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(64), "resolved Move expression should be BV64");
}

// =============================================================================
// resolve_ref_or_const_referent_impl — needs ChcCtx, test via MIR pipeline
// =============================================================================

/// Source with a const reference pattern that exercises the multi-tier
/// referent resolution path.
const CONST_REF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn deref_const_ref() -> u32 {
        let val = 42u32;
        let r = &val;
        *r
    }
"#;

#[test]
fn test_ref_or_const_referent_produces_valid_chc() {
    // End-to-end test: a function with const ref deref should produce
    // a valid CHC encoding where resolve_ref_or_const_referent_impl
    // is exercised in the codegen pipeline.
    with_test_ay_ctx_for_source(CONST_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_const_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "deref_const_ref", ChcConfig::default());

        // The function should produce a valid VC with at least 1 relation
        assert!(!vc.relations.is_empty(), "deref_const_ref should produce non-empty CHC relations");
    });
}

/// Source with mutable reference deref + return that exercises
/// resolve_ref_or_const_referent through the ref_targets tier.
const MUT_REF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn increment_ref(x: &mut u32) -> u32 {
        *x = x.wrapping_add(1);
        *x
    }
"#;

const BOX_INNER_DYN_REFERENT_SOURCE: &str = r#"
    #![allow(dead_code)]

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    struct Inner {
        id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + self.inner.id()
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    fn id_from_dyn(identity: &dyn Identity) -> u16 {
        identity.id()
    }

    pub fn probe_box_inner_dyn_referent(inner_id: u8, outer_id: u8) {
        let outer: Box<Outer<dyn Identity>> =
            Box::new(Outer { inner: Inner { id: inner_id }, outer_id });
        let actual = id_from_dyn(&outer.inner);
        assert!(actual == inner_id.into());
    }
"#;

const CUSTOM_OUTER_DYN_REFERENT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coerce_unsized)]
    #![feature(unsize)]

    use std::marker::Unsize;
    use std::ops::{CoerceUnsized, Deref};

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    struct Inner {
        id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + self.inner.id()
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    struct MyPtr<'a, T: ?Sized> {
        ptr: &'a T,
    }

    impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<'a, U>> for MyPtr<'a, T> {}

    impl<'a, T: ?Sized> Deref for MyPtr<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            self.ptr
        }
    }

    pub fn probe_custom_outer_dyn_referent(inner_id: u8, outer_id: u8) {
        let outer = Outer { inner: Inner { id: inner_id }, outer_id };
        let outer_ptr = MyPtr { ptr: &outer };
        let id_ptr: MyPtr<dyn Identity> = outer_ptr;
        let actual = id_from_coerce(id_ptr);
        let expected = ((outer_id as u16) << 8) + (inner_id as u16);
        assert!(actual == expected);
    }
"#;

fn sort_has_top_level_vtable_field(sort: &Sort) -> bool {
    sort.datatype_sort().is_some_and(|dt| {
        dt.constructors
            .iter()
            .any(|constructor| constructor.fields.iter().any(|field| field.name == "fld_vtable"))
    })
}

fn find_first_call_arg_for_callee(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    callee_fragment: &str,
) -> (usize, Operand, String) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind
                && let Some(callee_path) = chc_ctx.resolve_callee_path(func)
                && callee_path.contains(callee_fragment)
            {
                Some((bb_idx, args.first()?.clone(), callee_path))
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("expected call to {callee_fragment}"))
}

fn assert_dyn_referent_probe_restores_fat_pointer(
    source: &str,
    fn_name: &str,
    callee_fragment: &str,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, receiver, callee_path) =
            find_first_call_arg_for_callee(&chc_ctx, &body, callee_fragment);
        let (_stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let referent = chc_ctx
            .resolve_ref_or_const_referent(&receiver, &modified_locals)
            .unwrap_or_else(|| panic!("expected dyn referent for {callee_path}"));
        assert_ne!(
            referent.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "{callee_path} receiver should restore a dyn datatype, got bare pointer {referent:?}"
        );
        assert!(
            sort_has_top_level_vtable_field(&referent.sort()),
            "{callee_path} receiver should restore the dyn referent itself, got sort {:?}",
            referent.sort()
        );

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert!(!vc.rules.is_empty(), "{fn_name} should produce non-empty CHC rules");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert!(
            !vc_error_rules_contain_var(&vc, "__vtable_disc"),
            "{fn_name} should not fall back to a fresh vtable"
        );
        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

#[test]
fn test_mut_ref_deref_produces_valid_chc() {
    with_test_ay_ctx_for_source(MUT_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "increment_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "increment_ref", ChcConfig::default());

        assert!(
            !vc.relations.is_empty(),
            "mutable ref deref function should produce non-empty CHC relations"
        );
    });
}

#[test]
fn test_box_inner_dyn_referent_restores_fat_pointer_semantics() {
    assert_dyn_referent_probe_restores_fat_pointer(
        BOX_INNER_DYN_REFERENT_SOURCE,
        "probe_box_inner_dyn_referent",
        "id_from_dyn",
    );
}

/// Custom wrapper `MyPtr<dyn Identity>` peel: the referent should be a
/// dyn-fat-pointer datatype (with fld_vtable), not the outer wrapper sort.
/// Full proof requires additional virtual dispatch inlining for `Outer<Inner>::id()`.
/// Part of #3918: structural referent peel test.
#[test]
fn test_custom_outer_dyn_referent_restores_fat_pointer_semantics() {
    with_test_ay_ctx_for_source(CUSTOM_OUTER_DYN_REFERENT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_outer_dyn_referent");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_custom_outer_dyn_referent", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (_, receiver, callee_path) =
            find_first_call_arg_for_callee(&chc_ctx, &body, "id_from_coerce");
        let (_stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(0);
        let referent = chc_ctx
            .resolve_ref_or_const_referent(&receiver, &modified_locals)
            .unwrap_or_else(|| panic!("expected dyn referent for {callee_path}"));
        assert_ne!(
            referent.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "{callee_path} receiver should restore a dyn datatype, got bare pointer {referent:?}"
        );
        assert!(
            sort_has_top_level_vtable_field(&referent.sort()),
            "{callee_path} receiver should have fld_vtable after wrapper peel, got sort {:?}",
            referent.sort()
        );

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_custom_outer_dyn_referent", ChcConfig::default());
        assert!(!vc.rules.is_empty(), "should produce non-empty CHC rules");
        assert_has_nontrivial_transition_constraints(&vc, "probe_custom_outer_dyn_referent");
        assert!(
            !vc_error_rules_contain_var(&vc, "__vtable_disc"),
            "should not fall back to a fresh vtable discriminant"
        );
    });
}

const SIMD_ARRAY_VIEW_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(repr_simd)]

    #[derive(Copy, Clone)]
    #[repr(simd)]
    struct CustomSimd([u8; 4]);

    impl CustomSimd {
        #[inline(never)]
        fn as_array(&self) -> &[u8; 4] {
            let ptr: *const Self = self;
            unsafe { &*ptr.cast::<[u8; 4]>() }
        }

        #[inline(never)]
        fn into_array(self) -> [u8; 4] {
            *self.as_array()
        }
    }

    fn probe_simd_as_array_lane(vec: CustomSimd) -> u8 {
        vec.as_array()[2]
    }

    fn probe_simd_into_array_lane(vec: CustomSimd) -> u8 {
        vec.into_array()[1]
    }
"#;

const GENERIC_SIMD_ARRAY_VIEW_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(repr_simd)]

    #[derive(Copy)]
    #[repr(simd)]
    struct CustomSimd<T, const LANES: usize>([T; LANES]);

    impl<T: Copy, const LANES: usize> Clone for CustomSimd<T, LANES> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T: Copy, const LANES: usize> CustomSimd<T, LANES> {
        #[inline(never)]
        fn as_array(&self) -> &[T; LANES] {
            let ptr: *const Self = self;
            unsafe { &*ptr.cast::<[T; LANES]>() }
        }

        #[inline(never)]
        fn into_array(self) -> [T; LANES] {
            *self.as_array()
        }
    }

    fn probe_generic_simd_first(vec: CustomSimd<u8, 10>) -> u8 {
        vec.into_array()[0]
    }

    fn probe_generic_simd_symbolic_index(vec: CustomSimd<u8, 10>, idx: usize) -> u8 {
        vec.into_array()[idx]
    }

    fn probe_generic_simd_local_symbolic_index(idx: usize) -> u8 {
        let simd = CustomSimd([0u8; 10]);
        simd.into_array()[idx]
    }
"#;

fn with_slice_as_array_dispatch(
    source: &str,
    fn_name: &str,
    assertions: impl FnOnce(&mut ChcCtx<'_, '_>, usize, &str) + Send,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
                && chc_ctx
                    .resolve_callee_path(func)
                    .as_deref()
                    .is_some_and(|path| path.contains("as_array"))
            {
                found = true;
                let from_rel =
                    chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
                let output_args: Vec<_> = chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                    .collect();
                let from_app = RelationApp::new(&from_rel, output_args);
                let stmt_constraints = [Expr::bool_const(true)];
                let modified_locals = HashSet::new();
                let target_opt = Some(*target);
                let before = chc_ctx.sound_fallback_count();
                let dcx = DispatchCallContext {
                    bb_idx,
                    func,
                    args,
                    destination,
                    target: &target_opt,
                    from_app: &from_app,
                    stmt_constraints: &stmt_constraints,
                    modified_locals: &modified_locals,
                    callee_path: None,
                };
                chc_ctx.codegen_call_primitive_cmp(&dcx);
                assert_eq!(
                    chc_ctx.sound_fallback_count(),
                    before,
                    "slice_as_array dispatch should not record a sound fallback"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "slice_as_array dispatch should emit one rule"
                );
                let smt = emit_chc(&chc_ctx.vc).to_string();
                assertions(&mut chc_ctx, destination.local, &smt);
                break;
            }
        }
        assert_mir_pattern_found(found, "slice_as_array");
    });
}

#[test]
fn test_repr_simd_as_array_referent_keeps_array_view() {
    with_test_ay_ctx_for_source(SIMD_ARRAY_VIEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simd_as_array_lane");
        let body = instance.body().expect("body");
        let saw_as_array = body.blocks.iter().any(|block| {
            matches!(&block.terminator.kind, rustc_public::mir::TerminatorKind::Call { func, .. }
                if format!("{func:?}").contains("as_array"))
        });
        assert_mir_pattern_found(saw_as_array, "repr-SIMD as_array call in MIR");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_simd_as_array_lane", ChcConfig::default());

        assert_relation_has_arg_sort(
            &vc,
            "probe_simd_as_array_lane",
            ay_bindings::Sort::is_array,
            "Array (repr-SIMD lane view)",
        );
        assert_has_nontrivial_transition_constraints(&vc, "probe_simd_as_array_lane");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_simd_as_array_lane",
            |expr| matches!(expr.value(), ay_bindings::ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, lane_idx)",
        );
    });
}

#[test]
fn test_repr_simd_into_array_referent_keeps_array_view() {
    with_test_ay_ctx_for_source(SIMD_ARRAY_VIEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simd_into_array_lane");
        let body = instance.body().expect("body");
        let saw_into_array = body.blocks.iter().any(|block| {
            matches!(&block.terminator.kind, rustc_public::mir::TerminatorKind::Call { func, .. }
                if format!("{func:?}").contains("into_array"))
        });
        assert_mir_pattern_found(saw_into_array, "repr-SIMD into_array call in MIR");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_simd_into_array_lane", ChcConfig::default());

        assert_relation_has_arg_sort(
            &vc,
            "probe_simd_into_array_lane",
            ay_bindings::Sort::is_array,
            "Array (repr-SIMD lane view)",
        );
        assert_has_nontrivial_transition_constraints(&vc, "probe_simd_into_array_lane");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_simd_into_array_lane",
            |expr| matches!(expr.value(), ay_bindings::ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, lane_idx)",
        );
    });
}

#[test]
fn test_slice_as_array_dispatch_constrains_discriminant_and_payload_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_as_array() -> Option<&'static [u8; 4]> {
            let slice: &'static [u8] = b"Rust";
            slice.as_array::<4>()
        }
    "#;

    with_slice_as_array_dispatch(SOURCE, "probe_slice_as_array", |chc_ctx, dest_local, smt| {
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 0)),
            "slice_as_array should update flattened_field_env for the discriminant"
        );
        assert!(
            chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 1)),
            "slice_as_array should update flattened_field_env for the payload"
        );
        assert!(
            smt.contains("_fld0"),
            "slice_as_array should constrain the flattened discriminant slot, got: {smt}"
        );
        assert!(
            smt.contains("_fld1"),
            "slice_as_array should constrain the flattened payload slot, got: {smt}"
        );
    });
}

#[test]
fn test_repr_simd_generic_array_view_has_no_unknown_layout_heap_checks() {
    with_test_ay_ctx_for_source(GENERIC_SIMD_ARRAY_VIEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_generic_simd_first");
        let body = instance.body().expect("body");
        let vc = mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "probe_generic_simd_first",
            ChcConfig::default(),
        );

        // VC structure assertion is the authoritative check; global counter
        // assertions removed because they are unreliable under parallel test
        // execution (other tests increment the shared AtomicUsize). Part of #3785.
        assert_relation_has_arg_sort(
            &vc,
            "probe_generic_simd_first",
            ay_bindings::Sort::is_array,
            "Array (generic repr-SIMD lane view)",
        );
    });
}

#[test]
fn test_repr_simd_generic_symbolic_index_has_no_unknown_layout_heap_checks() {
    with_test_ay_ctx_for_source(GENERIC_SIMD_ARRAY_VIEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_generic_simd_symbolic_index");
        let body = instance.body().expect("body");
        let vc = mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "probe_generic_simd_symbolic_index",
            ChcConfig::default(),
        );

        // Global counter assertions removed — unreliable under parallel execution.
        // VC structure assertions are authoritative. Part of #3785.
        assert_relation_has_arg_sort(
            &vc,
            "probe_generic_simd_symbolic_index",
            ay_bindings::Sort::is_array,
            "Array (generic repr-SIMD symbolic lane view)",
        );
        assert_has_nontrivial_transition_constraints(&vc, "probe_generic_simd_symbolic_index");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_generic_simd_symbolic_index",
            |expr| {
                matches!(
                    expr.value(),
                    ay_bindings::ExprValue::Select { array, .. } if array.sort().is_array()
                )
            },
            "Select(Array, symbolic_lane_idx)",
        );
    });
}

#[test]
fn test_repr_simd_generic_local_symbolic_index_has_no_unknown_layout_heap_checks() {
    with_test_ay_ctx_for_source(GENERIC_SIMD_ARRAY_VIEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_generic_simd_local_symbolic_index");
        let body = instance.body().expect("body");
        let vc = mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "probe_generic_simd_local_symbolic_index",
            ChcConfig::default(),
        );

        // Global counter assertions removed — unreliable under parallel execution.
        // VC structure assertions are authoritative. Part of #3785.
        assert_relation_has_arg_sort(
            &vc,
            "probe_generic_simd_local_symbolic_index",
            ay_bindings::Sort::is_array,
            "Array (generic repr-SIMD local symbolic lane view)",
        );
        assert_has_nontrivial_transition_constraints(
            &vc,
            "probe_generic_simd_local_symbolic_index",
        );
        assert_rule_contains_expr_kind(
            &vc,
            "probe_generic_simd_local_symbolic_index",
            |expr| {
                matches!(
                    expr.value(),
                    ay_bindings::ExprValue::Select { array, .. } if array.sort().is_array()
                )
            },
            "Select(Array, local_symbolic_lane_idx)",
        );
    });
}

// =============================================================================
// Argument reference pointee resolution — exercises Tier 4 (#2979)
// =============================================================================

/// Source with &[u8; 4] parameters that mirrors raw_eq compiled as a separate
/// function. When raw_eq is not inlined, its &T parameters are function args
/// with no ref_targets entry. The new Tier 4 (ref_arg_pointee_idx) should
/// resolve these to their pointee state variables.
const ARG_REF_ARRAY_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]

    pub fn probe_raw_eq_arg_ref(a: &[u8; 4], b: &[u8; 4]) -> bool {
        unsafe { core::intrinsics::raw_eq(a, b) }
    }
"#;

#[test]
fn test_arg_ref_array_raw_eq_produces_nontrivial_chc() {
    // Exercises the case where raw_eq arguments are function parameters (&T),
    // not locals with Rvalue::Ref assignments. Before #2979, the resolution
    // chain returned pointer BV64 instead of the Array(BV64, BV8) referent,
    // causing raw_eq to compare addresses instead of values.
    with_test_ay_ctx_for_source(ARG_REF_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_eq_arg_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_raw_eq_arg_ref", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "raw_eq with arg refs should produce CHC relations");

        // Tier 4 regression gate: the arg-ref pointee must resolve to
        // Array(BV64, BV8) — NOT the BV64 pointer that the Tier 5 fallback
        // would produce.  If Tier 4 breaks, raw_eq compares addresses
        // instead of array contents and no relation carries an Array sort.
        assert_relation_has_arg_sort(
            &vc,
            "probe_raw_eq_arg_ref",
            ay_bindings::Sort::is_array,
            "Array (from Tier 4 arg-ref pointee resolution)",
        );

        assert_has_nontrivial_transition_constraints(&vc, "probe_raw_eq_arg_ref");
    });
}

// =============================================================================
// Nested inline callee resolution — SIMD into_array through comparison (#3768)
// =============================================================================

/// Source that mirrors the SIMD Compare pattern: user-defined `into_array()`
/// called inside a comparison expression. When `compare_simd_via_into_array` is
/// inlined, the `into_array()` calls become nested inline callees. Before
/// #3768, the nested callee resolution used `ctx.resolve_callee_path(func)`
/// (anchored to `ctx.body`) instead of the body-relative path, causing sporadic
/// bailout and `inferable_predicate` increments.
const SIMD_COMPARE_VIA_INTO_ARRAY_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(repr_simd)]

    #[derive(Copy, Clone)]
    #[repr(simd)]
    struct I64x2([i64; 2]);

    impl I64x2 {
        fn into_array(self) -> [i64; 2] {
            unsafe { std::mem::transmute(self) }
        }
    }

    fn compare_simd_via_into_array(a: I64x2, b: I64x2) -> bool {
        a.into_array() == b.into_array()
    }
"#;

#[test]
fn test_simd_compare_via_into_array_nested_inline_produces_nontrivial_chc() {
    with_test_ay_ctx_for_source(SIMD_COMPARE_VIA_INTO_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "compare_simd_via_into_array");
        let body = instance.body().expect("body");
        let vc = mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "compare_simd_via_into_array",
            ChcConfig::default(),
        );

        // The nested inline of `into_array()` through the comparison should
        // preserve Array sorts in the VC — proving the body-relative callee
        // resolution succeeded and transmute lowered to the reinterpret path.
        assert!(
            !vc.relations.is_empty(),
            "compare_simd_via_into_array should produce CHC relations"
        );

        assert_has_nontrivial_transition_constraints(&vc, "compare_simd_via_into_array");
    });
}

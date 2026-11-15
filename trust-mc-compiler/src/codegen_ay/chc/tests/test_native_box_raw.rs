// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native BoxRaw representation and identical-looking user types.

use super::common::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::shared::native_box_raw::native_thin_box_raw_pointer_field;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::{Rvalue, StatementKind};
use rustc_public::ty::{AdtDef, GenericArgs, Ty};
use std::collections::HashMap;

pub(super) const SOURCE: &str = r#"
    #![allow(dead_code)]
    use core::marker::PhantomData;
    use core::ptr::NonNull;
    #[repr(transparent)]
    pub struct BoxRaw<T> { pub pointer: NonNull<T>, pub marker: PhantomData<T> }
    #[repr(align(64))]
    pub struct AlignedZst;
    pub enum Empty {}
    pub struct ContainsEmptyRef { pub impossible: &'static Empty }
    pub fn arguments(a: Box<u8>, b: Box<i128>, wide: Box<[u8]>, fake: BoxRaw<u8>,
        word: Box<u32>, zst: Box<AlignedZst>, empty: Box<Empty>,
        reference: Box<&'static Empty>, compound: Box<ContainsEmptyRef>) {}
    pub fn construct(pointer: NonNull<u8>, marker: PhantomData<u8>) -> BoxRaw<u8> {
        BoxRaw { pointer, marker }
    }
    pub fn deref_box(value: &Box<u8>) -> *const u8 { &raw const **value }
    pub fn pointer_identity(value: *const u8) -> *const u8 { value }
    pub fn pointer_arguments(byte: *const u8, word: *const u32,
        zst: *const AlignedZst, empty: *const Empty,
        reference: *const &'static Empty, compound: *const ContainsEmptyRef) {}
    pub fn allocate_word() -> Box<u32> { Box::new(7) }
    pub fn allocate_repeated(mut count: usize) {
        while count > 0 {
            core::mem::forget(Box::new(7u32));
            count -= 1;
        }
    }
    pub fn allocate_layout(layout: core::alloc::Layout) -> *mut u8 {
        unsafe { std::alloc::alloc(layout) }
    }
    fn raw_identity(pointer: *const u64) -> *const u64 { pointer }
    pub fn reference_after_helper(value: Box<u64>) -> &'static u64 {
        let pointer = &raw const *value;
        let returned = raw_identity(pointer);
        let reference: &'static u64 = unsafe { core::mem::transmute(returned) };
        core::mem::forget(value);
        reference
    }
    pub fn deref_owned(value: Box<u8>) -> *const u8 {
        let pointer = &raw const *value;
        core::mem::forget(value);
        pointer
    }
"#;

fn adt(ty: Ty) -> (AdtDef, GenericArgs) {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
        panic!("expected ADT: {ty:?}");
    };
    (def, args)
}

pub(super) fn carrier(boxed: Ty) -> Ty {
    let (def, args) = adt(boxed);
    assert!(def.is_box());
    mono_ty::field_ty(&def.variants()[0].fields()[0], &args).unwrap()
}

#[test]
fn native_box_raw_thin_carriers_share_the_actual_pointer_representation() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let signature = fn_sig_by_suffix(ctx.tcx, "arguments");
        for (boxed, key) in signature.inputs()[..2].iter().zip(["ptr_u8", "ptr_i128"]) {
            let ty = carrier(*boxed);
            let (def, args) = adt(ty);
            let (_, field_ty) = native_thin_box_raw_pointer_field(ctx.tcx, def, &args)
                .expect("held compiler's authenticated thin BoxRaw carrier");
            assert_eq!(ChcCtx::translate_ty(ty), ChcCtx::translate_ty(field_ty));
            assert_eq!(ChcCtx::type_key_for_ty(ty), key);
            assert_eq!(ChcCtx::type_key_for_ty(*boxed), key);
            assert!(ChcCtx::value_is_address(ty));
        }
        let fat = carrier(signature.inputs()[2]);
        let (def, args) = adt(fat);
        assert!(native_thin_box_raw_pointer_field(ctx.tcx, def, &args).is_none());
        let fake = signature.inputs()[3];
        let (def, args) = adt(fake);
        assert!(native_thin_box_raw_pointer_field(ctx.tcx, def, &args).is_none());
        assert!(ChcCtx::translate_ty(fake).unwrap().is_datatype());
        assert_ne!(ChcCtx::type_key_for_ty(fake), "ptr_u8");
    });
}

#[test]
fn native_box_raw_aggregate_keeps_its_pointer_without_coercion() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let native = carrier(fn_sig_by_suffix(ctx.tcx, "arguments").inputs()[0]);
        let (native_def, native_args) = adt(native);
        let (index, _) =
            native_thin_box_raw_pointer_field(ctx.tcx, native_def, &native_args).unwrap();
        let body = find_instance_by_suffix(ctx.tcx, "construct").callee_body().unwrap();
        let (destination, original_kind, operands) = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(place, Rvalue::Aggregate(kind, operands))
                    if matches!(kind, AggregateKind::Adt(..)) =>
                {
                    Some((place, kind, operands))
                }
                _ => None,
            })
            .expect("fixture aggregate");
        let mut kind = original_kind.clone();
        let AggregateKind::Adt(def, _, args, _, _) = &mut kind else { unreachable!() };
        *def = native_def;
        *args = native_args;
        let mut locals = body.locals().to_vec();
        locals[destination.local].ty = native;
        let mut chc = ChcCtx::new(ctx.tcx, &body, "construct", ChcConfig::default());
        let pointer = Expr::bitvec_const(0x300000004u64, 64);
        let values = HashMap::from([(1, pointer.clone()), (2, Expr::bool_const(true))]);
        let fields = HashMap::new();
        let rvalue = Rvalue::Aggregate(kind.clone(), operands.clone());
        let translated = crate::codegen_ay::chc::call::inline_shared::inline_rvalue_to_expr(
            &mut chc,
            &rvalue,
            &values,
            &PlaceResolver::FieldMap(&fields),
            &locals,
            Some(destination.local),
        );
        assert_eq!(translated, Some(pointer));
        let malformed =
            HashMap::from([(1, Expr::bitvec_const(4u8, 8)), (2, Expr::bool_const(true))]);
        assert!(
            crate::codegen_ay::chc::call::inline_shared::inline_rvalue_to_expr(
                &mut chc,
                &rvalue,
                &malformed,
                &PlaceResolver::FieldMap(&fields),
                &locals,
                Some(destination.local),
            )
            .is_none(),
            "an element value cannot be widened into a pointer"
        );
        assert_eq!(index, 0, "the held layout's actual non-ZST field");
    });
}

#[cfg(all(trust_toolchain, version("1.101")))]
#[test]
fn inline_box_deref_cannot_pass_through_the_value_only_cast_api() {
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    use rustc_public::mir::CastKind;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let actual = find_instance_by_suffix(ctx.tcx, "deref_box").callee_body().unwrap();
        assert!(
            actual.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
                matches!(
                    statement.kind,
                    StatementKind::Assign(_, Rvalue::Cast(CastKind::BoxDerefTransmute, ..))
                )
            }),
            "the held compiler really emits the cast carrying the extra UB obligation"
        );

        let native = carrier(fn_sig_by_suffix(ctx.tcx, "arguments").inputs()[0]);
        let body = find_instance_by_suffix(ctx.tcx, "pointer_identity").callee_body().unwrap();
        let mut locals = body.locals().to_vec();
        locals[1].ty = native;
        let operand = Operand::Copy(Place { local: 1, projection: Vec::new() });
        let fields = HashMap::new();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_identity", ChcConfig::default());
        let translate = |chc: &mut ChcCtx<'_, '_>, kind, pointer: Expr| {
            crate::codegen_ay::chc::call::inline_shared::inline_rvalue_to_expr(
                chc,
                &Rvalue::Cast(kind, operand.clone(), locals[0].ty),
                &HashMap::from([(1, pointer)]),
                &PlaceResolver::FieldMap(&fields),
                &locals,
                Some(0),
            )
        };
        for bits in [0u64, 1, 0x300000004] {
            let pointer = Expr::bitvec_const(bits, 64);
            assert_eq!(
                translate(&mut chc, CastKind::PtrToPtr, pointer.clone()),
                Some(pointer.clone()),
                "the operand and target actually translate without the Box obligation"
            );
            let before = chc.diagnostics.place_translation_drop.get();
            assert!(translate(&mut chc, CastKind::BoxDerefTransmute, pointer).is_none());
            assert_eq!(chc.diagnostics.place_translation_drop.get(), before + 1);
        }
        assert_eq!(
            fallback_soundness("box_deref_validity_unmodeled"),
            FallbackSoundness::FailClose,
            "dropping the validity obligation must prevent a clean proof or certificate"
        );
    });
}

/// Check the actual returned MUST-HOLD conditions with AY, including the
/// full-extent and liveness cases that a value-preserving cast loses.
#[test]
fn checked_box_deref_requires_live_aligned_full_extent_and_handles_zsts() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let boxes = fn_sig_by_suffix(ctx.tcx, "arguments");
        let pointers = fn_sig_by_suffix(ctx.tcx, "pointer_arguments");
        let body = find_instance_by_suffix(ctx.tcx, "pointer_identity").callee_body().unwrap();
        for (offset, extent, live, expected) in [
            (0u32, 4u32, true, "unsat"),
            (0, 3, true, "sat"),
            (0, 0, true, "sat"),
            (0, 4, false, "sat"),
            (1, 8, true, "sat"),
            (u32::MAX, u32::MAX, true, "sat"),
        ] {
            let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_identity", ChcConfig::default());
            let id = chc.heap_state.next_heap_alloc_id().unwrap();
            chc.heap_state.record_heap_alloc_size(id, extent);
            chc.heap_state.record_heap_alloc_alignment(id, Some(4));
            let pointer = Expr::bitvec_const((u64::from(id) << 32) | u64::from(offset), 64);
            let checked = chc
                .checked_native_box_deref(
                    carrier(boxes.inputs()[4]),
                    pointers.inputs()[1],
                    pointer.clone(),
                )
                .expect("known native carrier and allocator alignment");
            assert_eq!(checked.value, pointer);
            let condition = checked.checks.into_iter().reduce(Expr::and).unwrap();
            let smt = format!(
                "(set-logic QF_AUFBV)\n\
                 (declare-const obj_valid (Array (_ BitVec 32) Bool))\n\
                 (declare-const obj_size (Array (_ BitVec 32) (_ BitVec 32)))\n\
                 (assert (= obj_valid ((as const (Array (_ BitVec 32) Bool)) {live})))\n\
                 (assert (= obj_size ((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv{extent} 32))))\n\
                 (assert (not {condition}))\n(check-sat)"
            );
            assert_z3_result(&smt, expected);
        }
        for (box_index, pointer_index, address, expected) in [
            (0usize, 0usize, 0u64, false),
            (5, 2, 64, true),
            (5, 2, 1, false),
            (5, 2, 0, false),
            (6, 3, 1, false),
        ] {
            let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_identity", ChcConfig::default());
            let checked = chc
                .checked_native_box_deref(
                    carrier(boxes.inputs()[box_index]),
                    pointers.inputs()[pointer_index],
                    Expr::bitvec_const(address, 64),
                )
                .expect("null and object-free ZST validity can be checked directly");
            let condition = checked.checks.into_iter().reduce(Expr::and).unwrap();
            assert_z3_result(
                &format!("(set-logic QF_BV)\n(assert (not {condition}))\n(check-sat)"),
                if expected { "unsat" } else { "sat" },
            );
        }
    });
}

#[test]
fn checked_box_deref_refuses_unowned_or_under_aligned_bases_and_wrong_types() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let boxes = fn_sig_by_suffix(ctx.tcx, "arguments");
        let pointers = fn_sig_by_suffix(ctx.tcx, "pointer_arguments");
        let body = find_instance_by_suffix(ctx.tcx, "pointer_identity").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_identity", ChcConfig::default());
        let id = chc.heap_state.next_heap_alloc_id().unwrap();
        chc.heap_state.record_heap_alloc_size(id, 4);
        let pointer = Expr::bitvec_const(u64::from(id) << 32, 64);
        let native = carrier(boxes.inputs()[4]);
        assert!(
            chc.checked_native_box_deref(native, pointers.inputs()[1], pointer.clone()).is_none()
        );
        chc.heap_state.record_heap_alloc_alignment(id, Some(1));
        assert!(
            chc.checked_native_box_deref(native, pointers.inputs()[1], pointer.clone()).is_none()
        );
        assert!(
            chc.checked_native_box_deref(boxes.inputs()[3], pointers.inputs()[0], pointer.clone())
                .is_none()
        );
        assert!(
            chc.checked_native_box_deref(
                carrier(boxes.inputs()[2]),
                pointers.inputs()[0],
                pointer.clone()
            )
            .is_none()
        );
        assert!(
            chc.checked_native_box_deref(
                carrier(boxes.inputs()[0]),
                pointers.inputs()[1],
                pointer.clone()
            )
            .is_none()
        );
        assert!(
            chc.checked_native_box_deref(native, pointers.inputs()[1], Expr::bitvec_const(1u8, 8))
                .is_none()
        );
    });
}

#[test]
fn native_box_allocator_alignment_is_actual_monotone_and_rollback_scoped() {
    use rustc_public::mir::TerminatorKind;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "allocate_word").callee_body().unwrap();
        let (func, args) = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, .. } => Some((func, args)),
                _ => None,
            })
            .expect("real Box::new call");
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(body.locals()).unwrap().kind() else {
            panic!("native Box constructor must be direct");
        };
        assert!(def.name().contains("boxed::Box") && def.name().ends_with("::new"));
        let mut chc = ChcCtx::new(ctx.tcx, &body, "allocate_word", ChcConfig::default());
        let allocated = chc.translate_alloc_call(StubKind::BoxNew, args, &HashSet::new()).unwrap();
        let id = allocated.alloc_obj_id.unwrap();
        assert_eq!(chc.heap_state.heap_alloc_size(id), Some(4));
        assert_eq!(chc.heap_state.heap_alloc_alignment(id), Some(4));
        let snapshot = chc.heap_state.snapshot_transient_rule_state();
        chc.heap_state.record_heap_alloc_alignment(id, None);
        assert_eq!(chc.heap_state.heap_alloc_alignment(id), None);
        chc.heap_state.restore_transient_rule_state(&snapshot);
        assert_eq!(chc.heap_state.heap_alloc_alignment(id), Some(4));
        chc.heap_state.record_heap_alloc_alignment(id, Some(1));
        chc.heap_state.record_heap_alloc_alignment(id, Some(64));
        assert_eq!(chc.heap_state.heap_alloc_alignment(id), Some(1));
        chc.heap_state.record_heap_alloc_alignment(id, None);
        chc.heap_state.record_heap_alloc_alignment(id, Some(64));
        assert_eq!(chc.heap_state.heap_alloc_alignment(id), None);
    });
}

#[test]
fn native_inline_box_cast_carries_its_checks_with_its_value() {
    use crate::codegen_ay::chc::call::inline_body::translate_inline_body;
    use trust_mc_core::violation::PropertyKind;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_owned");
        let body = instance.callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "deref_owned", ChcConfig::default());
        let id = chc.heap_state.next_heap_alloc_id().unwrap();
        chc.heap_state.record_heap_alloc_alignment(id, Some(1));
        chc.heap_state.record_heap_alloc_size(id, 1);
        let pointer = Expr::bitvec_const(u64::from(id) << 32, 64);
        let result = translate_inline_body(
            &mut chc,
            &body,
            &[pointer.clone()],
            0,
            &HashMap::new(),
            Some(instance),
            0,
        )
        .expect("real owned Box dereference body");
        assert_eq!(result.value, pointer);
        assert!(!result.deferred_checks.is_empty(), "returning pointer bits alone drops UB checks");
        assert!(
            result.deferred_checks.iter().all(|check| check.kind == PropertyKind::MemorySafety)
        );
        assert!(
            result
                .deferred_checks
                .iter()
                .any(|check| check.check.to_string().contains("obj_valid"))
        );
        assert!(
            result.deferred_checks.iter().any(|check| check.check.to_string().contains("obj_size"))
        );
    });
}

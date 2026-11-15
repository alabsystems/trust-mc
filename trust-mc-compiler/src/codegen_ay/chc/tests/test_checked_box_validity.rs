// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Adversarial native Box validity and event-time transport controls.

use super::common::*;
use super::test_native_box_raw::{SOURCE, carrier};
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::call::inline_body::translate_inline_body;
use crate::codegen_ay::chc::expr::codegen_expr_heap::{obj_size_in, obj_size_out};
use rustc_public::mir::TerminatorKind;
use std::collections::HashMap;

#[test]
fn native_box_free_requires_exact_current_extent_not_just_a_readable_pointee() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let native = carrier(fn_sig_by_suffix(ctx.tcx, "arguments").inputs()[4]);
        let target = fn_sig_by_suffix(ctx.tcx, "pointer_arguments").inputs()[1];
        let body = find_instance_by_suffix(ctx.tcx, "pointer_identity").callee_body().unwrap();
        for (extent, expected) in [(3u32, "sat"), (4, "unsat"), (8, "sat")] {
            let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_identity", ChcConfig::default());
            let id = chc.heap_state.next_heap_alloc_id().unwrap();
            chc.heap_state.record_heap_alloc_alignment(id, Some(4));
            let checked = chc
                .checked_native_box_deallocation(
                    native,
                    target,
                    Expr::bitvec_const(u64::from(id) << 32, 64),
                )
                .unwrap();
            let condition = checked.checks.into_iter().reduce(Expr::and).unwrap();
            let smt = format!(
                "(set-logic QF_AUFBV)\n\
                 (declare-const obj_valid (Array (_ BitVec 32) Bool))\n\
                 (declare-const obj_size (Array (_ BitVec 32) (_ BitVec 32)))\n\
                 (assert (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true)))\n\
                 (assert (= obj_size ((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv{extent} 32))))\n\
                 (assert (not {condition}))\n(check-sat)"
            );
            assert_z3_result(&smt, expected);
        }
    });
}

#[test]
fn repeated_allocation_ids_do_not_grant_new_box_alignment_authority() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, expected) in [("allocate_word", Some(4)), ("allocate_repeated", None)] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (bb, args) = body
                .blocks
                .iter()
                .enumerate()
                .find_map(|(bb, block)| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, .. } => {
                        let ty = func.ty(body.locals()).ok()?;
                        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind() else {
                            return None;
                        };
                        let def = rustc_internal::internal(ctx.tcx, def.def_id());
                        ctx.tcx
                            .is_diagnostic_item(rustc_span::sym::box_new, def)
                            .then_some((bb, args))
                    }
                    _ => None,
                })
                .expect("actual native Box::new allocation");
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.current_encode_bb = bb;
            let result = chc.translate_alloc_call(StubKind::BoxNew, args, &HashSet::new()).unwrap();
            assert_eq!(chc.heap_state.heap_alloc_alignment(result.alloc_obj_id.unwrap()), expected);
        }
    });
}

#[test]
fn legacy_layout_cache_cannot_grant_box_alignment_authority() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "allocate_layout").callee_body().unwrap();
        let args = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { args, .. } => Some(args),
                _ => None,
            })
            .expect("native alloc(Layout) call");
        assert_eq!(args.len(), 1);
        let Operand::Copy(place) = &args[0] else { panic!("actual symbolic Layout argument") };
        let mut chc = ChcCtx::new(ctx.tcx, &body, "allocate_layout", ChcConfig::default());
        // This legacy precision cache is not proof that an actual caller
        // supplies this alignment. The new authority must stay unknown.
        chc.known_layout_sizes.insert(place.local, (16, 64));
        let result = chc.translate_alloc_call(StubKind::RustAlloc, args, &HashSet::new()).unwrap();
        assert_eq!(chc.heap_state.heap_alloc_alignment(result.alloc_obj_id.unwrap()), None);
    });
}

#[test]
fn box_cast_checks_keep_the_metadata_at_the_cast_before_a_later_free() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let native = carrier(fn_sig_by_suffix(ctx.tcx, "arguments").inputs()[0]);
        let target = fn_sig_by_suffix(ctx.tcx, "pointer_arguments").inputs()[0];
        let body = find_instance_by_suffix(ctx.tcx, "pointer_identity").callee_body().unwrap();
        for freed_before in [false, true] {
            let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_identity", ChcConfig::default());
            let first = chc.heap_state.next_heap_alloc_id().unwrap();
            let second = chc.heap_state.next_heap_alloc_id().unwrap();
            chc.heap_state.record_heap_alloc_size(second, 1);
            chc.heap_state.record_heap_alloc_alignment(second, Some(1));
            let object = Expr::bitvec_const(second, 32);
            chc.push_pending_obj_valid_invalidation(Expr::bitvec_const(
                if freed_before { second } else { first },
                32,
            ));
            chc.heap_state.pending_updates.push(
                obj_size_out()
                    .eq(obj_size_in().store(object.clone(), Expr::bitvec_const(1u32, 32))),
            );
            chc.mark_obj_size_modified();
            let checked = chc
                .checked_native_box_deref(
                    native,
                    target,
                    Expr::bitvec_const(u64::from(second) << 32, 64),
                )
                .expect("single known metadata chain at the cast");
            // Both metadata outputs now change, after the cast's checks have
            // been captured. This must not change the earlier obligations.
            chc.push_pending_obj_valid_invalidation(object.clone());
            let size_update = chc.heap_state.pending_updates.iter_mut().find(|update| {
                matches!(update.value(), ExprValue::Eq(left, _) if *left == obj_size_out())
            }).unwrap();
            *size_update =
                obj_size_out().eq(obj_size_in().store(object, Expr::bitvec_const(0u32, 32)));
            let condition = checked.checks.into_iter().reduce(Expr::and).unwrap();
            assert!(!condition.to_string().contains("__out"));
            let smt = format!(
                "(set-logic QF_AUFBV)\n\
                 (declare-const obj_valid (Array (_ BitVec 32) Bool))\n\
                 (declare-const obj_size (Array (_ BitVec 32) (_ BitVec 32)))\n\
                 (assert (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true)))\n\
                 (assert (= obj_size ((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv1 32))))\n\
                 (assert (not {condition}))\n(check-sat)"
            );
            assert_z3_result(&smt, if freed_before { "sat" } else { "unsat" });
        }
    });
}

#[test]
fn pointer_sized_impossible_pointees_have_no_valid_box_pointer() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let boxes = fn_sig_by_suffix(ctx.tcx, "arguments");
        let pointers = fn_sig_by_suffix(ctx.tcx, "pointer_arguments");
        let body = find_instance_by_suffix(ctx.tcx, "pointer_identity").callee_body().unwrap();
        for (box_index, pointer_index) in [(7usize, 4usize), (8, 5)] {
            let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_identity", ChcConfig::default());
            let id = chc.heap_state.next_heap_alloc_id().unwrap();
            chc.heap_state.record_heap_alloc_size(id, 8);
            chc.heap_state.record_heap_alloc_alignment(id, Some(8));
            let checked = chc
                .checked_native_box_deref(
                    carrier(boxes.inputs()[box_index]),
                    pointers.inputs()[pointer_index],
                    Expr::bitvec_const(u64::from(id) << 32, 64),
                )
                .expect("native pointer-sized pointee layout");
            assert!(
                checked
                    .checks
                    .iter()
                    .any(|check| matches!(check.value(), ExprValue::BoolConst(false))),
                "a reference to Never is impossible even though its layout is pointer sized"
            );
        }
    });
}

#[test]
fn box_address_survives_raw_parameter_return_and_reference_transmute() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "reference_after_helper");
        let body = instance.callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "reference_after_helper", ChcConfig::default());
        let id = chc.heap_state.next_heap_alloc_id().unwrap();
        chc.heap_state.record_heap_alloc_size(id, 8);
        chc.heap_state.record_heap_alloc_alignment(id, Some(8));
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
        .expect("actual Box/raw-pointer/helper/reference path");
        assert_eq!(result.value, pointer);
        assert!(
            chc.inline_walk_returned_address,
            "the returned reference holds an address, never a matching-width u64 referent"
        );
        assert!(!result.deferred_checks.is_empty(), "native Box checks must survive helper calls");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real native coercions, metadata refusals, and mutable carrier invalidation.

use super::common::*;
use super::test_native_box_raw::carrier;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::call::native_dyn_origin::NativeDynOrigin;
use rustc_public::mir::{Body, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::Ty;

pub(super) const SOURCE: &str = r#"
    #![allow(dead_code, unused_variables, unused_assignments)]
    fn invoke(mut f: Box<dyn FnMut(&mut i32)>, value: &mut i32) { f(value) }
    fn add(value: &mut i32) { *value = value.wrapping_add(1) }
    fn subtract(value: &mut i32) { *value = value.wrapping_sub(1) }
    pub fn native_safe() {
        let mut value = 1i32;
        invoke(Box::new(&add), &mut value);
        assert!(value == 2);
    }
    pub fn native_bug() {
        let mut value = 1i32;
        invoke(Box::new(&add), &mut value);
        assert!(value == 1);
    }
    pub fn second_safe() {
        let decoy: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        core::mem::forget(decoy);
        let mut value = 1i32;
        invoke(Box::new(&subtract), &mut value);
        assert!(value == 0);
    }
    pub fn second_bug() {
        let decoy: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        core::mem::forget(decoy);
        let mut value = 1i32;
        invoke(Box::new(&subtract), &mut value);
        assert!(value == 2);
    }
    pub fn copy_carrier(value: Box<dyn FnMut(&mut i32)>) -> Box<dyn FnMut(&mut i32)> { value }
    pub fn borrowed_carrier(value: &mut Box<dyn FnMut(&mut i32)>) {}
    pub fn other_dynamic(value: Box<dyn FnMut(&mut i64)>) {}
    pub fn cyclic_birth(count: usize) {
        let mut value = 1i32;
        for _ in 0..count { invoke(Box::new(&add), &mut value); }
    }
    fn replace(value: &mut Box<dyn FnMut(&mut i32)>) { *value = Box::new(&subtract); }
    fn replaced(mut f: Box<dyn FnMut(&mut i32)>, value: &mut i32) {
        replace(&mut f);
        f(value);
    }
    pub fn replaced_bug() {
        let mut value = 1i32;
        replaced(Box::new(&add), &mut value);
        assert!(value == 2);
    }
    fn corrupt_payload(mut f: Box<dyn FnMut(&mut i32)>, value: &mut i32) {
        let pointer = &raw mut *f;
        unsafe { (pointer as *mut u8).write(0); }
        f(value);
    }
    pub fn corrupt_bug() {
        let mut value = 1i32;
        corrupt_payload(Box::new(&add), &mut value);
        assert!(value == 2);
    }
    pub fn missing_metadata_bug() {
        let mut value = 1i32;
        let malformed: *mut dyn FnMut(&mut i32) = unsafe { core::mem::transmute((1usize, 0usize)) };
        invoke(unsafe { Box::from_raw(malformed) }, &mut value);
        assert!(value == 2);
    }
    pub fn roundtrip_safe() {
        let mut value = 1i32;
        let boxed: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        let pointer = Box::into_raw(boxed);
        invoke(unsafe { Box::from_raw(pointer) }, &mut value);
        assert!(value == 2);
    }
    fn relay<T>(value: T) -> T { value }
    pub fn runtime_payload_safe() {
        let mut value = 1i32;
        let reference = relay(&add);
        invoke(Box::new(reference), &mut value);
        assert!(value == 2);
    }
    fn native_words(value: &Box<dyn FnMut(&mut i32)>) -> (usize, usize) {
        assert!(core::mem::size_of_val(value) == core::mem::size_of::<(usize, usize)>());
        unsafe { core::mem::transmute_copy(value) }
    }
    pub fn raw_words_safe() {
        let value: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        let words = native_words(&value);
        core::mem::forget(value);
        assert!(words.0 != 0 && words.1 != 0);
    }
    pub fn raw_words_bug() {
        let value: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        let words = native_words(&value);
        core::mem::forget(value);
        assert!(words.0 == 0 || words.1 == 0);
    }
    pub fn transmute_words_safe() {
        let value: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        let bits: u128 = unsafe { core::mem::transmute(value) };
        assert!(bits as u64 != 0 && (bits >> 64) as u64 != 0);
    }
    pub fn transmute_words_bug() {
        let value: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        let bits: u128 = unsafe { core::mem::transmute(value) };
        assert!(bits as u64 == 0 || (bits >> 64) as u64 == 0);
    }
    fn as_native_bits(value: Box<dyn FnMut(&mut i32)>) -> u128 {
        unsafe { core::mem::transmute(value) }
    }
    pub fn transmute_inline_safe() {
        let value: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        let bits = as_native_bits(value);
        assert!(bits as u64 != 0 && (bits >> 64) as u64 != 0);
    }
    pub fn transmute_inline_bug() {
        let value: Box<dyn FnMut(&mut i32)> = Box::new(&add);
        let bits = as_native_bits(value);
        assert!(bits as u64 == 0 || (bits >> 64) as u64 == 0);
    }
    fn panic_body(value: &mut i32) { assert!(*value < 1); }
    pub fn panic_call_bug() {
        let mut value = 1i32;
        invoke(Box::new(&panic_body), &mut value);
    }
"#;

/// Execute the real native allocator stub for the compiler's actual callsite.
/// Its next-rule input metadata is supplied explicitly by each AY obligation.
fn actual_origin(chc: &mut ChcCtx<'_, '_>) -> (NativeDynOrigin, Ty) {
    let calls: Vec<_> = chc
        .body
        .blocks
        .iter()
        .enumerate()
        .filter_map(|(block, body)| match &body.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. }
                if chc.detect_stub(func) == Some(StubKind::BoxNew) =>
            {
                Some((block, args.clone(), destination.local))
            }
            _ => None,
        })
        .collect();
    for (block, args, destination) in calls {
        chc.current_encode_bb = block;
        chc.heap_state.encode_bb = block;
        let result = chc.translate_alloc_call(StubKind::BoxNew, &args, &HashSet::new()).unwrap();
        chc.record_alloc_dest(destination, result.alloc_obj_id);
        chc.heap_state.reset_modified_arrays();
    }
    let local = chc
        .body
        .blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(
                place,
                Rvalue::Cast(
                    rustc_public::mir::CastKind::PointerCoercion(
                        rustc_public::mir::PointerCoercion::Unsize,
                    ),
                    _,
                    _,
                ),
            ) if place.projection.is_empty() => Some(place.local),
            _ => None,
        })
        .expect("actual native Box coercion");
    let origin = chc
        .host_native_dyn_origin(&Operand::Copy(Place { local, projection: vec![] }))
        .expect("actual authenticated native BoxNew + Unsize origin");
    (origin, chc.body.locals()[local].ty)
}

fn pointer(origin: &NativeDynOrigin) -> Expr {
    Expr::bitvec_const(u64::from(origin.allocation) << 32, 64)
}

#[test]
fn native_fat_box_cast_requires_exact_typed_coercion_metadata() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "native_safe").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "native_safe", ChcConfig::default());
        let (origin, boxed) = actual_origin(&mut chc);
        assert!(origin.constant_callable, "native promoted function-item constant");
        let raw = Ty::from_rigid_kind(RigidTy::RawPtr(
            origin.dynamic,
            rustc_public::mir::Mutability::Mut,
        ));
        let source = carrier(boxed);
        let value = pointer(&origin);
        assert!(
            chc.checked_native_box_deref_with_origin(source, raw, value.clone(), Some(&origin))
                .is_some()
        );
        assert!(
            chc.checked_native_box_deref_with_origin(source, raw, value.clone(), None).is_none()
        );
        assert!(
            chc.checked_native_box_deref(source, raw, value.clone()).is_none(),
            "thin-only API cannot drop metadata"
        );
        for malformed in [
            Expr::bitvec_const(0u64, 64),
            value.clone().bvadd(Expr::bitvec_const(1u64, 64)),
            Expr::bitvec_const(0u128, 128),
        ] {
            assert!(
                chc.checked_native_box_deref_with_origin(source, raw, malformed, Some(&origin))
                    .is_none()
            );
        }
        let mut wrong = origin.clone();
        wrong.vtable = wrong.vtable.wrapping_add(1);
        assert!(
            chc.checked_native_box_deref_with_origin(source, raw, value.clone(), Some(&wrong))
                .is_none()
        );
        let other = fn_sig_by_suffix(ctx.tcx, "other_dynamic").inputs()[0];
        assert!(
            chc.checked_native_box_deref_with_origin(
                carrier(other),
                raw,
                value.clone(),
                Some(&origin)
            )
            .is_none()
        );
        assert!(!chc.native_dyn_origin_matches(&origin, other));
        chc.heap_state.record_heap_alloc_alignment(origin.allocation, None);
        assert!(
            chc.checked_native_box_deref_with_origin(source, raw, value, Some(&origin)).is_none()
        );
    });
}

#[test]
fn native_fat_box_checks_freeze_liveness_and_full_extent_at_the_cast() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "native_safe").callee_body().unwrap();
        for (live, short, expected) in
            [(true, false, "unsat"), (false, false, "sat"), (true, true, "sat")]
        {
            let mut chc = ChcCtx::new(ctx.tcx, &body, "native_safe", ChcConfig::default());
            let (origin, _) = actual_origin(&mut chc);
            let size = chc.get_type_size(origin.concrete).unwrap();
            assert!(size > 0, "the admitted reference payload occupies real bytes");
            let checked = chc.checked_native_dyn_pointer(pointer(&origin), &origin).unwrap();
            // Free after capturing the obligation cannot retroactively turn an
            // earlier valid cast into a failure, or erase an earlier failure.
            chc.push_pending_obj_valid_invalidation(Expr::bitvec_const(origin.allocation, 32));
            let after_free = chc
                .checked_native_dyn_pointer(pointer(&origin), &origin)
                .expect("call-time validation sees the current freed metadata");
            let after_free_condition = after_free.checks.into_iter().reduce(Expr::and).unwrap();
            let condition = checked.checks.into_iter().reduce(Expr::and).unwrap();
            assert!(!condition.to_string().contains("__out"));
            let extent = size - usize::from(short);
            let smt = format!(
                "(set-logic QF_AUFBV)\n\
                (declare-const obj_valid (Array (_ BitVec 32) Bool))\n\
                (declare-const obj_size (Array (_ BitVec 32) (_ BitVec 32)))\n\
                (assert (= obj_valid ((as const (Array (_ BitVec 32) Bool)) {live})))\n\
                (assert (= obj_size ((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv{extent} 32))))\n\
                (assert (not {condition}))\n(check-sat)"
            );
            assert_z3_result(&smt, expected);
            assert_z3_result(
                &smt.replace(
                    &format!("(not {condition})"),
                    &format!("(not {after_free_condition})"),
                ),
                "sat",
            );
        }
    });
}

#[test]
fn native_fat_box_cyclic_birth_cannot_reuse_a_static_allocation_generation() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "cyclic_birth").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "cyclic_birth", ChcConfig::default());
        let (origin, _) = actual_origin(&mut chc);
        assert!(chc.checked_native_dyn_pointer(pointer(&origin), &origin).is_none());
    });
}

#[test]
fn native_fat_box_carrier_aliases_and_unknown_writes_revoke_all_frames() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "native_safe").callee_body().unwrap();
        let copy = find_instance_by_suffix(ctx.tcx, "copy_carrier").callee_body().unwrap();
        let borrowed = find_instance_by_suffix(ctx.tcx, "borrowed_carrier").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "native_safe", ChcConfig::default());
        let (origin, _) = actual_origin(&mut chc);
        let arg = Operand::Copy(Place { local: 1, projection: vec![] });
        for write in 0..3 {
            chc.inline_walk_param_native_dyn_seeds = Some(vec![(1, origin.clone())]);
            chc.with_inline_walk_frame(&copy, |chc| {
                assert_eq!(chc.inline_native_dyn_origin(&arg, copy.locals()), Some(origin.clone()));
                let rhs = copy
                    .blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .find_map(|statement| match &statement.kind {
                        StatementKind::Assign(place, rhs) if place.local == 0 => Some(rhs),
                        _ => None,
                    })
                    .unwrap();
                assert_eq!(
                    chc.note_native_dyn_assignment(&copy, 0, Some(rhs)),
                    Some(origin.clone())
                );
                // A proven distinct allocation does not invalidate this payload.
                chc.note_native_dyn_memory_write(&Expr::bitvec_const(
                    (u64::from(origin.allocation) + 1) << 32,
                    64,
                ));
                assert!(chc.inline_native_dyn_origin(&arg, copy.locals()).is_some());
                chc.inline_walk_param_native_dyn_seeds = Some(vec![(1, origin.clone())]);
                chc.with_inline_walk_frame(&borrowed, |chc| match write {
                    0 => chc.native_dyn_carrier_write(
                        borrowed.locals(),
                        &Place { local: 1, projection: vec![ProjectionElem::Deref] },
                    ),
                    1 => chc.note_native_dyn_memory_write(&pointer(&origin)),
                    _ => chc.note_native_dyn_memory_write(&Expr::var(
                        "unknown_pointer",
                        ay_bindings::Sort::bitvec(64),
                    )),
                });
                assert!(
                    chc.inline_native_dyn_origin(&arg, copy.locals()).is_none(),
                    "inner mutation must revoke outer copies"
                );
                assert!(
                    chc.set_native_dyn_binding(copy.locals(), 1, Some(origin.clone())).is_none(),
                    "a later speculative known branch cannot resurrect authority"
                );
            });
        }
        assert!(chc.diagnostics.place_translation_drop.get() > 0);
    });
}

#[test]
fn native_fat_box_reused_call_destinations_cannot_retain_metadata() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "native_safe").callee_body().unwrap();
        let copy = find_instance_by_suffix(ctx.tcx, "copy_carrier").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "native_safe", ChcConfig::default());
        let (origin, _) = actual_origin(&mut chc);
        chc.with_inline_walk_frame(&copy, |chc| {
            let fresh = chc.begin_native_dyn_return(copy.locals(), 0);
            assert!(fresh);
            assert_eq!(
                chc.finish_native_dyn_return(&copy, 0, fresh, Some(origin.clone())),
                Some(origin.clone())
            );
            let fresh = chc.begin_native_dyn_return(copy.locals(), 0);
            assert!(!fresh);
            assert!(chc.finish_native_dyn_return(&copy, 0, fresh, Some(origin.clone())).is_none());
            assert!(
                chc.inline_native_dyn_origin(
                    &Operand::Copy(Place { local: 0, projection: vec![] }),
                    copy.locals()
                )
                .is_none()
            );
        });
    });
}

#[test]
fn native_fat_box_source_twins_use_the_exact_callable_and_refuse_lost_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in [
            "native_safe",
            "native_bug",
            "second_safe",
            "second_bug",
            "replaced_bug",
            "corrupt_bug",
            "missing_metadata_bug",
            "roundtrip_safe",
            "runtime_payload_safe",
            "panic_call_bug",
        ] {
            let body: Body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let chc = ChcCtx::new(
                ctx.tcx,
                &body,
                name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let (vc, _, diagnostics) = chc.translate_with_diagnostics();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            let result = run_z3_on_smt2_with_timeout(&smt, 30);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            eprintln!(
                "FAT_BOX_CONTROL {name}: {result:?}; fail_closed={}; reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            if name.starts_with("native_") || name.starts_with("second_") {
                let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
                assert_eq!(
                    result.as_deref(),
                    Ok(expected),
                    "{name}: exact native callable must run"
                );
                assert_eq!(
                    diagnostics.place_translation_drop.get(),
                    0,
                    "{name}: supported route must keep its checks"
                );
            } else if name == "panic_call_bug" {
                assert_eq!(
                    result.as_deref(),
                    Ok("sat"),
                    "the checked native route must retain the actual callable panic"
                );
            } else {
                assert!(
                    diagnostics.place_translation_drop.get() > 0
                        && reasons.iter().any(|(reason, count)| *count > 0
                            && (reason.starts_with("native_dyn_")
                                || reason == "box_deref_validity_unmodeled")),
                    "{name}: unsupported or malformed metadata must be explicitly fail-closed: {reasons:?}"
                );
            }
            for reason in reasons.keys().filter(|reason| reason.starts_with("native_dyn_")) {
                assert_eq!(
                    super::super::codegen_ctx::fallback_soundness(reason),
                    super::super::codegen_ctx::FallbackSoundness::FailClose
                );
            }
        }
    });
}

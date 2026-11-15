// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Accesses through a pointer reached from a CONSTANT pointer into a static
//! or a constant allocation, and sub-word stores into an integer static.
//!
//! 1. Object bounds (`codegen_stmt_rvalue_offset_const_object.rs`). `let p:
//!    *const u32 = &V;` is `_1 = &raw const (*_2)` with `_2 = const {&V}`.
//!    Moved (`p.add(1)`), the pointer reaches its dereference with an opaque
//!    obj_id lane, so `heap_access_checks` stated no bound, and the
//!    const-ref value lane read a constant array's element without one. On
//!    main the out-of-bounds read failed only through a constant-false
//!    use-after-scope obligation (which failed the safe twin too); once that
//!    was removed (`ref_target_through_constant`) it PROVED. The global-object
//!    lane states the access bound of the static's or the allocation's bytes.
//! 2. A constant INTEGER address (`0x1000 as *const u32`) has no provenance:
//!    no non-empty access through it is valid.
//! 3. A byte stored at the base of `static mut N: u32` writes that byte only
//!    (`splice_integer_bytes`); the scalar store lane zero-extended it into
//!    the whole static.
//! 4. A reborrow `&*p` of a pointer joined on two paths fails closed
//!    (`deref_through_path_merged_pointer`), as a read through it does.
//!
//! Each bug probe must reach its error, and each safe twin must prove.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;

const CONST_OBJECT_PROBE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    use std::ptr::{addr_of, addr_of_mut};
    use std::sync::atomic::{AtomicU32, Ordering};

    static V: u32 = 7;
    static ARR: [u32; 2] = [1, 2];
    static A: AtomicU32 = AtomicU32::new(5);
    static AP: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
    static mut N_BUG: u32 = 0x0102_0304;
    static mut N_SAFE: u32 = 0x0102_0304;
    const P_INT: *const u32 = 0x1000 as *const u32;

    pub fn probe_raw_add1_bug() -> u32 {
        let p: *const u32 = &V;
        unsafe { *p.add(1) }
    }

    pub fn probe_raw_add0_safe() {
        let p: *const u32 = &V;
        kani::assert(unsafe { *p.add(0) } == 7, "the static itself");
    }

    pub fn probe_atomic_reborrow_add1_bug() -> u32 {
        let p = &A as *const AtomicU32;
        let q = unsafe { &*p.add(1) };
        q.load(Ordering::SeqCst)
    }

    pub fn probe_atomic_reborrow_add1_safe() {
        let p = &AP[0] as *const AtomicU32;
        let q = unsafe { &*p.add(1) };
        let _ = q;
    }

    pub fn probe_array_add2_bug() -> u32 {
        let p = addr_of!(ARR) as *const u32;
        unsafe { *p.add(2) }
    }

    pub fn probe_array_add1_safe() {
        let p = addr_of!(ARR) as *const u32;
        kani::assert(unsafe { *p.add(1) } == 2, "the second element");
    }

    pub fn probe_integer_address_bug() -> u32 {
        let p: *const u32 = addr_of!(*P_INT);
        unsafe { *p }
    }

    pub fn probe_byte_store_bug() {
        unsafe { *(addr_of_mut!(N_BUG) as *mut u8) = 9 };
        kani::assert(unsafe { N_BUG } == 9, "the byte zero-extended into the static");
    }

    pub fn probe_byte_store_safe() {
        unsafe { *(addr_of_mut!(N_SAFE) as *mut u8) = 9 };
        kani::assert(unsafe { N_SAFE } == 0x0102_0309, "the byte replaces the low byte");
    }

    pub fn probe_joined_atomic_reborrow(c: bool) -> u32 {
        let x = AtomicU32::new(3);
        let p: *const AtomicU32 = if c { &A } else { &x };
        unsafe { (*p).load(Ordering::SeqCst) }
    }
"#;

/// Encode `fn_name`, solve it, and return the verdict with the drop reasons.
fn solve_probe(fn_name: &str) -> (String, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(CONST_OBJECT_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = emit_chc(&vc).to_string();
        verdict = Some(
            run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .unwrap_or_else(|e| panic!("AY failed on {fn_name}: {e}")),
        );
    });
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (verdict.expect("the probe was encoded"), reasons)
}

fn assert_bug_reached(fn_name: &str) {
    let (verdict, reasons) = solve_probe(fn_name);
    assert_eq!(
        verdict, "sat",
        "{fn_name}: the invalid access must be refutable; reasons {reasons:?}"
    );
}

fn assert_safe_proves(fn_name: &str) {
    let (verdict, reasons) = solve_probe(fn_name);
    assert_eq!(verdict, "unsat", "{fn_name}: the in-bounds access must prove; reasons {reasons:?}");
}

/// `*(&V as *const u32).add(1)`: one past a static.
#[test]
fn test_read_past_a_static_through_a_constant_pointer_fails() {
    assert_bug_reached("probe_raw_add1_bug");
}

#[test]
fn test_read_of_the_static_through_a_constant_pointer_proves() {
    assert_safe_proves("probe_raw_add0_safe");
}

/// `&*p.add(1)` past an atomic static: the reference is invalid on creation.
#[test]
fn test_reborrow_past_an_atomic_static_fails() {
    assert_bug_reached("probe_atomic_reborrow_add1_bug");
}

/// The bound is the OBJECT's extent, not the pointee's: `&AP[0]` moved by one
/// element is still inside `AP`.
#[test]
fn test_reborrow_inside_an_atomic_array_static_proves() {
    assert_safe_proves("probe_atomic_reborrow_add1_safe");
}

/// The const-ref value lane selected element 2 of `[1, 2]` with no bound.
#[test]
fn test_read_past_a_static_array_fails() {
    assert_bug_reached("probe_array_add2_bug");
}

#[test]
fn test_read_inside_a_static_array_proves() {
    assert_safe_proves("probe_array_add1_safe");
}

/// `*(0x1000 as *const u32)`: an address with no provenance.
#[test]
fn test_read_through_a_constant_integer_address_fails() {
    assert_bug_reached("probe_integer_address_bug");
}

/// A byte store at the base of a `u32` static writes one byte.
#[test]
fn test_byte_store_into_an_integer_static_is_not_zero_extended() {
    assert_bug_reached("probe_byte_store_bug");
}

#[test]
fn test_byte_store_into_an_integer_static_replaces_its_low_byte() {
    assert_safe_proves("probe_byte_store_safe");
}

/// `&*p` with `p` joined from a static and a local fails closed. Read from
/// this context's own counters: the per-function reason map is global, and a
/// test running beside this one drains it. The fail-closed reason also bumps
/// the process-wide drop counter, which other tests read under
/// `METADATA_COUNTER_MUTEX` (`test_range_for_loop_int_lifted_has_zero_
/// translation_drops` failed in every full suite run beside this test), so it
/// holds that lock too.
#[test]
fn test_reborrow_of_a_path_merged_pointer_fails_closed() {
    use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
    use rustc_public::ty::{RigidTy, TyKind};
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(CONST_OBJECT_PROBE, |ctx| {
        let fn_name = "probe_joined_atomic_reborrow";
        let body = find_instance_by_suffix(ctx.tcx, fn_name).body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let reborrow = body
            .blocks
            .iter()
            .flat_map(|bb| &bb.statements)
            .find_map(|stmt| match &stmt.kind {
                StatementKind::Assign(_, Rvalue::Ref(_, _, place))
                    if matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                        && matches!(
                            body.locals()[place.local].ty.kind(),
                            TyKind::RigidTy(RigidTy::RawPtr(..))
                        ) =>
                {
                    Some(place.clone())
                }
                _ => None,
            })
            .expect("the reborrow `&(*p)` behind `(*p).load()`");
        let drops = |c: &ChcCtx<'_, '_>| {
            c.diagnostics.sound_havoc_drop.get() + c.diagnostics.place_translation_drop.get()
        };
        let before = drops(&chc_ctx);
        chc_ctx.fail_close_reborrow_of_path_merged_pointer(&reborrow);
        assert!(drops(&chc_ctx) > before, "the reborrow of a joined pointer must fail closed");
    });
}

/// `splice_integer_bytes` keeps the bits outside the window, little-endian.
#[test]
fn test_splice_integer_bytes_replaces_only_the_window() {
    use crate::codegen_ay::chc::decl::static_path::splice_integer_bytes;
    use ay_bindings::{Expr, ExprValue};
    use rustc_public::ty::{Ty, UintTy};
    let fold = |e: Expr| match trust_mc_core::chc_const_prop::eval::try_eval_to_const(&e)
        .expect("constant inputs fold")
        .value()
    {
        ExprValue::BitVecConst { value, .. } => value.clone(),
        other => panic!("expected a bitvector constant, got {other:?}"),
    };
    with_test_ay_ctx_for_source(CONST_OBJECT_PROBE, |_ctx| {
        let u32_ty = Ty::unsigned_ty(UintTy::U32);
        let u16_ty = Ty::unsigned_ty(UintTy::U16);
        let u8_ty = Ty::unsigned_ty(UintTy::U8);
        let current = Expr::bitvec_const(0x0102_0304u128, 32);
        let byte = Expr::bitvec_const(9u128, 8);
        let at0 = splice_integer_bytes(u32_ty, &current, 0, u8_ty, &byte).expect("byte 0");
        assert_eq!(fold(at0), num_bigint::BigInt::from(0x0102_0309u32));
        let at1 = splice_integer_bytes(u32_ty, &current, 1, u8_ty, &byte).expect("byte 1");
        assert_eq!(fold(at1), num_bigint::BigInt::from(0x0102_0904u32));
        let at3 = splice_integer_bytes(u32_ty, &current, 3, u8_ty, &byte).expect("byte 3");
        assert_eq!(fold(at3), num_bigint::BigInt::from(0x0902_0304u32));
        let half = Expr::bitvec_const(9u128, 16);
        let at2 = splice_integer_bytes(u32_ty, &current, 2, u16_ty, &half).expect("half 2");
        assert_eq!(fold(at2), num_bigint::BigInt::from(0x0009_0304u32));
        assert!(splice_integer_bytes(u32_ty, &current, 3, u16_ty, &half).is_none(), "straddles");
        assert!(splice_integer_bytes(u32_ty, &current, 0, u32_ty, &current).is_none(), "whole");
    });
}

/// A pointer whose every step from the constant is a constant displacement
/// has a compile-time offset into its object (`const_pointer_delta`), so its
/// bound folds instead of costing the solver an invariant over a
/// block-crossing pointer value (`modifies/global_pass.rs`: 5 s on round 1,
/// 17 s with the symbolic bound, 4.5 s folded).
#[test]
fn test_constant_steps_give_the_pointer_a_constant_offset() {
    use rustc_public::mir::TerminatorKind;
    with_test_ay_ctx_for_source(CONST_OBJECT_PROBE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_raw_add1_bug").body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_add1_bug",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const_prescan::compute_single_assign_locals(
            &mut chc_ctx,
        );
        // `p.add(1)`: the call (or the offset model it lowers to) whose
        // destination is the moved pointer.
        let moved = body
            .blocks
            .iter()
            .find_map(|bb| match &bb.terminator.kind {
                TerminatorKind::Call { func, destination, .. }
                    if chc_ctx
                        .resolve_callee_path(func)
                        .is_some_and(|path| path.ends_with("::add") || path.contains("offset")) =>
                {
                    Some(destination.local)
                }
                _ => None,
            })
            .expect("the pointer step");
        assert_eq!(chc_ctx.const_pointer_delta(moved), Some(4), "one u32 past the static's base");
    });
}

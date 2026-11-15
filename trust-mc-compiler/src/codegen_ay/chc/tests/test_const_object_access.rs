// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Accesses through a pointer into a static, reached from a constant pointer
//! in the shapes the round-2 global-object bound did not reach
//! (`codegen_stmt_rvalue_offset_const_access.rs`), and same-width stores of
//! another type into an aggregate static (`same_width_static_store_value`).
//!
//! 1. A pointer held in a struct or tuple field, a reference made by
//!    transmute, a projected reborrow of an atomic past the static, and a
//!    pointer read back through a shared reference to it. Round 2 skipped the
//!    use-after-scope obligation for these (`ref_target_through_constant`)
//!    without bounding them, so each proved where Kani reports "pointer
//!    outside object bounds".
//! 2. Where the skip stands but the lane cannot walk the pointer, the access
//!    fails closed (`bound_access_through_constant_or_fail_close`).
//! 3. `*(addr_of_mut!(PS) as *mut u32) = 0x0005_0006` into `#[repr(C)]
//!    { a: u16, b: u16 }` gives `a = 6, b = 5`; the scalar store lane
//!    unflattened the bits in declaration order and certified the safe twin's
//!    failure Genuine.
//! 4. The span bound is ONE obligation (`object_span_checks`): over a count a
//!    callee writes, its no-wrap half alone ran out of solver budget.
//!
//! Each bug probe must reach its error, and each safe twin must prove.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;

const CONST_ACCESS_PROBE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    use std::ptr::addr_of_mut;
    use std::sync::atomic::{AtomicU32, Ordering};

    static V: u32 = 7;
    static ARR: [u32; 2] = [1, 2];
    static A: AtomicU32 = AtomicU32::new(5);
    static AP: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];

    #[repr(C)]
    struct P2 {
        a: u16,
        b: u16,
    }
    static mut PS_BUG: P2 = P2 { a: 1, b: 2 };
    static mut PS_SAFE: P2 = P2 { a: 1, b: 2 };

    struct H {
        p: *const u32,
    }

    pub fn probe_struct_held_add1_bug() -> u32 {
        let h = H { p: &V };
        unsafe { *h.p.add(1) }
    }

    pub fn probe_struct_held_add1_safe() {
        let h = H { p: &ARR[0] };
        kani::assert(unsafe { *h.p.add(1) } == 2, "inside ARR");
    }

    pub fn probe_tuple_held_add1_bug() -> u32 {
        let t: (*const u32, u8) = (&V, 0);
        unsafe { *t.0.add(1) }
    }

    pub fn probe_transmuted_atomic_ref_load_bug() -> u32 {
        let p = &A as *const AtomicU32;
        let r: &AtomicU32 = unsafe { std::mem::transmute(p.add(1)) };
        r.load(Ordering::SeqCst)
    }

    pub fn probe_atomic_array_cast_elem_load_bug() -> u32 {
        let p = &A as *const AtomicU32 as *const [AtomicU32; 2];
        unsafe { (*p)[1].load(Ordering::SeqCst) }
    }

    pub fn probe_atomic_array_cast_elem_load_safe() {
        let p = &AP[0] as *const AtomicU32 as *const [AtomicU32; 2];
        kani::assert(unsafe { (*p)[1].load(Ordering::SeqCst) } == 2, "inside AP");
    }

    pub fn probe_ptr_to_ptr_add1_bug() -> u32 {
        let p: *const u32 = &V;
        let pp = &p;
        unsafe { *(*pp).add(1) }
    }

    pub fn probe_u32_into_u16_pair_bug() {
        unsafe { *(addr_of_mut!(PS_BUG) as *mut u32) = 0x0005_0006 };
        kani::assert(unsafe { PS_BUG.a } == 5, "declaration order");
    }

    pub fn probe_u32_into_u16_pair_safe() {
        unsafe { *(addr_of_mut!(PS_SAFE) as *mut u32) = 0x0005_0006 };
        kani::assert(unsafe { PS_SAFE.a } == 6 && unsafe { PS_SAFE.b } == 5, "memory order");
    }

    pub fn probe_reassigned_field_read(c: bool) -> u32 {
        let mut h = H { p: &ARR[0] };
        if c {
            h.p = &V;
        }
        unsafe { *h.p }
    }
"#;

/// Encode `fn_name`, solve it, and return the verdict with the drop reasons.
fn solve_probe(fn_name: &str) -> (String, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(CONST_ACCESS_PROBE, |ctx| {
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

/// `H { p: &V }.p.add(1)`: the walk follows the field back to the operand
/// the struct was built from.
#[test]
fn test_read_past_a_static_through_a_struct_held_pointer_fails() {
    assert_bug_reached("probe_struct_held_add1_bug");
}

#[test]
fn test_read_inside_a_static_through_a_struct_held_pointer_proves() {
    assert_safe_proves("probe_struct_held_add1_safe");
}

#[test]
fn test_read_past_a_static_through_a_tuple_held_pointer_fails() {
    assert_bug_reached("probe_tuple_held_add1_bug");
}

/// A reference made by transmute must be dereferenceable; the atomic call
/// model that reads through it makes no dereference in the body.
#[test]
fn test_transmuted_reference_past_an_atomic_static_fails() {
    assert_bug_reached("probe_transmuted_atomic_ref_load_bug");
}

/// `(*p)[1].load(..)` with `p` cast from `&A`: the atomic model's receiver
/// is bounded with the element's offset.
#[test]
fn test_atomic_element_past_the_static_through_a_projected_reborrow_fails() {
    assert_bug_reached("probe_atomic_array_cast_elem_load_bug");
}

#[test]
fn test_atomic_element_inside_the_static_through_a_projected_reborrow_proves() {
    assert_safe_proves("probe_atomic_array_cast_elem_load_safe");
}

/// `*(*pp).add(1)` with `pp = &p`: a shared borrow of a `Freeze` local does
/// not let anything write it, so the walk reads `p` through it.
#[test]
fn test_read_past_a_static_through_a_pointer_to_the_pointer_fails() {
    assert_bug_reached("probe_ptr_to_ptr_add1_bug");
}

/// The bits land in memory order: `a` is the low half.
#[test]
fn test_same_width_store_into_a_struct_static_is_not_declaration_order() {
    assert_bug_reached("probe_u32_into_u16_pair_bug");
}

#[test]
fn test_same_width_store_into_a_struct_static_takes_memory_order() {
    assert_safe_proves("probe_u32_into_u16_pair_safe");
}

/// A read through a pointer the global-object lane cannot walk (a struct
/// field written after the struct was built) fails closed where the
/// use-after-scope skip would otherwise stand. Read from this context's own
/// counters, under the lock that guards the process-wide ones.
#[test]
fn test_unwalkable_access_through_a_constant_pointer_fails_closed() {
    use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(CONST_ACCESS_PROBE, |ctx| {
        let fn_name = "probe_reassigned_field_read";
        let body = find_instance_by_suffix(ctx.tcx, fn_name).body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const_prescan::compute_single_assign_locals(
            &mut chc_ctx,
        );
        let read = body
            .blocks
            .iter()
            .flat_map(|bb| &bb.statements)
            .find_map(|stmt| match &stmt.kind {
                StatementKind::Assign(_, Rvalue::Use(op, ..)) => match op {
                    rustc_public::mir::Operand::Copy(place)
                        if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) =>
                    {
                        Some(place.clone())
                    }
                    _ => None,
                },
                _ => None,
            })
            .expect("the read `*h.p`");
        let drops = |c: &ChcCtx<'_, '_>| c.diagnostics.place_translation_drop.get();
        let before = drops(&chc_ctx);
        chc_ctx.bound_access_through_constant_or_fail_close(&read, &Default::default());
        assert!(drops(&chc_ctx) > before, "an access the lane cannot bound must fail closed");
    });
}

/// `object_span_checks` is one obligation that holds exactly when the span
/// is inside the object without wrapping the offset lane.
#[test]
fn test_object_span_bound_is_one_unsigned_comparison() {
    use ay_bindings::{Expr, ExprValue};
    let fold = |e: &Expr| match trust_mc_core::chc_const_prop::eval::try_eval_to_const(e)
        .expect("constant inputs fold")
        .value()
    {
        ExprValue::BoolConst(b) => *b,
        other => panic!("expected a bool constant, got {other:?}"),
    };
    with_test_ay_ctx_for_source(CONST_ACCESS_PROBE, |ctx| {
        let body =
            find_instance_by_suffix(ctx.tcx, "probe_struct_held_add1_bug").body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_struct_held_add1_bug",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let at = |offset: u64| {
            Expr::bitvec_const(7u128, 32).concat(Expr::bitvec_const(u128::from(offset), 32))
        };
        let holds = |offset: u64, size: u32, object: u32| {
            let checks = chc_ctx.object_span_checks(&at(offset), size, object, 7);
            assert_eq!(checks.len(), 1, "one obligation");
            fold(&checks[0])
        };
        assert!(holds(0, 4, 4), "the whole object");
        assert!(holds(4, 4, 8), "the second word");
        assert!(!holds(4, 4, 4), "one past the end");
        assert!(!holds(0xFFFF_FFFC, 4, 4), "below the base wraps the offset lane");
        assert!(!holds(0, 8, 4), "wider than the object");
        // Another object's lane at an offset inside this one: a step of 2^32.
        let other_lane = Expr::bitvec_const(8u128, 32).concat(Expr::bitvec_const(0u128, 32));
        let checks = chc_ctx.object_span_checks(&other_lane, 4, 4, 7);
        assert_eq!(checks.len(), 1, "one obligation");
        assert!(!fold(&checks[0]), "the lane is the object's");
    });
}

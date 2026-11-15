// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The image sync (`sync_static_image`) rewrites every view a static's memory
//! image seeds from the static's state variable after each store that changes
//! the state. That is sound only when every store into the image updates or
//! havocs the state too, and when every cell a store leaves is one the sync
//! rewrites (`decl::static_path::StaticImageWrites`).
//!
//! `write_volatile(A.as_ptr(), 9)` wrote the `u32` view only (the volatile
//! store's Mem bridge had no static route), so the state stayed 5; the next
//! `A.fetch_add(1)` synced the image from 5 + 1, and `*A.as_ptr() == 6`
//! PROVED where Kani reads 10 (review of fix/chc-atomic-as-ptr-live, round 1).
//! A `u8` written under an `AtomicU32` is a cell no sync rewrites, so it kept
//! 9 after `A.store(0)`. An address another static holds (`RS[i]`, `RSL[i]`)
//! reached no static either. Each bug probe must reach its error or fail
//! closed; each safe twin must prove with no unrouted store.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;

const IMAGE_HAZARD_PROBE: &str = r#"
    #![allow(dead_code, static_mut_refs, internal_features)]
    #![feature(register_tool, core_intrinsics)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    use std::ptr::{addr_of, addr_of_mut};
    use std::sync::atomic::{AtomicU32, Ordering};

    // `ptr::write_volatile` is the intrinsic `volatile_store`, which the
    // driver intercepts at the call (it has no stdlib MIR there). This test
    // context has that MIR and would walk `write_volatile`'s body instead, so
    // the probes call the intrinsic itself.
    use core::intrinsics::volatile_store as write_volatile;

    static VA_BUG: AtomicU32 = AtomicU32::new(5);
    static VA_SAFE: AtomicU32 = AtomicU32::new(5);
    static VL_BUG: AtomicU32 = AtomicU32::new(5);
    static VL_SAFE: AtomicU32 = AtomicU32::new(5);
    static VO_SAFE: AtomicU32 = AtomicU32::new(5);
    static mut Q_BUG: (u32, u32) = (1, 2);
    static mut Q_SAFE: (u32, u32) = (1, 2);
    static BYTE: AtomicU32 = AtomicU32::new(5);
    static BYTE_ALONE: AtomicU32 = AtomicU32::new(5);
    static AS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
    static RS: [&AtomicU32; 2] = [&AS[0], &AS[1]];
    static BS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
    static RSL: &[AtomicU32] = &BS;
    static mut G_BUG: [u32; 4] = [1, 2, 3, 4];

    pub fn probe_volatile_fetch_add_read_bug() {
        unsafe { write_volatile(VA_BUG.as_ptr(), 9) };
        VA_BUG.fetch_add(1, Ordering::SeqCst);
        kani::assert(unsafe { *VA_BUG.as_ptr() } == 6, "the stale state synced over the image");
    }

    pub fn probe_volatile_fetch_add_read_safe() {
        unsafe { write_volatile(VA_SAFE.as_ptr(), 9) };
        VA_SAFE.fetch_add(1, Ordering::SeqCst);
        kani::assert(unsafe { *VA_SAFE.as_ptr() } == 10, "the volatile value, bumped");
    }

    pub fn probe_volatile_load_bug() {
        unsafe { write_volatile(VL_BUG.as_ptr(), 9) };
        kani::assert(VL_BUG.load(Ordering::SeqCst) == 5, "the initializer loaded after the write");
    }

    pub fn probe_volatile_load_safe() {
        unsafe { write_volatile(VL_SAFE.as_ptr(), 9) };
        kani::assert(VL_SAFE.load(Ordering::SeqCst) == 9, "the volatile value loaded");
    }

    pub fn probe_volatile_fetch_or_read_safe() {
        unsafe { write_volatile(VO_SAFE.as_ptr(), 9) };
        VO_SAFE.fetch_or(0, Ordering::SeqCst);
        kani::assert(unsafe { *VO_SAFE.as_ptr() } == 9, "the volatile value survives fetch_or(0)");
    }

    pub fn probe_mut_volatile_field_bug() {
        unsafe {
            write_volatile(addr_of_mut!(Q_BUG.1), 9);
            kani::assert(Q_BUG.1 == 2, "the initializer read after the volatile write");
        }
    }

    pub fn probe_mut_volatile_field_safe() {
        unsafe {
            write_volatile(addr_of_mut!(Q_SAFE.1), 9);
            kani::assert(Q_SAFE.1 == 9, "the volatile value read directly");
        }
    }

    pub fn probe_byte_write_store_byte_read_bug() {
        unsafe { *(BYTE.as_ptr() as *mut u8) = 9 };
        BYTE.store(0, Ordering::SeqCst);
        kani::assert(unsafe { *(BYTE.as_ptr() as *const u8) } == 9, "the byte the store overwrote");
    }

    pub fn probe_byte_write_byte_read_alone() -> u8 {
        unsafe { *(BYTE_ALONE.as_ptr() as *mut u8) = 9 };
        unsafe { *(BYTE_ALONE.as_ptr() as *const u8) }
    }

    pub fn probe_static_ref_array_store_load_bug(i: usize) {
        if i < 2 {
            RS[i].store(7, Ordering::SeqCst);
            kani::assert(i == 0 || AS[1].load(Ordering::SeqCst) == 2, "RS[1] is &AS[1]");
        }
    }

    pub fn probe_static_slice_store_load_bug(i: usize) {
        if i == 1 {
            RSL[i].store(7, Ordering::SeqCst);
            kani::assert(BS[1].load(Ordering::SeqCst) == 2, "RSL[1] is BS[1]");
        }
    }

    static mut WCELL: i32 = 0;
    trait SetCell {
        fn set_cell(&self);
    }
    struct One;
    impl SetCell for One {
        fn set_cell(&self) {
            unsafe { WCELL = 1 };
        }
    }

    pub fn probe_walker_static_write_safe() {
        let s: &dyn SetCell = &One;
        s.set_cell();
        kani::assert(unsafe { WCELL } == 1, "the walked body's store, read through the state");
        kani::assert(unsafe { *addr_of!(WCELL) } == 1, "and through the image");
    }

    static COUNTER: AtomicU32 = AtomicU32::new(10);
    trait Bump {
        fn bump(&self) -> u32;
    }
    impl Bump for AtomicU32 {
        fn bump(&self) -> u32 {
            self.fetch_add(1, Ordering::SeqCst)
        }
    }

    pub fn probe_dyn_coerced_static_bump_safe() {
        let b: &dyn Bump = &COUNTER;
        b.bump();
        kani::assert(COUNTER.load(Ordering::SeqCst) == 11, "the bump through the trait object");
    }

    pub fn probe_array_pointer_element_store_bug() {
        let p = addr_of_mut!(G_BUG);
        unsafe { (*p)[1] = 9 };
        kani::assert(unsafe { G_BUG[1] } == 2, "the initializer read after the element store");
    }
"#;

/// Reasons a routed store into a static must never record.
const UNROUTED: [&str; 2] = ["static_image_written_unrouted", "static_image_unsynced"];

/// Encode `fn_name`, solve it, and return the verdict with the drop reasons.
fn solve_probe(fn_name: &str) -> (String, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(IMAGE_HAZARD_PROBE, |ctx| {
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
        "{fn_name}: the assertion over the stale value must be refutable; reasons {reasons:?}"
    );
}

fn assert_safe_routed(fn_name: &str) {
    let (verdict, reasons) = solve_probe(fn_name);
    assert_eq!(
        verdict, "unsat",
        "{fn_name}: the live value must be read back; reasons {reasons:?}"
    );
    for lost in UNROUTED {
        assert!(
            !reasons.contains_key(lost),
            "{fn_name}: the store must be routed, got {reasons:?}"
        );
    }
}

/// The review's introduced row: the volatile store reached the `u32` view
/// only, and the next exact store synced the image from the stale state.
#[test]
fn test_volatile_store_then_rmw_reads_the_live_value() {
    assert_bug_reached("probe_volatile_fetch_add_read_bug");
}

#[test]
fn test_volatile_store_then_rmw_safe_twin_proves() {
    assert_safe_routed("probe_volatile_fetch_add_read_safe");
}

/// The volatile store reaches the static's state: `load` sees it.
#[test]
fn test_volatile_store_reaches_the_state() {
    assert_bug_reached("probe_volatile_load_bug");
}

#[test]
fn test_volatile_store_load_safe_twin_proves() {
    assert_safe_routed("probe_volatile_load_safe");
}

/// The precision row main proved and the first fix false-failed: the sync
/// after `fetch_or(0)` must keep the volatile value.
#[test]
fn test_volatile_store_survives_an_identity_rmw() {
    assert_safe_routed("probe_volatile_fetch_or_read_safe");
}

/// A `static mut` field written volatile, read through its state: a missed
/// bug and a false certificate on both bundles before.
#[test]
fn test_volatile_store_into_a_static_mut_field_reaches_its_state() {
    assert_bug_reached("probe_mut_volatile_field_bug");
}

#[test]
fn test_volatile_store_into_a_static_mut_field_safe_twin_proves() {
    assert_safe_routed("probe_mut_volatile_field_safe");
}

/// A `u8` cell under an `AtomicU32` is no view the sync rewrites: with another
/// store into the static it may be stale, and the lane fails closed.
#[test]
fn test_unsynced_view_under_another_store_fails_closed() {
    let (_, reasons) = solve_probe("probe_byte_write_store_byte_read_bug");
    assert!(
        reasons.contains_key("static_image_view_unsynced"),
        "the byte cell the store left must fail closed: {reasons:?}"
    );
}

/// Alone, the same write is exact: no other store changes its bytes.
#[test]
fn test_unsynced_view_alone_is_not_refused() {
    let (_, reasons) = solve_probe("probe_byte_write_byte_read_alone");
    assert!(
        !reasons.contains_key("static_image_view_unsynced"),
        "nothing overwrote it: {reasons:?}"
    );
}

/// `RS[i]` is a reference another static's initializer holds: an untraced
/// receiver may write every LIVE static whose address memory holds.
#[test]
fn test_store_through_a_static_held_reference_havocs_its_target() {
    assert_bug_reached("probe_static_ref_array_store_load_bug");
}

#[test]
fn test_store_through_a_static_held_slice_havocs_its_target() {
    assert_bug_reached("probe_static_slice_store_load_bug");
}

/// A guard, not a repair: `(*p)[1] = 9` through `p = addr_of_mut!(G)` is
/// routed to the static's state by the register lane (it passed before this
/// change too), and the memory writer's backstop must not refuse it.
#[test]
fn test_array_pointer_element_store_stays_routed() {
    let (verdict, reasons) = solve_probe("probe_array_pointer_element_store_bug");
    assert_eq!(verdict, "sat", "the stored element must be read back; reasons {reasons:?}");
    assert!(!reasons.contains_key("static_image_written_unrouted"), "routed: {reasons:?}");
}

/// A guard: a store the inline walker makes into a `static mut` (a body walked
/// through `dyn`, as drop glue is) goes through the walker's static mirror,
/// which writes the state; it is a routed store, and the image follows it.
/// The backstop refused it at first (`Drop/drop_boxed_dyn.rs` lost parity).
#[test]
fn test_walker_static_mirror_is_a_routed_store() {
    let (verdict, reasons) = solve_probe("probe_walker_static_write_safe");
    assert_eq!(verdict, "unsat", "the walked store must be read back; reasons {reasons:?}");
    assert!(!reasons.contains_key("static_image_written_unrouted"), "routed: {reasons:?}");
}

/// A guard: coercing `&COUNTER` to `&dyn Bump` copies the static's value from
/// one memory view into the views the trait object is read through
/// (`unsize_dyn.rs`); that copy writes the image, not a program store, and the
/// backstop refused it at first (`const_pointer_live_atomic_reach_dual.rs`,
/// `safe_dyn_bump_load` false-failed).
#[test]
fn test_dyn_coercion_alias_copy_is_an_image_write() {
    let (verdict, reasons) = solve_probe("probe_dyn_coerced_static_bump_safe");
    assert_eq!(verdict, "unsat", "the bumped value must be read back; reasons {reasons:?}");
    assert!(!reasons.contains_key("static_image_written_unrouted"), "an image copy: {reasons:?}");
}

/// The memory writer's backstop: a store at a static's address that no routed
/// store made records the fail-closed reason once the body is translated,
/// whatever lane made it.
#[test]
fn test_unrouted_store_into_a_static_image_fails_closed() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let name = "probe_volatile_load_safe";
    with_test_ay_ctx_for_source(IMAGE_HAZARD_PROBE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, name).body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let (&obj_id, _) = chc_ctx
            .ref_resolution
            .static_state_idx_by_obj
            .iter()
            .next()
            .expect("the probe's static has an image");
        let addr = ay_bindings::Expr::bitvec_const(i128::from(obj_id), 32)
            .concat(ay_bindings::Expr::bitvec_const(0i128, 32));
        chc_ctx.with_static_store_routing(|ctx| ctx.note_type_array_store(&addr, "u32"));
        chc_ctx.with_static_image_writer(|ctx| ctx.note_type_array_store(&addr, "u32"));
        chc_ctx.fail_close_static_image_hazards();
        let routed = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove(name)
            .unwrap_or_default();
        assert!(
            !routed.contains_key("static_image_written_unrouted"),
            "a routed store and the image's own write are no unrouted store: {routed:?}"
        );
        chc_ctx.note_type_array_store(&addr, "u32");
        chc_ctx.fail_close_static_image_hazards();
        let unrouted = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove(name)
            .unwrap_or_default();
        assert!(
            unrouted.contains_key("static_image_written_unrouted"),
            "an unrouted store must fail closed: {unrouted:?}"
        );
    });
}

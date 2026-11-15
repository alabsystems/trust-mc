// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Writes the inline walker lost with no reason recorded, found by the review
//! of design 2 Phase 0 (`docs/chc-hole-fix-designs-2026-09-24.md`, "Design 2,
//! Phase 0: review findings"; `tools/soundness-duals/walker_referent_write_dual.rs`
//! has the driver measurements):
//!
//! * M1: `let p = &mut x; *p = v; x` rebound `p` only, and `x` read back its
//!   old value (`codegen_call_virtual_inline/referent_write.rs`).
//! * M2: a store through a raw-pointer copy of an argument reached memory
//!   only and recorded nothing (`classify_inline_walk_lane_store`).
//! * M3: the host fn-pointer route dropped a walked closure's alias updates
//!   (`codegen_call_fn_ptr.rs`).
//! * M6: the static mirror wrote the first `static mut` state variable of a
//!   matching sort, not the static the store reached
//!   (`mirror_static_state_var_update`).
//!
//! The solver probes come in pairs that differ only in the asserted
//! predicate, so the safe probe's `unsat` shows nothing else in the program
//! can fail, and the bug probe's `sat` is then its assertion. Before its fix
//! each bug probe was `unsat` (a false proof); `sat` means "can fail".

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

/// Spelled out rather than imported, so this file compiles, and fails, against
/// an encoder that never records them.
const REBIND_LOST: &str = "walker_deref_write_rebind_lost";
const WRITEBACK_MEMORY_ONLY: &str = "walker_deref_writeback_memory_only";
const READ_AFTER_WRITE: &str = "walker_deref_read_after_write";
const ADDRESS_AS_VALUE: &str = "walker_deref_read_address_as_value";

const REFERENT_WRITE_PROBE: &str = r#"
    #![allow(dead_code)]

    // --- M1: a write through a non-argument reference local ------------------
    // Two impls, receiver statically `A`: the dyn door walks one body and the
    // call's value is exactly the walk's.
    pub trait T {
        fn local_alias(&self, v: u8) -> u8;
        fn opt_arg(&self, o: Option<&mut u8>);
    }
    pub struct A;
    pub struct B;
    impl T for A {
        fn local_alias(&self, v: u8) -> u8 { let mut x: u8 = 0; let p = &mut x; *p = v; x }
        fn opt_arg(&self, o: Option<&mut u8>) { if let Some(r) = o { *r = 200; } }
    }
    impl T for B {
        fn local_alias(&self, v: u8) -> u8 { let mut x: u8 = 0; let p = &mut x; *p = v; x }
        fn opt_arg(&self, o: Option<&mut u8>) { if let Some(r) = o { *r = 200; } }
    }
    pub fn probe_m1_local_alias_bug() {
        let o: Box<dyn T> = Box::new(A);
        assert!(o.local_alias(255) == 0);
    }
    pub fn probe_m1_local_alias_safe() {
        let o: Box<dyn T> = Box::new(A);
        assert!(o.local_alias(255) == 255);
    }
    pub fn probe_m1_option_payload(c: bool) -> u8 {
        let mut a: u8 = 7;
        let o: Box<dyn T> = if c { Box::new(A) } else { Box::new(B) };
        o.opt_arg(Some(&mut a));
        a
    }

    // --- M2: a store through a raw-pointer copy of an argument ---------------
    // Two impls, receiver statically `MA`: the dyn door walks one body.
    pub trait M {
        fn raw_copy(&self, a: &mut u8);
    }
    pub struct MA;
    pub struct MB;
    impl M for MA {
        fn raw_copy(&self, a: &mut u8) { let p = a as *mut u8; unsafe { *p = 200; } }
    }
    impl M for MB {
        fn raw_copy(&self, a: &mut u8) { let p = a as *mut u8; unsafe { *p = 200; } }
    }
    pub fn probe_m2_raw_copy() -> u8 {
        let mut a: u8 = 7;
        let o: Box<dyn M> = Box::new(MA);
        o.raw_copy(&mut a);
        a
    }

    // --- M3: a closure behind a host fn pointer writes a `&mut` argument -----
    pub fn probe_m3_closure_write_bug(c: bool) {
        let mut a: u8 = 7;
        let mut b: u8 = 7;
        let f: fn(&mut u8, &mut u8) = if c {
            |_x: &mut u8, y: &mut u8| { *y = 200; }
        } else {
            |_x: &mut u8, y: &mut u8| { *y = 201; }
        };
        f(&mut a, &mut b);
        assert!(b == 7);
    }
    pub fn probe_m3_closure_write_safe(c: bool) {
        let mut a: u8 = 7;
        let mut b: u8 = 7;
        let f: fn(&mut u8, &mut u8) = if c {
            |_x: &mut u8, y: &mut u8| { *y = 200; }
        } else {
            |_x: &mut u8, y: &mut u8| { *y = 201; }
        };
        f(&mut a, &mut b);
        assert!(a == 7 && b >= 200);
    }

    // --- M6: a walked store to a static only a callee names ------------------
    static mut H: u8 = 0;
    static mut K: u8 = 0;
    pub trait Hs {
        fn to_h(&self);
    }
    pub struct HA;
    pub struct HB;
    impl Hs for HA {
        fn to_h(&self) { unsafe { H = 9; } }
    }
    impl Hs for HB {
        fn to_h(&self) { unsafe { H = 9; } }
    }
    pub fn probe_m6_callee_static_bug() {
        let o: Box<dyn Hs> = Box::new(HA);
        o.to_h();
        assert!(unsafe { K } == 9);
    }
    pub fn probe_m6_callee_static_safe() {
        let o: Box<dyn Hs> = Box::new(HA);
        o.to_h();
        assert!(unsafe { K } == 0);
    }
"#;

/// Encode `fn_name` from the probe crate at the driver's track level; return
/// its translation-drop site reasons and, when `solve` is set, the solver
/// verdict on its CHC.
fn encode_probe(fn_name: &str, solve: bool) -> (BTreeMap<String, usize>, Option<(String, String)>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let ran = AtomicBool::new(false);
    let mut verdict = None;
    with_test_ay_ctx_for_source(REFERENT_WRITE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, config);
        if solve {
            let smt = emit_chc(&vc).to_string();
            let result =
                run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(Z3_TEST_TIMEOUT_SECS))
                    .unwrap_or_else(|e| panic!("{fn_name}: AY execution failed: {e}. SMT:\n{smt}"));
            verdict = Some((result, smt));
        }
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and {fn_name} was encoded");
    let sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (sites, verdict)
}

/// Assert the solver verdict of an [`encode_probe`] run, showing the CHC when
/// it differs.
fn assert_verdict(fn_name: &str, verdict: Option<(String, String)>, expected: &str, why: &str) {
    let (result, smt) = verdict.unwrap_or_else(|| panic!("{fn_name}: the probe was not solved"));
    assert_eq!(result, expected, "{fn_name}: {why}. SMT:\n{smt}");
}

/// M1: `let p = &mut x; *p = v; x` through a dyn call returns `v`, so `== 0`
/// can fail. It used to return `x`'s entry value 0: a false proof.
#[test]
fn test_m1_local_alias_write_reaches_referent_bug_fails() {
    let fn_name = "probe_m1_local_alias_bug";
    let (sites, verdict) = encode_probe(fn_name, true);
    assert_verdict(fn_name, verdict, "sat", "the assertion must be refutable");
    assert!(!sites.contains_key(REBIND_LOST), "{fn_name}: the referent is named, got {sites:?}");
}

/// M1, precision (and the pair's control): the same write is EXACT, not a
/// havoc: `== v` is proved and no Phase 0 reason is recorded. It used to fail.
#[test]
fn test_m1_local_alias_write_reaches_referent_safe_proves() {
    let fn_name = "probe_m1_local_alias_safe";
    let (sites, verdict) = encode_probe(fn_name, true);
    assert_verdict(fn_name, verdict, "unsat", "the write must reach `x` exactly");
    for reason in [REBIND_LOST, READ_AFTER_WRITE, ADDRESS_AS_VALUE, WRITEBACK_MEMORY_ONLY] {
        assert!(!sites.contains_key(reason), "{fn_name}: must not record {reason}, got {sites:?}");
    }
}

/// M1: `if let Some(r) = o { *r = 200 }` for an `Option<&mut u8>` argument:
/// `r` is bound from the payload, which names no place, so the write is
/// recorded as lost (it used to record nothing).
#[test]
fn test_m1_option_payload_write_records_lost() {
    let fn_name = "probe_m1_option_payload";
    let (sites, _) = encode_probe(fn_name, false);
    assert!(
        sites.get(REBIND_LOST).copied().unwrap_or(0) >= 1,
        "{fn_name}: must record {REBIND_LOST}, got {sites:?}"
    );
}

/// M2: `let p = a as *mut u8; *p = 200` for a `&mut u8` argument of a
/// one-candidate dyn walk: the store reaches memory only, and the caller's
/// `a` keeps its state variable's old value, so it fails closed (it used to
/// record nothing: F3 looked only at argument roots).
#[test]
fn test_m2_raw_copy_store_records_memory_only() {
    let fn_name = "probe_m2_raw_copy";
    let (sites, _) = encode_probe(fn_name, false);
    assert!(
        sites.get(WRITEBACK_MEMORY_ONLY).copied().unwrap_or(0) >= 1,
        "{fn_name}: must record {WRITEBACK_MEMORY_ONLY}, got {sites:?}"
    );
}

/// M3: a closure behind a host fn pointer writes `*y = 200`: the caller's `b`
/// takes it, so `b == 7` can fail and `b >= 200` is proved (the closure's
/// alias update used to be dropped: a false proof, and a false failure).
#[test]
fn test_m3_fn_ptr_closure_write_reaches_caller() {
    let fn_name = "probe_m3_closure_write_safe";
    let (_, verdict) = encode_probe(fn_name, true);
    assert_verdict(fn_name, verdict, "unsat", "the write must reach `b` exactly");
    let fn_name = "probe_m3_closure_write_bug";
    let (_, verdict) = encode_probe(fn_name, true);
    assert_verdict(fn_name, verdict, "sat", "the write must reach `b`");
}

/// M6: a walked `H = 9`, where only the callee names `H`, leaves `K` alone, so
/// `K == 9` can fail and `K == 0` is proved (the mirror used to write `K`'s
/// state variable: a false proof).
#[test]
fn test_m6_static_mirror_writes_the_stored_static_only() {
    let fn_name = "probe_m6_callee_static_safe";
    let (_, verdict) = encode_probe(fn_name, true);
    assert_verdict(fn_name, verdict, "unsat", "nothing writes K");
    let fn_name = "probe_m6_callee_static_bug";
    let (_, verdict) = encode_probe(fn_name, true);
    assert_verdict(fn_name, verdict, "sat", "nothing writes K");
}

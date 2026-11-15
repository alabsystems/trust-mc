// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a standard-library callee the CHC
//! inline walker havocs, whose only obligation is in a closure of THIS crate
//! that it is handed (Mechanism B's family).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-26):
//!   bug_std_map_closure_multi   -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   bug_std_map_closure_single  -> VERIFICATION:- FAILED  (same check)
//!   safe_std_map_closure_single -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `o` is an array element read at a symbolic index,
//! which the walker skips, so `Option::map(o, |v| v + 200)` has an argument
//! the walker cannot translate and the nested-call fallback havocs the call
//! (`terminator_exec.rs`, `nested_call_overapprox`, a blessed SoundHavoc
//! reason). The obligation sighting that refuses the blessing
//! (`body_has_visible_obligation`) looked at callees of this crate only, and
//! `Option::map` is core's, so the closure's overflow check was dropped: the
//! bug rows verified SUCCESSFUL clean on main a15de6272. Since
//! fix/chc-walker-fail-closed (2026-09-26) a safe callee in another crate is
//! refused when the obligation walk sights a site in this crate's code it
//! reaches (`obligation_free_walk::local_obligation_reachable`), so the bug
//! rows FAIL non-certified; the safe twin pays the precision cost (the havoc
//! still happens, and now fails closed) until the walker builds the array.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_std_callee_local_obligation_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, a: u8, i: u8) -> u8;
}
pub struct A;
pub struct B;
impl Op for A {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [Some(a), None, Some(1), Some(2)];
        let o = arr[(i % 4) as usize];
        let r = o.map(|v| v + 200);
        sink(r);
        a
    }
}
impl Op for B {
    fn op(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_std_map_closure_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    sink(obj.op(a, i));
}

#[kani::proof]
fn bug_std_map_closure_single() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(A);
    sink(obj.op(a, i));
}

#[kani::proof]
fn safe_std_map_closure_single() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a < 50);
    let obj: Box<dyn Op> = Box::new(A);
    sink(obj.op(a, i));
}

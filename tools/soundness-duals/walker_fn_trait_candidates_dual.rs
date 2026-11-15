// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- a `dyn Fn` call with SEVERAL candidate
//! closures, reached through the CHC INLINE WALKER's Fn-trait direct dispatch.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_box_dyn_fn_ub_first   -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_box_dyn_fn_ub_second  -> VERIFICATION:- FAILED  (same check)
//!   bug_ref_dyn_fn_ub_second  -> VERIFICATION:- FAILED  (same check)
//!   safe_box_dyn_fn_ub_second -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `try_fn_trait_direct_dispatch` short-circuits the
//! `Fn::call` shim to the closure body. It used to walk the FIRST candidate
//! closure that has a body and return it unconditionally, whatever the number
//! of candidates, so a `Box<dyn Fn>` / `&dyn Fn` holding the SECOND closure
//! (`*_ub_second`) never walked the overflowing one and verified SUCCESSFUL
//! clean. With several candidates the dispatch now walks each and merges the
//! results under `vtable_disc == id`; when it cannot build that merge it keeps
//! the first-candidate walk for the bug it can still find and FAILS CLOSED
//! (`fn_trait_dispatch_unguarded_candidate`). Either way no row may be a clean
//! SUCCESSFUL on a bug. `safe_box_dyn_fn_ub_second` is the precision guard.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_fn_trait_candidates_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

#[kani::proof]
fn bug_box_dyn_fn_ub_first() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn Fn(u8, u8) -> u8> = if kani::any() {
        Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) })
    } else {
        Box::new(|x: u8, y: u8| x.wrapping_add(y))
    };
    sink(f(a, b));
}

#[kani::proof]
fn bug_box_dyn_fn_ub_second() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn Fn(u8, u8) -> u8> = if kani::any() {
        Box::new(|x: u8, y: u8| x.wrapping_add(y))
    } else {
        Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) })
    };
    sink(f(a, b));
}

#[kani::proof]
fn bug_ref_dyn_fn_ub_second() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c1 = |x: u8, y: u8| x.wrapping_add(y);
    let c2 = |x: u8, y: u8| unsafe { x.unchecked_add(y) };
    let f: &dyn Fn(u8, u8) -> u8 = if kani::any() { &c1 } else { &c2 };
    sink(f(a, b));
}

#[kani::proof]
fn safe_box_dyn_fn_ub_second() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let f: Box<dyn Fn(u8, u8) -> u8> = if kani::any() {
        Box::new(|x: u8, y: u8| x.wrapping_add(y))
    } else {
        Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) })
    };
    sink(f(a, b));
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a safe standard-library callee the CHC
//! inline walker havocs, whose own body panics on the caller's value
//! (Mechanism B's family).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_std_expect_none_single   -> VERIFICATION:- FAILED  (the `expect` panic on `None`)
//!   bug_std_expect_none_multi    -> VERIFICATION:- FAILED  (same)
//!   safe_std_expect_some_single  -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `o` is an array element read at a symbolic index,
//! which the walker skips, so `Option::expect(o, ..)` has an argument the
//! walker cannot translate and the nested-call fallback havocs the call under
//! the blessed `nested_call_overapprox`. The fallback refused the blessing for
//! a safe callee in another crate only on an obligation in the crate's own
//! code it reaches, and `expect` reaches none: its `None` panic was dropped and
//! the bug rows verified SUCCESSFUL clean on the a15de6272 base bundle and on
//! the first cut of fix/chc-walker-fail-closed. A panic in the callee's OWN body
//! (`obligation_free_walk::body_panics_directly`) now refuses it, so the bug
//! rows FAIL non-certified; the safe twin pays the precision cost until the
//! walker builds the array and walks the call.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_std_callee_own_panic_dual.rs

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
        sink(o.expect("walker_std_callee_own_panic_dual: None reached"));
        a
    }
}
impl Op for B {
    fn op(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_std_expect_none_single() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(A);
    sink(obj.op(a, i));
}

#[kani::proof]
fn bug_std_expect_none_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    sink(obj.op(a, i));
}

#[kani::proof]
fn safe_std_expect_some_single() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(i % 4 != 1);
    let obj: Box<dyn Op> = Box::new(A);
    sink(obj.op(a, i));
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- SIGNED `i8::unchecked_add` UB inside
//! a dyn-dispatched method body, reached through the CHC INLINE WALKER.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_multi_impl           -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_positive_multi_impl  -> VERIFICATION:- FAILED  (same check, positive overflow only)
//!   bug_single_impl_box      -> VERIFICATION:- FAILED  (same check)
//!   safe_multi_impl          -> VERIFICATION:- SUCCESSFUL
//!   bug_direct_call          -> VERIFICATION:- FAILED  (control, same check)
//!
//! MECHANISM UNDER TEST (Mechanism A of the 2026-09-23 walker investigation),
//! for a SIGNED operand. The walker's check must use the signed overflow
//! predicate (`bvadd_no_overflow_signed`), chosen from the operand type. The
//! unsigned predicate on the same bits is wrong in BOTH directions, and one
//! harness catches each: it MISSES `100 + 100` (no carry out of bit 7, yet
//! above `i8::MAX`), which is the only overflow `bug_positive_multi_impl` can
//! reach, and it FLAGS the defined `-1 + 1` (a carry out of bit 7), which is in
//! the operand range of the `safe_multi_impl` precision guard.
//!
//! New shape: the investigation suspected signed `unchecked_*` (the same walker
//! code path) and did not probe it. The receiver shape copies
//! `walker_unchecked_sub_dual.rs`.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_unchecked_add_signed_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, a: i8, b: i8) -> i8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn op(&self, a: i8, b: i8) -> i8 {
        unsafe { a.unchecked_add(b) }
    }
}
impl Op for ImplB {
    fn op(&self, a: i8, b: i8) -> i8 {
        unsafe { a.unchecked_add(b) }
    }
}

#[kani::proof]
fn bug_multi_impl() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, b));
}

#[kani::proof]
fn bug_positive_multi_impl() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(a > 0 && b > 0);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, b));
}

#[kani::proof]
fn bug_single_impl_box() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.op(a, b));
}

#[kani::proof]
fn safe_multi_impl() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(a > -60 && a < 60 && b > -60 && b < 60);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, b));
}

#[kani::proof]
fn bug_direct_call() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    sink(unsafe { a.unchecked_add(b) });
}

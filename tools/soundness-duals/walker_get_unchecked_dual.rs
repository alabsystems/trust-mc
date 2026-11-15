// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- `get_unchecked` out of bounds
//! inside a dyn-dispatched method body (Mechanism B).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_multi_impl       -> VERIFICATION:- FAILED  ('Rust intrinsic assumption failed')
//!   bug_single_impl_box  -> VERIFICATION:- FAILED  (same check)
//!   safe_multi_impl      -> VERIFICATION:- SUCCESSFUL
//!   bug_direct_call      -> VERIFICATION:- FAILED  (same check)
//!   safe_direct_call     -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM (B of the 2026-09-23 walker investigation): the std callee on
//! the out-of-bounds path is havocked by the walker's nested-call fallback
//! (`terminator_exec.rs`, `nested_call_overapprox`, a blessed SoundHavoc
//! reason), and the obligation sighting that refuses the havoc
//! (`body_has_visible_obligation`) looked at local-crate bodies only, so the
//! assume the callee carries was lost and the dyn rows verified SUCCESSFUL.
//! The BinOp checks the walker records since `rvalue_ub.rs` do not reach this:
//! the obligation is an `assume`, not an integer BinOp. FIXED on
//! fix/chc-walker-fail-closed (2026-09-26): an `unsafe` callee in another
//! crate keeps its blessing only when the obligation walk proves it
//! obligation-free (its preconditions are the caller's), so the dyn bug rows
//! FAIL non-certified; `safe_multi_impl` pays the precision cost (known-red
//! false-failure) until the walker builds the array and walks the call.
//!
//! Promoted from the blast-radius probe `p9_get_unchecked.rs`.
//!
//! FIXED: Rule D (decision REDS-FINAL) books the havocked callee fail-closed,
//! and decision TRUSTMC-OPEN-REDS walks it: the walker reads the slice length
//! of an array value unsized to a slice, so `slice.len()` translates and the
//! callee's assumption is checked. The safe dyn row proves.
//!
//! The direct-call pair is NOT a control. `bug_direct_call` FAILS in the CHC
//! lane, but on an over-approximated 'index out of bounds' check, not Kani's
//! assumption check, and its safe twin `safe_direct_call` FAILS too
//! (OverApproximation, zero failed checks demoted) on the bundles measured
//! 2026-09-23 (review probe rp_controls.rs): the direct row fails whether or
//! not the obligation is encoded, so it cannot localise a miss. The safe twin
//! is tracked known-red (false-failure).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_get_unchecked_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, a: u8, i: u8) -> u8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 20, 30, 40];
        unsafe { *arr.get_unchecked(i as usize) }
    }
}
impl Op for ImplB {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 21, 31, 41];
        unsafe { *arr.get_unchecked(i as usize) }
    }
}

#[kani::proof]
fn bug_multi_impl() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, i));
}

#[kani::proof]
fn bug_single_impl_box() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.op(a, i));
}

#[kani::proof]
fn safe_multi_impl() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(i < 4);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, i));
}

#[kani::proof]
fn bug_direct_call() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let arr = [a, 20, 30, 40];
    sink(unsafe { *arr.get_unchecked(i as usize) });
}

#[kani::proof]
fn safe_direct_call() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(i < 4);
    let arr = [a, 20, 30, 40];
    sink(unsafe { *arr.get_unchecked(i as usize) });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_volatile_then_compare_exchange_read  -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_then_compare_exchange_read   -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_sym_atomic_elem_load        -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_sym_atomic_elem_load         -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_elem_store_other_read       -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_elem_store_other_read        -> VERIFICATION:- FAILED (assertion)
//   safe_loop_sym_count_as_ptr                -> VERIFICATION:- SUCCESSFUL
//   bug_loop_sym_count_as_ptr                 -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. Siblings of const_pointer_live_volatile_dual.rs and
// const_pointer_live_review_reach_dual.rs whose BMC verdict is INCONCLUSIVE
// (Unknown) within the 30 s budget on main and on this branch, which leaves
// the BMC lane unchanged: a volatile write at a symbolic atomic index, into
// one element before a store to another, or before a compare_exchange; and a
// loop with a symbolic count of fetch_adds. Their twins gate the CHC lane,
// whose verdicts this branch changes.
//
// Measured 2026-10-15 (30 s per harness, ay d80d17a90, frozen nightly; this
// branch's round-1 bundle, compiler d52360f5e06d, by the strict dual gate;
// main and round 0 by the same driver invocation, one run per harness): CHC
// on main f5dfb8d48's bundle 1 missed bug and 0 false certificates; on round
// 0 (compiler f78b21069ddb) 0 missed bugs and 0 false certificates; here 0
// missed bugs and 0 false certificates, 4 of 8 rows match. BMC is not run on
// this file. The remaining red rows are known-red in the manifest with their
// cause.

#![allow(dead_code)]
use std::ptr::write_volatile;
use std::sync::atomic::{AtomicU32, Ordering};

static AS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static AY: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static VX: AtomicU32 = AtomicU32::new(5);
static LA: AtomicU32 = AtomicU32::new(5);

#[kani::proof]
fn safe_volatile_then_compare_exchange_read() {
    unsafe { write_volatile(VX.as_ptr(), 9) };
    let r = VX.compare_exchange(9, 4, Ordering::SeqCst, Ordering::SeqCst);
    unsafe { assert!(r == Ok(9) && *VX.as_ptr() == 4) }
}
#[kani::proof]
fn bug_volatile_then_compare_exchange_read() {
    unsafe { write_volatile(VX.as_ptr(), 9) };
    let _ = VX.compare_exchange(9, 4, Ordering::SeqCst, Ordering::SeqCst);
    unsafe { assert!(*VX.as_ptr() == 6) }
}
#[kani::proof]
fn safe_volatile_sym_atomic_elem_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    unsafe { write_volatile(AY[i].as_ptr(), 9) };
    assert!(AY[1].load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_volatile_sym_atomic_elem_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    unsafe { write_volatile(AY[i].as_ptr(), 9) };
    assert!(AY[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_volatile_elem_store_other_read() {
    unsafe { write_volatile(AS[1].as_ptr(), 9) };
    AS[0].store(4, Ordering::SeqCst);
    unsafe { assert!(*AS[1].as_ptr() == 9) }
}
#[kani::proof]
fn bug_volatile_elem_store_other_read() {
    unsafe { write_volatile(AS[1].as_ptr(), 9) };
    AS[0].store(4, Ordering::SeqCst);
    unsafe { assert!(*AS[1].as_ptr() == 2) }
}
#[kani::proof]
#[kani::unwind(5)]
fn safe_loop_sym_count_as_ptr() {
    let n: u8 = kani::any();
    kani::assume(n < 4);
    for _ in 0..n {
        LA.fetch_add(1, Ordering::SeqCst);
    }
    unsafe { assert!(*LA.as_ptr() == 5 + n as u32) }
}
#[kani::proof]
#[kani::unwind(5)]
fn bug_loop_sym_count_as_ptr() {
    let n: u8 = kani::any();
    kani::assume(n < 4 && n > 0);
    for _ in 0..n {
        LA.fetch_add(1, Ordering::SeqCst);
    }
    unsafe { assert!(*LA.as_ptr() == 5) }
}

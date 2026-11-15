// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_dyn_index_bump_load         -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_index_bump_load          -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_choice_store_load       -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_choice_store_load        -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_static_swap_as_ptr      -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_static_swap_as_ptr       -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_index_bump_helper_read  -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_index_bump_helper_read   -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_choice_helper_read      -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_choice_helper_read       -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. Shapes the round-1 review of
// fix/chc-atomic-as-ptr-live probed on which main's CHC lane gave a wrong
// verdict and that branch's first round fixed: stores the inline walker makes
// into a static through a `dyn` or generic receiver at a symbolic index or a
// joined choice, read back directly or through an `#[inline(never)]` helper.
//
// Measured 2026-10-15 (30 s per harness, ay d80d17a90, frozen nightly; this
// branch's round-1 bundle, compiler d52360f5e06d, by the strict dual gate;
// main and round 0 by the same driver invocation, one run per harness): CHC
// on main f5dfb8d48's bundle 5 missed bugs and 4 false certificates; on round
// 0 (compiler f78b21069ddb) 0 missed bugs and 0 false certificates; here 0
// missed bugs and 0 false certificates, 6 of 10 rows match. BMC (unchanged
// code): no missed bug or false certificate. The remaining red rows are
// known-red in the manifest with their cause.

#![allow(dead_code, static_mut_refs)]
use std::sync::atomic::{AtomicU32, Ordering};

static A: AtomicU32 = AtomicU32::new(10);
static AS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];

trait Bump {
    fn bump(&self) -> u64;
}
impl Bump for AtomicU32 {
    fn bump(&self) -> u64 {
        unsafe { *self.as_ptr() += 1 };
        0
    }
}
struct Z(usize);
impl Bump for Z {
    fn bump(&self) -> u64 {
        AS[self.0].fetch_add(1, Ordering::SeqCst) as u64
    }
}
struct ZC(bool);
impl Bump for ZC {
    fn bump(&self) -> u64 {
        let r = if self.0 { &AS[0] } else { &AS[1] };
        r.store(7, Ordering::SeqCst);
        0
    }
}
struct ZW;
impl Bump for ZW {
    fn bump(&self) -> u64 {
        unsafe { *AS[1].as_ptr() = 7 };
        0
    }
}
struct ZS;
impl Bump for ZS {
    fn bump(&self) -> u64 {
        A.swap(3, Ordering::SeqCst) as u64
    }
}
fn bump<T: Bump>(t: &T) -> u64 {
    t.bump()
}

#[kani::proof]
fn safe_dyn_index_bump_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    let z = Z(i);
    let b: &dyn Bump = &z;
    b.bump();
    assert!(AS[1].load(Ordering::SeqCst) == 3)
}
#[kani::proof]
fn bug_dyn_index_bump_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    let z = Z(i);
    let b: &dyn Bump = &z;
    b.bump();
    assert!(AS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_dyn_choice_store_load() {
    let c: bool = kani::any();
    let z = ZC(c);
    let b: &dyn Bump = &z;
    b.bump();
    assert!(c || AS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_dyn_choice_store_load() {
    let c: bool = kani::any();
    let z = ZC(c);
    let b: &dyn Bump = &z;
    b.bump();
    assert!(c || AS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_dyn_static_swap_as_ptr() {
    let b: &dyn Bump = &ZS;
    let old = b.bump();
    unsafe { assert!(old == 10 && *A.as_ptr() == 3) }
}
#[kani::proof]
fn bug_dyn_static_swap_as_ptr() {
    let b: &dyn Bump = &ZS;
    b.bump();
    unsafe { assert!(*A.as_ptr() == 10) }
}

static AS2: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static BS2: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static CS2: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];

trait Bump2 {
    fn bump2(&self) -> u64;
}
struct Z2(usize);
impl Bump2 for Z2 {
    fn bump2(&self) -> u64 {
        AS2[self.0].fetch_add(1, Ordering::SeqCst) as u64
    }
}
struct ZC2(bool);
impl Bump2 for ZC2 {
    fn bump2(&self) -> u64 {
        let r = if self.0 { &BS2[0] } else { &BS2[1] };
        r.store(7, Ordering::SeqCst);
        0
    }
}
struct ZP2(usize);
impl Bump2 for ZP2 {
    fn bump2(&self) -> u64 {
        unsafe { *CS2[0].as_ptr().add(self.0) = 7 };
        0
    }
}
#[inline(never)]
fn read_as1() -> u32 {
    AS2[1].load(Ordering::SeqCst)
}
#[inline(never)]
fn read_bs1() -> u32 {
    BS2[1].load(Ordering::SeqCst)
}
#[inline(never)]
fn read_cs1() -> u32 {
    unsafe { *CS2[1].as_ptr() }
}

#[kani::proof]
fn safe_dyn_index_bump_helper_read() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    let z = Z2(i);
    let b: &dyn Bump2 = &z;
    b.bump2();
    assert!(read_as1() == 3)
}
#[kani::proof]
fn bug_dyn_index_bump_helper_read() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    let z = Z2(i);
    let b: &dyn Bump2 = &z;
    b.bump2();
    assert!(read_as1() == 2)
}
#[kani::proof]
fn safe_dyn_choice_helper_read() {
    let c: bool = kani::any();
    let z = ZC2(c);
    let b: &dyn Bump2 = &z;
    b.bump2();
    assert!(c || read_bs1() == 7)
}
#[kani::proof]
fn bug_dyn_choice_helper_read() {
    let c: bool = kani::any();
    let z = ZC2(c);
    let b: &dyn Bump2 = &z;
    b.bump2();
    assert!(c || read_bs1() == 2)
}

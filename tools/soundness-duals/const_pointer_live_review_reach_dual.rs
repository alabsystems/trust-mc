// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_get_store_as_ptr                 -> VERIFICATION:- SUCCESSFUL
//   bug_get_store_as_ptr                  -> VERIFICATION:- FAILED (assertion)
//   safe_pick_store_load                  -> VERIFICATION:- SUCCESSFUL
//   bug_pick_store_load                   -> VERIFICATION:- FAILED (assertion)
//   safe_id_store_as_ptr                  -> VERIFICATION:- SUCCESSFUL
//   bug_id_store_as_ptr                   -> VERIFICATION:- FAILED (assertion)
//   safe_helper_choice_load               -> VERIFICATION:- SUCCESSFUL
//   bug_helper_choice_load                -> VERIFICATION:- FAILED (assertion)
//   safe_helper_raw_write_load            -> VERIFICATION:- SUCCESSFUL
//   bug_helper_raw_write_load             -> VERIFICATION:- FAILED (assertion)
//   safe_struct_local_store_load          -> VERIFICATION:- SUCCESSFUL
//   bug_struct_local_store_load           -> VERIFICATION:- FAILED (assertion)
//   safe_local_ref_array_sym_store_load   -> VERIFICATION:- SUCCESSFUL
//   bug_local_ref_array_sym_store_load    -> VERIFICATION:- FAILED (assertion)
//   safe_loop_as_ptr_write_load           -> VERIFICATION:- SUCCESSFUL
//   bug_loop_as_ptr_write_load            -> VERIFICATION:- FAILED (assertion)
//   safe_move_closure_store_load          -> VERIFICATION:- SUCCESSFUL
//   bug_move_closure_store_load           -> VERIFICATION:- FAILED (assertion)
//   safe_callee_ptr_store_load            -> VERIFICATION:- SUCCESSFUL
//   bug_callee_ptr_store_load             -> VERIFICATION:- FAILED (assertion)
//   safe_loop_cond_store_as_ptr           -> VERIFICATION:- SUCCESSFUL
//   bug_loop_cond_store_as_ptr            -> VERIFICATION:- FAILED (assertion)
//   safe_reordered_field_store_cast_read  -> VERIFICATION:- SUCCESSFUL
//   bug_reordered_field_store_cast_read   -> VERIFICATION:- FAILED (assertion)
//   safe_nested_field_store_cast_add      -> VERIFICATION:- SUCCESSFUL
//   bug_nested_field_store_cast_add       -> VERIFICATION:- FAILED (assertion)
//   safe_nested_inner_ptr_read            -> VERIFICATION:- SUCCESSFUL
//   bug_nested_inner_ptr_read             -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. Shapes the round-1 review of
// fix/chc-atomic-as-ptr-live probed on which main's CHC lane gave a wrong
// verdict and that branch's first round fixed: receivers that reach a static
// through a helper's return value, an identity function, a joined choice, a
// struct or Option local, a local array of references, a move closure or a
// callee's raw pointer; a loop that stores conditionally; and fields of
// reordered and nested struct statics read through casts. They are rows so
// that a change to the image sync or its routes cannot reopen them unseen.
//
// Measured 2026-10-15 (30 s per harness, ay d80d17a90, frozen nightly; this
// branch's round-1 bundle, compiler d52360f5e06d, by the strict dual gate;
// main and round 0 by the same driver invocation, one run per harness): CHC
// on main f5dfb8d48's bundle 14 missed bugs and 5 false certificates; on
// round 0 (compiler f78b21069ddb) 0 missed bugs and 0 false certificates;
// here 0 missed bugs and 0 false certificates, 22 of 28 rows match. BMC
// (unchanged code): no missed bug or false certificate. The remaining red
// rows are known-red in the manifest with their cause.

#![allow(dead_code, static_mut_refs)]
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicU8, Ordering};

static A: AtomicU32 = AtomicU32::new(5);
static AS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static RS: [&AtomicU32; 2] = [&AS[0], &AS[1]];
static PA: &AtomicU32 = &AS[1];
static RSL: &[AtomicU32] = &AS;
struct H {
    r: &'static AtomicU32,
}
static HH: H = H { r: &A };
static mut PTR: *const AtomicU32 = std::ptr::null();

#[inline(never)]
fn get() -> &'static AtomicU32 {
    &A
}
#[inline(never)]
fn pick(c: bool) -> &'static AtomicU32 {
    if c { &AS[0] } else { &AS[1] }
}
#[inline(never)]
fn id(a: &AtomicU32) -> &AtomicU32 {
    a
}
fn store_choice(c: bool) {
    let r = if c { &AS[0] } else { &AS[1] };
    r.store(7, Ordering::SeqCst);
}
fn store_index(i: usize) {
    AS[i].store(7, Ordering::SeqCst);
}
fn raw_write(p: *mut u32) {
    unsafe { *p = 7 };
}
struct W<'a> {
    r: &'a AtomicU32,
}

#[kani::proof]
fn safe_get_store_as_ptr() { get().store(7, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 7) } }
#[kani::proof]
fn bug_get_store_as_ptr() { get().store(7, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_pick_store_load() {
    let c: bool = kani::any();
    pick(c).store(7, Ordering::SeqCst);
    assert!(c || AS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_pick_store_load() {
    let c: bool = kani::any();
    pick(c).store(7, Ordering::SeqCst);
    assert!(c || AS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_id_store_as_ptr() { id(&A).store(7, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 7) } }
#[kani::proof]
fn bug_id_store_as_ptr() { id(&A).store(7, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_helper_choice_load() {
    let c: bool = kani::any();
    store_choice(c);
    assert!(c || AS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_helper_choice_load() {
    let c: bool = kani::any();
    store_choice(c);
    assert!(c || AS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_helper_raw_write_load() {
    raw_write(A.as_ptr());
    assert!(A.load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_helper_raw_write_load() {
    raw_write(A.as_ptr());
    assert!(A.load(Ordering::SeqCst) == 5)
}
#[kani::proof]
fn safe_struct_local_store_load() {
    let w = W { r: &AS[1] };
    w.r.store(7, Ordering::SeqCst);
    assert!(AS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_struct_local_store_load() {
    let w = W { r: &AS[1] };
    w.r.store(7, Ordering::SeqCst);
    assert!(AS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_local_ref_array_sym_store_load() {
    let rs = [&AS[0], &AS[1]];
    let i: usize = kani::any();
    kani::assume(i < 2);
    rs[i].store(7, Ordering::SeqCst);
    assert!(i == 0 || AS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_local_ref_array_sym_store_load() {
    let rs = [&AS[0], &AS[1]];
    let i: usize = kani::any();
    kani::assume(i < 2);
    rs[i].store(7, Ordering::SeqCst);
    assert!(i == 0 || AS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_loop_as_ptr_write_load() {
    for k in 0..3u32 {
        unsafe { *A.as_ptr() = k };
    }
    assert!(A.load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn bug_loop_as_ptr_write_load() {
    for k in 0..3u32 {
        unsafe { *A.as_ptr() = k };
    }
    assert!(A.load(Ordering::SeqCst) == 5)
}
#[kani::proof]
fn safe_move_closure_store_load() {
    let r = &AS[1];
    let f = move || r.store(7, Ordering::SeqCst);
    f();
    assert!(AS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_move_closure_store_load() {
    let r = &AS[1];
    let f = move || r.store(7, Ordering::SeqCst);
    f();
    assert!(AS[1].load(Ordering::SeqCst) == 2)
}

static A3: AtomicU32 = AtomicU32::new(5);
#[inline(never)]
fn ptr_of() -> *mut u32 {
    A3.as_ptr()
}
#[kani::proof]
fn safe_callee_ptr_store_load() {
    unsafe { *ptr_of() = 9 };
    assert!(A3.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_callee_ptr_store_load() {
    unsafe { *ptr_of() = 9 };
    assert!(A3.load(Ordering::SeqCst) == 5)
}

static LA: AtomicU32 = AtomicU32::new(5);

#[kani::proof]
#[kani::unwind(5)]
fn safe_loop_cond_store_as_ptr() {
    let n: u8 = kani::any();
    kani::assume(n < 4);
    let mut k = 0u8;
    while k < n {
        if k == 2 {
            LA.store(9, Ordering::SeqCst);
        }
        k += 1;
    }
    unsafe { assert!(n < 3 || *LA.as_ptr() == 9) }
}
#[kani::proof]
#[kani::unwind(5)]
fn bug_loop_cond_store_as_ptr() {
    let n: u8 = kani::any();
    kani::assume(n < 4);
    let mut k = 0u8;
    while k < n {
        if k == 2 {
            LA.store(9, Ordering::SeqCst);
        }
        k += 1;
    }
    unsafe { assert!(n < 3 || *LA.as_ptr() == 5) }
}

static VA: AtomicU32 = AtomicU32::new(5);
static VW: AtomicU64 = AtomicU64::new(5);
struct R {
    a: AtomicU8,
    b: AtomicU32,
}
static RR: R = R { a: AtomicU8::new(1), b: AtomicU32::new(2) };
struct Inner {
    x: AtomicU32,
}
#[repr(C)]
struct Outer {
    pad: AtomicU32,
    inner: Inner,
}
static O: Outer = Outer { pad: AtomicU32::new(1), inner: Inner { x: AtomicU32::new(2) } };
static VT: (AtomicU32, AtomicU64) = (AtomicU32::new(1), AtomicU64::new(2));
struct S(UnsafeCell<u32>);
unsafe impl Sync for S {}
static C: S = S(UnsafeCell::new(3));
#[repr(C)]
struct VPair {
    a: AtomicU32,
    b: AtomicU32,
}
static VPR: VPair = VPair { a: AtomicU32::new(1), b: AtomicU32::new(2) };

#[kani::proof]
fn safe_reordered_field_store_cast_read() {
    RR.b.store(9, Ordering::SeqCst);
    let off = std::mem::offset_of!(R, b);
    unsafe { assert!(*((&RR as *const R as *const u8).add(off) as *const u32) == 9) }
}
#[kani::proof]
fn bug_reordered_field_store_cast_read() {
    RR.b.store(9, Ordering::SeqCst);
    let off = std::mem::offset_of!(R, b);
    unsafe { assert!(*((&RR as *const R as *const u8).add(off) as *const u32) == 2) }
}
#[kani::proof]
fn safe_nested_field_store_cast_add() {
    O.inner.x.store(9, Ordering::SeqCst);
    unsafe { assert!(*(&O as *const Outer as *const u32).add(1) == 9) }
}
#[kani::proof]
fn bug_nested_field_store_cast_add() {
    O.inner.x.store(9, Ordering::SeqCst);
    unsafe { assert!(*(&O as *const Outer as *const u32).add(1) == 2) }
}
#[kani::proof]
fn safe_nested_inner_ptr_read() {
    O.inner.x.store(9, Ordering::SeqCst);
    let p = &O.inner as *const Inner as *const u32;
    unsafe { assert!(*p == 9) }
}
#[kani::proof]
fn bug_nested_inner_ptr_read() {
    O.inner.x.store(9, Ordering::SeqCst);
    let p = &O.inner as *const Inner as *const u32;
    unsafe { assert!(*p == 2) }
}

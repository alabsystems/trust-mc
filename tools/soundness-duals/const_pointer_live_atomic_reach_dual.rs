// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_slice_elem_store_load         -> VERIFICATION:- SUCCESSFUL
//   bug_slice_elem_store_load          -> VERIFICATION:- FAILED (assertion)
//   safe_iter_store_load               -> VERIFICATION:- SUCCESSFUL
//   bug_iter_store_load                -> VERIFICATION:- FAILED (assertion)
//   safe_choice_store_load             -> VERIFICATION:- SUCCESSFUL
//   bug_choice_store_load              -> VERIFICATION:- FAILED (assertion)
//   safe_ptr_param_store_load          -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_param_store_load           -> VERIFICATION:- FAILED (assertion)
//   safe_ref_static_store_as_ptr       -> VERIFICATION:- SUCCESSFUL
//   bug_ref_static_store_as_ptr        -> VERIFICATION:- FAILED (assertion)
//   safe_loop_fetch_add_as_ptr         -> VERIFICATION:- SUCCESSFUL
//   bug_loop_fetch_add_as_ptr          -> VERIFICATION:- FAILED (assertion)
//   safe_helper_store_load             -> VERIFICATION:- SUCCESSFUL
//   bug_helper_store_load              -> VERIFICATION:- FAILED (assertion)
//   safe_helper_store_as_ptr           -> VERIFICATION:- SUCCESSFUL
//   bug_helper_store_as_ptr            -> VERIFICATION:- FAILED (assertion)
//   safe_generic_helper_store_load     -> VERIFICATION:- SUCCESSFUL
//   bug_generic_helper_store_load      -> VERIFICATION:- FAILED (assertion)
//   safe_generic_helper_store_as_ptr   -> VERIFICATION:- SUCCESSFUL
//   bug_generic_helper_store_as_ptr    -> VERIFICATION:- FAILED (assertion)
//   safe_closure_store_load            -> VERIFICATION:- SUCCESSFUL
//   bug_closure_store_load             -> VERIFICATION:- FAILED (assertion)
//   safe_closure_store_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_closure_store_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_drop_counter_load             -> VERIFICATION:- SUCCESSFUL
//   bug_drop_counter_load              -> VERIFICATION:- FAILED (assertion)
//   safe_drop_counter_as_ptr           -> VERIFICATION:- SUCCESSFUL
//   bug_drop_counter_as_ptr            -> VERIFICATION:- FAILED (assertion)
//   safe_trait_bump_as_ptr             -> VERIFICATION:- SUCCESSFUL
//   bug_trait_bump_as_ptr              -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_bump_load                 -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_bump_load                  -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_bump_as_ptr               -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_bump_as_ptr                -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. The receivers of const_pointer_live_atomic_views_dual.rs
// name their static in the MIR that makes them. These reach it some other
// way: a slice of a static array, an iterator's item, a reference chosen on
// two paths, a raw pointer, a static holding a reference, a helper, a
// closure, a `Drop` impl, a trait method called generically or through
// `dyn`. A LIVE target's pointee is the lane's live state, or the lane fails
// closed (trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs). The CHC
// lane now routes a store it can name into the static's state and memory
// image, havocs every LIVE static whose address reaches an unnamed receiver
// or escapes the body's address-flow scan, and havocs the static a store in
// an inlined body makes (the inline walker's atomic model writes typed
// memory only), writing the stored value's own views back exactly.
//
// Measured on main ed592ea3d (bundle of f5dfb8d48, 30 s per harness, ay
// d80d17a90): CHC missed bugs bug_slice_elem_store_load,
// bug_iter_store_load, bug_choice_store_load, bug_ref_static_store_as_ptr,
// bug_loop_fetch_add_as_ptr, bug_helper_store_as_ptr,
// bug_generic_helper_store_as_ptr, bug_closure_store_as_ptr,
// bug_drop_counter_as_ptr, bug_trait_bump_as_ptr and bug_dyn_bump_as_ptr,
// and certified safe_choice_store_load and safe_slice_elem_store_load
// Genuine; BMC no wrong verdict. With the rule: no missed bug and no false certificate
// on either lane.

#![allow(dead_code)]
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

static A: AtomicU32 = AtomicU32::new(5);
static AS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static RA: &AtomicU32 = &A;
static DROPS: AtomicUsize = AtomicUsize::new(0);
static COUNTER: AtomicU32 = AtomicU32::new(10);

fn bump_store(a: &AtomicU32) {
    a.store(7, Ordering::SeqCst);
}

#[inline(never)]
fn bump_generic<T: Copy>(a: &AtomicU32, _t: T) {
    a.store(7, Ordering::SeqCst);
}

struct D;
impl Drop for D {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

trait Bump {
    fn bump(&self) -> u64;
}
impl Bump for AtomicU32 {
    fn bump(&self) -> u64 {
        self.fetch_add(1, Ordering::SeqCst) as u64
    }
}
fn bump<T: Bump>(t: &T) -> u64 {
    t.bump()
}

#[kani::proof]
fn safe_slice_elem_store_load() {
    let s: &[AtomicU32] = &AS;
    s[1].store(7, Ordering::SeqCst);
    assert!(AS[1].load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_slice_elem_store_load() {
    let s: &[AtomicU32] = &AS;
    s[1].store(7, Ordering::SeqCst);
    assert!(AS[1].load(Ordering::SeqCst) == 2);
}
#[kani::proof]
fn safe_iter_store_load() {
    for a in AS.iter() {
        a.store(7, Ordering::SeqCst);
    }
    assert!(AS[1].load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_iter_store_load() {
    for a in AS.iter() {
        a.store(7, Ordering::SeqCst);
    }
    assert!(AS[1].load(Ordering::SeqCst) == 2);
}
#[kani::proof]
fn safe_choice_store_load() {
    let c: bool = kani::any();
    let r = if c { &AS[0] } else { &AS[1] };
    r.store(7, Ordering::SeqCst);
    assert!(c || AS[1].load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_choice_store_load() {
    let c: bool = kani::any();
    let r = if c { &AS[0] } else { &AS[1] };
    r.store(7, Ordering::SeqCst);
    assert!(c || AS[1].load(Ordering::SeqCst) == 2);
}
#[kani::proof]
fn safe_ptr_param_store_load() {
    let p: *const AtomicU32 = &A;
    unsafe { (*p).store(7, Ordering::SeqCst) };
    assert!(A.load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_ptr_param_store_load() {
    let p: *const AtomicU32 = &A;
    unsafe { (*p).store(7, Ordering::SeqCst) };
    assert!(A.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn safe_ref_static_store_as_ptr() {
    RA.store(7, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 7) }
}
#[kani::proof]
fn bug_ref_static_store_as_ptr() {
    RA.store(7, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_loop_fetch_add_as_ptr() {
    for _ in 0..3 {
        A.fetch_add(1, Ordering::SeqCst);
    }
    unsafe { assert!(*A.as_ptr() == 8) }
}
#[kani::proof]
fn bug_loop_fetch_add_as_ptr() {
    for _ in 0..3 {
        A.fetch_add(1, Ordering::SeqCst);
    }
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_helper_store_load() {
    bump_store(&A);
    assert!(A.load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_helper_store_load() {
    bump_store(&A);
    assert!(A.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn safe_helper_store_as_ptr() {
    bump_store(&A);
    unsafe { assert!(*A.as_ptr() == 7) }
}
#[kani::proof]
fn bug_helper_store_as_ptr() {
    bump_store(&A);
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_generic_helper_store_load() {
    bump_generic(&A, 1u8);
    assert!(A.load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_generic_helper_store_load() {
    bump_generic(&A, 1u8);
    assert!(A.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn safe_generic_helper_store_as_ptr() {
    bump_generic(&A, 1u8);
    unsafe { assert!(*A.as_ptr() == 7) }
}
#[kani::proof]
fn bug_generic_helper_store_as_ptr() {
    bump_generic(&A, 1u8);
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_closure_store_load() {
    let f = || A.store(7, Ordering::SeqCst);
    f();
    assert!(A.load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_closure_store_load() {
    let f = || A.store(7, Ordering::SeqCst);
    f();
    assert!(A.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn safe_closure_store_as_ptr() {
    let f = || A.store(7, Ordering::SeqCst);
    f();
    unsafe { assert!(*A.as_ptr() == 7) }
}
#[kani::proof]
fn bug_closure_store_as_ptr() {
    let f = || A.store(7, Ordering::SeqCst);
    f();
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_drop_counter_load() {
    {
        let _d = D;
    }
    assert!(DROPS.load(Ordering::SeqCst) == 1);
}
#[kani::proof]
fn bug_drop_counter_load() {
    {
        let _d = D;
    }
    assert!(DROPS.load(Ordering::SeqCst) == 0);
}
#[kani::proof]
fn safe_drop_counter_as_ptr() {
    {
        let _d = D;
    }
    unsafe { assert!(*DROPS.as_ptr() == 1) }
}
#[kani::proof]
fn bug_drop_counter_as_ptr() {
    {
        let _d = D;
    }
    unsafe { assert!(*DROPS.as_ptr() == 0) }
}
#[kani::proof]
fn safe_trait_bump_as_ptr() {
    bump(&COUNTER);
    unsafe { assert!(*COUNTER.as_ptr() == 11) }
}
#[kani::proof]
fn bug_trait_bump_as_ptr() {
    bump(&COUNTER);
    unsafe { assert!(*COUNTER.as_ptr() == 10) }
}
#[kani::proof]
fn safe_dyn_bump_load() {
    let b: &dyn Bump = &COUNTER;
    b.bump();
    assert!(COUNTER.load(Ordering::SeqCst) == 11);
}
#[kani::proof]
fn bug_dyn_bump_load() {
    let b: &dyn Bump = &COUNTER;
    b.bump();
    assert!(COUNTER.load(Ordering::SeqCst) == 10);
}
#[kani::proof]
fn safe_dyn_bump_as_ptr() {
    let b: &dyn Bump = &COUNTER;
    b.bump();
    unsafe { assert!(*COUNTER.as_ptr() == 11) }
}
#[kani::proof]
fn bug_dyn_bump_as_ptr() {
    let b: &dyn Bump = &COUNTER;
    b.bump();
    unsafe { assert!(*COUNTER.as_ptr() == 10) }
}

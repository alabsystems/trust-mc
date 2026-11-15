// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness and seed):
//   safe_atomic_as_ptr_initial           -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_as_ptr_initial            -> VERIFICATION:- FAILED (assertion)
//   safe_atomic_as_ptr_after_store       -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_as_ptr_after_store        -> VERIFICATION:- FAILED (assertion)
//   safe_cell_get_initial                -> VERIFICATION:- SUCCESSFUL
//   bug_cell_get_initial                 -> VERIFICATION:- FAILED (assertion)
//   safe_cell_write_then_cast_read       -> VERIFICATION:- SUCCESSFUL
//   bug_cell_write_then_cast_read        -> VERIFICATION:- FAILED (assertion)
//   safe_mut_static_wrapping_after_write -> VERIFICATION:- SUCCESSFUL
//   bug_mut_static_wrapping_after_write  -> VERIFICATION:- FAILED (assertion)
//   safe_atomic_ref_cast_after_store     -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_ref_cast_after_store      -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A LIVE target (an atomic, an `UnsafeCell` static, a
// `static mut`) is never decoded from its initializer: its pointee is the
// lane's live state, or the lane fails closed
// (trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs). The `bug_`
// rows write the static and then read it through a raw pointer derived from
// a reference to it, asserting the INITIAL value: a lane that took the
// initial image for the state would prove them. They are the guard on the
// BMC lane's rule that only a FIXED target named by the reference lane gets
// its initializer bytes on memory (statement/global_alloc.rs).
//
// Measured on main 5b8582dd4 (round-10 resume, 30 s per harness, ay
// 48c98a43d): CHC every row an `error` (the R12 ICE on an atomic or
// `UnsafeCell` static, AtomicPrimitive::Storage); BMC no missed bug and no
// false certificate. With the rule: no missed bug and no false certificate
// on either lane; the safe rows that fail closed are recorded known-red
// false-failure.
//
// Measured again on main ed592ea3d (bundle of f5dfb8d48, 30 s, ay
// d80d17a90): CHC PROVED bug_atomic_as_ptr_after_store in 2 ms and failed
// its safe twin. The CHC lane keeps a static in its state variable and in a
// memory image seeded under every typed view (`AtomicU32` and `u32`); the
// atomic store wrote the `AtomicU32` view only (and could not reach the
// state variable: the path to the `u32` went through an `UnsafeCell` layer
// the encoding collapses), so the `u32` view `as_ptr` reads kept 5. Every
// store into a static now rewrites the whole image from the static's state,
// or havocs both (`stmt/codegen_stmt_store/static_image.rs`,
// `decl/static_path.rs`): both rows match. The siblings are
// const_pointer_live_atomic_views_dual.rs, const_pointer_live_atomic_reach_dual.rs
// and const_pointer_live_cell_views_dual.rs.


#![allow(dead_code, static_mut_refs)]
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicU32, Ordering};

static A: AtomicU32 = AtomicU32::new(5);
struct S(UnsafeCell<u32>);
unsafe impl Sync for S {}
static C: S = S(UnsafeCell::new(3));
static mut M: [u32; 2] = [1, 2];

#[kani::proof]
fn safe_atomic_as_ptr_initial() {
    let p = A.as_ptr();
    unsafe { assert!(*p == 5) }
}
#[kani::proof]
fn bug_atomic_as_ptr_initial() {
    let p = A.as_ptr();
    unsafe { assert!(*p == 6) }
}
#[kani::proof]
fn safe_atomic_as_ptr_after_store() {
    A.store(7, Ordering::SeqCst);
    let p = A.as_ptr();
    unsafe { assert!(*p == 7) }
}
#[kani::proof]
fn bug_atomic_as_ptr_after_store() {
    A.store(7, Ordering::SeqCst);
    let p = A.as_ptr();
    unsafe { assert!(*p == 5) }
}
#[kani::proof]
fn safe_cell_get_initial() {
    let p = C.0.get();
    unsafe { assert!(*p == 3) }
}
#[kani::proof]
fn bug_cell_get_initial() {
    let p = C.0.get();
    unsafe { assert!(*p == 4) }
}
#[kani::proof]
fn safe_cell_write_then_cast_read() {
    unsafe { *C.0.get() = 4 };
    let q = &C as *const S as *const u32;
    unsafe { assert!(*q == 4) }
}
#[kani::proof]
fn bug_cell_write_then_cast_read() {
    unsafe { *C.0.get() = 4 };
    let q = &C as *const S as *const u32;
    unsafe { assert!(*q == 3) }
}
#[kani::proof]
fn safe_mut_static_wrapping_after_write() {
    unsafe {
        M[1] = 9;
        let p = (std::ptr::addr_of!(M) as *const u32).wrapping_add(1);
        assert!(*p == 9);
    }
}
#[kani::proof]
fn bug_mut_static_wrapping_after_write() {
    unsafe {
        M[1] = 9;
        let p = (std::ptr::addr_of!(M) as *const u32).wrapping_add(1);
        assert!(*p == 2);
    }
}
#[kani::proof]
fn safe_atomic_ref_cast_after_store() {
    A.store(8, Ordering::SeqCst);
    let p = &A as *const AtomicU32 as *const u32;
    unsafe { assert!(*p == 8) }
}
#[kani::proof]
fn bug_atomic_ref_cast_after_store() {
    A.store(8, Ordering::SeqCst);
    let p = &A as *const AtomicU32 as *const u32;
    unsafe { assert!(*p == 5) }
}

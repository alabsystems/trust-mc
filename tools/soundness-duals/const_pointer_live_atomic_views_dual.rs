// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_bool_store_as_ptr                -> VERIFICATION:- SUCCESSFUL
//   bug_bool_store_as_ptr                 -> VERIFICATION:- FAILED (assertion)
//   safe_i64_store_as_ptr                 -> VERIFICATION:- SUCCESSFUL
//   bug_i64_store_as_ptr                  -> VERIFICATION:- FAILED (assertion)
//   safe_usize_store_as_ptr               -> VERIFICATION:- SUCCESSFUL
//   bug_usize_store_as_ptr                -> VERIFICATION:- FAILED (assertion)
//   safe_fetch_add_as_ptr                 -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_add_as_ptr                  -> VERIFICATION:- FAILED (assertion)
//   safe_swap_as_ptr                      -> VERIFICATION:- SUCCESSFUL
//   bug_swap_as_ptr                       -> VERIFICATION:- FAILED (assertion)
//   safe_compare_exchange_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_compare_exchange_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_compare_exchange_then_load       -> VERIFICATION:- SUCCESSFUL
//   bug_compare_exchange_then_load        -> VERIFICATION:- FAILED (assertion)
//   safe_compare_exchange_result          -> VERIFICATION:- SUCCESSFUL
//   bug_compare_exchange_result           -> VERIFICATION:- FAILED (assertion)
//   safe_as_ptr_write_then_load           -> VERIFICATION:- SUCCESSFUL
//   bug_as_ptr_write_then_load            -> VERIFICATION:- FAILED (assertion)
//   safe_as_ptr_write_then_read           -> VERIFICATION:- SUCCESSFUL
//   bug_as_ptr_write_then_read            -> VERIFICATION:- FAILED (assertion)
//   safe_ref_cast_after_fetch_add         -> VERIFICATION:- SUCCESSFUL
//   bug_ref_cast_after_fetch_add          -> VERIFICATION:- FAILED (assertion)
//   safe_array_elem_store_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_array_elem_store_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_array_store_cast_add             -> VERIFICATION:- SUCCESSFUL
//   bug_array_store_cast_add              -> VERIFICATION:- FAILED (assertion)
//   safe_symbolic_index_store_load        -> VERIFICATION:- SUCCESSFUL
//   bug_symbolic_index_store_load         -> VERIFICATION:- FAILED (assertion)
//   safe_symbolic_index_store_as_ptr      -> VERIFICATION:- SUCCESSFUL
//   bug_symbolic_index_store_as_ptr       -> VERIFICATION:- FAILED (assertion)
//   safe_struct_atomic_field_as_ptr       -> VERIFICATION:- SUCCESSFUL
//   bug_struct_atomic_field_as_ptr        -> VERIFICATION:- FAILED (assertion)
//   safe_struct_atomic_field_cast_add     -> VERIFICATION:- SUCCESSFUL
//   bug_struct_atomic_field_cast_add      -> VERIFICATION:- FAILED (assertion)
//   safe_from_ptr_store_then_load         -> VERIFICATION:- SUCCESSFUL
//   bug_from_ptr_store_then_load          -> VERIFICATION:- FAILED (assertion)
//   safe_local_atomic_store_as_ptr        -> VERIFICATION:- SUCCESSFUL
//   bug_local_atomic_store_as_ptr         -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. The siblings of
// const_pointer_live_raw_read_dual.rs::bug_atomic_as_ptr_after_store, which
// the CHC lane PROVED in 2 ms on main ed592ea3d. A LIVE target's pointee is
// the lane's live state, or the lane fails closed
// (trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs). The CHC lane
// keeps a static in its state variable AND in a memory image seeded under
// every typed view of its type (an `AtomicU32` under `AtomicU32` and `u32`; a
// struct under itself and each field), and a pointer a call returns
// (`as_ptr`) or a cast makes reads the image. A store wrote one view, so the
// others kept the initializer; a store whose receiver the MIR derives from the
// static (`AS[1]`, `CT.b`) never reached the static at all, and one at a
// symbolic index left its state variable at the initializer.
//
// Measured on main ed592ea3d (bundle of f5dfb8d48, 30 s per harness, ay
// d80d17a90): CHC missed bugs bug_i64_store_as_ptr, bug_usize_store_as_ptr,
// bug_fetch_add_as_ptr, bug_swap_as_ptr, bug_as_ptr_write_then_load,
// bug_array_store_cast_add, bug_symbolic_index_store_load (whose safe twin was
// certified Genuine) and bug_struct_atomic_field_cast_add; BMC no wrong
// verdict. With every store into a static rewriting the whole image from the
// static's state (or havocking both), and call-model receivers traced through
// the MIR: no missed bug and no false certificate on either lane.

#![allow(dead_code)]
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicU32, AtomicUsize, Ordering};

static A: AtomicU32 = AtomicU32::new(5);
static B: AtomicBool = AtomicBool::new(false);
static I: AtomicI64 = AtomicI64::new(-3);
static U: AtomicUsize = AtomicUsize::new(10);
static AS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
struct Counters {
    a: AtomicU32,
    b: AtomicU32,
}
static CT: Counters = Counters { a: AtomicU32::new(1), b: AtomicU32::new(2) };

#[kani::proof]
fn safe_bool_store_as_ptr() {
    B.store(true, Ordering::SeqCst);
    unsafe { assert!(*B.as_ptr()) }
}
#[kani::proof]
fn bug_bool_store_as_ptr() {
    B.store(true, Ordering::SeqCst);
    unsafe { assert!(!*B.as_ptr()) }
}
#[kani::proof]
fn safe_i64_store_as_ptr() {
    I.store(-7, Ordering::SeqCst);
    unsafe { assert!(*I.as_ptr() == -7) }
}
#[kani::proof]
fn bug_i64_store_as_ptr() {
    I.store(-7, Ordering::SeqCst);
    unsafe { assert!(*I.as_ptr() == -3) }
}
#[kani::proof]
fn safe_usize_store_as_ptr() {
    U.store(7, Ordering::SeqCst);
    unsafe { assert!(*U.as_ptr() == 7) }
}
#[kani::proof]
fn bug_usize_store_as_ptr() {
    U.store(7, Ordering::SeqCst);
    unsafe { assert!(*U.as_ptr() == 10) }
}
#[kani::proof]
fn safe_fetch_add_as_ptr() {
    A.fetch_add(2, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 7) }
}
#[kani::proof]
fn bug_fetch_add_as_ptr() {
    A.fetch_add(2, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_swap_as_ptr() {
    A.swap(9, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 9) }
}
#[kani::proof]
fn bug_swap_as_ptr() {
    A.swap(9, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_compare_exchange_as_ptr() {
    let _ = A.compare_exchange(5, 9, Ordering::SeqCst, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 9) }
}
#[kani::proof]
fn bug_compare_exchange_as_ptr() {
    let _ = A.compare_exchange(5, 9, Ordering::SeqCst, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_compare_exchange_then_load() {
    let _ = A.compare_exchange(5, 9, Ordering::SeqCst, Ordering::SeqCst);
    assert!(A.load(Ordering::SeqCst) == 9);
}
#[kani::proof]
fn bug_compare_exchange_then_load() {
    let _ = A.compare_exchange(5, 9, Ordering::SeqCst, Ordering::SeqCst);
    assert!(A.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn safe_compare_exchange_result() {
    let r = A.compare_exchange(5, 9, Ordering::SeqCst, Ordering::SeqCst);
    assert!(r == Ok(5));
}
#[kani::proof]
fn bug_compare_exchange_result() {
    let r = A.compare_exchange(5, 9, Ordering::SeqCst, Ordering::SeqCst);
    assert!(r == Err(5));
}
#[kani::proof]
fn safe_as_ptr_write_then_load() {
    unsafe { *A.as_ptr() = 9 };
    assert!(A.load(Ordering::SeqCst) == 9);
}
#[kani::proof]
fn bug_as_ptr_write_then_load() {
    unsafe { *A.as_ptr() = 9 };
    assert!(A.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn safe_as_ptr_write_then_read() {
    unsafe { *A.as_ptr() = 9 };
    unsafe { assert!(*A.as_ptr() == 9) }
}
#[kani::proof]
fn bug_as_ptr_write_then_read() {
    unsafe { *A.as_ptr() = 9 };
    unsafe { assert!(*A.as_ptr() == 5) }
}
#[kani::proof]
fn safe_ref_cast_after_fetch_add() {
    A.fetch_add(1, Ordering::SeqCst);
    let p = &A as *const AtomicU32 as *const u32;
    unsafe { assert!(*p == 6) }
}
#[kani::proof]
fn bug_ref_cast_after_fetch_add() {
    A.fetch_add(1, Ordering::SeqCst);
    let p = &A as *const AtomicU32 as *const u32;
    unsafe { assert!(*p == 5) }
}
#[kani::proof]
fn safe_array_elem_store_as_ptr() {
    AS[1].store(7, Ordering::SeqCst);
    unsafe { assert!(*AS[1].as_ptr() == 7) }
}
#[kani::proof]
fn bug_array_elem_store_as_ptr() {
    AS[1].store(7, Ordering::SeqCst);
    unsafe { assert!(*AS[1].as_ptr() == 2) }
}
#[kani::proof]
fn safe_array_store_cast_add() {
    AS[1].store(7, Ordering::SeqCst);
    let p = (&AS as *const [AtomicU32; 2] as *const u32).wrapping_add(1);
    unsafe { assert!(*p == 7) }
}
#[kani::proof]
fn bug_array_store_cast_add() {
    AS[1].store(7, Ordering::SeqCst);
    let p = (&AS as *const [AtomicU32; 2] as *const u32).wrapping_add(1);
    unsafe { assert!(*p == 2) }
}
#[kani::proof]
fn safe_symbolic_index_store_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    AS[i].store(7, Ordering::SeqCst);
    assert!(AS[1].load(Ordering::SeqCst) == 7);
}
#[kani::proof]
fn bug_symbolic_index_store_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    AS[i].store(7, Ordering::SeqCst);
    assert!(AS[1].load(Ordering::SeqCst) == 2);
}
#[kani::proof]
fn safe_symbolic_index_store_as_ptr() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    AS[i].store(7, Ordering::SeqCst);
    unsafe { assert!(*AS[1].as_ptr() == 7) }
}
#[kani::proof]
fn bug_symbolic_index_store_as_ptr() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    AS[i].store(7, Ordering::SeqCst);
    unsafe { assert!(*AS[1].as_ptr() == 2) }
}
#[kani::proof]
fn safe_struct_atomic_field_as_ptr() {
    CT.b.store(9, Ordering::SeqCst);
    unsafe { assert!(*CT.b.as_ptr() == 9) }
}
#[kani::proof]
fn bug_struct_atomic_field_as_ptr() {
    CT.b.store(9, Ordering::SeqCst);
    unsafe { assert!(*CT.b.as_ptr() == 2) }
}
#[kani::proof]
fn safe_struct_atomic_field_cast_add() {
    CT.b.store(9, Ordering::SeqCst);
    let p = (&CT as *const Counters as *const u32).wrapping_add(1);
    unsafe { assert!(*p == 9) }
}
#[kani::proof]
fn bug_struct_atomic_field_cast_add() {
    CT.b.store(9, Ordering::SeqCst);
    let p = (&CT as *const Counters as *const u32).wrapping_add(1);
    unsafe { assert!(*p == 2) }
}
#[kani::proof]
fn safe_from_ptr_store_then_load() {
    let p = A.as_ptr();
    unsafe { AtomicU32::from_ptr(p).store(8, Ordering::SeqCst) };
    assert!(A.load(Ordering::SeqCst) == 8);
}
#[kani::proof]
fn bug_from_ptr_store_then_load() {
    let p = A.as_ptr();
    unsafe { AtomicU32::from_ptr(p).store(8, Ordering::SeqCst) };
    assert!(A.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn safe_local_atomic_store_as_ptr() {
    let a = AtomicU32::new(5);
    a.store(7, Ordering::SeqCst);
    unsafe { assert!(*a.as_ptr() == 7) }
}
#[kani::proof]
fn bug_local_atomic_store_as_ptr() {
    let a = AtomicU32::new(5);
    a.store(7, Ordering::SeqCst);
    unsafe { assert!(*a.as_ptr() == 5) }
}

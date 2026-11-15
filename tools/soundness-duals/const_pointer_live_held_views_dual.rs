// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_static_ref_array_sym_store_load    -> VERIFICATION:- SUCCESSFUL
//   bug_static_ref_array_sym_store_load     -> VERIFICATION:- FAILED (assertion)
//   safe_static_ref_array_sym_store_as_ptr  -> VERIFICATION:- SUCCESSFUL
//   bug_static_ref_array_sym_store_as_ptr   -> VERIFICATION:- FAILED (assertion)
//   safe_static_ref_elem_store_as_ptr       -> VERIFICATION:- SUCCESSFUL
//   bug_static_ref_elem_store_as_ptr        -> VERIFICATION:- FAILED (assertion)
//   safe_static_slice_sym_store_load        -> VERIFICATION:- SUCCESSFUL
//   bug_static_slice_sym_store_load         -> VERIFICATION:- FAILED (assertion)
//   safe_static_struct_ref_store_load       -> VERIFICATION:- SUCCESSFUL
//   bug_static_struct_ref_store_load        -> VERIFICATION:- FAILED (assertion)
//   safe_static_slice_as_ptr_write_load     -> VERIFICATION:- SUCCESSFUL
//   bug_static_slice_as_ptr_write_load      -> VERIFICATION:- FAILED (assertion)
//   safe_atomic_ptr_held_write_read         -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_ptr_held_write_read          -> VERIFICATION:- FAILED (assertion)
//   safe_byte_write_store_byte_read         -> VERIFICATION:- SUCCESSFUL
//   bug_byte_write_store_byte_read          -> VERIFICATION:- FAILED (assertion)
//   safe_byte_write_load                    -> VERIFICATION:- SUCCESSFUL
//   bug_byte_write_load                     -> VERIFICATION:- FAILED (assertion)
//   safe_store_byte_read                    -> VERIFICATION:- SUCCESSFUL
//   bug_store_byte_read                     -> VERIFICATION:- FAILED (assertion)
//   safe_byte_write_byte_read               -> VERIFICATION:- SUCCESSFUL
//   bug_byte_write_byte_read                -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. Two holes in what the CHC image sync rests on
// (review round 1 of fix/chc-atomic-as-ptr-live, findings 4 and 5).
// (1) An address another static's initializer holds (`static RS: [&AtomicU32;
// 2] = [&AS[0], &AS[1]]`, `static RSL: &[AtomicU32] = &BS`) reaches a call
// model's receiver through memory, so no local holds it and the havoc of an
// untraced receiver never named AS: `RS[i].store(7)` then `AS[1].load() == 2`
// PROVED. A LIVE static whose address an object's bytes, or a constant
// aggregate, hold now counts as reachable from every untraced receiver
// (`statics_held_in_memory`). (2) A store under a view the image sync never
// rewrites (a `u8` under an `AtomicU32`) left a cell no later store updated:
// `*(A.as_ptr() as *mut u8) = 9; A.store(0); *(A.as_ptr() as *const u8) == 9`
// PROVED. Such a cell, with another store into the same static, now fails the
// harness closed (`static_image_view_unsynced`); alone it stays exact.
//
// Measured 2026-10-15 (30 s per harness, ay d80d17a90, frozen nightly; this
// branch's round-1 bundle, compiler d52360f5e06d, by the strict dual gate;
// main and round 0 by the same driver invocation, one run per harness): CHC
// on main f5dfb8d48's bundle 4 missed bugs and 0 false certificates; on round
// 0 (compiler f78b21069ddb) 3 missed bugs and 0 false certificates; here 0
// missed bugs and 0 false certificates, 13 of 22 rows match. BMC (unchanged
// code): no missed bug or false certificate. The remaining red rows are
// known-red in the manifest with their cause.

#![allow(dead_code, static_mut_refs)]
use std::sync::atomic::{AtomicPtr, AtomicU32, Ordering};

static A: AtomicU32 = AtomicU32::new(5);
static AS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static RS: [&AtomicU32; 2] = [&AS[0], &AS[1]];
static AP: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static RP: [&AtomicU32; 2] = [&AP[0], &AP[1]];
static AE: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static PA: &AtomicU32 = &AE[1];
static BS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static RSL: &[AtomicU32] = &BS;
static CS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static CSL: &[AtomicU32] = &CS;
struct H {
    r: &'static AtomicU32,
}
static HA: AtomicU32 = AtomicU32::new(5);
static HH: H = H { r: &HA };
static mut Y: u32 = 5;
static P: AtomicPtr<u32> = AtomicPtr::new(&raw mut Y);
static BYTE: AtomicU32 = AtomicU32::new(5);
static BYTE_LOAD: AtomicU32 = AtomicU32::new(5);
static BYTE_STORE: AtomicU32 = AtomicU32::new(5);
static BYTE_ALONE: AtomicU32 = AtomicU32::new(5);

// A reference another static's initializer holds: the store's receiver is
// loaded from memory, so no local holds the target's address.
#[kani::proof]
fn safe_static_ref_array_sym_store_load() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    RS[i].store(7, Ordering::SeqCst);
    assert!(i == 0 || AS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_static_ref_array_sym_store_load() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    RS[i].store(7, Ordering::SeqCst);
    assert!(i == 0 || AS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_static_ref_array_sym_store_as_ptr() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    RP[i].store(7, Ordering::SeqCst);
    unsafe { assert!(*AP[1].as_ptr() == 7) }
}
#[kani::proof]
fn bug_static_ref_array_sym_store_as_ptr() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    RP[i].store(7, Ordering::SeqCst);
    unsafe { assert!(*AP[1].as_ptr() == 2) }
}
#[kani::proof]
fn safe_static_ref_elem_store_as_ptr() {
    PA.store(7, Ordering::SeqCst);
    unsafe { assert!(*AE[1].as_ptr() == 7) }
}
#[kani::proof]
fn bug_static_ref_elem_store_as_ptr() {
    PA.store(7, Ordering::SeqCst);
    unsafe { assert!(*AE[1].as_ptr() == 2) }
}
#[kani::proof]
fn safe_static_slice_sym_store_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    RSL[i].store(7, Ordering::SeqCst);
    assert!(BS[1].load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_static_slice_sym_store_load() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    RSL[i].store(7, Ordering::SeqCst);
    assert!(BS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_static_struct_ref_store_load() {
    HH.r.store(7, Ordering::SeqCst);
    assert!(HA.load(Ordering::SeqCst) == 7)
}
#[kani::proof]
fn bug_static_struct_ref_store_load() {
    HH.r.store(7, Ordering::SeqCst);
    assert!(HA.load(Ordering::SeqCst) == 5)
}
// A raw store through a pointer memory holds.
#[kani::proof]
fn safe_static_slice_as_ptr_write_load() {
    unsafe { *CSL[1].as_ptr() = 9 };
    assert!(CS[1].load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_static_slice_as_ptr_write_load() {
    unsafe { *CSL[1].as_ptr() = 9 };
    assert!(CS[1].load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_atomic_ptr_held_write_read() {
    unsafe { *P.load(Ordering::SeqCst) = 9 };
    unsafe { assert!(Y == 9) }
}
#[kani::proof]
fn bug_atomic_ptr_held_write_read() {
    unsafe { *P.load(Ordering::SeqCst) = 9 };
    unsafe { assert!(Y == 5) }
}
// A byte under an `AtomicU32`: a cell the image sync does not rewrite.
#[kani::proof]
fn safe_byte_write_store_byte_read() {
    unsafe { *(BYTE.as_ptr() as *mut u8) = 9 };
    BYTE.store(0, Ordering::SeqCst);
    unsafe { assert!(*(BYTE.as_ptr() as *const u8) == 0) }
}
#[kani::proof]
fn bug_byte_write_store_byte_read() {
    unsafe { *(BYTE.as_ptr() as *mut u8) = 9 };
    BYTE.store(0, Ordering::SeqCst);
    unsafe { assert!(*(BYTE.as_ptr() as *const u8) == 9) }
}
#[kani::proof]
fn safe_byte_write_load() {
    unsafe { *(BYTE_LOAD.as_ptr() as *mut u8) = 9 };
    assert!(BYTE_LOAD.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_byte_write_load() {
    unsafe { *(BYTE_LOAD.as_ptr() as *mut u8) = 9 };
    assert!(BYTE_LOAD.load(Ordering::SeqCst) == 5)
}
#[kani::proof]
fn safe_store_byte_read() {
    BYTE_STORE.store(0x0102_0304, Ordering::SeqCst);
    unsafe { assert!(*(BYTE_STORE.as_ptr() as *const u8) == 4) }
}
#[kani::proof]
fn bug_store_byte_read() {
    BYTE_STORE.store(0x0102_0304, Ordering::SeqCst);
    unsafe { assert!(*(BYTE_STORE.as_ptr() as *const u8) == 5) }
}
#[kani::proof]
fn safe_byte_write_byte_read() {
    unsafe { *(BYTE_ALONE.as_ptr() as *mut u8) = 9 };
    unsafe { assert!(*(BYTE_ALONE.as_ptr() as *const u8) == 9) }
}
#[kani::proof]
fn bug_byte_write_byte_read() {
    unsafe { *(BYTE_ALONE.as_ptr() as *mut u8) = 9 };
    unsafe { assert!(*(BYTE_ALONE.as_ptr() as *const u8) == 5) }
}

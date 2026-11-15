// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_fetch_sub_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_sub_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_fetch_or_as_ptr           -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_or_as_ptr            -> VERIFICATION:- FAILED (assertion)
//   safe_fetch_and_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_and_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_fetch_xor_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_xor_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_fetch_nand_as_ptr         -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_nand_as_ptr          -> VERIFICATION:- FAILED (assertion)
//   safe_fetch_max_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_max_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_fetch_min_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_fetch_min_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_bool_fetch_or_byte        -> VERIFICATION:- SUCCESSFUL
//   bug_bool_fetch_or_byte         -> VERIFICATION:- FAILED (assertion)
//   safe_bool_swap_byte            -> VERIFICATION:- SUCCESSFUL
//   bug_bool_swap_byte             -> VERIFICATION:- FAILED (assertion)
//   safe_bool_as_ptr_write_load    -> VERIFICATION:- SUCCESSFUL
//   bug_bool_as_ptr_write_load     -> VERIFICATION:- FAILED (assertion)
//   safe_u8_store_as_ptr           -> VERIFICATION:- SUCCESSFUL
//   bug_u8_store_as_ptr            -> VERIFICATION:- FAILED (assertion)
//   safe_i8_store_as_ptr           -> VERIFICATION:- SUCCESSFUL
//   bug_i8_store_as_ptr            -> VERIFICATION:- FAILED (assertion)
//   safe_u16_store_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_u16_store_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_i32_fetch_add_as_ptr      -> VERIFICATION:- SUCCESSFUL
//   bug_i32_fetch_add_as_ptr       -> VERIFICATION:- FAILED (assertion)
//   safe_u64_store_as_ptr          -> VERIFICATION:- SUCCESSFUL
//   bug_u64_store_as_ptr           -> VERIFICATION:- FAILED (assertion)
//   safe_isize_swap_as_ptr         -> VERIFICATION:- SUCCESSFUL
//   bug_isize_swap_as_ptr          -> VERIFICATION:- FAILED (assertion)
//   safe_as_ptr_method_write_load  -> VERIFICATION:- SUCCESSFUL
//   bug_as_ptr_method_write_load   -> VERIFICATION:- FAILED (assertion)
//   safe_ptr_replace_load          -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_replace_load           -> VERIFICATION:- FAILED (assertion)
//   safe_as_ptr_add_assign_load    -> VERIFICATION:- SUCCESSFUL
//   bug_as_ptr_add_assign_load     -> VERIFICATION:- FAILED (assertion)
//   safe_ptr_before_store_read     -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_before_store_read      -> VERIFICATION:- FAILED (assertion)
//   safe_store_write_store_load    -> VERIFICATION:- SUCCESSFUL
//   bug_store_write_store_load     -> VERIFICATION:- FAILED (assertion)
//   safe_symbolic_store_as_ptr     -> VERIFICATION:- SUCCESSFUL
//   bug_symbolic_store_as_ptr      -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. Shapes the round-1 review of
// fix/chc-atomic-as-ptr-live probed on which main's CHC lane gave a wrong
// verdict and that branch's first round fixed: atomic statics of every width
// written by store, swap, every fetch_* RMW, ptr::replace and `*as_ptr() op=`,
// then read through `as_ptr` or `load`. They are rows so that a change to the
// image sync or its routes cannot reopen them unseen.
//
// Measured 2026-10-15 (30 s per harness, ay d80d17a90, frozen nightly; this
// branch's round-1 bundle, compiler d52360f5e06d, by the strict dual gate;
// main and round 0 by the same driver invocation, one run per harness): CHC
// on main f5dfb8d48's bundle 22 missed bugs and 0 false certificates; on
// round 0 (compiler f78b21069ddb) 0 missed bugs and 0 false certificates;
// here 0 missed bugs and 0 false certificates, 43 of 44 rows match. BMC
// (unchanged code): no missed bug or false certificate. The remaining red
// rows are known-red in the manifest with their cause.

#![allow(dead_code, static_mut_refs)]
use std::sync::atomic::{
    AtomicBool, AtomicI32, AtomicI8, AtomicIsize, AtomicPtr, AtomicU16, AtomicU32, AtomicU64,
    AtomicU8, Ordering,
};

static A: AtomicU32 = AtomicU32::new(5);
static B: AtomicBool = AtomicBool::new(false);
static U8: AtomicU8 = AtomicU8::new(5);
static I8: AtomicI8 = AtomicI8::new(-5);
static U16: AtomicU16 = AtomicU16::new(500);
static I32: AtomicI32 = AtomicI32::new(-5);
static U64: AtomicU64 = AtomicU64::new(1 << 40);
static IS: AtomicIsize = AtomicIsize::new(-9);
static mut TGT: u32 = 3;
static AP: AtomicPtr<u32> = AtomicPtr::new(std::ptr::null_mut());

#[kani::proof]
fn safe_fetch_sub_as_ptr() { A.fetch_sub(2, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 3) } }
#[kani::proof]
fn bug_fetch_sub_as_ptr() { A.fetch_sub(2, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_fetch_or_as_ptr() { A.fetch_or(8, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 13) } }
#[kani::proof]
fn bug_fetch_or_as_ptr() { A.fetch_or(8, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_fetch_and_as_ptr() { A.fetch_and(4, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 4) } }
#[kani::proof]
fn bug_fetch_and_as_ptr() { A.fetch_and(4, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_fetch_xor_as_ptr() { A.fetch_xor(1, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 4) } }
#[kani::proof]
fn bug_fetch_xor_as_ptr() { A.fetch_xor(1, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_fetch_nand_as_ptr() { A.fetch_nand(1, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == !1u32) } }
#[kani::proof]
fn bug_fetch_nand_as_ptr() { A.fetch_nand(1, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_fetch_max_as_ptr() { A.fetch_max(9, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 9) } }
#[kani::proof]
fn bug_fetch_max_as_ptr() { A.fetch_max(9, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_fetch_min_as_ptr() { A.fetch_min(2, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 2) } }
#[kani::proof]
fn bug_fetch_min_as_ptr() { A.fetch_min(2, Ordering::SeqCst); unsafe { assert!(*A.as_ptr() == 5) } }
#[kani::proof]
fn safe_bool_fetch_or_byte() {
    B.fetch_or(true, Ordering::SeqCst);
    unsafe { assert!(*(B.as_ptr() as *const u8) == 1) }
}
#[kani::proof]
fn bug_bool_fetch_or_byte() {
    B.fetch_or(true, Ordering::SeqCst);
    unsafe { assert!(*(B.as_ptr() as *const u8) == 0) }
}
#[kani::proof]
fn safe_bool_swap_byte() {
    B.swap(true, Ordering::SeqCst);
    unsafe { assert!(*(B.as_ptr() as *const u8) == 1) }
}
#[kani::proof]
fn bug_bool_swap_byte() {
    B.swap(true, Ordering::SeqCst);
    unsafe { assert!(*(B.as_ptr() as *const u8) == 0) }
}
#[kani::proof]
fn safe_bool_as_ptr_write_load() { unsafe { *B.as_ptr() = true }; assert!(B.load(Ordering::SeqCst)) }
#[kani::proof]
fn bug_bool_as_ptr_write_load() { unsafe { *B.as_ptr() = true }; assert!(!B.load(Ordering::SeqCst)) }
#[kani::proof]
fn safe_u8_store_as_ptr() { U8.store(7, Ordering::SeqCst); unsafe { assert!(*U8.as_ptr() == 7) } }
#[kani::proof]
fn bug_u8_store_as_ptr() { U8.store(7, Ordering::SeqCst); unsafe { assert!(*U8.as_ptr() == 5) } }
#[kani::proof]
fn safe_i8_store_as_ptr() { I8.store(-7, Ordering::SeqCst); unsafe { assert!(*I8.as_ptr() == -7) } }
#[kani::proof]
fn bug_i8_store_as_ptr() { I8.store(-7, Ordering::SeqCst); unsafe { assert!(*I8.as_ptr() == -5) } }
#[kani::proof]
fn safe_u16_store_as_ptr() { U16.store(7, Ordering::SeqCst); unsafe { assert!(*U16.as_ptr() == 7) } }
#[kani::proof]
fn bug_u16_store_as_ptr() { U16.store(7, Ordering::SeqCst); unsafe { assert!(*U16.as_ptr() == 500) } }
#[kani::proof]
fn safe_i32_fetch_add_as_ptr() { I32.fetch_add(2, Ordering::SeqCst); unsafe { assert!(*I32.as_ptr() == -3) } }
#[kani::proof]
fn bug_i32_fetch_add_as_ptr() { I32.fetch_add(2, Ordering::SeqCst); unsafe { assert!(*I32.as_ptr() == -5) } }
#[kani::proof]
fn safe_u64_store_as_ptr() { U64.store(7, Ordering::SeqCst); unsafe { assert!(*U64.as_ptr() == 7) } }
#[kani::proof]
fn bug_u64_store_as_ptr() { U64.store(7, Ordering::SeqCst); unsafe { assert!(*U64.as_ptr() == 1 << 40) } }
#[kani::proof]
fn safe_isize_swap_as_ptr() { IS.swap(4, Ordering::SeqCst); unsafe { assert!(*IS.as_ptr() == 4) } }
#[kani::proof]
fn bug_isize_swap_as_ptr() { IS.swap(4, Ordering::SeqCst); unsafe { assert!(*IS.as_ptr() == -9) } }
#[kani::proof]
fn safe_as_ptr_method_write_load() { unsafe { A.as_ptr().write(9) }; assert!(A.load(Ordering::SeqCst) == 9) }
#[kani::proof]
fn bug_as_ptr_method_write_load() { unsafe { A.as_ptr().write(9) }; assert!(A.load(Ordering::SeqCst) == 5) }
#[kani::proof]
fn safe_ptr_replace_load() {
    let old = unsafe { std::ptr::replace(A.as_ptr(), 9) };
    assert!(old == 5 && A.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_ptr_replace_load() {
    let _old = unsafe { std::ptr::replace(A.as_ptr(), 9) };
    assert!(A.load(Ordering::SeqCst) == 5)
}
#[kani::proof]
fn safe_as_ptr_add_assign_load() { unsafe { *A.as_ptr() += 1 }; assert!(A.load(Ordering::SeqCst) == 6) }
#[kani::proof]
fn bug_as_ptr_add_assign_load() { unsafe { *A.as_ptr() += 1 }; assert!(A.load(Ordering::SeqCst) == 5) }
#[kani::proof]
fn safe_ptr_before_store_read() {
    let p = A.as_ptr();
    A.store(7, Ordering::SeqCst);
    unsafe { assert!(*p == 7) }
}
#[kani::proof]
fn bug_ptr_before_store_read() {
    let p = A.as_ptr();
    A.store(7, Ordering::SeqCst);
    unsafe { assert!(*p == 5) }
}
#[kani::proof]
fn safe_store_write_store_load() {
    A.store(7, Ordering::SeqCst);
    unsafe { *A.as_ptr() = 8 };
    A.fetch_add(1, Ordering::SeqCst);
    assert!(A.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_store_write_store_load() {
    A.store(7, Ordering::SeqCst);
    unsafe { *A.as_ptr() = 8 };
    A.fetch_add(1, Ordering::SeqCst);
    assert!(A.load(Ordering::SeqCst) == 8)
}
#[kani::proof]
fn safe_symbolic_store_as_ptr() {
    let v: u32 = kani::any();
    A.store(v, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == v) }
}
#[kani::proof]
fn bug_symbolic_store_as_ptr() {
    let v: u32 = kani::any();
    A.store(v, Ordering::SeqCst);
    unsafe { assert!(*A.as_ptr() == 5) }
}

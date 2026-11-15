// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_interior_write_through_offset_ptr -> VERIFICATION:- SUCCESSFUL
//   bug_interior_write_through_offset_ptr  -> VERIFICATION:- FAILED (assertion)
//   safe_interior_read_initial             -> VERIFICATION:- SUCCESSFUL
//   bug_interior_read_initial              -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. An interior-mutable static (`UnsafeCell`, not `static
// mut`) reached ONLY through another static's initializer is still one object
// whose bytes a harness can read: the targets a harness can reach are the
// transitive closure of relocations through every reached target's bytes. The
// rule is stated once, in trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (round-10 challenge, 30 s per harness, ay
// 48c98a43d): `safe_interior_read_initial` FAILED certified Genuine on BOTH lanes
// (CHC never gave `RC` an object; BMC read `RP.0` as its raw offset).

#![allow(dead_code)]

use std::cell::UnsafeCell;
struct Racy(UnsafeCell<[u32; 2]>);
unsafe impl Sync for Racy {}
static RC: Racy = Racy(UnsafeCell::new([1, 2]));
struct SyncPtr(*mut u32);
unsafe impl Sync for SyncPtr {}
static RP: SyncPtr = SyncPtr(unsafe { (RC.0.get() as *mut u32).add(1) });

#[kani::proof]
fn safe_interior_write_through_offset_ptr() {
    unsafe {
        *RP.0 = 7;
        assert!((*RC.0.get())[1] == 7);
    }
}

#[kani::proof]
fn bug_interior_write_through_offset_ptr() {
    unsafe {
        *RP.0 = 7;
        assert!((*RC.0.get())[1] == 2);
    }
}

#[kani::proof]
fn safe_interior_read_initial() {
    unsafe {
        assert!(*RP.0 == 2);
    }
}

#[kani::proof]
fn bug_interior_read_initial() {
    unsafe {
        assert!(*RP.0 == 1);
    }
}

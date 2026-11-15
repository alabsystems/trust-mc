// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_cell_get_write_then_get_read      -> VERIFICATION:- SUCCESSFUL
//   bug_cell_get_write_then_get_read       -> VERIFICATION:- FAILED (assertion)
//   safe_sync_cell_write_then_cast_read    -> VERIFICATION:- SUCCESSFUL
//   bug_sync_cell_write_then_cast_read     -> VERIFICATION:- FAILED (assertion)
//   safe_sync_cell_write_then_get_read     -> VERIFICATION:- SUCCESSFUL
//   bug_sync_cell_write_then_get_read      -> VERIFICATION:- FAILED (assertion)
//   safe_sync_cell_set_as_ptr              -> VERIFICATION:- SUCCESSFUL
//   bug_sync_cell_set_as_ptr               -> VERIFICATION:- FAILED (assertion)
//   safe_sync_cell_set_get                 -> VERIFICATION:- SUCCESSFUL
//   bug_sync_cell_set_get                  -> VERIFICATION:- FAILED (assertion)
//   safe_mut_static_write_then_addr_read   -> VERIFICATION:- SUCCESSFUL
//   bug_mut_static_write_then_addr_read    -> VERIFICATION:- FAILED (assertion)
//   safe_mut_static_raw_write_then_read    -> VERIFICATION:- SUCCESSFUL
//   bug_mut_static_raw_write_then_read     -> VERIFICATION:- FAILED (assertion)
//   safe_mut_tuple_field_then_cast_read    -> VERIFICATION:- SUCCESSFUL
//   bug_mut_tuple_field_then_cast_read     -> VERIFICATION:- FAILED (assertion)
//   safe_mut_struct_field_then_cast_add    -> VERIFICATION:- SUCCESSFUL
//   bug_mut_struct_field_then_cast_add     -> VERIFICATION:- FAILED (assertion)
//   safe_mut_struct_whole_then_field_ptr   -> VERIFICATION:- SUCCESSFUL
//   bug_mut_struct_whole_then_field_ptr    -> VERIFICATION:- FAILED (assertion)
//   safe_mut_array_symbolic_raw_write_then_index -> VERIFICATION:- SUCCESSFUL
//   bug_mut_array_symbolic_raw_write_then_index  -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. The interior-mutable and `static mut` siblings of
// const_pointer_live_raw_read_dual.rs: an `UnsafeCell`, a `SyncUnsafeCell`
// and a `Cell` behind a `Sync` wrapper, and `static mut` scalars, tuples and
// structs, each written and then read through another view of the same bytes
// (a cast of the static's reference, `get`/`as_ptr`, a field pointer). A LIVE
// target's pointee is the lane's live state, or the lane fails closed
// (trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs). The CHC lane's
// static stores now rewrite the static's whole memory image from its state
// (`stmt/codegen_stmt_store/static_image.rs`, `sync_static_image`), so no
// view a raw read selects keeps the initializer.
//
// Measured on main ed592ea3d (bundle of f5dfb8d48, 30 s per harness, ay
// d80d17a90) and with the image rule: no missed bug and no false certificate
// on either lane; the safe rows that fail closed are recorded known-red
// false-failure.

#![allow(dead_code, static_mut_refs)]
#![feature(sync_unsafe_cell)]
use std::cell::{Cell, SyncUnsafeCell, UnsafeCell};
use std::ptr::{addr_of, addr_of_mut};

struct S(UnsafeCell<u32>);
unsafe impl Sync for S {}
static C: S = S(UnsafeCell::new(3));
static SC: SyncUnsafeCell<u32> = SyncUnsafeCell::new(3);
struct SyncCell(Cell<u32>);
unsafe impl Sync for SyncCell {}
static CS: SyncCell = SyncCell(Cell::new(3));
static mut X: u32 = 5;
static mut P: (u32, u32) = (1, 2);
#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}
static mut Q: Pair = Pair { a: 1, b: 2 };
static mut M: [u32; 2] = [1, 2];

#[kani::proof]
fn safe_cell_get_write_then_get_read() {
    unsafe { *C.0.get() = 4 };
    unsafe { assert!(*C.0.get() == 4) }
}
#[kani::proof]
fn bug_cell_get_write_then_get_read() {
    unsafe { *C.0.get() = 4 };
    unsafe { assert!(*C.0.get() == 3) }
}
#[kani::proof]
fn safe_sync_cell_write_then_cast_read() {
    unsafe { *SC.get() = 4 };
    let q = &SC as *const SyncUnsafeCell<u32> as *const u32;
    unsafe { assert!(*q == 4) }
}
#[kani::proof]
fn bug_sync_cell_write_then_cast_read() {
    unsafe { *SC.get() = 4 };
    let q = &SC as *const SyncUnsafeCell<u32> as *const u32;
    unsafe { assert!(*q == 3) }
}
#[kani::proof]
fn safe_sync_cell_write_then_get_read() {
    unsafe { *SC.get() = 4 };
    unsafe { assert!(*SC.get() == 4) }
}
#[kani::proof]
fn bug_sync_cell_write_then_get_read() {
    unsafe { *SC.get() = 4 };
    unsafe { assert!(*SC.get() == 3) }
}
#[kani::proof]
fn safe_sync_cell_set_as_ptr() {
    CS.0.set(4);
    unsafe { assert!(*CS.0.as_ptr() == 4) }
}
#[kani::proof]
fn bug_sync_cell_set_as_ptr() {
    CS.0.set(4);
    unsafe { assert!(*CS.0.as_ptr() == 3) }
}
#[kani::proof]
fn safe_sync_cell_set_get() {
    CS.0.set(4);
    assert!(CS.0.get() == 4);
}
#[kani::proof]
fn bug_sync_cell_set_get() {
    CS.0.set(4);
    assert!(CS.0.get() == 3);
}
#[kani::proof]
fn safe_mut_static_write_then_addr_read() {
    unsafe {
        X = 7;
        assert!(*addr_of!(X) == 7);
    }
}
#[kani::proof]
fn bug_mut_static_write_then_addr_read() {
    unsafe {
        X = 7;
        assert!(*addr_of!(X) == 5);
    }
}
#[kani::proof]
fn safe_mut_static_raw_write_then_read() {
    unsafe {
        *addr_of_mut!(X) = 7;
        assert!(X == 7);
    }
}
#[kani::proof]
fn bug_mut_static_raw_write_then_read() {
    unsafe {
        *addr_of_mut!(X) = 7;
        assert!(X == 5);
    }
}
#[kani::proof]
fn safe_mut_tuple_field_then_cast_read() {
    unsafe {
        P.0 = 3;
        assert!(*(addr_of!(P) as *const u32) == 3);
    }
}
#[kani::proof]
fn bug_mut_tuple_field_then_cast_read() {
    unsafe {
        P.0 = 3;
        assert!(*(addr_of!(P) as *const u32) == 1);
    }
}
#[kani::proof]
fn safe_mut_struct_field_then_cast_add() {
    unsafe {
        Q.b = 4;
        assert!(*(addr_of!(Q) as *const u32).add(1) == 4);
    }
}
#[kani::proof]
fn bug_mut_struct_field_then_cast_add() {
    unsafe {
        Q.b = 4;
        assert!(*(addr_of!(Q) as *const u32).add(1) == 2);
    }
}
#[kani::proof]
fn safe_mut_struct_whole_then_field_ptr() {
    unsafe {
        Q = Pair { a: 5, b: 6 };
        assert!(*addr_of!(Q.b) == 6);
    }
}
#[kani::proof]
fn bug_mut_struct_whole_then_field_ptr() {
    unsafe {
        Q = Pair { a: 5, b: 6 };
        assert!(*addr_of!(Q.b) == 2);
    }
}
#[kani::proof]
fn safe_mut_array_symbolic_raw_write_then_index() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    unsafe {
        let p = addr_of_mut!(M) as *mut u32;
        *p.add(i) = 9;
        assert!(M[1] == 9);
    }
}
#[kani::proof]
fn bug_mut_array_symbolic_raw_write_then_index() {
    let i: usize = kani::any();
    kani::assume(i == 1);
    unsafe {
        let p = addr_of_mut!(M) as *mut u32;
        *p.add(i) = 9;
        assert!(M[1] == 2);
    }
}

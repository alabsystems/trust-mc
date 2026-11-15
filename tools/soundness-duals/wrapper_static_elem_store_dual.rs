// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- element stores into wrapper statics (MaybeUninit, an UnsafeCell in an
//! immutable static, ManuallyDrop) and a static cast through *mut u8, through the wrapper's own
//! pointer methods, read back through the wrapper; the MaybeUninit lazy-init pattern was certified
//! Genuine on the branch (review of fix/chc-lost-writes, lostwrite round 1, finding 1).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_maybeuninit_static_mut_elem_store     -> SUCCESSFUL
//!   bug_maybeuninit_static_mut_elem_store      -> FAILED ('assertion failed: (*addr_of!(M2)).assume_init_ref()[1] == 2')
//!   safe_maybeuninit_lazy_init                 -> SUCCESSFUL
//!   bug_maybeuninit_lazy_init                  -> FAILED ('assertion failed: v[1] == 3')
//!   safe_unsafecell_static_elem_store          -> SUCCESSFUL
//!   bug_unsafecell_static_elem_store           -> FAILED ('assertion failed: (*C2.0.get())[1] == 2')
//!   safe_unsafecell_static_elem_store_ref_read -> SUCCESSFUL
//!   bug_unsafecell_static_elem_store_ref_read  -> FAILED ('assertion failed: r[1] == 2')
//!   safe_manuallydrop_static_mut_elem_store    -> SUCCESSFUL
//!   bug_manuallydrop_static_mut_elem_store     -> FAILED ('assertion failed: (&(*addr_of!(D2)))[1] == 2')
//!   safe_static_mut_cast_ptr_elem_store        -> SUCCESSFUL
//!   bug_static_mut_cast_ptr_elem_store         -> FAILED ('assertion failed: E2[1] == 2')
//!
#![allow(unused)]
use std::cell::UnsafeCell;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ptr::{addr_of, addr_of_mut};

static mut M1: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 2]);
#[kani::proof]
fn safe_maybeuninit_static_mut_elem_store() {
    unsafe {
        (*(*addr_of_mut!(M1)).as_mut_ptr())[1] = 5;
        assert!((*addr_of!(M1)).assume_init_ref()[1] == 5);
    }
}
static mut M2: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 2]);
#[kani::proof]
fn bug_maybeuninit_static_mut_elem_store() {
    unsafe {
        (*(*addr_of_mut!(M2)).as_mut_ptr())[1] = 5;
        assert!((*addr_of!(M2)).assume_init_ref()[1] == 2);
    }
}
static mut M3: MaybeUninit<[u16; 2]> = MaybeUninit::uninit();
#[kani::proof]
fn safe_maybeuninit_lazy_init() {
    unsafe {
        let p = (*addr_of_mut!(M3)).as_mut_ptr();
        (*p)[0] = 3;
        (*p)[1] = 4;
        let v = (*addr_of!(M3)).assume_init();
        assert!(v[1] == 4);
    }
}
static mut M4: MaybeUninit<[u16; 2]> = MaybeUninit::uninit();
#[kani::proof]
fn bug_maybeuninit_lazy_init() {
    unsafe {
        let p = (*addr_of_mut!(M4)).as_mut_ptr();
        (*p)[0] = 3;
        (*p)[1] = 4;
        let v = (*addr_of!(M4)).assume_init();
        assert!(v[1] == 3);
    }
}
struct SyncCell(UnsafeCell<[u16; 2]>);
unsafe impl Sync for SyncCell {}
static C1: SyncCell = SyncCell(UnsafeCell::new([1, 2]));
#[kani::proof]
fn safe_unsafecell_static_elem_store() {
    unsafe {
        (*C1.0.get())[1] = 5;
        assert!((*C1.0.get())[1] == 5);
    }
}
static C2: SyncCell = SyncCell(UnsafeCell::new([1, 2]));
#[kani::proof]
fn bug_unsafecell_static_elem_store() {
    unsafe {
        (*C2.0.get())[1] = 5;
        assert!((*C2.0.get())[1] == 2);
    }
}
static C3: SyncCell = SyncCell(UnsafeCell::new([1, 2]));
#[kani::proof]
fn safe_unsafecell_static_elem_store_ref_read() {
    unsafe {
        (*C3.0.get())[1] = 5;
        let r: &[u16; 2] = &*C3.0.get();
        assert!(r[1] == 5);
    }
}
static C4: SyncCell = SyncCell(UnsafeCell::new([1, 2]));
#[kani::proof]
fn bug_unsafecell_static_elem_store_ref_read() {
    unsafe {
        (*C4.0.get())[1] = 5;
        let r: &[u16; 2] = &*C4.0.get();
        assert!(r[1] == 2);
    }
}
static mut D1: ManuallyDrop<[u16; 2]> = ManuallyDrop::new([1, 2]);
#[kani::proof]
fn safe_manuallydrop_static_mut_elem_store() {
    unsafe {
        let p: *mut [u16; 2] = addr_of_mut!(D1) as *mut [u16; 2];
        (*p)[1] = 5;
        assert!((&(*addr_of!(D1)))[1] == 5);
    }
}
static mut D2: ManuallyDrop<[u16; 2]> = ManuallyDrop::new([1, 2]);
#[kani::proof]
fn bug_manuallydrop_static_mut_elem_store() {
    unsafe {
        let p: *mut [u16; 2] = addr_of_mut!(D2) as *mut [u16; 2];
        (*p)[1] = 5;
        assert!((&(*addr_of!(D2)))[1] == 2);
    }
}
static mut E1: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_mut_cast_ptr_elem_store() {
    unsafe {
        let p: *mut [u16; 2] = addr_of_mut!(E1) as *mut u8 as *mut [u16; 2];
        (*p)[1] = 5;
        assert!(E1[1] == 5);
    }
}
static mut E2: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_mut_cast_ptr_elem_store() {
    unsafe {
        let p: *mut [u16; 2] = addr_of_mut!(E2) as *mut u8 as *mut [u16; 2];
        (*p)[1] = 5;
        assert!(E2[1] == 2);
    }
}

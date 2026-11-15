// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a byte or wide writer from a non-pointer field's address
//! (`addr_of_mut!(s.x)`, a `u64`) reaching the sibling pointer field `s.p`:
//! walked forwards, backwards, by `copy_nonoverlapping` and `write_bytes`
//! (review of fix/chc-lost-writes round 3, finding 3: fail-closed on both
//! bundles).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_write_bytes_from_int_field_nulls_ptr_field -> FAILED ('null pointer dereference occurred')
//!   bug_copy_bytes_from_int_field_rebinds_ptr_field -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_bytes_from_int_field_rebinds_ptr_field -> SUCCESSFUL
//!   bug_wide_store_from_int_field_rebinds_ptr_field -> FAILED ('assertion failed: *y != 7')
//!   safe_wide_store_from_int_field_rebinds_ptr_field -> SUCCESSFUL
//!   bug_backwards_from_int_field_rebinds_ptr_field -> FAILED ('assertion failed: *y != 7')
//!   safe_backwards_from_int_field_rebinds_ptr_field -> SUCCESSFUL
//!
#![allow(unused)]
use std::ptr::{addr_of_mut, copy_nonoverlapping, write_bytes};

#[repr(C)]
struct S {
    x: u64,
    p: *mut u32,
}

#[kani::proof]
fn bug_write_bytes_from_int_field_nulls_ptr_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut s = S { x: 1, p: &mut *bx };
    unsafe { write_bytes(addr_of_mut!(s.x) as *mut u8, 0, 16) };
    unsafe {
        *s.p = 7;
    }
    assert!(*bx == 7);
}

#[kani::proof]
fn bug_copy_bytes_from_int_field_rebinds_ptr_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut s = S { x: 1, p: &mut *bx };
    let src: [u64; 2] = [0, yp as u64];
    unsafe { copy_nonoverlapping(src.as_ptr() as *const u8, addr_of_mut!(s.x) as *mut u8, 16) };
    unsafe {
        *s.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_bytes_from_int_field_rebinds_ptr_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut s = S { x: 1, p: &mut *bx };
    let src: [u64; 2] = [0, yp as u64];
    unsafe { copy_nonoverlapping(src.as_ptr() as *const u8, addr_of_mut!(s.x) as *mut u8, 16) };
    unsafe {
        *s.p = 7;
    }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_wide_store_from_int_field_rebinds_ptr_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut s = S { x: 1, p: &mut *bx };
    unsafe {
        *(addr_of_mut!(s.x) as *mut [u64; 2]) = [0, yp as u64];
    }
    unsafe {
        *s.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_wide_store_from_int_field_rebinds_ptr_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut s = S { x: 1, p: &mut *bx };
    unsafe {
        *(addr_of_mut!(s.x) as *mut [u64; 2]) = [0, yp as u64];
    }
    unsafe {
        *s.p = 7;
    }
    assert!(*bx == 0);
}

// the same through a struct whose pointer field comes first and a pointer to
// the trailing integer field walked backwards
#[repr(C)]
struct T {
    p: *mut u32,
    x: u64,
}

#[kani::proof]
fn bug_backwards_from_int_field_rebinds_ptr_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut t = T { p: &mut *bx, x: 1 };
    unsafe {
        *addr_of_mut!(t.x).sub(1) = yp as u64;
    }
    unsafe {
        *t.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_backwards_from_int_field_rebinds_ptr_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut t = T { p: &mut *bx, x: 1 };
    unsafe {
        *addr_of_mut!(t.x).sub(1) = yp as u64;
    }
    unsafe {
        *t.p = 7;
    }
    assert!(*bx == 0);
}

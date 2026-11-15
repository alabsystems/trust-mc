// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a `Box` element store placed exactly (Fix A), then a
//! narrower view of the same heap bytes (`u8` over `[u16; 2]`, `u16` over
//! `[u32; 2]`), a symbolic element store, and a raw-pointer element store read
//! as bytes (review of fix/chc-lost-writes round 3, finding 3: fail-closed on
//! both bundles).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_box_u16_elem_store_byte_read            -> SUCCESSFUL
//!   bug_box_u16_elem_store_byte_read             -> FAILED ('assertion failed: unsafe { *p.add(2) } == 2')
//!   safe_box_u32_elem_store_u16_read             -> SUCCESSFUL
//!   bug_box_u32_elem_store_u16_read              -> FAILED ('assertion failed: unsafe { *p.add(2) } == 2')
//!   safe_box_u16_nostore_byte_read               -> SUCCESSFUL
//!   safe_box_u16_sym_elem_store_byte_read        -> SUCCESSFUL
//!   safe_raw_arr_elem_store_byte_read            -> SUCCESSFUL
//!   bug_raw_arr_elem_store_byte_read             -> FAILED ('assertion failed: v == 2')
//!
#![allow(unused)]
use std::ptr::addr_of;

#[kani::proof]
fn safe_box_u16_elem_store_byte_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(2) } == 4);
}

#[kani::proof]
fn bug_box_u16_elem_store_byte_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn safe_box_u32_elem_store_u16_read() {
    let mut bx: Box<[u32; 2]> = Box::new([1, 0x0001_0002]);
    bx[1] = 0x0003_0004;
    let p = addr_of!(*bx) as *const u16;
    assert!(unsafe { *p.add(2) } == 4);
}

#[kani::proof]
fn bug_box_u32_elem_store_u16_read() {
    let mut bx: Box<[u32; 2]> = Box::new([1, 0x0001_0002]);
    bx[1] = 0x0003_0004;
    let p = addr_of!(*bx) as *const u16;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn safe_box_u16_nostore_byte_read() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

// symbolic index store, byte read
#[kani::proof]
fn safe_box_u16_sym_elem_store_byte_read() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[i] = 0x0304;
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(2 * i) } == 4);
}

// raw-pointer element store (not a Box), byte read
#[kani::proof]
fn safe_raw_arr_elem_store_byte_read() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let r: *mut [u16; 2] = Box::into_raw(bx);
    unsafe {
        (*r)[1] = 0x0304;
    }
    let p = r as *const u8;
    let v = unsafe { *p.add(2) };
    unsafe {
        drop(Box::from_raw(r));
    }
    assert!(v == 4);
}

#[kani::proof]
fn bug_raw_arr_elem_store_byte_read() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let r: *mut [u16; 2] = Box::into_raw(bx);
    unsafe {
        (*r)[1] = 0x0304;
    }
    let p = r as *const u8;
    let v = unsafe { *p.add(2) };
    unsafe {
        drop(Box::from_raw(r));
    }
    assert!(v == 2);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- element stores through a Box read back through views the store does not write:
//! a wider scalar, two stores read as one, a byte array, signedness and bool views, a whole copy, a
//! slice, memcpy out, element-pointer stores before an index read, and the no-store wide read that
//! was Genuine on main (review of fix/chc-lost-writes, lostwrite round 1, finding 3). The heap view
//! ledger fails a read closed where another store of the bytes did not write its key
//! (heap_view_read_stale) and records heap_view_read_unwritten where nothing wrote it.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_box_u16_store_wide_u32_read              -> SUCCESSFUL
//!   bug_box_u16_store_wide_u32_read               -> FAILED ('assertion failed: unsafe { *p } == 0x0002_0001')
//!   safe_box_u16_nostore_wide_u32_read            -> SUCCESSFUL
//!   bug_box_u16_nostore_wide_u32_read             -> FAILED ('assertion failed: unsafe { *p } == 0x0001_0002')
//!   safe_box_u32_store_i32_read                   -> SUCCESSFUL
//!   bug_box_u32_store_i32_read                    -> FAILED ('assertion failed: unsafe { *p.add(1) } == 2')
//!   safe_box_usize_store_u64_read                 -> SUCCESSFUL
//!   bug_box_usize_store_u64_read                  -> FAILED ('assertion failed: unsafe { *p.add(1) } == 2')
//!   safe_box_elem_store_whole_copy                -> SUCCESSFUL
//!   bug_box_elem_store_whole_copy                 -> FAILED ('assertion failed: a[1] == 2')
//!   safe_box_elem_store_slice_read                -> SUCCESSFUL
//!   bug_box_elem_store_slice_read                 -> FAILED ('assertion failed: s[1] == 2')
//!   safe_box_elem_store_memcpy_out                -> SUCCESSFUL
//!   bug_box_elem_store_memcpy_out                 -> FAILED ('assertion failed: d[1] == 2')
//!   safe_box_elem_store_byte_array_view           -> SUCCESSFUL
//!   bug_box_elem_store_byte_array_view            -> FAILED ('assertion failed: a[2] == 2')
//!   safe_box_i8_store_u8_read                     -> SUCCESSFUL
//!   bug_box_i8_store_u8_read                      -> FAILED ('assertion failed: unsafe { *p.add(1) } == 2')
//!   safe_box_bool_store_u8_read                   -> SUCCESSFUL
//!   bug_box_bool_store_u8_read                    -> FAILED ('assertion failed: unsafe { *p.add(1) } == 0')
//!   safe_box_elem_ptr_store_index_read            -> SUCCESSFUL
//!   bug_box_elem_ptr_store_index_read             -> FAILED ('assertion failed: bx[1] == 2')
//!   safe_box_store_then_elem_ptr_store_index_read -> SUCCESSFUL
//!   bug_box_store_then_elem_ptr_store_index_read  -> FAILED ('assertion failed: bx[1] == 5')
//!   safe_box_sym_store_other_elem                 -> SUCCESSFUL
//!   bug_box_sym_store_other_elem                  -> FAILED ('assertion failed: other != 7 && other == 2')
//!   safe_box_two_stores_wide_read                 -> SUCCESSFUL
//!   bug_box_two_stores_wide_read                  -> FAILED ('assertion failed: unsafe { *p } == 0x0002_0001')
//!
#![allow(unused)]
use std::ptr::{addr_of, addr_of_mut};

#[kani::proof]
fn safe_box_u16_store_wide_u32_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let p = addr_of!(*bx) as *const u32;
    assert!(unsafe { *p } == 0x0005_0001);
}
#[kani::proof]
fn bug_box_u16_store_wide_u32_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let p = addr_of!(*bx) as *const u32;
    assert!(unsafe { *p } == 0x0002_0001);
}
#[kani::proof]
fn safe_box_u16_nostore_wide_u32_read() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u32;
    assert!(unsafe { *p } == 0x0002_0001);
}
#[kani::proof]
fn bug_box_u16_nostore_wide_u32_read() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u32;
    assert!(unsafe { *p } == 0x0001_0002);
}
#[kani::proof]
fn safe_box_u32_store_i32_read() {
    let mut bx: Box<[u32; 2]> = Box::new([1, 2]);
    bx[1] = 0xFFFF_FFFF;
    let p = addr_of!(*bx) as *const i32;
    assert!(unsafe { *p.add(1) } == -1);
}
#[kani::proof]
fn bug_box_u32_store_i32_read() {
    let mut bx: Box<[u32; 2]> = Box::new([1, 2]);
    bx[1] = 0xFFFF_FFFF;
    let p = addr_of!(*bx) as *const i32;
    assert!(unsafe { *p.add(1) } == 2);
}
#[kani::proof]
fn safe_box_usize_store_u64_read() {
    let mut bx: Box<[usize; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let p = addr_of!(*bx) as *const u64;
    assert!(unsafe { *p.add(1) } == 5);
}
#[kani::proof]
fn bug_box_usize_store_u64_read() {
    let mut bx: Box<[usize; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let p = addr_of!(*bx) as *const u64;
    assert!(unsafe { *p.add(1) } == 2);
}
#[kani::proof]
fn safe_box_elem_store_whole_copy() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let a: [u16; 2] = *bx;
    assert!(a[1] == 5);
}
#[kani::proof]
fn bug_box_elem_store_whole_copy() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let a: [u16; 2] = *bx;
    assert!(a[1] == 2);
}
#[kani::proof]
fn safe_box_elem_store_slice_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let s: &[u16] = &bx[..];
    assert!(s[1] == 5);
}
#[kani::proof]
fn bug_box_elem_store_slice_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let s: &[u16] = &bx[..];
    assert!(s[1] == 2);
}
#[kani::proof]
fn safe_box_elem_store_memcpy_out() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let mut d = [0u16; 2];
    unsafe { std::ptr::copy_nonoverlapping(addr_of!(*bx) as *const u16, d.as_mut_ptr(), 2) };
    assert!(d[1] == 5);
}
#[kani::proof]
fn bug_box_elem_store_memcpy_out() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let mut d = [0u16; 2];
    unsafe { std::ptr::copy_nonoverlapping(addr_of!(*bx) as *const u16, d.as_mut_ptr(), 2) };
    assert!(d[1] == 2);
}
#[kani::proof]
fn safe_box_elem_store_byte_array_view() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let a: [u8; 4] = unsafe { *(addr_of!(*bx) as *const [u8; 4]) };
    assert!(a[2] == 5);
}
#[kani::proof]
fn bug_box_elem_store_byte_array_view() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let a: [u8; 4] = unsafe { *(addr_of!(*bx) as *const [u8; 4]) };
    assert!(a[2] == 2);
}
#[kani::proof]
fn safe_box_i8_store_u8_read() {
    let mut bx: Box<[i8; 2]> = Box::new([1, 2]);
    bx[1] = -1;
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(1) } == 255);
}
#[kani::proof]
fn bug_box_i8_store_u8_read() {
    let mut bx: Box<[i8; 2]> = Box::new([1, 2]);
    bx[1] = -1;
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(1) } == 2);
}
#[kani::proof]
fn safe_box_bool_store_u8_read() {
    let mut bx: Box<[bool; 2]> = Box::new([false, false]);
    bx[1] = true;
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(1) } == 1);
}
#[kani::proof]
fn bug_box_bool_store_u8_read() {
    let mut bx: Box<[bool; 2]> = Box::new([false, false]);
    bx[1] = true;
    let p = addr_of!(*bx) as *const u8;
    assert!(unsafe { *p.add(1) } == 0);
}
#[kani::proof]
fn safe_box_elem_ptr_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    unsafe { *(addr_of_mut!(*bx) as *mut u16).add(1) = 9 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn bug_box_elem_ptr_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    unsafe { *(addr_of_mut!(*bx) as *mut u16).add(1) = 9 };
    assert!(bx[1] == 2);
}
#[kani::proof]
fn safe_box_store_then_elem_ptr_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    unsafe { *(addr_of_mut!(*bx) as *mut u16).add(1) = 9 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn bug_box_store_then_elem_ptr_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    unsafe { *(addr_of_mut!(*bx) as *mut u16).add(1) = 9 };
    assert!(bx[1] == 5);
}
#[kani::proof]
fn safe_box_sym_store_other_elem() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[i] = 7;
    let p = addr_of!(*bx) as *const u16;
    let other = unsafe { *p.add(1 - i) };
    assert!(other == if i == 0 { 2 } else { 1 });
}
#[kani::proof]
fn bug_box_sym_store_other_elem() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[i] = 7;
    let p = addr_of!(*bx) as *const u16;
    let other = unsafe { *p.add(1 - i) };
    assert!(other != 7 && other == 2);
}
#[kani::proof]
fn safe_box_two_stores_wide_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[0] = 3;
    bx[1] = 4;
    let p = addr_of!(*bx) as *const u32;
    assert!(unsafe { *p } == 0x0004_0003);
}
#[kani::proof]
fn bug_box_two_stores_wide_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[0] = 3;
    bx[1] = 4;
    let p = addr_of!(*bx) as *const u32;
    assert!(unsafe { *p } == 0x0002_0001);
}

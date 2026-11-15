// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- more heap views: a raw element store read wide, a struct field array, a Vec
//! buffer as an array, alloc and alloc_zeroed element stores read as elements and bytes, a realloc
//! copy after element stores, a wide store before an index read (a clean missed bug on main), an
//! element store then a wide store, and u8/u32/tuple views (review of fix/chc-lost-writes,
//! lostwrite round 1, finding 3).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_raw_elem_store_wide_read                  -> SUCCESSFUL
//!   bug_raw_elem_store_wide_read                   -> FAILED ('assertion failed: v == 0x0002_0001')
//!   safe_box_field_buf_store_wide_read             -> SUCCESSFUL
//!   bug_box_field_buf_store_wide_read              -> FAILED ('assertion failed: v == 0x0002_0001')
//!   safe_vec_buf_as_array_store_wide_read          -> SUCCESSFUL
//!   bug_vec_buf_as_array_store_wide_read           -> FAILED ('assertion failed: w == 0x0002_0001')
//!   safe_vec_buf_as_array_store_index_read         -> SUCCESSFUL
//!   bug_vec_buf_as_array_store_index_read          -> FAILED ('assertion failed: v[1] == 2')
//!   safe_alloc_elem_store_read                     -> SUCCESSFUL
//!   bug_alloc_elem_store_read                      -> FAILED ('assertion failed: v == 1')
//!   safe_alloc_zeroed_elem_store_read              -> SUCCESSFUL
//!   bug_alloc_zeroed_elem_store_read               -> FAILED ('assertion failed: v0 == 0 && v1 == 0')
//!   safe_alloc_zeroed_elem_store_byte_read         -> SUCCESSFUL
//!   bug_alloc_zeroed_elem_store_byte_read          -> FAILED ('assertion failed: b == 0')
//!   safe_realloc_after_elem_store                  -> SUCCESSFUL
//!   bug_realloc_after_elem_store                   -> FAILED ('assertion failed: v == 1')
//!   safe_box_wide_store_index_read                 -> SUCCESSFUL
//!   bug_box_wide_store_index_read                  -> FAILED ('assertion failed: bx[1] == 2')
//!   safe_box_elem_store_then_wide_store_index_read -> SUCCESSFUL
//!   bug_box_elem_store_then_wide_store_index_read  -> FAILED ('assertion failed: bx[1] == 9')
//!   safe_box_u8_store_u32_read                     -> SUCCESSFUL
//!   bug_box_u8_store_u32_read                      -> FAILED ('assertion failed: v == 0x0403_0201')
//!   safe_box_u32_store_u64_read                    -> SUCCESSFUL
//!   bug_box_u32_store_u64_read                     -> FAILED ('assertion failed: v == 0x0000_0002_0000_0001')
//!   safe_box_elem_store_tuple_view                 -> SUCCESSFUL
//!   bug_box_elem_store_tuple_view                  -> FAILED ('assertion failed: t.0 != 5 && t.1 != 5')
//!
#![allow(unused)]
use std::alloc::{Layout, alloc, alloc_zeroed, dealloc, realloc};
use std::ptr::{addr_of, addr_of_mut};

#[kani::proof]
fn safe_raw_elem_store_wide_read() {
    let r: *mut [u16; 2] = Box::into_raw(Box::new([1u16, 2]));
    unsafe { (*r)[1] = 5 };
    let v = unsafe { *(r as *const u32) };
    unsafe { drop(Box::from_raw(r)) };
    assert!(v == 0x0005_0001);
}
#[kani::proof]
fn bug_raw_elem_store_wide_read() {
    let r: *mut [u16; 2] = Box::into_raw(Box::new([1u16, 2]));
    unsafe { (*r)[1] = 5 };
    let v = unsafe { *(r as *const u32) };
    unsafe { drop(Box::from_raw(r)) };
    assert!(v == 0x0002_0001);
}
struct S {
    n: u8,
    buf: [u16; 2],
}
#[kani::proof]
fn safe_box_field_buf_store_wide_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    let p: *mut S = addr_of_mut!(*bx);
    unsafe { (*p).buf[1] = 5 };
    let v = unsafe { *(addr_of!((*p).buf) as *const u32) };
    assert!(v == 0x0005_0001);
}
#[kani::proof]
fn bug_box_field_buf_store_wide_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    let p: *mut S = addr_of_mut!(*bx);
    unsafe { (*p).buf[1] = 5 };
    let v = unsafe { *(addr_of!((*p).buf) as *const u32) };
    assert!(v == 0x0002_0001);
}
#[kani::proof]
fn safe_vec_buf_as_array_store_wide_read() {
    let mut v: Vec<u16> = vec![1, 2];
    let a = v.as_mut_ptr() as *mut [u16; 2];
    unsafe { (*a)[1] = 5 };
    let w = unsafe { *(v.as_ptr() as *const u32) };
    assert!(w == 0x0005_0001);
}
#[kani::proof]
fn bug_vec_buf_as_array_store_wide_read() {
    let mut v: Vec<u16> = vec![1, 2];
    let a = v.as_mut_ptr() as *mut [u16; 2];
    unsafe { (*a)[1] = 5 };
    let w = unsafe { *(v.as_ptr() as *const u32) };
    assert!(w == 0x0002_0001);
}
#[kani::proof]
fn safe_vec_buf_as_array_store_index_read() {
    let mut v: Vec<u16> = vec![1, 2];
    let a = v.as_mut_ptr() as *mut [u16; 2];
    unsafe { (*a)[1] = 5 };
    assert!(v[1] == 5);
}
#[kani::proof]
fn bug_vec_buf_as_array_store_index_read() {
    let mut v: Vec<u16> = vec![1, 2];
    let a = v.as_mut_ptr() as *mut [u16; 2];
    unsafe { (*a)[1] = 5 };
    assert!(v[1] == 2);
}
#[kani::proof]
fn safe_alloc_elem_store_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc(l) as *mut [u16; 2];
        (*p)[0] = 1;
        (*p)[1] = 5;
        let v = *(p as *const u16).add(1);
        dealloc(p as *mut u8, l);
        assert!(v == 5);
    }
}
#[kani::proof]
fn bug_alloc_elem_store_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc(l) as *mut [u16; 2];
        (*p)[0] = 1;
        (*p)[1] = 5;
        let v = *(p as *const u16).add(1);
        dealloc(p as *mut u8, l);
        assert!(v == 1);
    }
}
#[kani::proof]
fn safe_alloc_zeroed_elem_store_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc_zeroed(l) as *mut [u16; 2];
        (*p)[1] = 5;
        let v0 = (*p)[0];
        let v1 = *(p as *const u16).add(1);
        dealloc(p as *mut u8, l);
        assert!(v0 == 0 && v1 == 5);
    }
}
#[kani::proof]
fn bug_alloc_zeroed_elem_store_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc_zeroed(l) as *mut [u16; 2];
        (*p)[1] = 5;
        let v0 = (*p)[0];
        let v1 = *(p as *const u16).add(1);
        dealloc(p as *mut u8, l);
        assert!(v0 == 0 && v1 == 0);
    }
}
#[kani::proof]
fn safe_alloc_zeroed_elem_store_byte_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc_zeroed(l) as *mut [u16; 2];
        (*p)[1] = 0x0305;
        let b = *(p as *const u8).add(2);
        dealloc(p as *mut u8, l);
        assert!(b == 5);
    }
}
#[kani::proof]
fn bug_alloc_zeroed_elem_store_byte_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc_zeroed(l) as *mut [u16; 2];
        (*p)[1] = 0x0305;
        let b = *(p as *const u8).add(2);
        dealloc(p as *mut u8, l);
        assert!(b == 0);
    }
}
#[kani::proof]
fn safe_realloc_after_elem_store() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc(l) as *mut [u16; 2];
        (*p)[0] = 1;
        (*p)[1] = 5;
        let q = realloc(p as *mut u8, l, 8) as *mut [u16; 4];
        let v = (*q)[1];
        dealloc(q as *mut u8, Layout::new::<[u16; 4]>());
        assert!(v == 5);
    }
}
#[kani::proof]
fn bug_realloc_after_elem_store() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc(l) as *mut [u16; 2];
        (*p)[0] = 1;
        (*p)[1] = 5;
        let q = realloc(p as *mut u8, l, 8) as *mut [u16; 4];
        let v = (*q)[1];
        dealloc(q as *mut u8, Layout::new::<[u16; 4]>());
        assert!(v == 1);
    }
}
#[kani::proof]
fn safe_box_wide_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    unsafe { *(addr_of_mut!(*bx) as *mut u32) = 0x0005_0003 };
    assert!(bx[1] == 5);
}
#[kani::proof]
fn bug_box_wide_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    unsafe { *(addr_of_mut!(*bx) as *mut u32) = 0x0005_0003 };
    assert!(bx[1] == 2);
}
#[kani::proof]
fn safe_box_elem_store_then_wide_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 9;
    unsafe { *(addr_of_mut!(*bx) as *mut u32) = 0x0005_0003 };
    assert!(bx[1] == 5);
}
#[kani::proof]
fn bug_box_elem_store_then_wide_store_index_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 9;
    unsafe { *(addr_of_mut!(*bx) as *mut u32) = 0x0005_0003 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn safe_box_u8_store_u32_read() {
    let mut bx: Box<[u8; 4]> = Box::new([1, 2, 3, 4]);
    bx[2] = 9;
    let v = unsafe { *(addr_of!(*bx) as *const u32) };
    assert!(v == 0x0409_0201);
}
#[kani::proof]
fn bug_box_u8_store_u32_read() {
    let mut bx: Box<[u8; 4]> = Box::new([1, 2, 3, 4]);
    bx[2] = 9;
    let v = unsafe { *(addr_of!(*bx) as *const u32) };
    assert!(v == 0x0403_0201);
}
#[kani::proof]
fn safe_box_u32_store_u64_read() {
    let mut bx: Box<[u32; 2]> = Box::new([1, 2]);
    bx[0] = 7;
    let v = unsafe { *(addr_of!(*bx) as *const u64) };
    assert!(v == 0x0000_0002_0000_0007);
}
#[kani::proof]
fn bug_box_u32_store_u64_read() {
    let mut bx: Box<[u32; 2]> = Box::new([1, 2]);
    bx[0] = 7;
    let v = unsafe { *(addr_of!(*bx) as *const u64) };
    assert!(v == 0x0000_0002_0000_0001);
}
#[kani::proof]
fn safe_box_elem_store_tuple_view() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let t: (u16, u16) = unsafe { *(addr_of!(*bx) as *const (u16, u16)) };
    assert!(t.1 == 5 || t.0 == 5);
}
#[kani::proof]
fn bug_box_elem_store_tuple_view() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let t: (u16, u16) = unsafe { *(addr_of!(*bx) as *const (u16, u16)) };
    assert!(t.0 != 5 && t.1 != 5);
}

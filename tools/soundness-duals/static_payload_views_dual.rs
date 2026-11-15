// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- static stores through raw pointers read via the state variable (wide, element-
//! pointer and laundered stores), an alloc_zeroed scalar store read as bytes, and Box payload array
//! element stores read whole, through a field, through dyn and through a slice unsize (review of
//! fix/chc-lost-writes, lostwrite round 1, findings 1 and 3).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_static_wide_raw_store_index_read       -> SUCCESSFUL
//!   bug_static_wide_raw_store_index_read        -> FAILED ('assertion failed: G2[1] == 2')
//!   safe_static_elem_ptr_store_index_read       -> SUCCESSFUL
//!   bug_static_elem_ptr_store_index_read        -> FAILED ('assertion failed: G4[1] == 2')
//!   safe_static_elem_store_then_wide_store      -> SUCCESSFUL
//!   bug_static_elem_store_then_wide_store       -> FAILED ('assertion failed: G6[1] == 9')
//!   safe_static_laundered_elem_store_index_read -> SUCCESSFUL
//!   bug_static_laundered_elem_store_index_read  -> FAILED ('assertion failed: G8[1] == 2')
//!   safe_static_elem_store_laundered_read       -> SUCCESSFUL
//!   bug_static_elem_store_laundered_read        -> FAILED ('assertion failed: (*q)[1] == 2')
//!   safe_alloc_zeroed_scalar_store_byte_read    -> SUCCESSFUL
//!   bug_alloc_zeroed_scalar_store_byte_read     -> FAILED ('assertion failed: b == 0')
//!   safe_payload_buf_store_whole_read           -> SUCCESSFUL
//!   bug_payload_buf_store_whole_read            -> FAILED ('assertion failed: s.buf[1] == 2')
//!   safe_payload_buf_store_field_read           -> SUCCESSFUL
//!   bug_payload_buf_store_field_read            -> FAILED ('assertion failed: bx.buf[1] == 2')
//!   safe_payload_buf_store_dyn_read             -> SUCCESSFUL
//!   bug_payload_buf_store_dyn_read              -> FAILED ('assertion failed: d.get() == 2')
//!   safe_box_array_store_dyn_read               -> SUCCESSFUL
//!   bug_box_array_store_dyn_read                -> FAILED ('assertion failed: d.get() == 2')
//!   safe_box_array_store_slice_unsize           -> SUCCESSFUL
//!   bug_box_array_store_slice_unsize            -> FAILED ('assertion failed: s[1] == 2')
//!   safe_payload_field_store_then_buf_store_dyn -> SUCCESSFUL
//!   bug_payload_field_store_then_buf_store_dyn  -> FAILED ('assertion failed: d.get() == 2')
//!
#![allow(unused)]
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::ptr::{addr_of, addr_of_mut};

static mut G1: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_wide_raw_store_index_read() {
    unsafe {
        *(addr_of_mut!(G1) as *mut u32) = 0x0005_0003;
        assert!(G1[1] == 5);
    }
}
static mut G2: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_wide_raw_store_index_read() {
    unsafe {
        *(addr_of_mut!(G2) as *mut u32) = 0x0005_0003;
        assert!(G2[1] == 2);
    }
}
static mut G3: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_elem_ptr_store_index_read() {
    unsafe {
        *(addr_of_mut!(G3) as *mut u16).add(1) = 5;
        assert!(G3[1] == 5);
    }
}
static mut G4: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_elem_ptr_store_index_read() {
    unsafe {
        *(addr_of_mut!(G4) as *mut u16).add(1) = 5;
        assert!(G4[1] == 2);
    }
}
static mut G5: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_elem_store_then_wide_store() {
    unsafe {
        G5[1] = 9;
        *(addr_of_mut!(G5) as *mut u32) = 0x0005_0003;
        assert!(G5[1] == 5);
    }
}
static mut G6: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_elem_store_then_wide_store() {
    unsafe {
        G6[1] = 9;
        *(addr_of_mut!(G6) as *mut u32) = 0x0005_0003;
        assert!(G6[1] == 9);
    }
}
static mut G7: [u16; 2] = [1, 2];
fn launder<T>(p: *mut T) -> *mut T {
    let b = Box::new(p);
    *b
}
#[kani::proof]
fn safe_static_laundered_elem_store_index_read() {
    unsafe {
        let q = launder(addr_of_mut!(G7));
        (*q)[1] = 5;
        assert!(G7[1] == 5);
    }
}
static mut G8: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_laundered_elem_store_index_read() {
    unsafe {
        let q = launder(addr_of_mut!(G8));
        (*q)[1] = 5;
        assert!(G8[1] == 2);
    }
}
static mut G9: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_elem_store_laundered_read() {
    unsafe {
        G9[1] = 5;
        let q = launder(addr_of_mut!(G9));
        assert!((*q)[1] == 5);
    }
}
static mut G10: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_elem_store_laundered_read() {
    unsafe {
        G10[1] = 5;
        let q = launder(addr_of_mut!(G10));
        assert!((*q)[1] == 2);
    }
}
#[kani::proof]
fn safe_alloc_zeroed_scalar_store_byte_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc_zeroed(l) as *mut u16;
        *p.add(1) = 0x0305;
        let b = *(p as *const u8).add(2);
        dealloc(p as *mut u8, l);
        assert!(b == 5);
    }
}
#[kani::proof]
fn bug_alloc_zeroed_scalar_store_byte_read() {
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc_zeroed(l) as *mut u16;
        *p.add(1) = 0x0305;
        let b = *(p as *const u8).add(2);
        dealloc(p as *mut u8, l);
        assert!(b == 0);
    }
}
#[derive(Clone, Copy)]
struct S {
    n: u8,
    buf: [u16; 2],
}
#[kani::proof]
fn safe_payload_buf_store_whole_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    let p: *mut S = addr_of_mut!(*bx);
    unsafe { (*p).buf[1] = 5 };
    let s: S = *bx;
    assert!(s.buf[1] == 5);
}
#[kani::proof]
fn bug_payload_buf_store_whole_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    let p: *mut S = addr_of_mut!(*bx);
    unsafe { (*p).buf[1] = 5 };
    let s: S = *bx;
    assert!(s.buf[1] == 2);
}
#[kani::proof]
fn safe_payload_buf_store_field_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    bx.buf[1] = 5;
    assert!(bx.buf[1] == 5);
}
#[kani::proof]
fn bug_payload_buf_store_field_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    bx.buf[1] = 5;
    assert!(bx.buf[1] == 2);
}
trait Tr {
    fn get(&self) -> u16;
}
impl Tr for S {
    fn get(&self) -> u16 {
        self.buf[1]
    }
}
impl Tr for [u16; 2] {
    fn get(&self) -> u16 {
        self[1]
    }
}
#[kani::proof]
fn safe_payload_buf_store_dyn_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    bx.buf[1] = 5;
    let d: Box<dyn Tr> = bx;
    assert!(d.get() == 5);
}
#[kani::proof]
fn bug_payload_buf_store_dyn_read() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    bx.buf[1] = 5;
    let d: Box<dyn Tr> = bx;
    assert!(d.get() == 2);
}
#[kani::proof]
fn safe_box_array_store_dyn_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let d: Box<dyn Tr> = bx;
    assert!(d.get() == 5);
}
#[kani::proof]
fn bug_box_array_store_dyn_read() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let d: Box<dyn Tr> = bx;
    assert!(d.get() == 2);
}
#[kani::proof]
fn safe_box_array_store_slice_unsize() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let s: Box<[u16]> = bx;
    assert!(s[1] == 5);
}
#[kani::proof]
fn bug_box_array_store_slice_unsize() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 5;
    let s: Box<[u16]> = bx;
    assert!(s[1] == 2);
}
#[kani::proof]
fn safe_payload_field_store_then_buf_store_dyn() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    bx.n = 3;
    bx.buf[1] = 5;
    let d: Box<dyn Tr> = bx;
    assert!(d.get() == 5);
}
#[kani::proof]
fn bug_payload_field_store_then_buf_store_dyn() {
    let mut bx = Box::new(S { n: 0, buf: [1, 2] });
    bx.n = 3;
    bx.buf[1] = 5;
    let d: Box<dyn Tr> = bx;
    assert!(d.get() == 2);
}

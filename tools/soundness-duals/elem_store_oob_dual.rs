// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- element stores through pointers that are out of bounds (a wrapping step past a
//! Box or a static, a NonNull transmuted from an address past the Box, a constant-lane partial
//! overrun, a symbolic offset), dangling (use after free, a stale pointer after realloc) or null,
//! each with an in-bounds twin (review of fix/chc-lost-writes, lostwrite round 1, finding 2). The
//! element lane wrote through a symbolic object lane unchecked; it now fails closed there, and
//! heap_access_checks bounds a symbolic lane by the object's size.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_elem_store_wrapping_oob                -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_elem_store_wrapping_inbounds          -> SUCCESSFUL
//!   bug_elem_store_nonnull_transmute_oob       -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_elem_store_static_wrapping_oob         -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_elem_store_use_after_free              -> FAILED ('dereference failure: deallocated dynamic object')
//!   bug_elem_store_null                        -> FAILED ('null pointer dereference occurred')
//!   bug_elem_store_partial_oob_const_lane      -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_elem_store_sym_offset_oob              -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_elem_store_sym_offset_inbounds        -> SUCCESSFUL
//!   bug_elem_store_sym_offset_value            -> FAILED ('assertion failed: bx[k + 1] != 9')
//!   bug_elem_store_after_realloc_stale         -> FAILED ('dereference failure: deallocated dynamic object')
//!   safe_elem_store_nonnull_transmute_inbounds -> SUCCESSFUL
//!   safe_elem_store_static_wrapping_inbounds   -> SUCCESSFUL
//!   safe_elem_store_before_free                -> SUCCESSFUL
//!   safe_elem_store_nonnull                    -> SUCCESSFUL
//!   safe_elem_store_const_lane_inbounds        -> SUCCESSFUL
//!   safe_elem_store_after_realloc_fresh        -> SUCCESSFUL
//!
#![allow(unused)]
use std::ptr::{NonNull, addr_of_mut, null_mut};

#[kani::proof]
fn bug_elem_store_wrapping_oob() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (addr_of_mut!(*bx) as *mut u16).wrapping_add(2) as *mut [u16; 2];
    unsafe { (*p)[1] = 9 };
}
#[kani::proof]
fn safe_elem_store_wrapping_inbounds() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (addr_of_mut!(*bx) as *mut u16).wrapping_add(0) as *mut [u16; 2];
    unsafe { (*p)[1] = 9 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn bug_elem_store_nonnull_transmute_oob() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of_mut!(*bx) as usize;
    let p: NonNull<[u16; 2]> = unsafe { std::mem::transmute::<usize, NonNull<[u16; 2]>>(a + 4) };
    unsafe { (*p.as_ptr())[1] = 9 };
}
#[kani::proof]
fn bug_elem_store_static_wrapping_oob() {
    static mut G: [u16; 2] = [1, 2];
    let p = unsafe { (addr_of_mut!(G) as *mut u16).wrapping_add(2) as *mut [u16; 2] };
    unsafe { (*p)[1] = 9 };
}
#[kani::proof]
fn bug_elem_store_use_after_free() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let r = Box::into_raw(bx);
    unsafe { drop(Box::from_raw(r)) };
    unsafe { (*r)[1] = 9 };
}
#[kani::proof]
fn bug_elem_store_null() {
    let p: *mut [u16; 2] = null_mut();
    unsafe { (*p)[1] = 9 };
}
#[kani::proof]
fn bug_elem_store_partial_oob_const_lane() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let q = unsafe { (addr_of_mut!(*bx) as *mut u16).add(1) } as *mut [u16; 2];
    unsafe { (*q)[1] = 9 };
}
#[kani::proof]
fn bug_elem_store_sym_offset_oob() {
    let mut bx: Box<[u16; 4]> = Box::new([1, 2, 3, 4]);
    let k: usize = kani::any();
    kani::assume(k <= 3);
    let q = unsafe { (addr_of_mut!(*bx) as *mut u16).add(k) } as *mut [u16; 2];
    unsafe { (*q)[1] = 9 };
}
#[kani::proof]
fn safe_elem_store_sym_offset_inbounds() {
    let mut bx: Box<[u16; 4]> = Box::new([1, 2, 3, 4]);
    let k: usize = kani::any();
    kani::assume(k <= 2);
    let q = unsafe { (addr_of_mut!(*bx) as *mut u16).add(k) } as *mut [u16; 2];
    unsafe { (*q)[1] = 9 };
    assert!(bx[k + 1] == 9);
}
#[kani::proof]
fn bug_elem_store_sym_offset_value() {
    let mut bx: Box<[u16; 4]> = Box::new([1, 2, 3, 4]);
    let k: usize = kani::any();
    kani::assume(k <= 2);
    let q = unsafe { (addr_of_mut!(*bx) as *mut u16).add(k) } as *mut [u16; 2];
    unsafe { (*q)[1] = 9 };
    assert!(bx[k + 1] != 9);
}
#[kani::proof]
fn bug_elem_store_after_realloc_stale() {
    use std::alloc::{Layout, alloc, dealloc, realloc};
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc(l) as *mut [u16; 2];
        (*p)[0] = 1;
        let q = realloc(p as *mut u8, l, 64) as *mut [u16; 32];
        (*p)[1] = 9;
        dealloc(q as *mut u8, Layout::new::<[u16; 32]>());
    }
}

#[kani::proof]
fn safe_elem_store_nonnull_transmute_inbounds() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of_mut!(*bx) as usize;
    let p: NonNull<[u16; 2]> = unsafe { std::mem::transmute::<usize, NonNull<[u16; 2]>>(a) };
    unsafe { (*p.as_ptr())[1] = 9 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn safe_elem_store_static_wrapping_inbounds() {
    static mut G: [u16; 2] = [1, 2];
    let p = unsafe { (addr_of_mut!(G) as *mut u16).wrapping_add(0) as *mut [u16; 2] };
    unsafe { (*p)[1] = 9 };
    assert!(unsafe { G[1] } == 9);
}
#[kani::proof]
fn safe_elem_store_before_free() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let r = Box::into_raw(bx);
    unsafe { (*r)[1] = 9 };
    let back = unsafe { Box::from_raw(r) };
    assert!(back[1] == 9);
}
#[kani::proof]
fn safe_elem_store_nonnull() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p: *mut [u16; 2] = addr_of_mut!(*bx);
    unsafe { (*p)[1] = 9 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn safe_elem_store_const_lane_inbounds() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let q = unsafe { (addr_of_mut!(*bx) as *mut u16).add(0) } as *mut [u16; 2];
    unsafe { (*q)[1] = 9 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn safe_elem_store_after_realloc_fresh() {
    use std::alloc::{Layout, alloc, dealloc, realloc};
    unsafe {
        let l = Layout::new::<[u16; 2]>();
        let p = alloc(l) as *mut [u16; 2];
        (*p)[0] = 1;
        let q = realloc(p as *mut u8, l, 64) as *mut [u16; 32];
        (*q)[1] = 9;
        let v = (*q)[1];
        dealloc(q as *mut u8, Layout::new::<[u16; 32]>());
        assert!(v == 9);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- reads and writes past a Box, a Vec or a static through a pointer whose object
//! lane does not fold: the wrapping family, map_addr, with_addr, byte_offset, slice::from_raw_parts
//! with a length the allocation does not hold, and integers turned into pointers by transmutes into
//! NonNull, &T, Option<&T>, [usize; 1] and [u32; 2], a union and a pointer read of an integer, each
//! with an in-bounds twin (review of fix/chc-lost-writes, lostwrite round 1, finding 4).
//! heap_access_checks used to skip the bounds for a non-constant lane; it now bounds the access by
//! obj_size of the lane.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_transmute_nonnull_oob            -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_transmute_ref_oob                -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_transmute_option_ref_oob         -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_transmute_array1_oob             -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_transmute_u32_pair_oob           -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_union_usize_ptr_oob              -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_ptr_read_usize_as_ptr_oob        -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_map_addr_oob                     -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_map_addr_inbounds               -> SUCCESSFUL
//!   bug_with_addr_oob                    -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_wrapping_sub_oob                 -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_wrapping_add_oob                 -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_wrapping_add_oob_write           -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_byte_offset_oob                  -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_slice_from_raw_parts_oob         -> FAILED ('dereference failure: pointer invalid')
//!   bug_vec_wrapping_add_oob_write       -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_static_wrapping_add_oob          -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_transmute_nonnull_inbounds      -> SUCCESSFUL
//!   safe_transmute_ref_inbounds          -> SUCCESSFUL
//!   safe_transmute_option_ref_inbounds   -> SUCCESSFUL
//!   safe_transmute_array1_inbounds       -> SUCCESSFUL
//!   safe_transmute_u32_pair_inbounds     -> SUCCESSFUL
//!   safe_union_usize_ptr_inbounds        -> SUCCESSFUL
//!   safe_ptr_read_usize_as_ptr_inbounds  -> SUCCESSFUL
//!   safe_with_addr_inbounds              -> SUCCESSFUL
//!   safe_wrapping_sub_inbounds           -> SUCCESSFUL
//!   safe_wrapping_add_inbounds           -> SUCCESSFUL
//!   safe_wrapping_add_inbounds_write     -> SUCCESSFUL
//!   safe_byte_offset_inbounds            -> SUCCESSFUL
//!   safe_slice_from_raw_parts_inbounds   -> SUCCESSFUL
//!   safe_vec_wrapping_add_inbounds_write -> SUCCESSFUL
//!   safe_static_wrapping_add_inbounds    -> SUCCESSFUL
//!   bug_copy_into_wrapping_oob           -> FAILED ('memcpy destination region writeable')
//!   safe_copy_into_wrapping_inbounds     -> SUCCESSFUL
//!
#![allow(unused)]
use std::ptr::{NonNull, addr_of};

#[kani::proof]
fn bug_transmute_nonnull_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let p: NonNull<u16> = unsafe { std::mem::transmute::<usize, NonNull<u16>>(a + 4) };
    let v = unsafe { *p.as_ptr() };
    assert!(v == v);
}
#[kani::proof]
fn bug_transmute_ref_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let r: &u16 = unsafe { std::mem::transmute::<usize, &u16>(a + 4) };
    let v = *r;
    assert!(v == v);
}
#[kani::proof]
fn bug_transmute_option_ref_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let r: Option<&u16> = unsafe { std::mem::transmute::<usize, Option<&u16>>(a + 4) };
    let v = *r.unwrap();
    assert!(v == v);
}
#[kani::proof]
fn bug_transmute_array1_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let p: *const u16 = unsafe { std::mem::transmute::<[usize; 1], *const u16>([a + 4]) };
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_transmute_u32_pair_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize + 4;
    let parts = [a as u32, (a >> 32) as u32];
    let p: *const u16 = unsafe { std::mem::transmute::<[u32; 2], *const u16>(parts) };
    let v = unsafe { *p };
    assert!(v == v);
}
union UP {
    a: usize,
    p: *const u16,
}
#[kani::proof]
fn bug_union_usize_ptr_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let u = UP { a: a + 4 };
    let v = unsafe { *u.p };
    assert!(v == v);
}
#[kani::proof]
fn bug_ptr_read_usize_as_ptr_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize + 4;
    let p: *const u16 = unsafe { *(&a as *const usize as *const *const u16) };
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_map_addr_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (addr_of!(*bx) as *const u16).map_addr(|a| a + 4);
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn safe_map_addr_inbounds() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    bx[1] = 7;
    let p = (addr_of!(*bx) as *const u16).map_addr(|a| a + 2);
    let v = unsafe { *p };
    assert!(v == 7);
}
#[kani::proof]
fn bug_with_addr_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.with_addr(p.addr() + 4);
    let v = unsafe { *q };
    assert!(v == v);
}
#[kani::proof]
fn bug_wrapping_sub_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (addr_of!(*bx) as *const u16).wrapping_sub(1);
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_wrapping_add_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (addr_of!(*bx) as *const u16).wrapping_add(2);
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_wrapping_add_oob_write() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (std::ptr::addr_of_mut!(*bx) as *mut u16).wrapping_add(2);
    unsafe { *p = 9 };
}
#[kani::proof]
fn bug_byte_offset_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = unsafe { p.byte_offset(4) };
    let v = unsafe { *q };
    assert!(v == v);
}
#[kani::proof]
fn bug_slice_from_raw_parts_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let s: &[u16] = unsafe { std::slice::from_raw_parts(addr_of!(*bx) as *const u16, 3) };
    let v = s[2];
    assert!(v == v);
}
#[kani::proof]
fn bug_vec_wrapping_add_oob_write() {
    let mut v: Vec<u16> = vec![1, 2];
    let p = v.as_mut_ptr().wrapping_add(2);
    unsafe { *p = 9 };
}
#[kani::proof]
fn bug_static_wrapping_add_oob() {
    static G: [u16; 2] = [1, 2];
    let p = (addr_of!(G) as *const u16).wrapping_add(2);
    let v = unsafe { *p };
    assert!(v == v);
}

#[kani::proof]
fn safe_transmute_nonnull_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let p: NonNull<u16> = unsafe { std::mem::transmute::<usize, NonNull<u16>>(a + 2) };
    let v = unsafe { *p.as_ptr() };
    assert!(v == 2);
}
#[kani::proof]
fn safe_transmute_ref_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let r: &u16 = unsafe { std::mem::transmute::<usize, &u16>(a + 2) };
    assert!(*r == 2);
}
#[kani::proof]
fn safe_transmute_option_ref_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let r: Option<&u16> = unsafe { std::mem::transmute::<usize, Option<&u16>>(a + 2) };
    assert!(*r.unwrap() == 2);
}
#[kani::proof]
fn safe_transmute_array1_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let p: *const u16 = unsafe { std::mem::transmute::<[usize; 1], *const u16>([a + 2]) };
    assert!(unsafe { *p } == 2);
}
#[kani::proof]
fn safe_transmute_u32_pair_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize + 2;
    let parts = [a as u32, (a >> 32) as u32];
    let p: *const u16 = unsafe { std::mem::transmute::<[u32; 2], *const u16>(parts) };
    assert!(unsafe { *p } == 2);
}
#[kani::proof]
fn safe_union_usize_ptr_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let u = UP { a: a + 2 };
    assert!(unsafe { *u.p } == 2);
}
#[kani::proof]
fn safe_ptr_read_usize_as_ptr_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize + 2;
    let p: *const u16 = unsafe { *(&a as *const usize as *const *const u16) };
    assert!(unsafe { *p } == 2);
}
#[kani::proof]
fn safe_with_addr_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.with_addr(p.addr() + 2);
    assert!(unsafe { *q } == 2);
}
#[kani::proof]
fn safe_wrapping_sub_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (addr_of!(*bx) as *const u16).wrapping_add(1).wrapping_sub(1);
    assert!(unsafe { *p } == 1);
}
#[kani::proof]
fn safe_wrapping_add_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (addr_of!(*bx) as *const u16).wrapping_add(1);
    assert!(unsafe { *p } == 2);
}
#[kani::proof]
fn safe_wrapping_add_inbounds_write() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = (std::ptr::addr_of_mut!(*bx) as *mut u16).wrapping_add(1);
    unsafe { *p = 9 };
    assert!(bx[1] == 9);
}
#[kani::proof]
fn safe_byte_offset_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = unsafe { p.byte_offset(2) };
    assert!(unsafe { *q } == 2);
}
#[kani::proof]
fn safe_slice_from_raw_parts_inbounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let s: &[u16] = unsafe { std::slice::from_raw_parts(addr_of!(*bx) as *const u16, 2) };
    assert!(s[1] == 2);
}
#[kani::proof]
fn safe_vec_wrapping_add_inbounds_write() {
    let mut v: Vec<u16> = vec![1, 2];
    let p = v.as_mut_ptr().wrapping_add(1);
    unsafe { *p = 9 };
    assert!(v[1] == 9);
}
#[kani::proof]
fn safe_static_wrapping_add_inbounds() {
    static G: [u16; 2] = [1, 2];
    let p = (addr_of!(G) as *const u16).wrapping_add(1);
    assert!(unsafe { *p } == 2);
}
#[kani::proof]
fn bug_copy_into_wrapping_oob() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let src: [u16; 2] = [7, 8];
    let p = (std::ptr::addr_of_mut!(*bx) as *mut u16).wrapping_add(1);
    unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), p, 2) };
}
#[kani::proof]
fn safe_copy_into_wrapping_inbounds() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
    let src: [u16; 2] = [7, 8];
    let p = (std::ptr::addr_of_mut!(*bx) as *mut u16).wrapping_add(0);
    unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), p, 2) };
    assert!(bx[1] == 8);
}

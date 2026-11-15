// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a pointer local or pointer field rebound by ptr::write_volatile (the
//! volatile_store intrinsic, no MIR assignment), then written or read through (review of fix/chc-
//! lost-writes, lostwrite round 1, finding 5). Untyped-view net 1 now counts the volatile store
//! intrinsics as byte writers, so pointer_bytes_rewritten_untyped fails the block closed.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_local_rebind_write_volatile      -> SUCCESSFUL
//!   bug_local_rebind_write_volatile       -> FAILED ('assertion failed: x == 7')
//!   safe_field_rebind_write_volatile_heap -> SUCCESSFUL
//!   bug_field_rebind_write_volatile_heap  -> FAILED ('assertion failed: x == 7')
//!   safe_field_rebind_write_volatile_read -> SUCCESSFUL
//!   bug_field_rebind_write_volatile_read  -> FAILED ('assertion failed: v == 1')
//!   safe_field_rebind_write_volatile      -> SUCCESSFUL
//!   bug_field_rebind_write_volatile       -> FAILED ('assertion failed: x == 7')
//!
#![allow(unused)]
use std::ptr::addr_of_mut;

struct H {
    n: u32,
    p: *mut u32,
}
#[kani::proof]
fn safe_local_rebind_write_volatile() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let mut q: *mut u32 = addr_of_mut!(x);
    unsafe { std::ptr::write_volatile(&mut q, addr_of_mut!(y)) };
    unsafe { *q = 7 };
    assert!(y == 7 && x == 1);
}
#[kani::proof]
fn bug_local_rebind_write_volatile() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let mut q: *mut u32 = addr_of_mut!(x);
    unsafe { std::ptr::write_volatile(&mut q, addr_of_mut!(y)) };
    unsafe { *q = 7 };
    assert!(x == 7);
}
#[kani::proof]
fn safe_field_rebind_write_volatile_heap() {
    let mut x: u32 = 1;
    let mut y: Box<u32> = Box::new(2);
    let mut h = H { n: 0, p: addr_of_mut!(x) };
    unsafe { std::ptr::write_volatile(addr_of_mut!(h.p), addr_of_mut!(*y)) };
    unsafe { *h.p = 7 };
    assert!(*y == 7 && x == 1);
}
#[kani::proof]
fn bug_field_rebind_write_volatile_heap() {
    let mut x: u32 = 1;
    let mut y: Box<u32> = Box::new(2);
    let mut h = H { n: 0, p: addr_of_mut!(x) };
    unsafe { std::ptr::write_volatile(addr_of_mut!(h.p), addr_of_mut!(*y)) };
    unsafe { *h.p = 7 };
    assert!(x == 7);
}
#[kani::proof]
fn safe_field_rebind_write_volatile_read() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let mut h = H { n: 0, p: addr_of_mut!(x) };
    unsafe { std::ptr::write_volatile(addr_of_mut!(h.p), addr_of_mut!(y)) };
    let v = unsafe { *h.p };
    assert!(v == 2);
}
#[kani::proof]
fn bug_field_rebind_write_volatile_read() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let mut h = H { n: 0, p: addr_of_mut!(x) };
    unsafe { std::ptr::write_volatile(addr_of_mut!(h.p), addr_of_mut!(y)) };
    let v = unsafe { *h.p };
    assert!(v == 1);
}

#[kani::proof]
fn safe_field_rebind_write_volatile() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let mut h = H { n: 0, p: addr_of_mut!(x) };
    unsafe { std::ptr::write_volatile(addr_of_mut!(h.p), addr_of_mut!(y)) };
    unsafe { *h.p = 7 };
    assert!(y == 7 && x == 1);
}
#[kani::proof]
fn bug_field_rebind_write_volatile() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let mut h = H { n: 0, p: addr_of_mut!(x) };
    unsafe { std::ptr::write_volatile(addr_of_mut!(h.p), addr_of_mut!(y)) };
    unsafe { *h.p = 7 };
    assert!(x == 7);
}

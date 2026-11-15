// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a pointer local whose bytes are rewritten without a typed
//! pointer store, then dereferenced directly (`*a = 7`, `*a`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_direct_local_rewritten    -> FAILED ('assertion failed: *y != 7')
//!   safe_direct_local_rewritten   -> SUCCESSFUL
//!   bug_direct_memcpy             -> FAILED ('assertion failed: *y != 7')
//!   safe_direct_memcpy            -> SUCCESSFUL
//!   bug_direct_swapped            -> FAILED ('assertion failed: *y != 7')
//!   safe_direct_swapped           -> SUCCESSFUL
//!   bug_direct_transmuted         -> FAILED ('assertion failed: *y != 7')
//!   safe_direct_transmuted        -> SUCCESSFUL
//!   bug_direct_zeroed_null_deref  -> FAILED (null pointer dereference)
//!   bug_direct_read_after_rewrite -> FAILED ('assertion failed: unsafe { *a } == 0')
//!   safe_direct_read_after_rewrite -> SUCCESSFUL
//!   bug_helper_untyped_rebind     -> FAILED ('assertion failed: *y != 7')
//!   safe_helper_untyped_rebind    -> SUCCESSFUL
//!   bug_scalar_byte_store         -> FAILED ('assertion failed: x == 0'; control)
//!   safe_scalar_byte_store        -> SUCCESSFUL (control)
//!   bug_scalar_swap               -> FAILED ('assertion failed: x == 1'; control)
//!   safe_scalar_swap              -> SUCCESSFUL (control)
//!
//! MECHANISM (pre-existing on main 22db3bcc1-era c22e1022e and on
//! fix/chc-lost-writes before round 7). The provenance facts kept for a local
//! that holds a pointer — the allocation its definition names
//! (`known_alloc_ids`, `trace_deref_store_alloc_id`), its points-at edge — are
//! read off its single definition. A typed pointer store into the local fails
//! closed where it is made, but a store through a pointer cast to another
//! pointee (`usize`, `[u8; 8]`), a byte copy, `write_bytes` and `mem::swap`
//! change the local's bytes with no pointer store: `*a = 7` still wrote the
//! object the definition named. Every bug row was SUCCESSFUL clean on main
//! (a missed bug) and `safe_direct_local_rewritten` was FAILED Genuine
//! (review of fix/chc-lost-writes round 6, 2026-09-27, finding 3).
//!
//! FIX (fix/chc-lost-writes round 7): the untyped-view net
//! (stmt/codegen_stmt_store/untyped_view_scan.rs) fails a block closed
//! (`pointer_bytes_rewritten_untyped`) when it can rewrite bytes that can hold
//! a pointer without a typed pointer store; the helper row is caught in the
//! inlined helper's body. Every bug row now FAILS without a certificate, and
//! the safe rows are known-red false failures. The scalar controls hold bytes
//! that cannot be a pointer; the net does not fire and they stay exact.

#![allow(unused)]
use std::ptr::addr_of_mut;

#[kani::proof]
fn bug_direct_local_rewritten() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(addr_of_mut!(a) as *mut usize) = yp as usize; }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_direct_local_rewritten() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(addr_of_mut!(a) as *mut usize) = yp as usize; }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_direct_memcpy() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { std::ptr::copy_nonoverlapping(&yp as *const *mut u32, &mut a as *mut *mut u32, 1); }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_direct_memcpy() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { std::ptr::copy_nonoverlapping(&yp as *const *mut u32, &mut a as *mut *mut u32, 1); }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_direct_swapped() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let mut yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    core::mem::swap(&mut a, &mut yp);
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_direct_swapped() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let mut yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    core::mem::swap(&mut a, &mut yp);
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_direct_transmuted() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let pa = addr_of_mut!(a) as *mut [u8; 8];
    unsafe { *pa = core::mem::transmute::<usize, [u8; 8]>(yp as usize); }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_direct_transmuted() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let pa = addr_of_mut!(a) as *mut [u8; 8];
    unsafe { *pa = core::mem::transmute::<usize, [u8; 8]>(yp as usize); }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_direct_zeroed_null_deref() {
    let mut bx: Box<u32> = Box::new(0);
    let mut a: *mut u32 = &mut *bx;
    unsafe { core::ptr::write_bytes(&mut a as *mut *mut u32, 0, 1); }
    unsafe { *a = 7; }
}

#[kani::proof]
fn bug_direct_read_after_rewrite() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(5);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(addr_of_mut!(a) as *mut usize) = yp as usize; }
    assert!(unsafe { *a } == 0);
}

#[kani::proof]
fn safe_direct_read_after_rewrite() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(5);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(addr_of_mut!(a) as *mut usize) = yp as usize; }
    assert!(unsafe { *a } == 5);
}

fn rebind_untyped(p: &mut *mut u32, q: *mut u32) {
    unsafe { *(p as *mut *mut u32 as *mut usize) = q as usize; }
}

#[kani::proof]
fn bug_helper_untyped_rebind() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    rebind_untyped(&mut a, yp);
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_helper_untyped_rebind() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    rebind_untyped(&mut a, yp);
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_scalar_byte_store() {
    let mut x: u16 = 0;
    unsafe { *(addr_of_mut!(x) as *mut u8) = 1; }
    assert!(x == 0);
}

#[kani::proof]
fn safe_scalar_byte_store() {
    let mut x: u16 = 0;
    unsafe { *(addr_of_mut!(x) as *mut u8) = 1; }
    assert!(x == 1);
}

#[kani::proof]
fn bug_scalar_swap() {
    let mut x: u32 = 1;
    let mut z: u32 = 2;
    core::mem::swap(&mut x, &mut z);
    assert!(x == 1);
}

#[kani::proof]
fn safe_scalar_swap() {
    let mut x: u32 = 1;
    let mut z: u32 = 2;
    core::mem::swap(&mut x, &mut z);
    assert!(x == 2 && z == 1);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- an integer local holding an exposed address, rewritten
//! through a pointer to it, then cast back and stored through.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   bug_int_addr_rebound                     -> FAILED ('assertion failed: *y != 7')
//!   safe_int_addr_rebound                    -> SUCCESSFUL
//!   bug_int_addr_mem_replace                 -> FAILED ('assertion failed: *y != 7')
//!   safe_int_addr_mem_replace                -> SUCCESSFUL
//!   bug_int_addr_field_rebound               -> FAILED ('assertion failed: *y != 7')
//!   safe_int_addr_field_rebound              -> SUCCESSFUL
//!   bug_int_addr_reassigned                  -> FAILED ('assertion failed: *y != 7')
//!   safe_int_addr_reassigned                 -> SUCCESSFUL
//!
//! MECHANISM (pre-existing on main c22e1022e and on the round-7 branch). An
//! int-to-pointer store `*(addr as *mut u32) = 7` follows `addr` back to the
//! pointer its definition exposed and writes that object. After
//! `let pa = &mut addr; *pa = yp as usize` (or `mem::replace(&mut addr, ..)`)
//! the store still wrote the object the definition named: the safe twin was
//! certified Genuine on both bundles (review of fix/chc-lost-writes round 7,
//! finding 4; the bug twin ended Unknown). The round-7 untyped-view net is
//! decided by type, and `usize` cannot hold a pointer.
//!
//! FIX (fix/chc-lost-writes round 8): net 1 tracks integers made from pointers
//! (`addr` in stmt/codegen_stmt_store/untyped_view_scan.rs) through every
//! carrier, and a block that stores through a pointer into such a local, or
//! passes a pointer to it to a call that may write it, fails closed
//! (`pointer_bytes_rewritten_untyped`). The direct reassignment control keeps
//! its own handling.

#![allow(unused)]

#[kani::proof]
fn bug_int_addr_rebound() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut addr: usize = (&mut *bx as *mut u32) as usize;
    {
        let pa = &mut addr;
        *pa = yp as usize;
    }
    unsafe { *(addr as *mut u32) = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_int_addr_rebound() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut addr: usize = (&mut *bx as *mut u32) as usize;
    {
        let pa = &mut addr;
        *pa = yp as usize;
    }
    unsafe { *(addr as *mut u32) = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_int_addr_mem_replace() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut addr: usize = (&mut *bx as *mut u32) as usize;
    let _old = core::mem::replace(&mut addr, yp as usize);
    unsafe { *(addr as *mut u32) = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_int_addr_mem_replace() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut addr: usize = (&mut *bx as *mut u32) as usize;
    let _old = core::mem::replace(&mut addr, yp as usize);
    unsafe { *(addr as *mut u32) = 7; }
    assert!(*bx == 0);
}

struct Slot {
    addr: usize,
    tag: u8,
}

#[kani::proof]
fn bug_int_addr_field_rebound() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut s = Slot { addr: (&mut *bx as *mut u32) as usize, tag: 0 };
    {
        let ps = &mut s;
        ps.addr = yp as usize;
    }
    unsafe { *(s.addr as *mut u32) = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_int_addr_field_rebound() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut s = Slot { addr: (&mut *bx as *mut u32) as usize, tag: 0 };
    {
        let ps = &mut s;
        ps.addr = yp as usize;
    }
    unsafe { *(s.addr as *mut u32) = 7; }
    assert!(*bx == 0);
}

// Control: the address integer reassigned directly (a second definition).
#[kani::proof]
fn bug_int_addr_reassigned() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut addr: usize = (&mut *bx as *mut u32) as usize;
    addr = yp as usize;
    unsafe { *(addr as *mut u32) = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_int_addr_reassigned() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut addr: usize = (&mut *bx as *mut u32) as usize;
    addr = yp as usize;
    unsafe { *(addr as *mut u32) = 7; }
    assert!(*bx == 0);
}

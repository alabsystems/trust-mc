// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a pointer local's bytes rewritten through a pun that
//! travels through a carrier before the store: a reference to the punned
//! pointer, a helper taking that reference, a closure capturing it by
//! reference, an `Option` payload, a one-element array, an array repeat, an
//! integer launder.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   bug_pun_through_ref_to_ptr               -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_through_ref_to_ptr              -> SUCCESSFUL
//!   bug_pun_mut_ref_carrier                  -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_mut_ref_carrier                 -> SUCCESSFUL
//!   bug_pun_ref_to_helper                    -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_ref_to_helper                   -> SUCCESSFUL
//!   bug_pun_option_downcast                  -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_option_downcast                 -> SUCCESSFUL
//!   bug_pun_closure_ref_capture              -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_closure_ref_capture             -> SUCCESSFUL
//!   bug_pun_through_one_elem_array           -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_through_one_elem_array          -> SUCCESSFUL
//!   bug_pun_through_repeat                   -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_through_repeat                  -> SUCCESSFUL
//!   bug_int_launder_checked_add              -> FAILED ('assertion failed: *y != 7')
//!   safe_int_launder_checked_add             -> SUCCESSFUL
//!   bug_int_launder_not                      -> FAILED ('assertion failed: *y != 7')
//!   safe_int_launder_not                     -> SUCCESSFUL
//!   bug_pun_ref_carrier_read                 -> FAILED ('assertion failed: unsafe { *a } == 0')
//!   safe_pun_ref_carrier_read                -> SUCCESSFUL
//!
//! MECHANISM (pre-existing on main c22e1022e; the round-7 net did not follow
//! these carriers). The provenance facts kept for a pointer local are read off
//! its definition, so after `*q = yp as usize` through a pun of `&mut a`,
//! `*a = 7` still wrote the object `a`'s definition named. Round 7's
//! untyped-view net 1 refused a store through a punned pointer, but it
//! followed the pun only through direct copies, casts and field-only reads: a
//! reference to the pointer local read back as `copy (*rq)`, a closure
//! environment holding `&q`, an `Option` downcast, a checked add or a bitwise
//! not dropped it. The bug rows through a reference, a helper, a closure and an
//! `Option` were SUCCESSFUL clean on main and on the round-7 branch (missed
//! bugs) and their safe twins FAILED Genuine (review of fix/chc-lost-writes
//! round 7, finding 2). The launder, one-element-array and repeat rows were
//! masked by `deref_store_referent_unresolved` on both.
//!
//! FIX (fix/chc-lost-writes round 8): net 1 runs on a value flow that follows
//! every carrier (stmt/codegen_stmt_store/untyped_view_flow.rs): the store
//! through the pun fails the block closed (`pointer_bytes_rewritten_untyped`)
//! however the pun got there, and a call that may write through its arguments
//! and receives a reference to a pun fails closed too. Every bug row FAILS
//! without a certificate; the safe rows are known-red false failures.

#![allow(unused)]
use std::ptr::addr_of_mut;

#[kani::proof]
fn bug_pun_through_ref_to_ptr() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    let rq = &q;
    unsafe { **rq = yp as usize; }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_through_ref_to_ptr() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    let rq = &q;
    unsafe { **rq = yp as usize; }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_pun_mut_ref_carrier() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let mut q: *mut usize = addr_of_mut!(a) as *mut usize;
    let rq = &mut q;
    unsafe { **rq = yp as usize; }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_mut_ref_carrier() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let mut q: *mut usize = addr_of_mut!(a) as *mut usize;
    let rq = &mut q;
    unsafe { **rq = yp as usize; }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[inline(never)]
fn store_through(p: &*mut usize, v: usize) {
    unsafe { **p = v; }
}

#[kani::proof]
fn bug_pun_ref_to_helper() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    store_through(&q, yp as usize);
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_ref_to_helper() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    store_through(&q, yp as usize);
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_pun_option_downcast() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let o = Some(addr_of_mut!(a) as *mut usize);
    if let Some(q) = o {
        unsafe { *q = yp as usize; }
    }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_option_downcast() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let o = Some(addr_of_mut!(a) as *mut usize);
    if let Some(q) = o {
        unsafe { *q = yp as usize; }
    }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_pun_closure_ref_capture() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    let st = || unsafe { *q = yp as usize };
    st();
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_closure_ref_capture() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    let st = || unsafe { *q = yp as usize };
    st();
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_pun_through_one_elem_array() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let arr = [addr_of_mut!(a) as *mut usize];
    let q = arr[0];
    unsafe { *q = yp as usize; }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_through_one_elem_array() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let arr = [addr_of_mut!(a) as *mut usize];
    let q = arr[0];
    unsafe { *q = yp as usize; }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_pun_through_repeat() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q0: *mut usize = addr_of_mut!(a) as *mut usize;
    let arr = [q0; 1];
    let q = arr[0];
    unsafe { *q = yp as usize; }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_through_repeat() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q0: *mut usize = addr_of_mut!(a) as *mut usize;
    let arr = [q0; 1];
    let q = arr[0];
    unsafe { *q = yp as usize; }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_int_launder_checked_add() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let k: usize = kani::any();
    kani::assume(k == 0);
    let addr = addr_of_mut!(a) as usize + k;
    unsafe { *(addr as *mut usize) = yp as usize; }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_int_launder_checked_add() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let k: usize = kani::any();
    kani::assume(k == 0);
    let addr = addr_of_mut!(a) as usize + k;
    unsafe { *(addr as *mut usize) = yp as usize; }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_int_launder_not() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let addr = !(!(addr_of_mut!(a) as usize));
    unsafe { *(addr as *mut usize) = yp as usize; }
    unsafe { *a = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_int_launder_not() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let addr = !(!(addr_of_mut!(a) as usize));
    unsafe { *(addr as *mut usize) = yp as usize; }
    unsafe { *a = 7; }
    assert!(*bx == 0);
}

// Controls: the pun read back through the reference and then only READ.
#[kani::proof]
fn bug_pun_ref_carrier_read() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(5);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    let rq = &q;
    unsafe { **rq = yp as usize; }
    assert!(unsafe { *a } == 0);
}

#[kani::proof]
fn safe_pun_ref_carrier_read() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(5);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q: *mut usize = addr_of_mut!(a) as *mut usize;
    let rq = &q;
    unsafe { **rq = yp as usize; }
    assert!(unsafe { *a } == 5);
}

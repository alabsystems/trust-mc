// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- an atomic built with `AtomicU32::from_ptr` over a pointer
//! no live object backs (review of fix/chc-lost-writes, lostwrite track round 3,
//! finding 3). The atomic load's memory lane for a wrapper whose own array is
//! unwritten (the repr(transparent) alias lane) read the cell with no validity
//! or bounds check, so a load through an integer-to-pointer result or a freed
//! `Box` verified SUCCESSFUL where Kani reports the invalid access; the lane now
//! carries the dereference's checks (`heap_access_checks`). The lane also chose
//! its alias array by the first match of a `HashMap` walk, so the safe `Box`
//! row read `mem_Ordering` in some runs: it picks the wrapped type's array.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_atomic_load_lane1         -> FAILED ('dereference failure: invalid integer address')
//!   bug_atomic_load_lane3         -> FAILED ('dereference failure: invalid integer address')
//!   bug_atomic_load_freed_box     -> FAILED ('dereference failure: deallocated dynamic object')
//!   safe_atomic_load_box          -> SUCCESSFUL
//!   safe_atomic_load_stack        -> SUCCESSFUL
//!   safe_atomic_bool_static       -> SUCCESSFUL
//!
#![allow(unused)]
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};

#[kani::proof]
fn bug_atomic_load_lane1() {
    let y = 4u32;
    let r = &y;
    let p = (1usize << 32) as *mut u32;
    let a = unsafe { AtomicU32::from_ptr(p) };
    let v = a.load(Ordering::Relaxed);
    assert!(v == v || *r == 0);
}

#[kani::proof]
fn bug_atomic_load_lane3() {
    let y = 4u32;
    let r = &y;
    let p = (3usize << 32) as *mut u32;
    let a = unsafe { AtomicU32::from_ptr(p) };
    let v = a.load(Ordering::Relaxed);
    assert!(v == v || *r == 0);
}

#[kani::proof]
fn bug_atomic_load_freed_box() {
    let p = Box::into_raw(Box::new(5u32));
    unsafe { drop(Box::from_raw(p)) };
    let a = unsafe { AtomicU32::from_ptr(p) };
    let v = a.load(Ordering::Relaxed);
    assert!(v == v);
}

#[kani::proof]
fn safe_atomic_load_box() {
    let p = Box::into_raw(Box::new(5u32));
    let a = unsafe { AtomicU32::from_ptr(p) };
    assert!(a.load(Ordering::Relaxed) == 5);
    a.store(6, Ordering::Relaxed);
    assert!(a.load(Ordering::Relaxed) == 6);
    unsafe { drop(Box::from_raw(p)) };
}

#[kani::proof]
fn safe_atomic_load_stack() {
    let mut x = 9u32;
    let p = &mut x as *mut u32;
    let a = unsafe { AtomicU32::from_ptr(p) };
    assert!(a.fetch_add(1, Ordering::Relaxed) == 9);
    assert!(a.load(Ordering::Relaxed) == 10);
}

#[kani::proof]
fn safe_atomic_bool_static() {
    static FLAG: AtomicBool = AtomicBool::new(false);
    FLAG.store(true, Ordering::SeqCst);
    assert!(FLAG.load(Ordering::SeqCst));
}

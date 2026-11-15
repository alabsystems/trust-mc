// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- ptr::null(), null_mut() and NonNull::dangling() beside an exposed stack
//! address, and one allocation site executed twice in a loop or by two calls (review of fix/chc-
//! lost-writes, lostwrite round 1, finding 6). The null literal went through the stack-range
//! mapping of the integer-to-pointer lane and lost its constant lane; a literal integer is now
//! decided first.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_null_with_stack_addr            -> FAILED ('assertion failed: n.is_null() && v != 7')
//!   safe_null_with_stack_addr           -> SUCCESSFUL
//!   bug_null_mut_with_stack_array_addr  -> FAILED ('assertion failed: a[0] != 9')
//!   bug_dangling_with_stack_addr        -> FAILED ('assertion failed: v != 7 && d.as_ptr() as usize == 8')
//!   bug_null_no_stack_addr              -> FAILED ('assertion failed: n.is_null() && x != 7')
//!   bug_null_cmp_box                    -> FAILED ('assertion failed: pb != n && x != 7')
//!   safe_null_mut_with_stack_array_addr -> SUCCESSFUL
//!   safe_dangling_with_stack_addr       -> SUCCESSFUL
//!   safe_null_no_stack_addr             -> SUCCESSFUL
//!   safe_null_cmp_box                   -> SUCCESSFUL
//!   safe_loop_site_elem_store           -> SUCCESSFUL
//!   bug_loop_site_elem_store            -> FAILED ('assertion failed: v0 == 11')
//!   safe_loop_site_scalar_store         -> SUCCESSFUL
//!   bug_loop_site_scalar_store          -> FAILED ('assertion failed: v0 == 11')
//!   safe_two_call_site_elem_store       -> SUCCESSFUL
//!   bug_two_call_site_elem_store        -> FAILED ('assertion failed: v0 == 11')
//!
#![allow(unused)]
use std::ptr::{NonNull, null, null_mut};

#[kani::proof]
fn bug_null_with_stack_addr() {
    let x: u32 = kani::any();
    let px = &x as *const u32;
    let n: *const u8 = null();
    let v = unsafe { *px };
    assert!(n.is_null() && v != 7);
}
#[kani::proof]
fn safe_null_with_stack_addr() {
    let x: u32 = kani::any();
    kani::assume(x != 7);
    let px = &x as *const u32;
    let n: *const u8 = null();
    let v = unsafe { *px };
    assert!(n.is_null() && v != 7);
}
#[kani::proof]
fn bug_null_mut_with_stack_array_addr() {
    let mut a: [u16; 2] = [1, 2];
    let pa = a.as_mut_ptr();
    let mut q: *mut u16 = null_mut();
    let i: usize = kani::any();
    kani::assume(i < 2);
    q = unsafe { pa.add(i) };
    unsafe { *q = 9 };
    assert!(a[0] != 9);
}
#[kani::proof]
fn bug_dangling_with_stack_addr() {
    let x: u32 = kani::any();
    let px = &x as *const u32;
    let d: NonNull<u64> = NonNull::dangling();
    let v = unsafe { *px };
    assert!(v != 7 && d.as_ptr() as usize == 8);
}
#[kani::proof]
fn bug_null_no_stack_addr() {
    let x: u32 = kani::any();
    let n: *const u8 = null();
    assert!(n.is_null() && x != 7);
}
#[kani::proof]
fn bug_null_cmp_box() {
    let b = Box::new(5u32);
    let x: u32 = kani::any();
    let pb: *const u32 = &*b;
    let n: *const u32 = null();
    assert!(pb != n && x != 7);
}

#[kani::proof]
fn safe_null_mut_with_stack_array_addr() {
    let mut a: [u16; 2] = [1, 2];
    let pa = a.as_mut_ptr();
    let mut q: *mut u16 = null_mut();
    let i: usize = kani::any();
    kani::assume(i < 2);
    q = unsafe { pa.add(i) };
    unsafe { *q = 9 };
    assert!(a[i] == 9);
}
#[kani::proof]
fn safe_dangling_with_stack_addr() {
    let x: u32 = kani::any();
    kani::assume(x != 7);
    let px = &x as *const u32;
    let d: NonNull<u64> = NonNull::dangling();
    let v = unsafe { *px };
    assert!(v != 7 && d.as_ptr() as usize == 8);
}
#[kani::proof]
fn safe_null_no_stack_addr() {
    let x: u32 = kani::any();
    kani::assume(x != 7);
    let n: *const u8 = null();
    assert!(n.is_null() && x != 7);
}
#[kani::proof]
fn safe_null_cmp_box() {
    let b = Box::new(5u32);
    let x: u32 = kani::any();
    kani::assume(x != 7);
    let pb: *const u32 = &*b;
    let n: *const u32 = null();
    assert!(pb != n && x != 7);
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_loop_site_elem_store() {
    let mut p0: *mut [u16; 2] = null_mut();
    let mut p1: *mut [u16; 2] = null_mut();
    for k in 0..2u16 {
        let b = Box::into_raw(Box::new([0u16; 2]));
        unsafe { (*b)[1] = k + 10 };
        if k == 0 { p0 = b } else { p1 = b }
    }
    let v0 = unsafe { (*p0)[1] };
    unsafe {
        drop(Box::from_raw(p0));
        drop(Box::from_raw(p1));
    }
    assert!(v0 == 10);
}
#[kani::proof]
#[kani::unwind(3)]
fn bug_loop_site_elem_store() {
    let mut p0: *mut [u16; 2] = null_mut();
    let mut p1: *mut [u16; 2] = null_mut();
    for k in 0..2u16 {
        let b = Box::into_raw(Box::new([0u16; 2]));
        unsafe { (*b)[1] = k + 10 };
        if k == 0 { p0 = b } else { p1 = b }
    }
    let v0 = unsafe { (*p0)[1] };
    unsafe {
        drop(Box::from_raw(p0));
        drop(Box::from_raw(p1));
    }
    assert!(v0 == 11);
}
#[kani::proof]
#[kani::unwind(3)]
fn safe_loop_site_scalar_store() {
    let mut p0: *mut u16 = null_mut();
    let mut p1: *mut u16 = null_mut();
    for k in 0..2u16 {
        let b = Box::into_raw(Box::new(0u16));
        unsafe { *b = k + 10 };
        if k == 0 { p0 = b } else { p1 = b }
    }
    let v0 = unsafe { *p0 };
    unsafe {
        drop(Box::from_raw(p0));
        drop(Box::from_raw(p1));
    }
    assert!(v0 == 10);
}
#[kani::proof]
#[kani::unwind(3)]
fn bug_loop_site_scalar_store() {
    let mut p0: *mut u16 = null_mut();
    let mut p1: *mut u16 = null_mut();
    for k in 0..2u16 {
        let b = Box::into_raw(Box::new(0u16));
        unsafe { *b = k + 10 };
        if k == 0 { p0 = b } else { p1 = b }
    }
    let v0 = unsafe { *p0 };
    unsafe {
        drop(Box::from_raw(p0));
        drop(Box::from_raw(p1));
    }
    assert!(v0 == 11);
}
#[kani::proof]
fn safe_two_call_site_elem_store() {
    fn mk(k: u16) -> *mut [u16; 2] {
        let b = Box::into_raw(Box::new([0u16; 2]));
        unsafe { (*b)[1] = k };
        b
    }
    let p0 = mk(10);
    let p1 = mk(11);
    let v0 = unsafe { (*p0)[1] };
    unsafe {
        drop(Box::from_raw(p0));
        drop(Box::from_raw(p1));
    }
    assert!(v0 == 10);
}
#[kani::proof]
fn bug_two_call_site_elem_store() {
    fn mk(k: u16) -> *mut [u16; 2] {
        let b = Box::into_raw(Box::new([0u16; 2]));
        unsafe { (*b)[1] = k };
        b
    }
    let p0 = mk(10);
    let p1 = mk(11);
    let v0 = unsafe { (*p0)[1] };
    unsafe {
        drop(Box::from_raw(p0));
        drop(Box::from_raw(p1));
    }
    assert!(v0 == 11);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- the untyped-view net 1 exempts a local array of two or more
//! elements (read through memory). These rows attack the exemption with struct
//! elements holding a pointer, an element copied to a pointer local before the
//! store, `write_bytes` over one element of `[Option<&u32>; 2]`, and a byte copy
//! from an integer array into a pointer array (review of fix/chc-lost-writes
//! round 3, finding 3: every row held on the round-8 bundle; main certified the
//! `write_bytes` safe row Genuine).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_copy_into_struct_array_then_store        -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_into_struct_array_then_store       -> SUCCESSFUL
//!   bug_copy_into_ptr_array_then_local           -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_into_ptr_array_then_local          -> SUCCESSFUL
//!   bug_copy_into_struct_array_then_local        -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_into_struct_array_then_local       -> SUCCESSFUL
//!   bug_write_bytes_option_ref_array_elem        -> FAILED ('assertion failed: arr[0].is_some()')
//!   safe_write_bytes_option_ref_array_elem       -> SUCCESSFUL
//!   bug_byte_copy_from_int_array_into_ptr_array  -> FAILED ('assertion failed: *y != 7')
//!   safe_byte_copy_from_int_array_into_ptr_array -> SUCCESSFUL
//!
#![allow(unused)]
use std::ptr::copy_nonoverlapping;

#[derive(Clone, Copy)]
struct S {
    p: *mut u32,
}

#[kani::proof]
fn bug_copy_into_struct_array_then_store() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src = [S { p: yp }, S { p: yp }];
    let mut arr = [S { p: &mut *b1 }, S { p: &mut *b2 }];
    unsafe { copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    unsafe {
        *arr[0].p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_into_struct_array_then_store() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src = [S { p: yp }, S { p: yp }];
    let mut arr = [S { p: &mut *b1 }, S { p: &mut *b2 }];
    unsafe { copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    unsafe {
        *arr[0].p = 7;
    }
    assert!(*b1 == 0 && *b2 == 0);
}

#[kani::proof]
fn bug_copy_into_ptr_array_then_local() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [*mut u32; 2] = [yp, yp];
    let mut arr: [*mut u32; 2] = [&mut *b1, &mut *b2];
    unsafe { copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    let p = arr[0];
    unsafe {
        *p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_into_ptr_array_then_local() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [*mut u32; 2] = [yp, yp];
    let mut arr: [*mut u32; 2] = [&mut *b1, &mut *b2];
    unsafe { copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    let p = arr[0];
    unsafe {
        *p = 7;
    }
    assert!(*b1 == 0 && *b2 == 0);
}

#[kani::proof]
fn bug_copy_into_struct_array_then_local() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src = [S { p: yp }, S { p: yp }];
    let mut arr = [S { p: &mut *b1 }, S { p: &mut *b2 }];
    unsafe { copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    let s = arr[0];
    unsafe {
        *s.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_into_struct_array_then_local() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src = [S { p: yp }, S { p: yp }];
    let mut arr = [S { p: &mut *b1 }, S { p: &mut *b2 }];
    unsafe { copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    let s = arr[0];
    unsafe {
        *s.p = 7;
    }
    assert!(*b1 == 0 && *b2 == 0);
}

// write_bytes zeroing one element of an array of Option<&u32>
#[kani::proof]
fn bug_write_bytes_option_ref_array_elem() {
    let x = 1u32;
    let mut arr: [Option<&u32>; 2] = [Some(&x), Some(&x)];
    unsafe { std::ptr::write_bytes(arr.as_mut_ptr(), 0, 1) };
    assert!(arr[0].is_some());
}

#[kani::proof]
fn safe_write_bytes_option_ref_array_elem() {
    let x = 1u32;
    let mut arr: [Option<&u32>; 2] = [Some(&x), Some(&x)];
    unsafe { std::ptr::write_bytes(arr.as_mut_ptr(), 0, 1) };
    assert!(arr[0].is_none() && arr[1].is_some());
}

// a 2-element array of pointers rewritten by bytes from an integer array
#[kani::proof]
fn bug_byte_copy_from_int_array_into_ptr_array() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [usize; 2] = [yp as usize, yp as usize];
    let mut arr: [*mut u32; 2] = [&mut *b1, &mut *b2];
    unsafe { copy_nonoverlapping(src.as_ptr() as *const u8, arr.as_mut_ptr() as *mut u8, 8) };
    let p = arr[0];
    unsafe {
        *p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_byte_copy_from_int_array_into_ptr_array() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [usize; 2] = [yp as usize, yp as usize];
    let mut arr: [*mut u32; 2] = [&mut *b1, &mut *b2];
    unsafe { copy_nonoverlapping(src.as_ptr() as *const u8, arr.as_mut_ptr() as *mut u8, 8) };
    let p = arr[0];
    unsafe {
        *p = 7;
    }
    assert!(*b1 == 0);
}

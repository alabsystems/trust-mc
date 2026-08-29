// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: test_deref_stack_ptr_offset=PROOF
// kani-expect: test_deref_vec_ptr_offset=PROOF

//! Probe: does dereferencing a raw pointer to a stack array work?
//! Tests the minimum pointer dereference path without offset arithmetic.

#[kani::proof]
fn test_deref_stack_ptr() {
    let arr: [i32; 3] = [1, 2, 3];
    let ptr: *const i32 = arr.as_ptr();
    let val = unsafe { *ptr };
    assert_eq!(val, 1);
}

#[kani::proof]
fn test_deref_stack_ptr_offset() {
    let arr: [i32; 3] = [1, 2, 3];
    let ptr: *const i32 = arr.as_ptr();
    let ptr1 = unsafe { ptr.add(1) };
    let val = unsafe { *ptr1 };
    assert_eq!(val, 2);
}

#[kani::proof]
fn test_deref_vec_ptr() {
    let v = vec![10i32, 20, 30];
    let ptr: *const i32 = v.as_ptr();
    let val = unsafe { *ptr };
    assert_eq!(val, 10);
}

#[kani::proof]
fn test_deref_vec_ptr_offset() {
    let v = vec![10i32, 20, 30];
    let ptr: *const i32 = v.as_ptr();
    let ptr1 = unsafe { ptr.add(1) };
    let val = unsafe { *ptr1 };
    assert_eq!(val, 20);
}

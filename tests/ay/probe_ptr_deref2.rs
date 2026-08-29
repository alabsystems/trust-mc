// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: All 4 raw stack/local deref probes are PROOF at ay 733ba8cd.

//! Probe: narrow down the pointer dereference failure.
//! Does *ptr work on a stack array vs Vec?
//! Does ptr.add(0) (zero offset) work?

#[kani::proof]
fn test_stack_raw_deref() {
    let arr: [i32; 3] = [1, 2, 3];
    let ptr: *const i32 = &arr[0] as *const i32;
    let val = unsafe { *ptr };
    assert_eq!(val, 1);
}

#[kani::proof]
fn test_stack_add_zero() {
    let arr: [i32; 3] = [1, 2, 3];
    let ptr: *const i32 = &arr[0] as *const i32;
    let ptr0 = unsafe { ptr.add(0) };
    let val = unsafe { *ptr0 };
    assert_eq!(val, 1);
}

#[kani::proof]
fn test_stack_add_one() {
    let arr: [i32; 3] = [1, 2, 3];
    let ptr: *const i32 = &arr[0] as *const i32;
    let ptr1 = unsafe { ptr.add(1) };
    let val = unsafe { *ptr1 };
    assert_eq!(val, 2);
}

#[kani::proof]
fn test_local_i32_raw_deref() {
    let x: i32 = 42;
    let ptr: *const i32 = &x as *const i32;
    let val = unsafe { *ptr };
    assert_eq!(val, 42);
}

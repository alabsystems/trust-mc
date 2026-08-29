// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: UNKNOWN
// kani-expect: step1_string_len=PROOF
// NOTE: 5 harness(es) CTREX→UNKNOWN (solver nondeterminism).

//! Probe: step-by-step isolation of MyStr::new chain.
//! Part of #4163 — find exactly which step loses the metadata.

use std::mem::size_of_val;

struct MyStr {
    header_0: u8,
    header_1: u8,
    data: str,
}

/// Step 1: String length tracking
#[kani::proof]
fn step1_string_len() {
    let mut buf = String::from("000");
    assert_eq!(buf.len(), 3);
}

/// Step 2: get_mut returns correct &mut str
#[kani::proof]
fn step2_get_mut_len() {
    let mut buf = String::from("000");
    let s = buf.get_mut(..).unwrap();
    assert_eq!(s.len(), 3);
}

/// Step 3: size_of_val of &mut str from get_mut
#[kani::proof]
fn step3_str_size_of_val() {
    let mut buf = String::from("000");
    let s = buf.get_mut(..).unwrap();
    assert_eq!(size_of_val(s), 3);
}

/// Step 4: arithmetic on str length
#[kani::proof]
fn step4_unsized_len() {
    let mut buf = String::from("000");
    let s = buf.get_mut(..).unwrap();
    let unsized_len = s.len() - 2;
    assert_eq!(unsized_len, 1);
}

/// Step 5: slice_from_raw_parts_mut produces correct length
#[kani::proof]
fn step5_raw_parts_len() {
    let mut buf = String::from("000");
    let s = buf.get_mut(..).unwrap();
    let unsized_len = s.len() - 2;
    let ptr = std::ptr::slice_from_raw_parts_mut(s.as_mut_ptr(), unsized_len);
    let slice: &mut [u8] = unsafe { &mut *ptr };
    assert_eq!(slice.len(), 1);
}

/// Step 6: cast to custom DST and check size_of_val
#[kani::proof]
fn step6_cast_size_of_val() {
    let mut buf = String::from("000");
    let s = buf.get_mut(..).unwrap();
    let unsized_len = s.len() - 2;
    let ptr = std::ptr::slice_from_raw_parts_mut(s.as_mut_ptr(), unsized_len);
    let my_str: &mut MyStr = unsafe { &mut *(ptr as *mut MyStr) };
    assert_eq!(size_of_val(my_str), 3);
}

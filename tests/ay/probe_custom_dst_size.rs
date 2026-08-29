// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: Some harnesses (1/3) demoted PROOF→UNKNOWN by false proof defense (ay#8578).

//! Probe: isolate size_of_val for custom DSTs without String complexity.
//! Part of #4163 — narrow down where the encoding fails.

use std::mem::size_of_val;

/// Custom DST with a [u8] tail instead of str.
struct MyDst {
    header: u8,
    data: [u8],
}

#[kani::proof]
fn probe_sized_array_size() {
    // Baseline: sized types should be trivial.
    let arr: [u8; 3] = [1, 2, 3];
    assert_eq!(size_of_val(&arr), 3);
}

#[kani::proof]
fn probe_slice_size() {
    // Slice from array: size_of_val should return the dynamic size.
    let arr: [u8; 3] = [1, 2, 3];
    let slice: &[u8] = &arr;
    assert_eq!(size_of_val(slice), 3);
}

#[kani::proof]
fn probe_custom_dst_size_from_raw_parts() {
    // Construct a custom DST via raw pointer cast.
    let buf: [u8; 4] = [0xAA, 1, 2, 3];
    let unsized_len: usize = 3; // 3 bytes of data after header
    let ptr = std::ptr::slice_from_raw_parts(&buf as *const u8, unsized_len);
    let my_dst: &MyDst = unsafe { &*(ptr as *const MyDst) };
    // MyDst { header: u8(1 byte), data: [u8](3 bytes) } = 4 bytes total
    assert_eq!(size_of_val(my_dst), 4);
}

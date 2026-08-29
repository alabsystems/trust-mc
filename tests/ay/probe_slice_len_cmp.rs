// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_slice_len_cmp_only=PROOF

//! Minimal probe: fat pointer comparison where data address is same, length differs.
//! Part of #4166: isolates whether BV128 Ord::cmp decomposition produces correct results.

use std::cmp::Ordering;

#[cfg_attr(kani, kani::proof)]
fn probe_slice_len_cmp_only() {
    let array = [0u8; 10];
    let first_ptr: *const [u8] = &array[0..2]; // len=2
    let second_ptr: *const [u8] = &array[0..4]; // len=4

    // Ord::cmp: same address, shorter length → Less
    assert_eq!(first_ptr.cmp(&second_ptr), Ordering::Less);
    assert_eq!(second_ptr.cmp(&first_ptr), Ordering::Greater);

    // PartialOrd relational
    assert!(first_ptr < second_ptr);
    assert!(second_ptr > first_ptr);
    assert!(first_ptr != second_ptr);
    assert!(!(first_ptr == second_ptr));
}

fn main() {}

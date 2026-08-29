// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_as_array_add=PROOF
// kani-expect: probe_as_array_identity=PROOF
// kani-expect: probe_splat_from_to=PROOF

//! Probe: isolate as_array() vs to_array() comparison for portable SIMD.
//! Part of #4086 — if to_array passes but as_array fails, the gap is in
//! the as_array ref-chain resolution inside PartialEq::eq.
//!
//! `as_array()` returns `&[T; N]`. The `assert_eq!` macro creates `&&[T; N]`
//! double-reference patterns that the CHC PartialEq::eq inline walker cannot
//! resolve back to the underlying Array expression. Tracked by #3792.
//! `to_array()` returns `[T; N]` by value and works correctly.
#![feature(portable_simd)]
use std::simd::u32x4;

/// Probe 1: to_array should work (owned comparison).
#[kani::proof]
fn probe_to_array_add() {
    let a = u32x4::splat(0);
    let b = u32x4::from_array(kani::any());
    assert_eq!((a + b).to_array(), b.to_array());
}

/// Probe 2: as_array comparison (reference comparison).
/// CTREX expected: as_array ref chain through PartialEq::eq (#3792).
#[kani::proof]
fn probe_as_array_add() {
    let a = u32x4::splat(0);
    let b = u32x4::from_array(kani::any());
    assert_eq!((a + b).as_array(), b.as_array());
}

/// Probe 3: as_array on a single value (no addition).
/// CTREX expected: same as_array ref chain issue (#3792).
#[kani::proof]
fn probe_as_array_identity() {
    let b = u32x4::from_array(kani::any());
    assert_eq!(b.as_array(), b.as_array());
}

/// Probe 4: splat + from_array with to_array (owned).
/// Isolates whether the + encoding is correct independently.
#[kani::proof]
fn probe_splat_from_to() {
    let a = u32x4::splat(0);
    let b = u32x4::from_array([1, 2, 3, 4]);
    let sum = a + b;
    assert_eq!(sum.to_array(), [1, 2, 3, 4]);
}

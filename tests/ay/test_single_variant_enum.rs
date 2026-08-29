// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! Test case for single-variant enum payload offset (Part of #3041).
//!
//! Verifies that single-variant enums with one payload field are correctly
//! encoded via Downcast+Field projection. The W1:3349 fix corrected
//! payload_start for n_fields==1 single-variant enums.
//!
//! Multi-field single-variant enums (Pair::Both(u32, u32)) and multi-match
//! patterns (matching two Wrapper values) still fail (CTREX) — those need
//! further work on multi-field Downcast projection.

/// Single-variant enum with one scalar payload (newtype pattern).
enum Wrapper {
    Val(u32),
}

/// Construct and destructure a single-variant newtype enum.
#[kani::proof]
fn test_single_variant_newtype_roundtrip() {
    let x: u32 = kani::any();
    kani::assume(x < 1000);

    let w = Wrapper::Val(x);
    match w {
        Wrapper::Val(v) => assert!(v == x),
    }
}

/// Single-variant enum constructed from function return.
fn make_wrapper(v: u32) -> Wrapper {
    Wrapper::Val(v)
}

#[kani::proof]
fn test_single_variant_from_function() {
    let x: u32 = kani::any();
    kani::assume(x < 500);

    let w = make_wrapper(x);
    match w {
        Wrapper::Val(v) => assert!(v == x),
    }
}

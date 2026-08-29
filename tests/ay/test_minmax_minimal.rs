// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Minimal reproduction for #4213: mixed i32/usize Ord::min encoding.
//!
//! Part of #4213

// kani-expect: UNKNOWN
// kani-expect: i32_max_usize_max_both=PROOF
// kani-expect: i32_min_usize_min_both=PROOF
// kani-expect: just_usize_min=PROOF
// kani-expect: usize_min_with_i32_var=PROOF
// NOTE: 2 harness(es) demoted PROOF→UNKNOWN by false proof defense (ay#8578).

/// Pure i32 min.
#[kani::proof]
fn just_i32_min() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    kani::assert(a.min(b) <= a, "min(a,b) <= a");
    kani::assert(a.min(b) <= b, "min(a,b) <= b");
}

/// Pure usize min.
#[kani::proof]
fn just_usize_min() {
    let a: usize = kani::any();
    let b: usize = kani::any();
    kani::assert(a.min(b) <= a, "min(a,b) <= a");
    kani::assert(a.min(b) <= b, "min(a,b) <= b");
}

/// i32 min, but usize variable exists (not used in min).
#[kani::proof]
fn i32_min_with_usize_var() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    let _c: usize = kani::any();
    kani::assert(a.min(b) <= a, "min(a,b) <= a");
    kani::assert(a.min(b) <= b, "min(a,b) <= b");
}

/// usize min, but i32 variable exists (not used in min).
#[kani::proof]
fn usize_min_with_i32_var() {
    let _a: i32 = kani::any();
    let c: usize = kani::any();
    let d: usize = kani::any();
    kani::assert(c.min(d) <= c, "min(c,d) <= c");
    kani::assert(c.min(d) <= d, "min(c,d) <= d");
}

/// Both i32 min and usize min in same harness.
#[kani::proof]
fn i32_min_usize_min_both() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    let c: usize = kani::any();
    let d: usize = kani::any();
    kani::assert(a.min(b) <= a, "i32 min(a,b) <= a");
    kani::assert(c.min(d) <= c, "usize min(c,d) <= c");
}

/// Both i32 max and usize max in same harness.
#[kani::proof]
fn i32_max_usize_max_both() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    let c: usize = kani::any();
    let d: usize = kani::any();
    kani::assert(a.max(b) >= a, "i32 max(a,b) >= a");
    kani::assert(c.max(d) >= c, "usize max(c,d) >= c");
}

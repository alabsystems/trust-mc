// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! Isolation: two BTreeMap::get calls in same harness on different maps.
//!
//! Part of #3348: is the issue in method inlining or direct operations?

use std::collections::BTreeMap;

/// Two gets on different maps (no struct wrapping).
#[kani::proof]
fn dual_get_direct() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let mut m1: BTreeMap<u32, u32> = BTreeMap::new();
    let m2: BTreeMap<u32, u32> = m1.clone();  // empty clone
    m1.insert(i, val);

    // m1 has store at i, m2 is empty
    let r1 = m1.get(&j).copied().unwrap_or(default);
    let r2 = m2.get(&j).copied().unwrap_or(default);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// Single get on the inserted map only.
#[kani::proof]
fn single_get_inserted_miss() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let mut m1: BTreeMap<u32, u32> = BTreeMap::new();
    m1.insert(i, val);
    let r1 = m1.get(&j).copied().unwrap_or(default);
    assert_eq!(r1, default);
}

/// Single get on the empty clone only.
#[kani::proof]
fn single_get_empty_clone() {
    let default: u32 = kani::any();
    let j: u32 = kani::any();
    let val: u32 = kani::any();
    let i: u32 = kani::any();

    let mut m1: BTreeMap<u32, u32> = BTreeMap::new();
    let m2: BTreeMap<u32, u32> = m1.clone();
    m1.insert(i, val);  // modify m1 after clone
    let r2 = m2.get(&j).copied().unwrap_or(default);
    assert_eq!(r2, default);
}

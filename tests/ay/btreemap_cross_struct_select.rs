// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: original_select_after_clone=PROOF
// kani-expect: cross_struct_read_over_write_miss=PROOF

//! Isolation test for cross-struct select pattern.
//!
//! Tests: after store(i, val), calling select on ORIGINAL struct (not clone).
//! The issue is whether a.select(j) still works after a.store(i, val) borrows a.
//!
//! Part of #3348: isolating cross-struct method call gap.

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
struct Array {
    stores: BTreeMap<u32, u32>,
    default: u32,
}

impl Array {
    fn new(default: u32) -> Self {
        Self { stores: BTreeMap::new(), default }
    }

    fn store(&self, idx: u32, val: u32) -> Self {
        let mut result = self.clone();
        result.stores.insert(idx, val);
        result
    }

    fn select(&self, idx: u32) -> u32 {
        self.stores.get(&idx).copied().unwrap_or(self.default)
    }
}

/// Calling select on original array after clone should still return default.
#[kani::proof]
fn original_select_after_clone() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let _a_stored = a.store(i, val); // Clone a, modify clone

    // Original a should be unaffected
    assert_eq!(a.select(j), default);
}

/// Cross-struct comparison: both selects should return default
#[kani::proof]
fn cross_struct_read_over_write_miss() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a_stored = a.store(i, val);

    // Both should be default: a is unmodified, a_stored has store only at i
    assert_eq!(a_stored.select(j), a.select(j));
}

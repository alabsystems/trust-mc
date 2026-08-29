// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! Isolation: store + dual select. Which combination breaks?
//!
//! Part of #3348: narrowing the store+dual-select gap.

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

/// Store, then select on STORED struct only (hit).
#[kani::proof]
fn store_select_stored_hit() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a2 = a.store(i, val);
    assert_eq!(a2.select(i), val);
}

/// Store, then select on STORED struct only (miss).
#[kani::proof]
fn store_select_stored_miss() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a2 = a.store(i, val);
    assert_eq!(a2.select(j), default);
}

/// Store, then select on ORIGINAL struct only.
#[kani::proof]
fn store_select_original_only() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    let val: u32 = kani::any();

    let a = Array::new(default);
    let _a2 = a.store(i, val);
    // a should still be unmodified
    assert_eq!(a.select(j), default);
}

/// Store, then select on BOTH structs (the failing pattern).
#[kani::proof]
fn store_select_both() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a2 = a.store(i, val);

    let r1 = a2.select(j);
    let r2 = a.select(j);
    assert_eq!(r1, default);  // a2 has no store at j
    assert_eq!(r2, default);  // a is unmodified
}

/// Store + select both: assert equality instead of default.
#[kani::proof]
fn store_select_both_eq() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a2 = a.store(i, val);
    assert_eq!(a2.select(j), a.select(j));
}

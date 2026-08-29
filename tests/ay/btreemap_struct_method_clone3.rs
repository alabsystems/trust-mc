// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! Isolation: dual lookup at DIFFERENT key from store key.
//!
//! Part of #3348.

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
struct TwoFieldMap {
    data: BTreeMap<u32, u32>,
    default_val: u32,
}

impl TwoFieldMap {
    fn new(default: u32) -> Self {
        Self { data: BTreeMap::new(), default_val: default }
    }
    fn put(&self, key: u32, val: u32) -> Self {
        let mut result = self.clone();
        result.data.insert(key, val);
        result
    }
    fn lookup(&self, key: u32) -> u32 {
        self.data.get(&key).copied().unwrap_or(self.default_val)
    }
}

/// Dual lookup at different key than store (the exact failing pattern)
#[kani::proof]
fn dual_lookup_different_key() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let m = TwoFieldMap::new(default);
    let m2 = m.put(i, val);

    let r1 = m2.lookup(j);
    let r2 = m.lookup(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// Same as above but compare directly
#[kani::proof]
fn dual_lookup_eq() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let m = TwoFieldMap::new(default);
    let m2 = m.put(i, val);
    assert_eq!(m2.lookup(j), m.lookup(j));
}

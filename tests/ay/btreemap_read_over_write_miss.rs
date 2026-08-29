// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! Isolation test for read-over-write-miss pattern.
//!
//! Tests: after store(i, val), reading at j (j!=i) should return default.
//! This requires SMT array theory: Select(Store(a, i, v), j) = Select(a, j) when i!=j.
//!
//! Part of #3348: isolating which patterns work after Clone force-inline.

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

/// After storing at i, reading at j (j!=i) should still be default.
#[kani::proof]
fn read_over_write_miss() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a_stored = a.store(i, val);

    // a_stored.select(j) should be default since we only stored at i, not j
    assert_eq!(a_stored.select(j), default);
}

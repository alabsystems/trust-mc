// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: BMC_SAFE

//! Isolation: exact same struct as ay_self_verify_array_store.
//!
//! Part of #3348: binary search for the difference.

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

/// Exact same pattern as store_select_both (from btreemap_store_dual_select).
#[kani::proof]
fn store_select_both_v2() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a2 = a.store(i, val);

    let r1 = a2.select(j);
    let r2 = a.select(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

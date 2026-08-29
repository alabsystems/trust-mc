// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! Isolation test for clone-return-from-method pattern with multi-field structs.
//!
//! Tests the exact pattern from ay_self_verify_array_store.rs:
//!   fn store(&self, idx, val) -> Self { let mut r = self.clone(); r.field.insert(idx, val); r }
//!
//! Part of #3348: isolating the method boundary gap.

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

/// Simplest case: construct, put, lookup.
#[kani::proof]
fn two_field_method_put_lookup() {
    let default: u32 = kani::any();
    let key: u32 = kani::any();
    let val: u32 = kani::any();

    let m = TwoFieldMap::new(default);
    let m2 = m.put(key, val);

    assert_eq!(m2.lookup(key), val);
}

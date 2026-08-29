// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: dual_lookup=PROOF
// kani-expect: single_lookup_original=PROOF
// kani-expect: single_lookup_modified=PROOF

//! Isolation test: struct method clone with dual lookup.
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

/// Single lookup on modified struct (should work — btreemap_struct_method_clone passes)
#[kani::proof]
fn single_lookup_modified() {
    let default: u32 = kani::any();
    let key: u32 = kani::any();
    let val: u32 = kani::any();
    let m = TwoFieldMap::new(default);
    let m2 = m.put(key, val);
    assert_eq!(m2.lookup(key), val);
}

/// Single lookup on original struct after put
#[kani::proof]
fn single_lookup_original() {
    let default: u32 = kani::any();
    let key: u32 = kani::any();
    let val: u32 = kani::any();
    let m = TwoFieldMap::new(default);
    let _m2 = m.put(key, val);
    assert_eq!(m.lookup(key), default);
}

/// Dual lookup: both original and modified (hypothesis: this fails)
#[kani::proof]
fn dual_lookup() {
    let default: u32 = kani::any();
    let key: u32 = kani::any();
    let val: u32 = kani::any();
    let m = TwoFieldMap::new(default);
    let m2 = m.put(key, val);
    assert_eq!(m2.lookup(key), val);
    assert_eq!(m.lookup(key), default);
}

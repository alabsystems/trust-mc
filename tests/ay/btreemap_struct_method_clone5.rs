// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: direct_put_lookup_method=PROOF
// kani-expect: put_method_direct_lookup=PROOF
// kani-expect: put_method_lookup_method=PROOF

//! Final isolation: which methods trigger the failure?
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

/// new() + put method + direct lookup (not method)
#[kani::proof]
fn put_method_direct_lookup() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let m = TwoFieldMap::new(default);
    let m2 = m.put(i, val); // method
    // direct field access for lookups
    let r1 = m2.data.get(&j).copied().unwrap_or(m2.default_val);
    let r2 = m.data.get(&j).copied().unwrap_or(m.default_val);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// new() + direct put + lookup method
#[kani::proof]
fn direct_put_lookup_method() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let m = TwoFieldMap::new(default);
    let mut m2 = m.clone();
    m2.data.insert(i, val); // direct, not method
    // lookup method for both
    let r1 = m2.lookup(j);
    let r2 = m.lookup(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// new() + put method + lookup method (the failing combo)
#[kani::proof]
fn put_method_lookup_method() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let m = TwoFieldMap::new(default);
    let m2 = m.put(i, val); // method
    let r1 = m2.lookup(j); // method
    let r2 = m.lookup(j); // method
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

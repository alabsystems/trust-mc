// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: array_struct_literal_constructor=PROOF
// kani-expect: mymap_with_new_method=PROOF

//! Binary search: which difference between MyMap and Array matters?
//!
//! Part of #3348.

use std::collections::BTreeMap;

// Test A: Array struct, but use struct literal (not new method)
#[derive(Debug, Clone)]
struct ArrayLit {
    stores: BTreeMap<u32, u32>,
    default: u32,
}

impl ArrayLit {
    fn store(&self, idx: u32, val: u32) -> Self {
        let mut result = self.clone();
        result.stores.insert(idx, val);
        result
    }
    fn select(&self, idx: u32) -> u32 {
        self.stores.get(&idx).copied().unwrap_or(self.default)
    }
}

/// Uses struct literal constructor instead of new().
#[kani::proof]
fn array_struct_literal_constructor() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = ArrayLit { stores: BTreeMap::new(), default };
    let a2 = a.store(i, val);
    let r1 = a2.select(j);
    let r2 = a.select(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

// Test B: MyMap struct but with new() method
#[derive(Debug, Clone)]
struct MyMap2 {
    data: BTreeMap<u32, u32>,
    default: u32,
}

impl MyMap2 {
    fn new(default: u32) -> Self {
        Self { data: BTreeMap::new(), default }
    }
    fn put(&self, key: u32, val: u32) -> Self {
        let mut result = self.clone();
        result.data.insert(key, val);
        result
    }
    fn lookup(&self, key: u32) -> u32 {
        self.data.get(&key).copied().unwrap_or(self.default)
    }
}

/// MyMap struct with new() method.
#[kani::proof]
fn mymap_with_new_method() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = MyMap2::new(default);
    let a2 = a.put(i, val);
    let r1 = a2.lookup(j);
    let r2 = a.lookup(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

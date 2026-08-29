// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: mymap_literal_dual_get=PROOF
// kani-expect: mymap_new_dual_get=PROOF

//! Exact reproduction: is it the new() method that breaks it?
//!
//! Part of #3348.

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
struct MyMap {
    data: BTreeMap<u32, u32>,
    default: u32,
}

impl MyMap {
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

/// Same as the passing btreemap_struct_dual_get test but using new().
#[kani::proof]
fn mymap_new_dual_get() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = MyMap::new(default);  // This is what changes
    let a2 = a.put(i, val);

    let r1 = a2.lookup(j);
    let r2 = a.lookup(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// Control: struct literal, should pass.
#[kani::proof]
fn mymap_literal_dual_get() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = MyMap { data: BTreeMap::new(), default };
    let a2 = a.put(i, val);

    let r1 = a2.lookup(j);
    let r2 = a.lookup(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

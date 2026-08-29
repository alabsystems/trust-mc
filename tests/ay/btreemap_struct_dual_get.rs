// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: dual_get_struct_via_method=PROOF

//! Isolation: dual gets on struct-embedded BTreeMaps.
//!
//! Part of #3348: is the issue in struct-embedding or in method inlining?

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
struct MyMap {
    data: BTreeMap<u32, u32>,
    default: u32,
}

/// Two direct gets on different struct-embedded BTreeMaps.
#[kani::proof]
fn dual_get_struct_embedded_direct() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = MyMap { data: BTreeMap::new(), default };
    let mut a2 = a.clone();
    a2.data.insert(i, val);

    // Direct struct field access, no method call
    let r1 = a2.data.get(&j).copied().unwrap_or(a2.default);
    let r2 = a.data.get(&j).copied().unwrap_or(a.default);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// Same but with method calls (the failing pattern).
#[kani::proof]
fn dual_get_struct_via_method() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = MyMap { data: BTreeMap::new(), default };
    let a2 = MyMap::put(&a, i, val);

    let r1 = MyMap::lookup(&a2, j);
    let r2 = MyMap::lookup(&a, j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

impl MyMap {
    fn put(&self, key: u32, val: u32) -> Self {
        let mut result = self.clone();
        result.data.insert(key, val);
        result
    }

    fn lookup(&self, key: u32) -> u32 {
        self.data.get(&key).copied().unwrap_or(self.default)
    }
}

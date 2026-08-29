// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! Final isolation: new() constructor + direct field access (no lookup method).
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
}

/// new() + put + direct field get (no lookup method)
#[kani::proof]
fn direct_field_access() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let m = TwoFieldMap::new(default);
    let m2 = m.put(i, val);

    let r1 = m2.data.get(&j).copied().unwrap_or(m2.default_val);
    let r2 = m.data.get(&j).copied().unwrap_or(m.default_val);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// struct literal + put + lookup method (should pass — control)
#[kani::proof]
fn struct_literal_lookup_method() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i != j);
    let val: u32 = kani::any();

    let m = TwoFieldMap { data: BTreeMap::new(), default_val: default };
    let m2 = m.put(i, val);

    let r1 = m2.data.get(&j).copied().unwrap_or(m2.default_val);
    let r2 = m.data.get(&j).copied().unwrap_or(m.default_val);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

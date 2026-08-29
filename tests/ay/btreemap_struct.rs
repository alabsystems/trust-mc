// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: two_field_empty_default=PROOF

//! Struct-embedded BTreeMap isolation test for #3348.
//!
//! Tests BTreeMap operations through struct field projections at
//! increasing complexity levels. Determines which level of struct
//! embedding breaks the CHC encoding.

use std::collections::BTreeMap;

/// Simplest struct: single BTreeMap field, no other fields.
struct Wrapper {
    data: BTreeMap<u32, u32>,
}

/// Level 1: Constructor + direct field access (no clone, no self methods).
#[kani::proof]
fn struct_btreemap_construct_insert_get() {
    let mut w = Wrapper { data: BTreeMap::new() };
    let key: u32 = kani::any();
    let val: u32 = kani::any();

    w.data.insert(key, val);
    let result = w.data.get(&key).copied().unwrap_or(0);
    assert_eq!(result, val);
}

/// Level 2: Two-field struct matching Array layout.
struct TwoField {
    stores: BTreeMap<u32, u32>,
    default: u32,
}

#[kani::proof]
fn two_field_insert_get() {
    let default: u32 = kani::any();
    let mut s = TwoField { stores: BTreeMap::new(), default };
    let key: u32 = kani::any();
    let val: u32 = kani::any();

    s.stores.insert(key, val);
    let result = s.stores.get(&key).copied().unwrap_or(s.default);
    assert_eq!(result, val);
}

/// Level 3: Read from empty struct (no insert, just default).
#[kani::proof]
fn two_field_empty_default() {
    let default: u32 = kani::any();
    let s = TwoField { stores: BTreeMap::new(), default };
    let key: u32 = kani::any();

    let result = s.stores.get(&key).copied().unwrap_or(s.default);
    assert_eq!(result, default);
}

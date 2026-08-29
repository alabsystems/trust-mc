// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: BMC_SAFE

//! Minimal BTreeMap test: direct operations WITHOUT struct embedding.
//! Routed to BMC because these are acyclic SMT Array store/select obligations;
//! CHC/Spacer currently returns clean UNKNOWN on the two-insert isolation case.
//!
//! Isolation test for #3348: determines whether BTreeMap CTREX in
//! ay_self_verify_array_store.rs is caused by:
//!   (a) BTreeMap→HashMap stub routing failure, or
//!   (b) struct-embedded collection state propagation gap
//!
//! If this file PROOFs fully (3/3), the issue is (b) struct embedding.
//! If any harness CTREX, the issue is (a) BTreeMap stub routing.

use std::collections::BTreeMap;

/// Direct insert + get with copied + unwrap_or — the exact chain
/// used by Array::select in ay_self_verify_array_store.rs.
#[kani::proof]
fn btreemap_insert_get_copied_unwrap_or() {
    let mut map: BTreeMap<u32, u32> = BTreeMap::new();
    let key: u32 = kani::any();
    let val: u32 = kani::any();

    map.insert(key, val);
    let result = map.get(&key).copied().unwrap_or(0);

    assert_eq!(result, val);
}

/// Direct insert isolation — two different keys don't interfere.
#[kani::proof]
fn btreemap_insert_isolation() {
    let mut map: BTreeMap<u32, u32> = BTreeMap::new();
    let k1: u32 = kani::any();
    let k2: u32 = kani::any();
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();

    kani::assume(k1 != k2);

    map.insert(k1, v1);
    map.insert(k2, v2);

    assert_eq!(map.get(&k1).copied().unwrap_or(0), v1);
    assert_eq!(map.get(&k2).copied().unwrap_or(0), v2);
}

/// Default value: get on empty map returns None, unwrap_or returns default.
#[kani::proof]
fn btreemap_default_value() {
    let map: BTreeMap<u32, u32> = BTreeMap::new();
    let key: u32 = kani::any();
    let default: u32 = kani::any();

    let result = map.get(&key).copied().unwrap_or(default);
    assert_eq!(result, default);
}

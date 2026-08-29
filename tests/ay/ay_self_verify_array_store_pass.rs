// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: array_read_over_write_hit=PROOF
// kani-expect: array_read_over_write_miss=PROOF
// kani-expect: array_store_overwrites=PROOF

//! AY self-verification: array store/select harnesses that now achieve PROOF.
//!
//! These harnesses were split from `ay_self_verify_array_store.rs`
//! (`kani-expect: UNKNOWN`) because Part of #3348 recovered precise
//! BTreeMap-backed `select()` semantics across struct methods:
//! - `array_default_value`: PROOF
//! - `array_read_over_write_hit`: PROOF
//! - `array_read_over_write_miss`: PROOF
//! - `array_store_isolation`: PROOF
//! - `array_store_overwrites`: PROOF
//!
//! The remaining commutativity harness stays in `ay_self_verify_array_store.rs`.

use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Array {
    /// Explicit stores: index -> value
    stores: BTreeMap<u32, u32>,
    /// Default value for indices not in stores
    default: u32,
}

impl Array {
    fn new(default: u32) -> Self {
        Self { stores: BTreeMap::new(), default }
    }

    /// store(a, idx, val): returns new array with a[idx] = val
    fn store(&self, idx: u32, val: u32) -> Self {
        let mut result = self.clone();
        result.stores.insert(idx, val);
        result
    }

    /// select(a, idx): returns a[idx]
    fn select(&self, idx: u32) -> u32 {
        self.stores.get(&idx).copied().unwrap_or(self.default)
    }
}

/// Read-over-write-hit: select(store(a, i, v), i) == v
///
/// This is the axiom that ay#6087 violated by inverting the store mapping.
#[kani::proof]
fn array_read_over_write_hit() {
    let default: u32 = kani::any();
    let idx: u32 = kani::any();
    kani::assume(idx < 100);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a_stored = a.store(idx, val);

    assert_eq!(a_stored.select(idx), val, "select(store(a, i, v), i) must equal v");
}

/// Read-over-write-miss: select(store(a, i, v), j) == select(a, j) when i != j
#[kani::proof]
fn array_read_over_write_miss() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i < 100 && j < 100);
    kani::assume(i != j);
    let val: u32 = kani::any();

    let a = Array::new(default);
    let a_stored = a.store(i, val);

    assert_eq!(
        a_stored.select(j),
        a.select(j),
        "select(store(a, i, v), j) must equal select(a, j) when i != j"
    );
}

/// Store overwrites: consecutive stores to same index keep last value
#[kani::proof]
fn array_store_overwrites() {
    let default: u32 = kani::any();
    let idx: u32 = kani::any();
    kani::assume(idx < 100);
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();

    let a = Array::new(default);
    let a1 = a.store(idx, v1);
    let a2 = a1.store(idx, v2);

    assert_eq!(
        a2.select(idx),
        v2,
        "Last store wins: store(store(a, i, v1), i, v2) at i must be v2"
    );
}

/// Default value: unwritten indices return default
#[kani::proof]
fn array_default_value() {
    let default: u32 = kani::any();
    let idx: u32 = kani::any();
    kani::assume(idx < 100);

    let a = Array::new(default);
    assert_eq!(a.select(idx), default, "Unwritten index must return default");
}

/// Store isolation: storing at one index doesn't affect others
#[kani::proof]
fn array_store_isolation() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    let k: u32 = kani::any();
    kani::assume(i < 50 && j < 50 && k < 50);
    kani::assume(i != j && i != k && j != k);
    let vi: u32 = kani::any();
    let vj: u32 = kani::any();

    let a = Array::new(default);
    let a2 = a.store(i, vi).store(j, vj);

    // k is different from both i and j, so it should still be default
    assert_eq!(a2.select(k), default);
    // i should have vi
    assert_eq!(a2.select(i), vi);
    // j should have vj
    assert_eq!(a2.select(j), vj);
}

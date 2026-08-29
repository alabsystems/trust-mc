// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! AY self-verification: array store/select semantics
//!
//! Remaining unresolved array-store harness.
//!
//! The provable harnesses from this family moved to
//! `ay_self_verify_array_store_pass.rs` after the Part of #3348 BTreeMap
//! accessor dispatch recovered precise `get().copied().unwrap_or()` semantics.
//! The remaining commutativity case is still `UNKNOWN`.
//!
//! These harnesses verify the fundamental axioms of the theory of arrays,
//! which AY implements in ay-theories/arrays/. The inverted store semantics
//! bug (ay#6087) showed that scalarize_store_equality mapped idx==k to
//! base_k instead of val — exactly the kind of bug these proofs catch.
//!
//! Array theory axioms (McCarthy):
//!   select(store(a, i, v), i) == v           (read-over-write-hit)
//!   i != j => select(store(a, i, v), j) == select(a, j)  (read-over-write-miss)
//!   extensionality: (forall i. select(a,i) == select(b,i)) => a == b

/// Minimal array model: BTreeMap-backed for Kani compatibility
/// (avoids HashMap which AY's kani_compat maps to BTreeMap anyway)
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

/// Store commutativity for different indices
///
/// This remains UNKNOWN after the Part of #3348 BTreeMap accessor recovery.
#[kani::proof]
fn array_store_commutative_different_indices() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();
    kani::assume(i < 50 && j < 50);
    kani::assume(i != j);
    let vi: u32 = kani::any();
    let vj: u32 = kani::any();

    let a = Array::new(default);

    // Order 1: store i then j
    let a_ij = a.store(i, vi).store(j, vj);
    // Order 2: store j then i
    let a_ji = a.store(j, vj).store(i, vi);

    // Both orders should produce same reads at i and j
    assert_eq!(a_ij.select(i), a_ji.select(i));
    assert_eq!(a_ij.select(j), a_ji.select(j));
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: dual_select_different_structs=PROOF
// kani-expect: dual_select_same_struct=PROOF

//! Isolation test: two select calls on different structs in same harness.
//!
//! Part of #3348: isolating dual-select encoding gap.

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
struct Array {
    stores: BTreeMap<u32, u32>,
    default: u32,
}

impl Array {
    fn new(default: u32) -> Self {
        Self { stores: BTreeMap::new(), default }
    }

    fn select(&self, idx: u32) -> u32 {
        self.stores.get(&idx).copied().unwrap_or(self.default)
    }
}

/// Two selects on the SAME struct, no store involved.
#[kani::proof]
fn dual_select_same_struct() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();
    let j: u32 = kani::any();

    let a = Array::new(default);
    let r1 = a.select(i);
    let r2 = a.select(j);
    assert_eq!(r1, default);
    assert_eq!(r2, default);
}

/// Two selects on two DIFFERENT structs (both fresh, no store).
#[kani::proof]
fn dual_select_different_structs() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();

    let a = Array::new(default);
    let b = Array::new(default);  // same default
    assert_eq!(a.select(i), b.select(i));
}

/// Two selects: one on original, one on clone (no store).
#[kani::proof]
fn dual_select_clone_no_store() {
    let default: u32 = kani::any();
    let i: u32 = kani::any();

    let a = Array::new(default);
    let b = a.clone();
    assert_eq!(a.select(i), b.select(i));
}

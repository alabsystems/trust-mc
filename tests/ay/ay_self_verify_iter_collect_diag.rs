// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! Diagnostic harness: IterCollect chain isolation for #3348.
//!
//! Tests whether the iter().map().collect() chain correctly propagates length
//! through IterCollect. Uses vec![val; n] (VecFromElem) to avoid loop
//! complexity in Vec construction.
//!
//! Element-value constraints use sound over-approximation (symbolic data)
//! because Spacer cannot handle forall quantifiers in CHC rules.
//! Length constraints are precise.

/// Test 1: iter().map(|&b| !b).collect() preserves length
#[kani::proof]
fn iter_map_collect_preserves_len() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 8);

    let v: Vec<bool> = vec![true; n];
    let result: Vec<bool> = v.iter().map(|&b| !b).collect();

    assert_eq!(result.len(), n);
}

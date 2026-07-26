// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// compile-flags: --edition 2018

// This test checks that TrustMcMap types require -Z symbolic-collections.

use kani::hashmap::{TrustMcMap, TrustMcMapIntoIter};

#[kani::proof]
fn test_missing_symbolic_collections() {
    let map: TrustMcMap<u32, u32> = Default::default();
    let _iter: Option<TrustMcMapIntoIter<u32, u32>> = None;
    let _clone = map.clone();
}

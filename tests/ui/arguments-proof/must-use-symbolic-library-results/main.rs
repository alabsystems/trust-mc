// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// compile-flags: --edition 2018
// kani-flags: -Zghost-state --unstable=symbolic-collections

#![deny(unused_must_use)]

use kani::hashmap::TrustMcMap;
use kani::shadow::ShadowMem;
use kani::vec::{any_vec, exact_vec};

#[kani::proof]
fn main() {
    any_vec::<u8, 4>();
    exact_vec::<u8, 2>();

    TrustMcMap::<u8, u8>::new();
    let map: TrustMcMap<u8, u8> = TrustMcMap::new();
    map.get(&0_u8);
    map.contains_key(&0_u8);
    map.is_empty();
    map.len();

    ShadowMem::new(false);
    let sm = ShadowMem::new(false);
    sm.get(core::ptr::null::<u8>());
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#[repr(C)]
struct Pair {
    first: u64,
    second: u64,
}

#[inline(never)]
fn second_address(pair: &Pair) -> *const u64 {
    &raw const pair.second
}

#[kani::proof]
fn correct_address_safe() {
    let pair = Pair { first: 3, second: 7 };
    assert!(second_address(&pair) == &raw const pair.second);
}

#[kani::proof]
fn wrong_address_bug() {
    let pair = Pair { first: 3, second: 7 };
    assert!(second_address(&pair) == &raw const pair.first);
}

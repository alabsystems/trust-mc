// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#[repr(C)]
struct Pair {
    first: u64,
    second: [u64; 2],
}

#[inline(never)]
fn other_address(pair: &Pair) -> *const u64 {
    &raw const pair.second[1]
}

#[kani::proof]
fn correct_indexed_address_safe() {
    let pair = Pair { first: 3, second: [5, 7] };
    assert!(other_address(&pair) == &raw const pair.second[1]);
}

#[kani::proof]
fn wrong_indexed_address_bug() {
    let pair = Pair { first: 3, second: [5, 7] };
    assert!(other_address(&pair) == &raw const pair.first);
}

#[inline(never)]
fn address_at(pair: &Pair, index: usize) -> *const u64 {
    &raw const pair.second[index]
}

#[kani::proof]
fn different_indices_safe() {
    let pair = Pair { first: 3, second: [5, 7] };
    assert!(address_at(&pair, 0) != address_at(&pair, 1));
}

#[kani::proof]
fn different_indices_bug() {
    let pair = Pair { first: 3, second: [5, 7] };
    assert!(address_at(&pair, 0) == address_at(&pair, 1));
}

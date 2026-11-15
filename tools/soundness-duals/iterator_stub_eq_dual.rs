// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Iterator equality must execute transitive unit stubs of element comparison.

fn never_eq(_: &u8, _: &u8) -> bool {
    false
}
fn always_eq(_: &u8, _: &u8) -> bool {
    true
}

#[kani::proof]
#[kani::stub(u8::eq, never_eq)]
fn stubbed_element_equality_rejects_identical_values_bug() {
    let a = [1u8];
    let b = [1u8];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
#[kani::stub(u8::eq, always_eq)]
fn stubbed_element_equality_accepts_different_values_safe() {
    let a = [1u8];
    let b = [2u8];
    assert!(a.iter().eq(b.iter()));
}

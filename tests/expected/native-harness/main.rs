// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The native harness surface (two-language design E7/R2): `#[kani::harness]`
//! with parameters as the nondeterministic inputs and the bare vocabulary
//! (`any`, `assume`) in scope with zero imports. Must produce verdicts
//! identical to the equivalent `#[kani::proof]` + `kani::any()` spelling —
//! both harnesses below encode the same property and must both succeed.

fn scale(n: u32, k: u32) -> u32 {
    n.saturating_mul(k)
}

#[kani::harness]
fn check_scale_native(n: u32, k: u32) {
    assume(n <= 100);
    assume(k <= 100);
    assert!(scale(n, k) <= 10_000);
}

#[kani::proof]
fn check_scale_legacy() {
    let n: u32 = kani::any();
    let k: u32 = kani::any();
    kani::assume(n <= 100);
    kani::assume(k <= 100);
    assert!(scale(n, k) <= 10_000);
}

// A native harness with a compound nondet input and a bare `any()` call in
// the body — both lanes of the vocabulary.
#[kani::harness]
fn check_array_sum_native(xs: [u8; 4]) {
    let extra: u8 = any();
    assume(extra <= 1);
    let sum: u32 = xs.iter().map(|&b| b as u32).sum::<u32>() + extra as u32;
    assert!(sum <= 4 * 255 + 1);
}

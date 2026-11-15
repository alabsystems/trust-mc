// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// A float `Iterator::sum` whose value nothing reads, beside a check elsewhere
// (AY alignment round 8, review round 5, findings 2 and 4).
//
// Since review round 2 the BMC lane sums floats exactly, with an `fp.add`
// chain. Over operands that do not fold on the host (symbolic elements, a
// `map` or a `filter` of a local array) ay `d80d17a90` answers `unknown` for
// every query that carries such a chain beside the iterator's datatypes, so a
// harness whose real bug lies elsewhere came out INCONCLUSIVE, where main
// reported that bug FAILED Genuine. The only symbolic float sum in the other
// sum-stub duals reads its own value, so the gate could not see it. A float
// sum nothing reads now gets a fresh value (exact: nothing observes it) unless
// `--nan-check` asks for the NaN checks of its adds.
//
// Kani checks NaN generation by default (`--nan-check` whenever overflow
// checks are on, kani-driver call_cbmc.rs), so a symbolic float sum fails on
// "NaN on addition" unless its elements are finite. trust-mc does not, by
// default (`--nan-check` is opt-in): `f32_sym_sum_nan_only_bug` is the
// known-red record of that difference (finding 5), and
// `iter_sum_nan_check_dual.rs` checks the sum's NaN obligations under the flag.
//
// Oracles (Kani 0.67.0, measured 2026-10-15):
//   every `*_bug`   MUST FAIL
//   every `*_safe`  MUST be SUCCESSFUL

#[kani::proof]
fn f32_sym_sum_unread_beside_bug() {
    let a: [f32; 2] = [kani::any(), kani::any()];
    let _s: f32 = a.iter().sum();
    let x: u8 = kani::any();
    assert!(x != 7, "unrelated check");
}

#[kani::proof]
fn f64_sym_sum_unread_beside_bug() {
    let a: [f64; 3] = [kani::any(), kani::any(), kani::any()];
    let _s: f64 = a.iter().sum();
    let x: u8 = kani::any();
    assert!(x != 7, "unrelated check");
}

#[kani::proof]
fn f32_map_sum_unread_beside_bug() {
    let a = [1u8, 2, 3];
    let _s: f32 = a.iter().map(|x| *x as f32).sum();
    let x: u8 = kani::any();
    assert!(x != 7, "unrelated check");
}

#[kani::proof]
fn f32_filter_sum_unread_beside_bug() {
    let a = [1.0f32, 2.0, 3.0];
    let _s: f32 = a.iter().filter(|v| **v > 1.5).sum();
    let x: u8 = kani::any();
    assert!(x != 7, "unrelated check");
}

#[kani::proof]
fn f32_sym_sum_unread_finite_safe() {
    let a: [f32; 2] = [kani::any(), kani::any()];
    kani::assume(a[0].is_finite() && a[1].is_finite());
    let _s: f32 = a.iter().sum();
    let x: u8 = kani::any();
    kani::assume(x < 5);
    assert!(x != 7, "unrelated check");
}

#[kani::proof]
fn f32_map_sum_unread_safe() {
    let a = [1u8, 2, 3];
    let _s: f32 = a.iter().map(|x| *x as f32).sum();
    let x: u8 = kani::any();
    kani::assume(x < 5);
    assert!(x != 7, "unrelated check");
}

// Kani FAILED only on "NaN on addition" (two symbolic f32s may be +inf and
// -inf); trust-mc checks NaN generation only under `--nan-check`.
#[kani::proof]
fn f32_sym_sum_nan_only_bug() {
    let a: [f32; 2] = [kani::any(), kani::any()];
    let _s: f32 = a.iter().sum();
    let x: u8 = kani::any();
    kani::assume(x < 5);
    assert!(x != 7, "unrelated check");
}

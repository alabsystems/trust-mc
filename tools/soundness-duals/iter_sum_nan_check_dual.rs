// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Kani's "NaN on addition" inside a float `Iterator::sum`, under `--nan-check`
// (AY alignment round 8, review round 5, finding 5).
//
// std's float `Sum` is `fold(-0.0, |a, b| a + b)`, and Kani checks that `+`
// (`<f32 as Sum>::sum::{closure#0}.NaN.1`). Both lanes stub the sum, and the
// stub's adds carried no NaN obligation even under `--nan-check`: the CHC lane
// proved `[f32::INFINITY, f32::NEG_INFINITY].iter().sum()`. The BMC lane now
// checks each kept step's NaN generation exactly (both operands infinite with
// opposite signs); the CHC lane, which has no FP theory to compute the partial
// sums, adds a conservative rule for any float sum it reaches with an item.
//
// Oracles (Kani 0.67.0 with its default checks, measured 2026-10-15):
//   every `*_bug`   MUST FAIL ("NaN on addition")
//   every `*_safe`  MUST be SUCCESSFUL

#[kani::proof]
fn sum_inf_neg_inf_nan_bug() {
    let s: f32 = [f32::INFINITY, f32::NEG_INFINITY].iter().sum();
    let _ = s;
}

#[kani::proof]
fn sum_inf_then_neg_inf_nan_bug() {
    let s: f64 = [1.0f64, f64::INFINITY, 2.0, f64::NEG_INFINITY].iter().sum();
    let _ = s;
}

#[kani::proof]
fn sum_constants_safe() {
    let s: f32 = [1.5f32, 2.25].iter().sum();
    assert!(s == 3.75);
}

#[kani::proof]
fn sum_inf_same_sign_safe() {
    let s: f32 = [f32::INFINITY, f32::INFINITY].iter().sum();
    assert!(s.is_infinite());
}

#[kani::proof]
fn sum_symbolic_nan_bug() {
    let a: [f32; 2] = [kani::any(), kani::any()];
    let s: f32 = a.iter().sum();
    let _ = s;
}

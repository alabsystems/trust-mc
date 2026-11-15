// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Two `Iterator::sum` calls writing ONE MIR place (AY alignment round 8,
// review round 3, findings 1 and 5), CHC lane. rustc writes the result of an
// `if`/`match` whose arms each end in `.sum()` into one local. The stub looked
// a sum up by its destination place, saw two different `Iterator::sum`
// instances there and refused both as `Unknown`: a havocked value, and (once
// an unmodelled impl got its conservative panic rule) no proof. It now reads
// each call's own callee operand. The arms use iterator shapes the CHC replay
// encodes exactly (a range, a slice iterator, `Vec::into_iter`).
//
// Before the fix: `two_calls_range_slice_safe` FAILED Unknown (main SUCCESSFUL)
// and `two_calls_slice_vec_into_iter_overflow_bug` SUCCESSFUL (a missed bug on
// main and on the branch alike: the overflow of the slice arm was dropped).
//
// Oracles (Kani 0.67.0, measured 2026-10-14):
//   every `*_bug`   MUST FAIL
//   every `*_safe`  MUST be SUCCESSFUL
fn hold() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    assert!(x < 20);
}

#[kani::proof]
fn two_calls_range_slice_safe() {
    let c: bool = kani::any();
    let s: u8 = if c { (0u8..3).sum() } else { [1u8, 2].iter().sum() };
    assert!(s == 3);
}

#[kani::proof]
fn two_calls_range_slice_overflow_bug() {
    let c: bool = kani::any();
    let s: u8 = if c { (0u8..3).sum() } else { [200u8, 100].iter().sum() };
    hold();
    let _ = s;
}

#[kani::proof]
fn two_calls_slice_vec_into_iter_overflow_bug() {
    let c: bool = kani::any();
    let v = vec![1u8, 2];
    let s: u8 = if c { v.into_iter().sum() } else { [200u8, 100].iter().sum() };
    hold();
    let _ = s;
}

#[kani::proof]
fn two_calls_range_slice_value_bug() {
    let c: bool = kani::any();
    let s: u8 = if c { (0u8..3).sum() } else { [10u8, 20].iter().sum() };
    assert!(s == 3);
}

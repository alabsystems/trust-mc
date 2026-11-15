// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Two `Iterator::sum` calls writing ONE MIR place (AY alignment round 8,
// review round 3, findings 1 and 5), BMC lane. rustc writes the result of an
// `if`/`match` whose arms each end in `.sum()` into one local. The stub looked
// a sum up by its destination place, saw two different `Iterator::sum`
// instances there and refused both as `Unknown`, which the BMC lane havocs
// through its demoting fallback: FAILED EncodingGap on programs main and Kani
// prove. It now reads each call's own callee operand. The arms use iterator
// shapes the BMC unroll encodes exactly (a slice iterator, `copied`, `map`).
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
fn two_calls_copied_safe() {
    let c: bool = kani::any();
    let s: u8 = if c { [100u8, 100].iter().sum() } else { [1u8, 2].iter().copied().sum() };
    assert!(s >= 3);
}

#[kani::proof]
fn two_calls_map_safe() {
    let c: bool = kani::any();
    let s: u8 = if c { [100u8, 100].iter().sum() } else { [1u8, 2].iter().map(|x| *x).sum() };
    assert!(s >= 3);
}

#[kani::proof]
fn match_arms_safe() {
    let k: u8 = kani::any();
    let a = [10u8, 20];
    let s: u8 = match k % 2 {
        0 => a.iter().sum(),
        _ => a.iter().copied().sum(),
    };
    assert!(s == 30);
}

#[kani::proof]
fn two_calls_copied_overflow_bug() {
    let c: bool = kani::any();
    let s: u8 = if c { [200u8, 100].iter().sum() } else { [1u8, 2].iter().copied().sum() };
    hold();
    let _ = s;
}

#[kani::proof]
fn two_calls_map_value_bug() {
    let c: bool = kani::any();
    let s: u8 = if c { [10u8, 20].iter().sum() } else { [1u8, 2].iter().map(|x| *x).sum() };
    assert!(s == 3);
}

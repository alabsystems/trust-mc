// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
//
//! Regression for bool-return denominator guards flowing through helper calls.

#[inline(never)]
fn denominator_is_valid_i32(x: i32) -> bool {
    x != 0
}

#[inline(never)]
fn guarded_div_i32(numer: i32, denom: i32) -> i32 {
    if denominator_is_valid_i32(denom) && !(numer == i32::MIN && denom == -1) {
        numer / denom
    } else {
        0
    }
}

#[kani::proof]
fn interprocedural_denominator_guard_i32() {
    let numer: i32 = kani::any();
    let denom: i32 = kani::any();
    let _ = guarded_div_i32(numer, denom);
}

#[inline(never)]
fn denominator_is_valid_u32(x: u32) -> bool {
    x != 0
}

#[inline(never)]
fn guarded_rem_u32(numer: u32, denom: u32) -> u32 {
    if denominator_is_valid_u32(denom) {
        numer % denom
    } else {
        0
    }
}

#[kani::proof]
fn interprocedural_denominator_guard_u32() {
    let numer: u32 = kani::any();
    let denom: u32 = kani::any();
    let _ = guarded_rem_u32(numer, denom);
}

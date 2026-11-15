// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: -Z loop-contracts
//
// The loop-contract retry must not overturn a vacuity verdict (AY alignment
// review round 2, finding 1).
//
// V4 fails a harness closed when every check it emitted is unreachable, because
// that is also what a mis-encoded guard leaves. The guard here (`s` is
// infinite) was mis-encoded until the same round: the float sum stub added the
// IEEE bit patterns as integers, so in the BMC lane every check of
// `v4_retry_f32_bug` was unreachable and V4 failed it closed. The retry then ran
// on that non-success, its CHC child proved the same mis-encoded program, and
// the merge printed `VERIFICATION:- SUCCESSFUL` where Kani fails. The retry no
// longer starts after a vacuity gate (`loop_two_lane::FailClosedGate`), and the
// sum is exact, so both harnesses fail in both lanes.
//
// Oracles (Kani 0.67.0, measured 2026-10-02):
//   v4_retry_f32_bug   MUST FAIL ("sum overflowed to infinity"; the loop is never
//                     entered and the invariant's checks pass)
//   v4_noloop_f32_bug  MUST FAIL (the same, without the loop contract: V4 alone)
#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

#[kani::proof]
fn v4_retry_f32_bug() {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    let mut x: u8 = 7;
    #[kani::loop_invariant(x != 7)]
    while x > 7 {
        x = 6;
    }
    if s.is_infinite() {
        panic!("sum overflowed to infinity");
    }
}

#[kani::proof]
fn v4_noloop_f32_bug() {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    if s.is_infinite() {
        panic!("sum overflowed to infinity");
    }
}

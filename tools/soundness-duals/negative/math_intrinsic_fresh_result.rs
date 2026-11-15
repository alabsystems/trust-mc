// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Negative pack: a math intrinsic the BMC lane cannot encode exactly returns a
// fresh float. A proof over that value is sound; a counterexample that reads it
// is not evidence of a bug and must never be certified Genuine.
//
// Found by the soundness-fixes-1 corpus sample: once `u16 as f32` stopped
// reinterpreting bits, kani/Intrinsics/Math/Arith/powf32.rs went from VACUOUS
// (its assumption `x < u16::MAX.into()` read 0x0000FFFF as a subnormal) to a
// Genuine-certified FAILED on a safe program.
//
// Oracle (per harness):
//   powf_square_nonnegative_safe    NOT_GENUINE  x*x >= 0 for x in (1, 65535); SUCCESSFUL,
//                                                or FAILED only without a Genuine certificate
//   powf_square_negative_must_fail  FAILED       x.powf(2.0) < 0.0 is false for every such x

#[kani::proof]
fn powf_square_nonnegative_safe() {
    let x: f32 = kani::any();
    kani::assume(x.is_normal());
    kani::assume(x > 1.0 && x < u16::MAX.into());
    let x2 = x.powf(2.0);
    assert!(x2 >= 0.0);
}

#[kani::proof]
fn powf_square_negative_must_fail() {
    let x: f32 = kani::any();
    kani::assume(x.is_normal());
    kani::assume(x > 1.0 && x < u16::MAX.into());
    let x2 = x.powf(2.0);
    assert!(x2 < 0.0);
}

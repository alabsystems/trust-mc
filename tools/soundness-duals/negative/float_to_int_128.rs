// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z float-lib
//
// NEGATIVE PACK: `kani::float::float_to_int_in_range` at 128-bit widths with
// infinities, NaN, the `i128` / `u128` boundaries, and symbolic operands.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-12) around
// ddcb42b9c (exact predicate in both lanes; saturation at int_width + 2 = 130
// bits, bounds built from BigInt). Truncation semantics: NaN and +/-inf are
// never in range; `i128::MIN as f64` (-2^127) is in range, `i128::MAX as f64`
// (2^127) and `u128::MAX as f64` (2^128) are not; `f32::MAX` (2^128 - 2^104)
// fits u128 but not i128.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample


#[kani::proof]
fn f64_inf_i128_not_in_range_safe() {
    let f: f64 = f64::INFINITY;
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_inf_i128_claim_must_fail() {
    let f: f64 = f64::INFINITY;
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_inf_i128_not_in_range_safe() {
    let f: f64 = f64::NEG_INFINITY;
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_inf_u128_claim_must_fail() {
    let f: f64 = f64::NEG_INFINITY;
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_nan_u128_not_in_range_safe() {
    let f: f64 = f64::NAN;
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_nan_i128_claim_must_fail() {
    let f: f64 = f64::NAN;
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f32_inf_u128_not_in_range_safe() {
    let f: f32 = f32::INFINITY;
    assert!(!kani::float::float_to_int_in_range::<f32, u128>(f));
}

#[kani::proof]
fn f32_nan_i128_claim_must_fail() {
    let f: f32 = f32::NAN;
    assert!(kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f64_1e38_i128_in_range_safe() {
    let f: f64 = 1e38;
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_1e38_i128_not_claim_must_fail() {
    let f: f64 = 1e38;
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_2e38_i128_not_in_range_safe() {
    let f: f64 = 2e38;
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_2e38_i128_claim_must_fail() {
    let f: f64 = 2e38;
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_1e38_i128_in_range_safe() {
    let f: f64 = -1e38;
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_2e38_i128_not_in_range_safe() {
    let f: f64 = -2e38;
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_3e38_u128_in_range_safe() {
    let f: f64 = 3e38;
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_3e38_u128_not_claim_must_fail() {
    let f: f64 = 3e38;
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_4e38_u128_not_in_range_safe() {
    let f: f64 = 4e38;
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_neg_one_u128_not_in_range_safe() {
    let f: f64 = -1.0;
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_neg_half_u128_in_range_safe() {
    // Truncation of -0.5 is 0, which u128 holds.
    let f: f64 = -0.5;
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_i128_min_in_range_safe() {
    let f: f64 = i128::MIN as f64;
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_i128_max_not_in_range_safe() {
    // i128::MAX rounds up to 2^127 as f64, which i128 does not hold.
    let f: f64 = i128::MAX as f64;
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_i128_max_claim_must_fail() {
    let f: f64 = i128::MAX as f64;
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_u128_max_not_in_range_safe() {
    // u128::MAX rounds up to 2^128 as f64.
    let f: f64 = u128::MAX as f64;
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_u128_max_claim_must_fail() {
    let f: f64 = u128::MAX as f64;
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f32_max_u128_in_range_safe() {
    let f: f32 = f32::MAX;
    assert!(kani::float::float_to_int_in_range::<f32, u128>(f));
}

#[kani::proof]
fn f32_max_i128_not_in_range_safe() {
    let f: f32 = f32::MAX;
    assert!(!kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f32_max_i128_claim_must_fail() {
    let f: f32 = f32::MAX;
    assert!(kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f64_symbolic_nan_not_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x.is_nan());
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(x));
}

#[kani::proof]
fn f64_symbolic_small_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x.is_finite() && x > -1e30 && x < 1e30);
    assert!(kani::float::float_to_int_in_range::<f64, i128>(x));
}

#[kani::proof]
fn f64_symbolic_finite_claim_must_fail() {
    let x: f64 = kani::any();
    kani::assume(x.is_finite());
    assert!(kani::float::float_to_int_in_range::<f64, i128>(x));
}

#[kani::proof]
fn f64_symbolic_infinite_claim_must_fail() {
    let x: f64 = kani::any();
    kani::assume(x.is_infinite());
    assert!(kani::float::float_to_int_in_range::<f64, u128>(x));
}

#[kani::proof]
fn f64_symbolic_huge_not_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x > 3.5e38);
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(x));
}

#[kani::proof]
fn f64_symbolic_negative_u128_not_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x <= -1.0);
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(x));
}

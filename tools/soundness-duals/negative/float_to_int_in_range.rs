// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z float-lib
//
// NEGATIVE PACK: kani::float::float_to_int_in_range on a non-literal operand.
//
// Audit evidence: kani-surface/lib-float-to-int-in-range and
// kani-surface/z-float-lib. In the BMC lane the intrinsic has only a
// literal-constant fast path; a local operand falls to a fresh unconstrained
// bool with no demotion, so Kani's own tests/kani/FloatToIntInRange/test.rs
// FAILS (certified Genuine) while the CHC lane passes it.
//
// Oracle (per harness):
//   in_range_local_operand_safe       -> VERIFICATION:- SUCCESSFUL
//   out_of_range_claim_must_fail      -> VERIFICATION:- FAILED (assertion)
//   huge_f64_i128_claim_must_fail     -> VERIFICATION:- FAILED (assertion)
//   huge_f64_i128_not_in_range_safe   -> VERIFICATION:- SUCCESSFUL
//
// The two i128 harnesses pin a 128-bit Int: the exact predicate saturates at
// int_width + 2 = 130 bits, and bounds computed in u128 (`1u128 << 129`)
// wrapped in a release build, so 1e300 read as in range and the false claim
// PROVED (review of m3/soundness-fixes-1, 2026-09-12).

#[kani::proof]
fn in_range_local_operand_safe() {
    let f: f32 = 5.6;
    let fits_in_u16 = kani::float::float_to_int_in_range::<f32, u16>(f);
    assert!(fits_in_u16);
    let g: f32 = 145.7;
    let fits_in_i8 = kani::float::float_to_int_in_range::<f32, i8>(g);
    assert!(!fits_in_i8);
}

#[kani::proof]
fn out_of_range_claim_must_fail() {
    let f: f32 = 70000.5;
    let fits_in_u16 = kani::float::float_to_int_in_range::<f32, u16>(f);
    // FALSE: 70000.5 truncates to 70000, which does not fit in u16.
    assert!(fits_in_u16);
}

#[kani::proof]
fn huge_f64_i128_claim_must_fail() {
    let f: f64 = 1e300;
    // FALSE: 1e300 is far outside i128.
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn huge_f64_i128_not_in_range_safe() {
    let f: f64 = 1e300;
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

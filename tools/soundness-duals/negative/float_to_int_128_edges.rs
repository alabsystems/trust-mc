// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z float-lib
//
// NEGATIVE PACK: `kani::float::float_to_int_in_range` at the exact 128-bit
// boundaries, by bit pattern: the largest f64 / f32 below 2^127 and 2^128, the
// powers themselves, -2^127 and the next float below it, the negative floats whose
// truncation is 0, a subnormal, -0.0, and symbolic operands bounded at 2^127.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-13) around
// ddcb42b9c (the exact predicate; saturation at int_width + 2 bits). Truncation
// semantics: `x` is in range of `I` iff `x` is finite and `trunc(x)` lies in
// [I::MIN, I::MAX]; so every float in (-1, 1) is in range of u128.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample


// 0x47EFFFFFFFFFFFFF = (2 - 2^-52) * 2^127 = 2^128 - 2^75: the largest f64 below 2^128.
const F64_BELOW_2P128: u64 = 0x47EF_FFFF_FFFF_FFFF;
// 0x47F0000000000000 = 2^128.
const F64_2P128: u64 = 0x47F0_0000_0000_0000;
// 0x47DFFFFFFFFFFFFF = 2^127 - 2^74: the largest f64 below 2^127.
const F64_BELOW_2P127: u64 = 0x47DF_FFFF_FFFF_FFFF;
// 0x47E0000000000000 = 2^127.
const F64_2P127: u64 = 0x47E0_0000_0000_0000;
// 0xC7E0000000000000 = -2^127 = i128::MIN.
const F64_NEG_2P127: u64 = 0xC7E0_0000_0000_0000;
// 0xC7E0000000000001 = -(2^127 + 2^75): the first f64 below i128::MIN.
const F64_BELOW_NEG_2P127: u64 = 0xC7E0_0000_0000_0001;
// 0xBFEFFFFFFFFFFFFF = -(1 - 2^-53): truncates to 0.
const F64_NEG_JUST_ABOVE_MINUS_ONE: u64 = 0xBFEF_FFFF_FFFF_FFFF;
// 0x7EFFFFFF = 2^127 - 2^103: the largest f32 below 2^127.
const F32_BELOW_2P127: u32 = 0x7EFF_FFFF;
// 0x7F000000 = 2^127.
const F32_2P127: u32 = 0x7F00_0000;
// 0xFF000000 = -2^127.
const F32_NEG_2P127: u32 = 0xFF00_0000;
// 0xFF000001 = -(2^127 + 2^104): the first f32 below i128::MIN.
const F32_BELOW_NEG_2P127: u32 = 0xFF00_0001;

#[kani::proof]
fn f64_below_2p128_u128_in_range_safe() {
    let f = f64::from_bits(F64_BELOW_2P128);
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_below_2p128_u128_not_claim_must_fail() {
    let f = f64::from_bits(F64_BELOW_2P128);
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_2p128_u128_not_in_range_safe() {
    let f = f64::from_bits(F64_2P128);
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_2p128_u128_claim_must_fail() {
    let f = f64::from_bits(F64_2P128);
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_below_2p127_i128_in_range_safe() {
    let f = f64::from_bits(F64_BELOW_2P127);
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f) && kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_below_2p127_i128_not_claim_must_fail() {
    let f = f64::from_bits(F64_BELOW_2P127);
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_2p127_i128_not_in_range_safe() {
    let f = f64::from_bits(F64_2P127);
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f) && kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_2p127_i128_claim_must_fail() {
    let f = f64::from_bits(F64_2P127);
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_2p127_i128_in_range_safe() {
    let f = f64::from_bits(F64_NEG_2P127);
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f) && !kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_neg_2p127_i128_not_claim_must_fail() {
    let f = f64::from_bits(F64_NEG_2P127);
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_below_neg_2p127_i128_not_in_range_safe() {
    let f = f64::from_bits(F64_BELOW_NEG_2P127);
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_below_neg_2p127_i128_claim_must_fail() {
    let f = f64::from_bits(F64_BELOW_NEG_2P127);
    assert!(kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_just_above_minus_one_u128_in_range_safe() {
    let f = f64::from_bits(F64_NEG_JUST_ABOVE_MINUS_ONE);
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f) && kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_just_above_minus_one_u128_not_claim_must_fail() {
    let f = f64::from_bits(F64_NEG_JUST_ABOVE_MINUS_ONE);
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_minus_one_u128_not_in_range_safe() {
    let f: f64 = -1.0;
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f) && kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_minus_one_u128_claim_must_fail() {
    let f: f64 = -1.0;
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_subnormal_in_range_safe() {
    let f = f64::from_bits(1);
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f) && kani::float::float_to_int_in_range::<f64, i128>(f));
}

#[kani::proof]
fn f64_neg_zero_u128_in_range_safe() {
    let f: f64 = -0.0;
    assert!(kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f64_neg_zero_u128_not_claim_must_fail() {
    let f: f64 = -0.0;
    assert!(!kani::float::float_to_int_in_range::<f64, u128>(f));
}

#[kani::proof]
fn f32_below_2p127_i128_in_range_safe() {
    let f = f32::from_bits(F32_BELOW_2P127);
    assert!(kani::float::float_to_int_in_range::<f32, i128>(f) && kani::float::float_to_int_in_range::<f32, u128>(f));
}

#[kani::proof]
fn f32_below_2p127_i128_not_claim_must_fail() {
    let f = f32::from_bits(F32_BELOW_2P127);
    assert!(!kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f32_2p127_i128_not_in_range_safe() {
    let f = f32::from_bits(F32_2P127);
    assert!(!kani::float::float_to_int_in_range::<f32, i128>(f) && kani::float::float_to_int_in_range::<f32, u128>(f));
}

#[kani::proof]
fn f32_2p127_i128_claim_must_fail() {
    let f = f32::from_bits(F32_2P127);
    assert!(kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f32_neg_2p127_i128_in_range_safe() {
    let f = f32::from_bits(F32_NEG_2P127);
    assert!(kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f32_below_neg_2p127_i128_not_in_range_safe() {
    let f = f32::from_bits(F32_BELOW_NEG_2P127);
    assert!(!kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f32_below_neg_2p127_i128_claim_must_fail() {
    let f = f32::from_bits(F32_BELOW_NEG_2P127);
    assert!(kani::float::float_to_int_in_range::<f32, i128>(f));
}

#[kani::proof]
fn f32_neg_half_u128_in_range_safe() {
    let f: f32 = -0.5;
    assert!(kani::float::float_to_int_in_range::<f32, u128>(f));
}

#[kani::proof]
fn f32_neg_half_u128_not_claim_must_fail() {
    let f: f32 = -0.5;
    assert!(!kani::float::float_to_int_in_range::<f32, u128>(f));
}

#[kani::proof]
fn f64_symbolic_at_or_above_2p127_i128_not_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x >= f64::from_bits(F64_2P127));
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(x));
}

#[kani::proof]
fn f64_symbolic_at_or_above_2p127_i128_claim_must_fail() {
    let x: f64 = kani::any();
    kani::assume(x >= f64::from_bits(F64_2P127));
    assert!(kani::float::float_to_int_in_range::<f64, i128>(x));
}

#[kani::proof]
fn f64_symbolic_inside_i128_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x >= f64::from_bits(F64_NEG_2P127) && x < f64::from_bits(F64_2P127));
    assert!(kani::float::float_to_int_in_range::<f64, i128>(x));
}

#[kani::proof]
fn f64_symbolic_inside_i128_not_claim_must_fail() {
    let x: f64 = kani::any();
    kani::assume(x >= f64::from_bits(F64_NEG_2P127) && x < f64::from_bits(F64_2P127));
    assert!(!kani::float::float_to_int_in_range::<f64, i128>(x));
}

#[kani::proof]
fn f64_symbolic_unit_interval_u128_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x > -1.0 && x < 1.0);
    assert!(kani::float::float_to_int_in_range::<f64, u128>(x));
}

#[kani::proof]
fn f64_symbolic_below_2p128_u128_in_range_safe() {
    let x: f64 = kani::any();
    kani::assume(x > -1.0 && x < f64::from_bits(F64_2P128));
    assert!(kani::float::float_to_int_in_range::<f64, u128>(x));
}

#[kani::proof]
fn f64_symbolic_at_or_above_2p128_u128_claim_must_fail() {
    let x: f64 = kani::any();
    kani::assume(x >= f64::from_bits(F64_2P128));
    assert!(kani::float::float_to_int_in_range::<f64, u128>(x));
}

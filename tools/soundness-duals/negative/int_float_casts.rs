// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: numeric int-to-float and float-to-int casts.
//
// Audit evidence: bmc-codegen/int-float-cast-bit-reinterpret. The BMC lane
// encodes `int as f32` and `float as int` as bitvector width coercion (bit
// reinterpretation) instead of numeric conversion: `x == 3; (x as f32) == 3.0`
// was a certified-Genuine FAILURE. The same encoding is a false-PROOF vector
// in the other direction, which the `_bit_pattern_must_fail` harnesses pin:
// each asserts exactly what bit reinterpretation would compute.
//
// Oracle (per harness):
//   int_to_float_value_safe                   -> VERIFICATION:- SUCCESSFUL
//   int_to_float_bit_pattern_must_fail        -> VERIFICATION:- FAILED (assertion)
//   float_to_int_value_safe                   -> VERIFICATION:- SUCCESSFUL
//   float_to_int_bit_pattern_must_fail        -> VERIFICATION:- FAILED (assertion)
//   float_to_int_saturates_safe               -> VERIFICATION:- SUCCESSFUL
//   float_to_int_truncated_bits_must_fail     -> VERIFICATION:- FAILED (assertion)
//   signed_int_to_float_value_safe            -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn int_to_float_value_safe() {
    let x: u8 = kani::any();
    kani::assume(x == 3);
    assert!((x as f32) == 3.0);
}

#[kani::proof]
fn int_to_float_bit_pattern_must_fail() {
    let x: u32 = kani::any();
    kani::assume(x == 0x4080_0000);
    // FALSE: 0x4080_0000 as f32 == 1082130432.0; 4.0 is its bit pattern read as f32.
    assert!((x as f32) == 4.0);
}

#[kani::proof]
fn float_to_int_value_safe() {
    let f: f32 = kani::any();
    kani::assume(f == 3.0);
    assert!((f as u32) == 3);
}

#[kani::proof]
fn float_to_int_bit_pattern_must_fail() {
    let f: f32 = kani::any();
    kani::assume(f == 3.0);
    // FALSE: 3.0f32 as u32 == 3; 0x4040_0000 is the bit pattern of 3.0f32.
    assert!((f as u32) == 0x4040_0000);
}

#[kani::proof]
fn float_to_int_saturates_safe() {
    let f: f32 = kani::any();
    kani::assume(f == 300.0);
    assert!((f as u8) == 255);
    let g: f32 = kani::any();
    kani::assume(g == -1.0);
    assert!((g as u8) == 0);
}

#[kani::proof]
fn float_to_int_truncated_bits_must_fail() {
    let f: f32 = kani::any();
    kani::assume(f == 300.0);
    // FALSE: `as` saturates to 255; 0 is the low byte of 300.0f32's bits (0x4396_0000).
    assert!((f as u8) == 0);
}

#[kani::proof]
fn signed_int_to_float_value_safe() {
    let x: i16 = kani::any();
    kani::assume(x == -2);
    assert!((x as f64) == -2.0);
}

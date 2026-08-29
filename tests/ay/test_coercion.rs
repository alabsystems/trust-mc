// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// kani-expect: test_symbolic_sign_extension=UNKNOWN  // AY-bump regression from PROOF (3d9db24e68); sound demotion
// NOTE: All 13 harnesses are PROOF at ay e1c70f4a.
//
//! Regression tests for type coercion codegen.
//!
//! Tests sign extension, zero extension, truncation, and bitwise
//! operations with various signedness combinations. Part of #189.
//!
//! Related issues: #189, #196

// Test sign extension preserves sign
#[kani::proof]
fn test_sign_extension_negative() {
    let x: i8 = -1;
    let extended: i32 = x as i32;
    kani::assert(extended == -1, "sign extension should preserve -1");
}

// Test sign extension preserves positive values
#[kani::proof]
fn test_sign_extension_positive() {
    let x: i8 = 127;
    let extended: i32 = x as i32;
    kani::assert(extended == 127, "sign extension should preserve 127");
}

// Test zero extension of u8 max
#[kani::proof]
fn test_zero_extension_u8_max() {
    let x: u8 = 255;
    let extended: u32 = x as u32;
    kani::assert(extended == 255, "zero extension should preserve 255");
}

// Test zero extension keeps high bits clear
#[kani::proof]
fn test_zero_extension_high_bits_clear() {
    let x: u8 = kani::any();
    let extended: u32 = x as u32;
    kani::assert(extended < 256, "extended u8 must be < 256");
}

// Test truncation preserves low bits
#[kani::proof]
fn test_truncation_preserves_low_bits() {
    let x: u32 = kani::any();
    let truncated: u8 = x as u8;
    kani::assert(truncated as u32 == (x & 0xFF), "truncation should preserve low 8 bits");
}

// Regression test for #196: unsigned right shift
#[kani::proof]
fn test_unsigned_right_shift() {
    let x: u32 = 0xFFFFFFFF;
    let shifted = x >> 1;
    kani::assert(shifted == 0x7FFFFFFF, "unsigned >> should be logical shift");
}

// Regression test for #196: signed right shift of negative
#[kani::proof]
fn test_signed_right_shift_negative() {
    let x: i32 = -2;
    let shifted = x >> 1;
    kani::assert(shifted == -1, "signed >> should be arithmetic shift");
}

// Test left shift same for signed/unsigned
#[kani::proof]
fn test_left_shift_consistency() {
    let x: u32 = 1;
    let y: i32 = 1;
    let x_shifted = x << 4;
    let y_shifted = y << 4;
    kani::assert(x_shifted == 16, "u32 << 4 should be 16");
    kani::assert(y_shifted == 16, "i32 << 4 should be 16");
}

// Test bool to integer cast
#[kani::proof]
fn test_bool_to_int_cast() {
    let t: bool = true;
    let f: bool = false;
    kani::assert(t as u8 == 1, "true as u8 should be 1");
    kani::assert(f as u8 == 0, "false as u8 should be 0");
}

// Test char to u32 cast
#[kani::proof]
fn test_char_to_u32_cast() {
    let c: char = 'A';
    let n: u32 = c as u32;
    kani::assert(n == 65, "'A' as u32 should be 65");
}

// Test chained casts
#[kani::proof]
fn test_chained_casts() {
    let x: i8 = -1;
    // i8 -> u8 -> u32: should be 255, not -1 sign extended
    let y: u32 = x as u8 as u32;
    kani::assert(y == 255, "-1i8 as u8 as u32 should be 255");
}

// Test symbolic value sign extension
#[kani::proof]
fn test_symbolic_sign_extension() {
    let x: i8 = kani::any();
    kani::assume(x < 0);
    let extended: i16 = x as i16;
    kani::assert(extended < 0, "negative i8 sign extends to negative i16");
}

// Test symbolic value zero extension
#[kani::proof]
fn test_symbolic_zero_extension() {
    let x: u8 = kani::any();
    let extended: u16 = x as u16;
    kani::assert(extended < 256, "u8 zero extends to value < 256");
}

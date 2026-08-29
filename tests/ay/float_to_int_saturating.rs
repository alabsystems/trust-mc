// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF
// kani-expect: check_f32_truncation=UNKNOWN  // AY-bump regression from PROOF (3d9db24e68); sound demotion

//! Regression tests for float-to-int saturating casts.
//! Part of #3787.

#[kani::proof]
fn check_issue_4536_f32_to_u8() {
    let x: f32 = 300.0;
    let y: u8 = x as u8;
    assert_eq!(y, u8::MAX);
}

#[kani::proof]
fn check_f32_to_u8_above_max() {
    let y: u8 = 300.0f32 as u8;
    assert_eq!(y, u8::MAX);
}

#[kani::proof]
fn check_f32_to_u8_below_min() {
    let y: u8 = (-10.0f32) as u8;
    assert_eq!(y, 0);
}

#[kani::proof]
fn check_f32_to_u8_nan() {
    let y: u8 = f32::NAN as u8;
    assert_eq!(y, 0);
}

#[kani::proof]
fn check_f32_to_u8_infinity() {
    let y: u8 = f32::INFINITY as u8;
    assert_eq!(y, u8::MAX);
}

#[kani::proof]
fn check_f32_to_i8_above_max() {
    let y: i8 = 200.0f32 as i8;
    assert_eq!(y, i8::MAX);
}

#[kani::proof]
fn check_f32_to_i8_below_min() {
    let y: i8 = (-200.0f32) as i8;
    assert_eq!(y, i8::MIN);
}

#[kani::proof]
fn check_f64_to_u8_above_max() {
    let y: u8 = 300.0f64 as u8;
    assert_eq!(y, u8::MAX);
}

#[kani::proof]
fn check_f64_to_i8_below_min() {
    let y: i8 = (-200.0f64) as i8;
    assert_eq!(y, i8::MIN);
}

#[kani::proof]
fn check_f32_truncation() {
    let y: i8 = (-99.9f32) as i8;
    assert_eq!(y, -99);
}

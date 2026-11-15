// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `chars().nth(k)` on non-ASCII text
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 6).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   m1_nth1_is_none_bug        -> VERIFICATION:- FAILED  ('assertion failed: s.chars().nth(1).is_none()')
//!   m2_nth1_is_first_byte_bug  -> VERIFICATION:- FAILED  ('assertion failed: s.chars().nth(1) == Some(\u{c3})')
//!   m2_nth1_is_e_acute_safe    -> VERIFICATION:- SUCCESSFUL
//!   m3_nth2_after_euros_bug    -> VERIFICATION:- FAILED  ('assertion failed: s.chars().nth(2).is_none()')
//!   m3_nth2_after_euros_safe   -> VERIFICATION:- SUCCESSFUL
//!   m4_nth0_multibyte_bug      -> VERIFICATION:- FAILED  ('assertion failed: s.chars().nth(0).is_none()')
//!   m4_nth0_multibyte_safe     -> VERIFICATION:- SUCCESSFUL
//!   m5_nth_value_ne_bug        -> VERIFICATION:- FAILED  ('assertion failed: c != Some(\u{e9})')
//!   m6_nth_past_multibyte_bug  -> VERIFICATION:- FAILED  ('assertion failed: s.chars().nth(4).is_none()')
//!   m6_nth_past_multibyte_safe -> VERIFICATION:- SUCCESSFUL
//!   m7_nth2_u3_safe            -> VERIFICATION:- SUCCESSFUL
//!   a1_ascii_nth_control_bug   -> VERIFICATION:- FAILED  ('assertion failed: s.chars().nth(1) == Some(h)')
//!   a1_ascii_nth_control_safe  -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `SimpleStrIterPass` rewrites `s.chars().nth(k)` to
//! kani_core's `kani_str_chars_nth`, and the CHC encoder modelled that helper
//! as the `k`-th BYTE: `"h\u{e9}llo".chars().nth(1)` was `Some('\u{c3}')`, so
//! value assertions Kani fails proved clean and the true values were
//! certified Genuine failures. Known bytes are now decoded as UTF-8 at
//! codegen time, and the byte model is used only under an ASCII guard over
//! the bytes up to the index, a recorded sound havoc otherwise
//! (`codegen_call_string_nth.rs`).

#[kani::proof]
fn m1_nth1_is_none_bug() {
    let s = "h\u{e9}llo";
    assert!(s.chars().nth(1).is_none());
}

#[kani::proof]
fn m2_nth1_is_first_byte_bug() {
    let s = "h\u{e9}llo";
    assert!(s.chars().nth(1) == Some('\u{c3}'));
}

#[kani::proof]
fn m2_nth1_is_e_acute_safe() {
    let s = "h\u{e9}llo";
    assert!(s.chars().nth(1) == Some('\u{e9}'));
}

#[kani::proof]
fn m3_nth2_after_euros_bug() {
    let s = "\u{20ac}\u{20ac}ab";
    assert!(s.chars().nth(2).is_none());
}

#[kani::proof]
fn m3_nth2_after_euros_safe() {
    let s = "\u{20ac}\u{20ac}ab";
    assert!(s.chars().nth(2) == Some('a'));
}

#[kani::proof]
fn m4_nth0_multibyte_bug() {
    let s = "\u{e9}a";
    assert!(s.chars().nth(0).is_none());
}

#[kani::proof]
fn m4_nth0_multibyte_safe() {
    let s = "\u{e9}a";
    assert!(s.chars().nth(0) == Some('\u{e9}'));
}

#[kani::proof]
fn m5_nth_value_ne_bug() {
    let s = "h\u{e9}llo";
    let c = s.chars().nth(1);
    assert!(c != Some('\u{e9}'));
}

#[kani::proof]
fn m6_nth_past_multibyte_bug() {
    let s = "h\u{e9}llo";
    assert!(s.chars().nth(4).is_none());
}

#[kani::proof]
fn m6_nth_past_multibyte_safe() {
    let s = "h\u{e9}llo";
    assert!(s.chars().nth(4) == Some('o') && s.chars().nth(5).is_none());
}

#[kani::proof]
#[kani::unwind(3)]
fn m7_nth2_u3_safe() {
    let s = "h\u{e9}llo";
    assert!(s.chars().nth(2) == Some('l'));
}

#[kani::proof]
fn a1_ascii_nth_control_bug() {
    let s = "hello";
    assert!(s.chars().nth(1) == Some('h'));
}

#[kani::proof]
fn a1_ascii_nth_control_safe() {
    let s = "hello";
    assert!(s.chars().nth(1) == Some('e'));
}

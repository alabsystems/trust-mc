// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the element count of `Vec::extend`
//! from a `Range` / `RangeInclusive` of signed integers, 128-bit integers and
//! `char`, its capacity-overflow panic, and its loop's unwinding bound
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 1 (a) and (b)).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   s1_signed_i8_range_len_bug        -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 0')
//!   s1_signed_i8_range_len_safe       -> VERIFICATION:- SUCCESSFUL
//!   s2_signed_i64_range_len_bug       -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 0')
//!   s2_signed_i64_range_len_safe      -> VERIFICATION:- SUCCESSFUL
//!   s3_negative_inclusive_len_bug     -> VERIFICATION:- FAILED  ('assertion failed: v.len() != 3')
//!   s3_negative_inclusive_len_safe    -> VERIFICATION:- SUCCESSFUL
//!   s4_isize_inclusive_crossing_bug   -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 0')
//!   s4_isize_inclusive_crossing_safe  -> VERIFICATION:- SUCCESSFUL
//!   s5_reversed_signed_range_bug      -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 253')
//!   s5_reversed_signed_range_safe     -> VERIFICATION:- SUCCESSFUL
//!   s6_signed_range_unwind_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   s6_signed_range_unwind_u6_safe    -> VERIFICATION:- SUCCESSFUL
//!   s7_symbolic_signed_len_u8_bug     -> VERIFICATION:- FAILED  ('assertion failed: v.len() <= 2')
//!   s7_symbolic_signed_len_u8_safe    -> VERIFICATION:- SUCCESSFUL
//!   s8_symbolic_signed_unwind_u3_bug  -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   s9_symbolic_crossing_u6_safe      -> VERIFICATION:- SUCCESSFUL
//!   s9_symbolic_crossing_u6_bug       -> VERIFICATION:- FAILED  ('assertion failed: v.len() <= 3')
//!   w1_i128_range_len_bug             -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 0')
//!   w1_i128_range_len_safe            -> VERIFICATION:- SUCCESSFUL
//!   w2_u128_near_max_len_bug          -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 4')
//!   w2_u128_near_max_len_safe         -> VERIFICATION:- SUCCESSFUL
//!   w3_u64_inclusive_to_max_bug       -> VERIFICATION:- FAILED  ('assertion failed: v.len() != 3')
//!   w3_u64_inclusive_to_max_safe      -> VERIFICATION:- SUCCESSFUL
//!   c1_char_range_len_bug             -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 4')
//!   c1_char_range_len_safe            -> VERIFICATION:- SUCCESSFUL
//!   c2_char_surrogate_gap_bug         -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 2050')
//!   c2_char_surrogate_gap_safe        -> VERIFICATION:- SUCCESSFUL
//!   c3_char_inclusive_gap_bug         -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 2050')
//!   c3_char_inclusive_gap_safe        -> VERIFICATION:- SUCCESSFUL
//!   k1_extend_capacity_overflow_bug   -> VERIFICATION:- FAILED  ('a panic whose message Kani does not format')
//!   k1_extend_capacity_overflow_safe  -> VERIFICATION:- SUCCESSFUL
//!   k2_extend_unbounded_size_hint_bug -> VERIFICATION:- FAILED  ('a panic whose message Kani does not format')
//!
//! MECHANISM UNDER TEST. The CHC extend model zero-extended the bounds and
//! compared them unsigned, and folded constants as unsigned: `-2i8..3`
//! yielded no element, `2i8..-1` yielded 253, `-2i32..3` bounded the loop of
//! `extend_trusted` by 0 under `unwind(3)`, and a char range counted the
//! 0x800 surrogate code points. Signed bounds are now sign-extended and
//! compared signed, the count is `Step::steps_between` (the surrogate gap
//! skipped for `char`) at the pointer width or 128 bits
//! (`chc/call/range_span.rs`), and the reservation's "capacity overflow"
//! panic is a check where the length used to be assumed not to wrap.

#[kani::proof]
fn s1_signed_i8_range_len_bug() {
    let mut v: Vec<i8> = Vec::new();
    v.extend(-2i8..3);
    assert!(v.len() == 0);
}

#[kani::proof]
fn s1_signed_i8_range_len_safe() {
    let mut v: Vec<i8> = Vec::new();
    v.extend(-2i8..3);
    assert!(v.len() == 5);
}

#[kani::proof]
fn s2_signed_i64_range_len_bug() {
    let mut v: Vec<i64> = Vec::new();
    v.extend(-2i64..3);
    assert!(v.len() == 0);
}

#[kani::proof]
fn s2_signed_i64_range_len_safe() {
    let mut v: Vec<i64> = Vec::new();
    v.extend(-2i64..3);
    assert!(v.len() == 5);
}

#[kani::proof]
fn s3_negative_inclusive_len_bug() {
    let mut v: Vec<i32> = Vec::new();
    v.extend(-3i32..=-1);
    assert!(v.len() != 3);
}

#[kani::proof]
fn s3_negative_inclusive_len_safe() {
    let mut v: Vec<i32> = Vec::new();
    v.extend(-3i32..=-1);
    assert!(v.len() == 3);
}

#[kani::proof]
fn s4_isize_inclusive_crossing_bug() {
    let mut v: Vec<isize> = Vec::new();
    v.extend(-1isize..=1);
    assert!(v.len() == 0);
}

#[kani::proof]
fn s4_isize_inclusive_crossing_safe() {
    let mut v: Vec<isize> = Vec::new();
    v.extend(-1isize..=1);
    assert!(v.len() == 3);
}

#[kani::proof]
fn s5_reversed_signed_range_bug() {
    let mut v: Vec<i8> = Vec::new();
    v.extend(2i8..-1);
    assert!(v.len() == 253);
}

#[kani::proof]
fn s5_reversed_signed_range_safe() {
    let mut v: Vec<i8> = Vec::new();
    v.extend(2i8..-1);
    assert!(v.len() == 0);
}

#[kani::proof]
#[kani::unwind(3)]
fn s6_signed_range_unwind_u3_bug() {
    let mut v: Vec<i32> = Vec::new();
    v.extend(-2i32..3);
    assert!(v.len() <= 5);
}

#[kani::proof]
#[kani::unwind(6)]
fn s6_signed_range_unwind_u6_safe() {
    let mut v: Vec<i32> = Vec::new();
    v.extend(-2i32..3);
    assert!(v.len() == 5);
}

#[kani::proof]
#[kani::unwind(8)]
fn s7_symbolic_signed_len_u8_bug() {
    let lo: i8 = kani::any();
    kani::assume(lo >= -4 && lo <= 0);
    let mut v: Vec<i8> = Vec::new();
    v.extend(lo..2);
    assert!(v.len() <= 2);
}

#[kani::proof]
#[kani::unwind(8)]
fn s7_symbolic_signed_len_u8_safe() {
    let lo: i8 = kani::any();
    kani::assume(lo >= -4 && lo <= 0);
    let mut v: Vec<i8> = Vec::new();
    v.extend(lo..2);
    assert!(v.len() == (2 - lo) as usize);
}

#[kani::proof]
#[kani::unwind(3)]
fn s8_symbolic_signed_unwind_u3_bug() {
    let lo: i8 = kani::any();
    kani::assume(lo >= -4 && lo <= 0);
    let mut v: Vec<i8> = Vec::new();
    v.extend(lo..2);
    assert!(v.len() <= 6);
}

#[kani::proof]
#[kani::unwind(6)]
fn s9_symbolic_crossing_u6_safe() {
    let lo: i16 = kani::any();
    let hi: i16 = kani::any();
    kani::assume(lo >= -2 && lo <= 0 && hi >= 0 && hi <= 2);
    let mut v: Vec<i16> = Vec::new();
    v.extend(lo..hi);
    assert!(v.len() <= 4);
}

#[kani::proof]
#[kani::unwind(6)]
fn s9_symbolic_crossing_u6_bug() {
    let lo: i16 = kani::any();
    let hi: i16 = kani::any();
    kani::assume(lo >= -2 && lo <= 0 && hi >= 0 && hi <= 2);
    let mut v: Vec<i16> = Vec::new();
    v.extend(lo..hi);
    assert!(v.len() <= 3);
}

#[kani::proof]
fn w1_i128_range_len_bug() {
    let mut v: Vec<i128> = Vec::new();
    v.extend(-1i128..1);
    assert!(v.len() == 0);
}

#[kani::proof]
fn w1_i128_range_len_safe() {
    let mut v: Vec<i128> = Vec::new();
    v.extend(-1i128..1);
    assert!(v.len() == 2);
}

#[kani::proof]
fn w2_u128_near_max_len_bug() {
    let mut v: Vec<u128> = Vec::new();
    v.extend((u128::MAX - 3)..u128::MAX);
    assert!(v.len() == 4);
}

#[kani::proof]
fn w2_u128_near_max_len_safe() {
    let mut v: Vec<u128> = Vec::new();
    v.extend((u128::MAX - 3)..u128::MAX);
    assert!(v.len() == 3);
}

#[kani::proof]
fn w3_u64_inclusive_to_max_bug() {
    let mut v: Vec<u64> = Vec::new();
    v.extend((u64::MAX - 2)..=u64::MAX);
    assert!(v.len() != 3);
}

#[kani::proof]
fn w3_u64_inclusive_to_max_safe() {
    let mut v: Vec<u64> = Vec::new();
    v.extend((u64::MAX - 2)..=u64::MAX);
    assert!(v.len() == 3);
}

#[kani::proof]
fn c1_char_range_len_bug() {
    let mut v: Vec<char> = Vec::new();
    v.extend('a'..'d');
    assert!(v.len() == 4);
}

#[kani::proof]
fn c1_char_range_len_safe() {
    let mut v: Vec<char> = Vec::new();
    v.extend('a'..'d');
    assert!(v.len() == 3);
}

#[kani::proof]
fn c2_char_surrogate_gap_bug() {
    let mut v: Vec<char> = Vec::new();
    v.extend('\u{D7FF}'..'\u{E001}');
    assert!(v.len() == 2050);
}

#[kani::proof]
fn c2_char_surrogate_gap_safe() {
    let mut v: Vec<char> = Vec::new();
    v.extend('\u{D7FF}'..'\u{E001}');
    assert!(v.len() == 2);
}

#[kani::proof]
fn c3_char_inclusive_gap_bug() {
    let mut v: Vec<char> = Vec::new();
    v.extend('\u{D7FF}'..='\u{E000}');
    assert!(v.len() == 2050);
}

#[kani::proof]
fn c3_char_inclusive_gap_safe() {
    let mut v: Vec<char> = Vec::new();
    v.extend('\u{D7FF}'..='\u{E000}');
    assert!(v.len() == 2);
}

#[kani::proof]
fn k1_extend_capacity_overflow_bug() {
    let mut v: Vec<u64> = Vec::new();
    v.extend(0u64..u64::MAX);
    assert!(v.len() > 0);
}

#[kani::proof]
fn k1_extend_capacity_overflow_safe() {
    let mut v: Vec<u64> = Vec::new();
    v.extend(0u64..3);
    assert!(v.len() == 3);
}

#[kani::proof]
fn k2_extend_unbounded_size_hint_bug() {
    let mut w: Vec<u64> = Vec::new();
    w.extend(0u64..=u64::MAX);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Iterator::eq compares remaining ELEMENTS. These semantic controls do not
//! confer a new frozen-Kani measurement; each assertion states Rust behavior.

#![feature(iter_order_by)]

#[kani::proof]
fn equal_values_distinct_storage_safe() {
    let a = [1u8, 2, 3];
    let b = [1u8, 2, 3];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn equal_suffixes_different_positions_safe() {
    let a = [9u8, 1, 2];
    let b = [1u8, 2];
    let mut left = a.iter();
    left.next();
    assert!(left.eq(b.iter()));
}

#[kani::proof]
fn consumed_prefix_does_not_decide_equality_safe() {
    let a = [9u8, 1, 2];
    let b = [8u8, 1, 2];
    let mut left = a.iter();
    let mut right = b.iter();
    left.next();
    right.next();
    assert!(left.eq(right));
}

#[kani::proof]
fn exhausted_different_storage_safe() {
    let a = [1u8, 2];
    let b = [3u8];
    let mut left = a.iter();
    let mut right = b.iter();
    left.next();
    left.next();
    right.next();
    assert!(left.eq(right));
}

#[kani::proof]
fn unequal_remaining_lengths_bug() {
    let a = [1u8, 2];
    let b = [1u8, 2];
    let mut left = a.iter();
    left.next();
    assert!(left.eq(b.iter()));
}

#[kani::proof]
fn chars_unicode_equal_safe() {
    assert!("é🦀".chars().eq("é🦀".chars()));
}

#[kani::proof]
fn chars_unicode_difference_bug() {
    assert!("é🦀".chars().eq("é🐍".chars()));
}

#[kani::proof]
fn chars_advanced_ascii_suffix_safe() {
    let mut left = "xé".chars();
    left.next();
    assert!(left.eq("é".chars()));
}

#[kani::proof]
fn float_signed_zero_safe() {
    let a = [0.0f32];
    let b = [-0.0f32];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn float_nan_is_not_equal_bug() {
    let a = [f32::NAN];
    assert!(a.iter().eq(a.iter()));
}

#[derive(Clone, Copy)]
struct Parity(u8);
impl PartialEq for Parity {
    fn eq(&self, rhs: &Self) -> bool {
        self.0 % 2 == rhs.0 % 2
    }
}

#[kani::proof]
fn custom_parity_equal_safe() {
    let a = [Parity(1)];
    let b = [Parity(3)];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn custom_parity_different_bug() {
    let a = [Parity(1)];
    let b = [Parity(2)];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn take_changes_remaining_sequence_bug() {
    let a = [1u8, 2];
    assert!(a.iter().take(1).eq(a.iter()));
}

#[kani::proof]
fn map_changes_elements_bug() {
    let a = [1u8, 2];
    assert!(a.iter().map(|x| x.wrapping_add(1)).eq(a.iter().copied()));
}

#[kani::proof]
fn reverse_changes_order_bug() {
    let a = [1u8, 2];
    assert!(a.iter().rev().eq(a.iter()));
}

#[kani::proof]
fn comparator_can_reject_identical_elements_bug() {
    let a = [1u8];
    assert!(a.iter().cmp_by(a.iter(), |_, _| core::cmp::Ordering::Less).is_eq());
}

#[kani::proof]
fn float_signed_zero_equal_not_unequal_bug() {
    let a = [0.0f32];
    let b = [-0.0f32];
    assert!(!a.iter().eq(b.iter()));
}

#[kani::proof]
fn float64_signed_zero_safe() {
    let a = [0.0f64];
    let b = [-0.0f64];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn float64_nan_is_not_equal_bug() {
    let a = [f64::NAN];
    assert!(a.iter().eq(a.iter()));
}

#[kani::proof]
fn float_symbolic_non_nan_reflexive_safe() {
    let value: f32 = kani::any();
    kani::assume(!value.is_nan());
    let a = [value];
    assert!(a.iter().eq(a.iter()));
}

#[kani::proof]
fn chars_advanced_multibyte_suffix_safe() {
    let mut left = "é🦀".chars();
    assert_eq!(left.next(), Some('é'));
    assert!(left.eq("🦀".chars()));
}

#[kani::proof]
fn chars_four_byte_advance_and_exhaustion_safe() {
    let mut left = "🦀é".chars();
    assert_eq!(left.next(), Some('🦀'));
    assert_eq!(left.next(), Some('é'));
    assert_eq!(left.next(), None);
    assert!(left.eq("".chars()));
}

#[kani::proof]
fn chars_multibyte_next_wrong_value_bug() {
    let mut left = "é".chars();
    assert_eq!(left.next(), Some('x'));
}

#[kani::proof]
fn chars_consumed_suffix_difference_bug() {
    let mut left = "éx".chars();
    left.next();
    assert!(left.eq("y".chars()));
}

#[kani::proof]
fn chars_empty_literal_next_and_equality_safe() {
    let mut empty = "".chars();
    assert_eq!(empty.next(), None);
    assert!(empty.eq("".chars()));
}

#[kani::proof]
fn chars_empty_literal_wrong_next_bug() {
    let mut empty = "".chars();
    assert_eq!(empty.next(), Some('x'));
}

#[kani::proof]
fn chars_nonempty_literal_is_not_empty_bug() {
    assert!("é".chars().eq("".chars()));
}

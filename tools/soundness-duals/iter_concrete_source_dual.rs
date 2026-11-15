// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the concrete string replays of
//! `flat_map(|s| s.chars())` and `filter_map(|s| s.parse::<T>().ok())`
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, found
//! while repairing review finding 8's `flat_map.rs` trip bound).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   fm1_other_array_first_bug        -> VERIFICATION:- FAILED  ('assertion failed: it.next() == Some(a)')
//!   fm1_other_array_first_safe       -> VERIFICATION:- SUCCESSFUL
//!   fm2_other_closure_bug            -> VERIFICATION:- FAILED  ('assertion failed: it.next() == Some(H)')
//!   fm3_plain_control_safe           -> VERIFICATION:- SUCCESSFUL
//!   fp1_parse_u8_out_of_range_bug    -> VERIFICATION:- FAILED  ('assertion failed: numbers.len() == 2')
//!   fp1_parse_u8_out_of_range_safe   -> VERIFICATION:- SUCCESSFUL
//!   fp2_parse_other_array_first_bug  -> VERIFICATION:- FAILED  ('assertion failed: numbers.len() == 3')
//!   fp2_parse_other_array_first_safe -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Both replays took the FIRST `[&str; N]` literal of
//! the body as the iterator's source, whatever the iterator read, and
//! accepted any closure that called `chars` / `parse`: with another string
//! array before the source, `flat_map(..).next() == Some('a')` verified clean
//! where Kani fails and the true `Some('H')` was certified Genuine; a
//! `chars().rev()` closure was read as `chars()`; a `parse::<u8>()` closure
//! was replayed as `parse::<i32>()`. The source is now traced exactly from
//! the iterator (`concrete_strs_of_iter_source`) and the closure must be
//! exactly `|s| s.chars()` / `|s| s.parse::<T>().ok()`, `T` read from its
//! return type (`closure_is_str_chars`, `int_parse_ok_closure_target`).

#[kani::proof]
fn fm1_other_array_first_bug() {
    let names = ["ab", "c"];
    let hi = ["H", "i"];
    let mut it = hi.iter().flat_map(|s| s.chars());
    assert!(names.len() == 2);
    assert_eq!(it.next(), Some('a'));
}

#[kani::proof]
fn fm1_other_array_first_safe() {
    let names = ["ab", "c"];
    let hi = ["H", "i"];
    let mut it = hi.iter().flat_map(|s| s.chars());
    assert!(names.len() == 2);
    assert_eq!(it.next(), Some('H'));
}

#[kani::proof]
fn fm2_other_closure_bug() {
    let hi = ["Hx", "i"];
    let mut it = hi.iter().flat_map(|s| s.chars().rev());
    assert_eq!(it.next(), Some('H'));
}

#[kani::proof]
#[kani::unwind(3)]
fn fm3_plain_control_safe() {
    let hi = ["H", "i"];
    let mut it = hi.iter().flat_map(|s| s.chars());
    assert_eq!(it.next(), Some('H'));
    assert_eq!(it.next(), Some('i'));
    assert_eq!(it.next(), None);
}

#[kani::proof]
fn fp1_parse_u8_out_of_range_bug() {
    let strings = vec!["300", "7"];
    let numbers: Vec<u8> = strings.into_iter().filter_map(|s| s.parse::<u8>().ok()).collect();
    assert_eq!(numbers.len(), 2);
}

#[kani::proof]
fn fp1_parse_u8_out_of_range_safe() {
    let strings = vec!["300", "7"];
    let numbers: Vec<u8> = strings.into_iter().filter_map(|s| s.parse::<u8>().ok()).collect();
    assert_eq!(numbers.len(), 1);
}

#[kani::proof]
fn fp2_parse_other_array_first_bug() {
    let decoy = ["1", "2", "3"];
    let strings = vec!["tofu", "93"];
    let numbers: Vec<i32> = strings.into_iter().filter_map(|s| s.parse::<i32>().ok()).collect();
    assert!(decoy.len() == 3);
    assert_eq!(numbers.len(), 3);
}

#[kani::proof]
fn fp2_parse_other_array_first_safe() {
    let decoy = ["1", "2", "3"];
    let strings = vec!["tofu", "93"];
    let numbers: Vec<i32> = strings.into_iter().filter_map(|s| s.parse::<i32>().ok()).collect();
    assert!(decoy.len() == 3);
    assert_eq!(numbers.len(), 1);
}

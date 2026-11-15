// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r11a): Joined Option == over other payload layouts (char niche, Ordering niche, tuple, array).
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r11a. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   opt_char_join_must_fail     -> VERIFICATION:- FAILED (assertion)
//   opt_char_join_safe          -> VERIFICATION:- SUCCESSFUL
//   opt_ordering_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   opt_ordering_join_safe      -> VERIFICATION:- SUCCESSFUL
//   opt_pair_join_must_fail     -> VERIFICATION:- FAILED (assertion)
//   opt_pair_join_safe          -> VERIFICATION:- SUCCESSFUL
//   opt_array_join_must_fail    -> VERIFICATION:- FAILED (assertion)
//   opt_array_join_safe         -> VERIFICATION:- SUCCESSFUL

use std::cmp::Ordering;
#[kani::proof]
fn opt_char_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<char> = if b { Some('a') } else { Some('a') };
    assert!(!(o == Some('a')));
}
#[kani::proof]
fn opt_char_join_safe() {
    let b: bool = kani::any();
    let o: Option<char> = if b { Some('a') } else { Some('a') };
    assert!(o == Some('a'));
}
#[kani::proof]
fn opt_ordering_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<Ordering> = if b { Some(Ordering::Less) } else { Some(Ordering::Less) };
    assert!(!(o == Some(Ordering::Less)));
}
#[kani::proof]
fn opt_ordering_join_safe() {
    let b: bool = kani::any();
    let o: Option<Ordering> = if b { Some(Ordering::Less) } else { Some(Ordering::Less) };
    assert!(o == Some(Ordering::Less));
}
#[kani::proof]
fn opt_pair_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<(u8, u8)> = if b { Some((1, 2)) } else { Some((1, 2)) };
    assert!(!(o == Some((1, 2))));
}
#[kani::proof]
fn opt_pair_join_safe() {
    let b: bool = kani::any();
    let o: Option<(u8, u8)> = if b { Some((1, 2)) } else { Some((1, 2)) };
    assert!(o == Some((1, 2)));
}
#[kani::proof]
fn opt_array_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<[u8; 2]> = if b { Some([1, 2]) } else { Some([1, 2]) };
    assert!(!(o == Some([1, 2])));
}
#[kani::proof]
fn opt_array_join_safe() {
    let b: bool = kani::any();
    let o: Option<[u8; 2]> = if b { Some([1, 2]) } else { Some([1, 2]) };
    assert!(o == Some([1, 2]));
}

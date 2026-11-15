// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `str::chars().nth(k)` under a declared
//! `#[kani::unwind(U)]` (fix/chc-walker-fail-closed, repair round 3, walker
//! fail-closed review 6 round 3 finding 6; the review's probe
//! `q4_loop_passes.rs`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   n1_chars_nth_u3_bug      -> VERIFICATION:- FAILED  ('unwinding assertion loop 3')
//!   n1_chars_nth_u8_safe     -> VERIFICATION:- SUCCESSFUL
//!   n3_chars_nth2_u3_safe    -> VERIFICATION:- SUCCESSFUL
//!   n4_chars_nth3_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 3')
//!   n2_bytes_nth_u3_safe     -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `SimpleStrIterPass` rewrote `chars().nth(k)` into a
//! loop-free helper under any declared unwind, so the std loop Kani's
//! unwinding assertion checks (`Chars::advance_by`, one pass per skipped
//! char) disappeared and `n1_chars_nth_u3_bug` verified clean. Measured on
//! Kani over `"abcdefgh".chars().nth(k)`, `k` in 0..=5, `U` in 1..=6: the
//! harness passes exactly when `k < U`. Under a declared bound only a
//! constant `k < U` (below the 32-byte chunked path) is rewritten now
//! (`kani_middle/transform/simple_str_iter.rs`); `bytes().nth(k)` is a slice
//! index in std and stays rewritten.
#[kani::proof]
#[kani::unwind(3)]
fn n1_chars_nth_u3_bug() {
    let s = "abcdef";
    let c = s.chars().nth(4);
    assert!(c == Some('e'));
}

#[kani::proof]
#[kani::unwind(8)]
fn n1_chars_nth_u8_safe() {
    let s = "abcdef";
    let c = s.chars().nth(4);
    assert!(c == Some('e'));
}

#[kani::proof]
#[kani::unwind(3)]
fn n3_chars_nth2_u3_safe() {
    let s = "abcdef";
    let c = s.chars().nth(2);
    assert!(c == Some('c'));
}

#[kani::proof]
#[kani::unwind(3)]
fn n4_chars_nth3_u3_bug() {
    let s = "abcdef";
    let c = s.chars().nth(3);
    assert!(c == Some('d'));
}

#[kani::proof]
#[kani::unwind(3)]
fn n2_bytes_nth_u3_safe() {
    let s = "abcdef";
    let c = s.bytes().nth(4);
    assert!(c == Some(b'e'));
}

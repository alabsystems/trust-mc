// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- Rule E (design trust-mc-reds-final §4.4): a value the
//! encoding does not compute is a booked havoc. A `&str` literal longer than
//! 64 bytes is not read out byte by byte; its bytes were a fresh value booked
//! nowhere, so a counterexample through them was certified Genuine on a safe
//! program (`safe_long_const_str`, CHC, main 756f6eabf). The safe rows may
//! fail closed (over-approximation), never Genuine; the bug rows must fail.
//!
//! Oracle: the native run, measured 2026-10-14 (each harness 4096 times with
//! `kani::any` as a xorshift u8 source, built by trustc with verification
//! off): no safe_ row panics, every bug_ row panics on some input.

const S: &str = "0123456789012345678901234567890123456789012345678901234567890123456789";

#[kani::proof]
fn safe_long_const_str() {
    assert!(S.as_bytes()[0] == b'0');
}

#[kani::proof]
fn bug_long_const_str() {
    assert!(S.as_bytes()[0] == b'1');
}

#[kani::proof]
fn safe_long_const_str_past_64() {
    assert!(S.as_bytes()[69] == b'9');
}

#[kani::proof]
fn bug_long_const_str_past_64() {
    assert!(S.as_bytes()[69] == b'0');
}

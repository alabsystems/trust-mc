// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! `String::into_bytes` is a stub (StringIntoBytes): a layout identity from
//! the String model to the Vec<u8> model. The call survives the inline pass
//! (every `String::` call does) and the BMC mini-inliner's `self.vec` field
//! projection lost the fields — `b.len() == s.len()` reported a spurious
//! counterexample. The broken variant pins the discriminating direction.

#[kani::proof]
fn into_bytes_keeps_len() {
    let s = String::from("ab");
    let n = s.len();
    let b = s.into_bytes();
    assert_eq!(b.len(), n);
}

// Deliberately broken: the byte length is exactly the String length — must FAIL.
#[kani::proof]
fn into_bytes_changed_len_fails() {
    let s = String::from("ab");
    let n = s.len();
    let b = s.into_bytes();
    assert_ne!(b.len(), n);
}

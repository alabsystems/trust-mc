// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! `Option::unwrap_or_default` is deliberately NOT stubbed. The inline pass
//! keeps it as a Call (the `unwrap` substring rule) and the BMC mini-inliner
//! then runs the REAL library body, so `T::default()` is whatever MIR says it
//! is — a stub would have to invent a default per type. This file pins that
//! route in both directions so a future stub cannot silently replace it.

#[kani::proof]
fn unwrap_or_default_none_is_default() {
    let o: Option<u8> = None;
    assert_eq!(o.unwrap_or_default(), 0);
}

#[kani::proof]
fn unwrap_or_default_some_is_payload() {
    let x: u8 = kani::any();
    let o = Some(x);
    assert_eq!(o.unwrap_or_default(), x);
}

// Deliberately broken: `u8::default()` is 0, not 1 — must FAIL.
#[kani::proof]
fn unwrap_or_default_none_wrong_default_fails() {
    let o: Option<u8> = None;
    assert_eq!(o.unwrap_or_default(), 1);
}

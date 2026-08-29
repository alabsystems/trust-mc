// kani-expect: PROOF
// NOTE: Some harnesses (2/6) demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// NOTE: test_option_bool_phi_merge was ERROR at ay 417854b7, now UNKNOWN at ay 8a4a9bcc2.
// kani-flags: --ay-chc-track=mem
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Regression tests for Option<bool> sort mismatch (#3260).
//
// Option<bool> has dual representation: Datatype(Option_bool) from
// reconstruct_option_like_enum, and BitVec(1) from BV-flattened paths.
// These tests exercise the phi node merges and ITE construction paths
// where the two representations previously caused sort mismatch crashes.

#[kani::proof]
fn test_option_bool_some_true() {
    let x: Option<bool> = Some(true);
    assert!(x.unwrap());
}

#[kani::proof]
fn test_option_bool_some_false() {
    let x: Option<bool> = Some(false);
    assert!(!x.unwrap());
}

#[kani::proof]
fn test_option_bool_none() {
    let x: Option<bool> = None;
    assert!(x.is_none());
}

#[kani::proof]
fn test_option_bool_unwrap_or() {
    let x: Option<bool> = None;
    assert!(!x.unwrap_or(false));
    let y: Option<bool> = Some(true);
    assert!(y.unwrap_or(false));
}

#[kani::proof]
fn test_option_bool_phi_merge() {
    // Exercises phi node merge: one branch produces Some(true),
    // the other produces None. The ITE at the merge point must
    // harmonize Datatype and BitVec sorts.
    let cond: bool = kani::any();
    let x: Option<bool> = if cond { Some(true) } else { None };
    assert!(x.unwrap_or(false) || !x.unwrap_or(false));
}

#[kani::proof]
fn test_option_bool_pattern_match() {
    let cond: bool = kani::any();
    let x: Option<bool> = if cond { Some(true) } else { None };
    match x {
        Some(v) => assert_eq!(v, true),
        None => assert!(!cond),
    }
}

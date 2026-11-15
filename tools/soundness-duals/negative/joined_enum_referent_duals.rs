// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `==` and `&mut` callees on enum values joined from several
// producers, beyond `Option<u8>`.
//
// Audit evidence: limits-page/chc-joined-option-eq-false-proof, related-construct
// probes of 2026-09-12 (base 7b7f719f7, ay 0.26.0 94bf24d0f). Under --ay-chc every
// `_must_fail` harness here was SUCCESSFUL on the base bundle except the
// `matches!` control, and every `_safe` twin except the control FAILED labelled
// Genuine: the inlined callee took the reference's address for its referent.
// The default lane proved `option_ref_join_eq_must_fail` and
// `nested_option_join_eq_must_fail` on the same bundle.
//
// Oracle (per harness):
//   option_ref_join_eq_must_fail      -> VERIFICATION:- FAILED (assertion)
//   option_ref_join_eq_safe           -> VERIFICATION:- SUCCESSFUL
//   option_nonzero_join_eq_must_fail  -> VERIFICATION:- FAILED (assertion)
//   option_nonzero_join_eq_safe       -> VERIFICATION:- SUCCESSFUL
//   option_bool_join_eq_must_fail     -> VERIFICATION:- FAILED (assertion)
//   option_bool_join_eq_safe          -> VERIFICATION:- SUCCESSFUL
//   nested_option_join_eq_must_fail   -> VERIFICATION:- FAILED (assertion)
//   nested_option_join_eq_safe        -> VERIFICATION:- SUCCESSFUL
//   result_join_eq_must_fail          -> VERIFICATION:- FAILED (assertion)
//   result_join_eq_safe               -> VERIFICATION:- SUCCESSFUL
//   option_u32_join_eq_must_fail      -> VERIFICATION:- FAILED (assertion)
//   option_u32_join_eq_safe           -> VERIFICATION:- SUCCESSFUL
//   tuple_option_join_eq_must_fail    -> VERIFICATION:- FAILED (assertion)
//   tuple_option_join_eq_safe         -> VERIFICATION:- SUCCESSFUL
//   option_as_mut_join_must_fail      -> VERIFICATION:- FAILED (assertion)
//   option_as_mut_join_safe           -> VERIFICATION:- SUCCESSFUL
//   matches_join_control_must_fail    -> VERIFICATION:- FAILED (assertion)
//   matches_join_control_safe         -> VERIFICATION:- SUCCESSFUL
//
// Both arms of every join produce the same value, so each `_must_fail`
// assertion is false and each `_safe` assertion true on every path.

use std::num::NonZeroU32;

#[kani::proof]
fn option_ref_join_eq_must_fail() {
    let x = 5u8;
    let y = 5u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&x) } else { Some(&y) };
    assert!(!(o == Some(&5)));
}

#[kani::proof]
fn option_ref_join_eq_safe() {
    let x = 5u8;
    let y = 5u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&x) } else { Some(&y) };
    assert!(o == Some(&5));
}

#[kani::proof]
fn option_nonzero_join_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<NonZeroU32> = if b { NonZeroU32::new(4) } else { NonZeroU32::new(4) };
    assert!(!(o == NonZeroU32::new(4)));
}

#[kani::proof]
fn option_nonzero_join_eq_safe() {
    let b: bool = kani::any();
    let o: Option<NonZeroU32> = if b { NonZeroU32::new(4) } else { NonZeroU32::new(4) };
    assert!(o == NonZeroU32::new(4));
}

#[kani::proof]
fn option_bool_join_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<bool> = if b { Some(true) } else { Some(true) };
    assert!(!(o == Some(true)));
}

#[kani::proof]
fn option_bool_join_eq_safe() {
    let b: bool = kani::any();
    let o: Option<bool> = if b { Some(true) } else { Some(true) };
    assert!(o == Some(true));
}

#[kani::proof]
fn nested_option_join_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<Option<u8>> = if b { Some(Some(4)) } else { Some(Some(4)) };
    assert!(!(o == Some(Some(4))));
}

#[kani::proof]
fn nested_option_join_eq_safe() {
    let b: bool = kani::any();
    let o: Option<Option<u8>> = if b { Some(Some(4)) } else { Some(Some(4)) };
    assert!(o == Some(Some(4)));
}

#[kani::proof]
fn result_join_eq_must_fail() {
    let b: bool = kani::any();
    let o: Result<u8, u16> = if b { Ok(4) } else { Ok(4) };
    assert!(!(o == Ok(4)));
}

#[kani::proof]
fn result_join_eq_safe() {
    let b: bool = kani::any();
    let o: Result<u8, u16> = if b { Ok(4) } else { Ok(4) };
    assert!(o == Ok(4));
}

#[kani::proof]
fn option_u32_join_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u32> = if b { Some(70000) } else { Some(70000) };
    assert!(!(o == Some(70000)));
}

#[kani::proof]
fn option_u32_join_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u32> = if b { Some(70000) } else { Some(70000) };
    assert!(o == Some(70000));
}

#[kani::proof]
fn tuple_option_join_eq_must_fail() {
    let b: bool = kani::any();
    let t: (Option<u8>, u8) = if b { (Some(4), 1) } else { (Some(4), 1) };
    assert!(!(t == (Some(4), 1)));
}

#[kani::proof]
fn tuple_option_join_eq_safe() {
    let b: bool = kani::any();
    let t: (Option<u8>, u8) = if b { (Some(4), 1) } else { (Some(4), 1) };
    assert!(t == (Some(4), 1));
}

#[kani::proof]
fn option_as_mut_join_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    if let Some(x) = o.as_mut() {
        *x += 1;
    }
    assert!(!matches!(o, Some(5)));
}

#[kani::proof]
fn option_as_mut_join_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    if let Some(x) = o.as_mut() {
        *x += 1;
    }
    assert!(matches!(o, Some(5)));
}

#[kani::proof]
fn matches_join_control_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(!matches!(o, Some(4)));
}

#[kani::proof]
fn matches_join_control_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(matches!(o, Some(4)));
}

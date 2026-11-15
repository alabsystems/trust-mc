// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: writes through a `&mut` joined from two borrows, then a direct
// read of the local the write reached.
//
// Audit evidence: related-construct probes of 2026-09-12 for
// limits-page/chc-joined-option-eq-false-proof (base 7b7f719f7, ay 0.26.0
// 94bf24d0f). With the points-at edge of `r` gone (two producers), the store
// lands in typed memory at `r`'s address while the borrowed locals keep their
// own state, so the direct read after the write sees the value before it. On
// the base bundle `scalar_store_first_path_must_fail`,
// `option_write_second_path_must_fail` and `option_as_mut_second_path_must_fail`
// were SUCCESSFUL under --ay-chc; the default lane proved
// `scalar_store_first_path_must_fail`, `option_take_second_path_must_fail` and
// `option_as_mut_second_path_must_fail`.
//
// Oracle (per harness):
//   scalar_store_first_path_must_fail    -> VERIFICATION:- FAILED (assertion)
//   scalar_store_first_path_safe         -> VERIFICATION:- SUCCESSFUL
//   option_write_second_path_must_fail   -> VERIFICATION:- FAILED (assertion)
//   option_write_second_path_safe        -> VERIFICATION:- SUCCESSFUL
//   option_take_second_path_must_fail    -> VERIFICATION:- FAILED (assertion)
//   option_take_second_path_safe         -> VERIFICATION:- SUCCESSFUL
//   option_as_mut_second_path_must_fail  -> VERIFICATION:- FAILED (assertion)
//   option_as_mut_second_path_safe       -> VERIFICATION:- SUCCESSFUL
//
// Each harness keeps one path through the join (`assume`) and asserts, after
// the write, the local that path did (safe) or did not (must_fail) update.

#[kani::proof]
fn scalar_store_first_path_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let r: &mut u8 = if b { &mut m } else { &mut n };
    *r = 9;
    assert!(m == 1);
}

#[kani::proof]
fn scalar_store_first_path_safe() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let r: &mut u8 = if b { &mut m } else { &mut n };
    *r = 9;
    assert!(m == 9 && n == 2);
}

#[kani::proof]
fn option_write_second_path_must_fail() {
    let mut m = Some(4u8);
    let mut n = Some(4u8);
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut Option<u8> = if b { &mut m } else { &mut n };
    *r = None;
    assert!(n == Some(4));
}

#[kani::proof]
fn option_write_second_path_safe() {
    let mut m = Some(4u8);
    let mut n = Some(4u8);
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut Option<u8> = if b { &mut m } else { &mut n };
    *r = None;
    assert!(n == None && m == Some(4));
}

#[kani::proof]
fn option_take_second_path_must_fail() {
    let mut m = Some(4u8);
    let mut n = Some(4u8);
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut Option<u8> = if b { &mut m } else { &mut n };
    let _ = r.take();
    assert!(n.is_some());
}

#[kani::proof]
fn option_take_second_path_safe() {
    let mut m = Some(4u8);
    let mut n = Some(4u8);
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut Option<u8> = if b { &mut m } else { &mut n };
    let _ = r.take();
    assert!(n.is_none() && m.is_some());
}

#[kani::proof]
fn option_as_mut_second_path_must_fail() {
    let mut m = Some(4u8);
    let mut n = Some(4u8);
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut Option<u8> = if b { &mut m } else { &mut n };
    if let Some(x) = r.as_mut() {
        *x = 9;
    }
    assert!(n == Some(4));
}

#[kani::proof]
fn option_as_mut_second_path_safe() {
    let mut m = Some(4u8);
    let mut n = Some(4u8);
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut Option<u8> = if b { &mut m } else { &mut n };
    if let Some(x) = r.as_mut() {
        *x = 9;
    }
    assert!(n == Some(9) && m == Some(4));
}

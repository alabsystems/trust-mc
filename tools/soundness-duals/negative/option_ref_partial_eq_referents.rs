// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `==` on `Option<&T>` with no join anywhere.
//
// Audit evidence: related-construct probes of 2026-09-12 for
// limits-page/chc-joined-option-eq-false-proof (base 7b7f719f7 and the fix head,
// ay 0.26.0 94bf24d0f). `Option<&u8>`'s `eq` compares REFERENTS (`*l == *r`).
// Both lanes proved `opt_ref_single_must_fail` on both bundles: every value and
// reference here has one producer, so this is not the joined-value defect. Under
// --ay-chc the inlined `eq` reaches `<&u8 as PartialEq>::eq` through the walker's
// nested virtual dispatch ("following ref_targets for vtable lookup" with the
// callee's local indices), and the known-call fast paths used SMT equality of the
// reference values (gated since, which did not close the channel).
//
// Oracle (per harness):
//   opt_ref_single_must_fail          -> VERIFICATION:- FAILED (assertion)
//   opt_ref_single_safe               -> VERIFICATION:- SUCCESSFUL
//   opt_ref_single_differ_must_fail   -> VERIFICATION:- FAILED (assertion)
//   opt_ref_single_differ_safe        -> VERIFICATION:- SUCCESSFUL
//
// `x == 5` makes `Some(&x) == Some(&5)` true however the two referents are laid
// out, and `x == 6` makes it false; native Rust panics on each `_must_fail`.

#[kani::proof]
fn opt_ref_single_must_fail() {
    let x = 5u8;
    let o: Option<&u8> = Some(&x);
    assert!(!(o == Some(&5)));
}

#[kani::proof]
fn opt_ref_single_safe() {
    let x = 5u8;
    let o: Option<&u8> = Some(&x);
    assert!(o == Some(&5));
}

#[kani::proof]
fn opt_ref_single_differ_must_fail() {
    let x = 6u8;
    let o: Option<&u8> = Some(&x);
    assert!(o == Some(&5));
}

#[kani::proof]
fn opt_ref_single_differ_safe() {
    let x = 6u8;
    let o: Option<&u8> = Some(&x);
    assert!(!(o == Some(&5)));
}

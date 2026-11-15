// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: the minimal repros of the m3/chc-joined-option-eq review that no
// review bypass pack carries verbatim, with their safe twins.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// minimal repros m6, m8, m12, m14a and m14b. m14a (a scalar joined from two branches,
// swapped, then compared) was VERIFICATION:- SUCCESSFUL under --ay-chc on base and head:
// the swap fallback dropped the write. m8 (`Option<(u8, u8)>` compared with no join)
// was SUCCESSFUL under --ay-chc: the payload comparison folded to false.
//
// Oracle (per harness):
//   tuple_of_ref_nojoin_must_fail  -> VERIFICATION:- FAILED (assertion)
//   tuple_of_ref_nojoin_safe       -> VERIFICATION:- SUCCESSFUL
//   opt_pair_nojoin_must_fail      -> VERIFICATION:- FAILED (assertion)
//   opt_pair_nojoin_safe           -> VERIFICATION:- SUCCESSFUL
//   swap_option_nojoin_must_fail   -> VERIFICATION:- FAILED (assertion)
//   swap_option_nojoin_safe        -> VERIFICATION:- SUCCESSFUL
//   swap_joined_scalar_must_fail   -> VERIFICATION:- FAILED (assertion)
//   swap_joined_scalar_safe        -> VERIFICATION:- SUCCESSFUL
//   swap_unjoined_scalar_must_fail -> VERIFICATION:- FAILED (assertion)
//   swap_unjoined_scalar_safe      -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn tuple_of_ref_nojoin_must_fail() {
    let x = 4u8;
    let y = 4u8;
    assert!(!((&x, 1u8) == (&y, 1u8)));
}
#[kani::proof]
fn tuple_of_ref_nojoin_safe() {
    let x = 4u8;
    let y = 4u8;
    assert!((&x, 1u8) == (&y, 1u8));
}
#[kani::proof]
fn opt_pair_nojoin_must_fail() {
    let o: Option<(u8, u8)> = Some((1, 2));
    assert!(!(o == Some((1, 2))));
}
#[kani::proof]
fn opt_pair_nojoin_safe() {
    let o: Option<(u8, u8)> = Some((1, 2));
    assert!(o == Some((1, 2)));
}
#[kani::proof]
fn swap_option_nojoin_must_fail() {
    let mut o: Option<u8> = Some(4);
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(!(o == None));
}
#[kani::proof]
fn swap_option_nojoin_safe() {
    let mut o: Option<u8> = Some(4);
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(o == None && q == Some(4));
}
#[kani::proof]
fn swap_joined_scalar_must_fail() {
    let b: bool = kani::any();
    let mut a: u8 = if b { 1 } else { 3 };
    let mut c: u8 = 2;
    core::mem::swap(&mut a, &mut c);
    assert!(a != 2);
}
#[kani::proof]
fn swap_joined_scalar_safe() {
    let b: bool = kani::any();
    let mut a: u8 = if b { 1 } else { 3 };
    let mut c: u8 = 2;
    core::mem::swap(&mut a, &mut c);
    assert!(a == 2 && (c == 1) == b);
}
#[kani::proof]
fn swap_unjoined_scalar_must_fail() {
    let mut a: u8 = 1;
    let mut c: u8 = 2;
    core::mem::swap(&mut a, &mut c);
    assert!(a != 2);
}
#[kani::proof]
fn swap_unjoined_scalar_safe() {
    let mut a: u8 = 1;
    let mut c: u8 = 2;
    core::mem::swap(&mut a, &mut c);
    assert!(a == 2 && c == 1);
}

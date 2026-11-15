// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r14): Joined references to statics and to array elements.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r14. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   static_opt_refjoin_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   static_opt_refjoin_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   static_opt_refjoin_safe        -> VERIFICATION:- SUCCESSFUL
//   static_u8_refjoin_a_must_fail  -> VERIFICATION:- FAILED (assertion)
//   static_u8_refjoin_b_must_fail  -> VERIFICATION:- FAILED (assertion)
//   static_u8_refjoin_safe         -> VERIFICATION:- SUCCESSFUL
//   elem_refjoin_a_must_fail       -> VERIFICATION:- FAILED (assertion)
//   elem_refjoin_b_must_fail       -> VERIFICATION:- FAILED (assertion)
//   elem_refjoin_safe              -> VERIFICATION:- SUCCESSFUL
//   opt_elem_refjoin_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   opt_elem_refjoin_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   opt_elem_refjoin_safe          -> VERIFICATION:- SUCCESSFUL

static S1: Option<u8> = Some(1);
static S2: Option<u8> = Some(2);
static U1: u8 = 1;
static U2: u8 = 2;

#[kani::proof]
fn static_opt_refjoin_a_must_fail() {
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &S1 } else { &S2 };
    assert!(*r == Some(1));
}
#[kani::proof]
fn static_opt_refjoin_b_must_fail() {
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &S1 } else { &S2 };
    assert!(*r == Some(2));
}
#[kani::proof]
fn static_opt_refjoin_safe() {
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &S1 } else { &S2 };
    assert!((*r == Some(1)) == b);
}
#[kani::proof]
fn static_u8_refjoin_a_must_fail() {
    let b: bool = kani::any();
    let r: &u8 = if b { &U1 } else { &U2 };
    assert!(*r == 1);
}
#[kani::proof]
fn static_u8_refjoin_b_must_fail() {
    let b: bool = kani::any();
    let r: &u8 = if b { &U1 } else { &U2 };
    assert!(*r == 2);
}
#[kani::proof]
fn static_u8_refjoin_safe() {
    let b: bool = kani::any();
    let r: &u8 = if b { &U1 } else { &U2 };
    assert!((*r == 1) == b);
}
#[kani::proof]
fn elem_refjoin_a_must_fail() {
    let a = [1u8, 2];
    let b: bool = kani::any();
    let r: &u8 = if b { &a[0] } else { &a[1] };
    assert!(*r == 1);
}
#[kani::proof]
fn elem_refjoin_b_must_fail() {
    let a = [1u8, 2];
    let b: bool = kani::any();
    let r: &u8 = if b { &a[0] } else { &a[1] };
    assert!(*r == 2);
}
#[kani::proof]
fn elem_refjoin_safe() {
    let a = [1u8, 2];
    let b: bool = kani::any();
    let r: &u8 = if b { &a[0] } else { &a[1] };
    assert!((*r == 1) == b);
}
#[kani::proof]
fn opt_elem_refjoin_a_must_fail() {
    let a = [Some(1u8), Some(2)];
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &a[0] } else { &a[1] };
    assert!(*r == Some(1));
}
#[kani::proof]
fn opt_elem_refjoin_b_must_fail() {
    let a = [Some(1u8), Some(2)];
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &a[0] } else { &a[1] };
    assert!(*r == Some(2));
}
#[kani::proof]
fn opt_elem_refjoin_safe() {
    let a = [Some(1u8), Some(2)];
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &a[0] } else { &a[1] };
    assert!((*r == Some(1)) == b);
}

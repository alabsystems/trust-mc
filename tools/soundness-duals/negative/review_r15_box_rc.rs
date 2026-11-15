// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r15): Joined heap-backed referents: Box<Option<u8>> and Rc<Option<u8>>.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r15. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   box_opt_differ_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   box_opt_differ_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   box_opt_differ_safe        -> VERIFICATION:- SUCCESSFUL
//   rc_opt_join_must_fail      -> VERIFICATION:- FAILED (assertion)
//   rc_opt_join_safe           -> VERIFICATION:- SUCCESSFUL

use std::rc::Rc;
#[kani::proof]
fn box_opt_differ_a_must_fail() {
    let b: bool = kani::any();
    let bx: Box<Option<u8>> = if b { Box::new(Some(1)) } else { Box::new(Some(2)) };
    assert!(*bx == Some(1));
}
#[kani::proof]
fn box_opt_differ_b_must_fail() {
    let b: bool = kani::any();
    let bx: Box<Option<u8>> = if b { Box::new(Some(1)) } else { Box::new(Some(2)) };
    assert!(*bx == Some(2));
}
#[kani::proof]
fn box_opt_differ_safe() {
    let b: bool = kani::any();
    let bx: Box<Option<u8>> = if b { Box::new(Some(1)) } else { Box::new(Some(2)) };
    assert!((*bx == Some(1)) == b);
}
#[kani::proof]
fn rc_opt_join_must_fail() {
    let b: bool = kani::any();
    let rc = if b { Rc::new(Some(4u8)) } else { Rc::new(Some(4u8)) };
    assert!(!(*rc == Some(4)));
}
#[kani::proof]
fn rc_opt_join_safe() {
    let b: bool = kani::any();
    let rc = if b { Rc::new(Some(4u8)) } else { Rc::new(Some(4u8)) };
    assert!(*rc == Some(4));
}

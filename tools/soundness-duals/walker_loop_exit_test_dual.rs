// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the CHC inline walker's loop replay
//! at the visit that finds a loop header's fuel spent.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-26):
//!   bug_break_const_bound_truncated       -> VERIFICATION:- FAILED  ('assertion failed: obj.count_to(x, 8) == x.wrapping_add(5)')
//!   safe_break_const_bound                -> VERIFICATION:- SUCCESSFUL
//!   bug_break_sym_bound_truncated         -> VERIFICATION:- FAILED  ('assertion failed: obj.count_to(x, n) == x.wrapping_add(5)')
//!   safe_break_sym_bound_small            -> VERIFICATION:- SUCCESSFUL
//!   bug_while_sym_bound_extra_iteration   -> VERIFICATION:- FAILED  ('assertion failed: obj.while_to(x, n) == x.wrapping_add(6)')
//!   safe_while_sym_bound_small            -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The walker replays a loop in a walked body with a
//! per-header fuel of five visits. Until 2026-09-26 the visit that found the
//! fuel spent jumped to the header SwitchInt's `otherwise` target WITHOUT
//! evaluating the exit test (`walker.rs`, the #4050 "exit branch"):
//!  * for `if i == n { break }` the `otherwise` target is the exit, so every
//!    trip count past the fuel left the loop with the fifth iteration's
//!    state: `count_to(x, 8)` returned `x + 5`. `bug_*_truncated` verified
//!    SUCCESSFUL clean and `safe_break_const_bound` FAILED Genuine on main
//!    a15de6272 (a false certificate);
//!  * for `while i < n` the `otherwise` target is the loop body, so the walk
//!    ran one more iteration than the program on paths where the exit test
//!    held (a bail usually followed; `safe_while_sym_bound_small` FAILED as
//!    an over-approximation on main).
//! The fix (fix/chc-walker-fail-closed) makes that visit the loop's LAST
//! pass: the exit test is evaluated like any branch, a path that comes back
//! to the header fails its walk and the enclosing SwitchInt arm takes the
//! bailed-arm fallback, and an iteration whose exit test folds to a constant
//! is refunded its visit, so a constant-bound loop replays exactly.
//!
//! Lane scope: CHC only (the dyn dispatch these rest on is walker territory).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_loop_exit_test_dual.rs

pub trait Op {
    fn count_to(&self, x: u8, n: u8) -> u8;
    fn while_to(&self, x: u8, n: u8) -> u8;
}
pub struct A;
pub struct B;
impl Op for A {
    fn count_to(&self, x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        loop {
            if i == n {
                break;
            }
            acc = acc.wrapping_add(1);
            i += 1;
        }
        acc
    }
    fn while_to(&self, x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        while i < n {
            acc = acc.wrapping_add(1);
            i += 1;
        }
        acc
    }
}
impl Op for B {
    fn count_to(&self, x: u8, n: u8) -> u8 { x.wrapping_add(n) }
    fn while_to(&self, x: u8, n: u8) -> u8 { x.wrapping_add(n) }
}
#[kani::proof]
fn bug_break_const_bound_truncated() {
    let x: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(A);
    assert!(obj.count_to(x, 8) == x.wrapping_add(5));
}
#[kani::proof]
fn safe_break_const_bound() {
    let x: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    assert!(obj.count_to(x, 8) == x.wrapping_add(8));
}
#[kani::proof]
fn bug_break_sym_bound_truncated() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n == 8);
    let obj: Box<dyn Op> = Box::new(A);
    assert!(obj.count_to(x, n) == x.wrapping_add(5));
}
#[kani::proof]
fn safe_break_sym_bound_small() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 5);
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    assert!(obj.count_to(x, n) == x.wrapping_add(n));
}
#[kani::proof]
fn bug_while_sym_bound_extra_iteration() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n == 5);
    let obj: Box<dyn Op> = Box::new(A);
    assert!(obj.while_to(x, n) == x.wrapping_add(6));
}
#[kani::proof]
fn safe_while_sym_bound_small() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 5);
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    assert!(obj.while_to(x, n) == x.wrapping_add(n));
}

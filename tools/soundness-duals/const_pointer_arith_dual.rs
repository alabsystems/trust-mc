// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_offset0_arith        -> VERIFICATION:- SUCCESSFUL
//   bug_offset0_arith         -> VERIFICATION:- FAILED (assertion)
//   safe_forward_past_pointee -> VERIFICATION:- SUCCESSFUL
//   bug_forward_past_pointee  -> VERIFICATION:- FAILED (assertion)
//   safe_back_past_pointee    -> VERIFICATION:- SUCCESSFUL
//   bug_back_past_pointee     -> VERIFICATION:- FAILED (assertion)
//   safe_back_to_static_base  -> VERIFICATION:- SUCCESSFUL
//   bug_back_to_static_base   -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A value fact about `*p` describes ONE window. A pointer
// derived from `p` by a known delta addresses another window, and the fact must
// not answer a read there; and a fixed object is known WHOLE, so a read through
// `p + d` reads a determined cell, not a free one. The rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (round-10 challenge, 30 s per harness, ay
// 48c98a43d): on the CHC lane `*ONE.add(1) == 1` PROVED (the fact about `*ONE`
// was copied to `ONE + 1`, at offset ZERO), and `safe_offset0_arith` /
// `safe_forward_past_pointee` FAILED certified Genuine (only the named window
// was seeded). A prototype that decoded the window correctly but kept copying
// the fact turned `*E.add(1) == 2` from a correct refutation into a PROOF.

#![allow(dead_code)]

const ONE: &u32 = &[1u32, 2, 3][0];
const E: &u32 = &[1u32, 2, 3][1];
#[repr(C)]
struct PairC {
    x: u32,
    y: u32,
}
static PAIR: PairC = PairC { x: 1, y: 2 };
const F1: &u32 = &PAIR.y;

#[kani::proof]
fn safe_offset0_arith() {
    assert!(unsafe { *(ONE as *const u32).add(1) } == 2);
}

#[kani::proof]
fn bug_offset0_arith() {
    assert!(unsafe { *(ONE as *const u32).add(1) } == 1);
}

#[kani::proof]
fn safe_forward_past_pointee() {
    assert!(unsafe { *(E as *const u32).add(1) } == 3);
}

#[kani::proof]
fn bug_forward_past_pointee() {
    assert!(unsafe { *(E as *const u32).add(1) } == 2);
}

#[kani::proof]
fn safe_back_past_pointee() {
    assert!(unsafe { *(E as *const u32).sub(1) } == 1);
}

#[kani::proof]
fn bug_back_past_pointee() {
    assert!(unsafe { *(E as *const u32).sub(1) } == 2);
}

#[kani::proof]
fn safe_back_to_static_base() {
    assert!(unsafe { *(F1 as *const u32).sub(1) } == 1);
}

#[kani::proof]
fn bug_back_to_static_base() {
    assert!(unsafe { *(F1 as *const u32).sub(1) } == 2);
}

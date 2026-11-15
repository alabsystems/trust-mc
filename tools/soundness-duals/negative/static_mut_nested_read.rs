// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: reading a `static mut`, plain and through a nested static ref.
//
// Audit evidence: soundness/static-mut-read-bmc-false-failure. In the BMC lane
// `read_initial_plain_static_mut` and `read_initial_through_static_ref` report
// FAILED with [AY:CTREX_CAT:Genuine] (operand_ref.rs refuses mutable statics,
// so the initializer is unmodelled); the CHC lane proves both. The must-fail
// harnesses pin the missed-bug direction (soundness/static-mut-stale-read-dual).
//
// Oracle (per harness):
//   read_initial_plain_static_mut_safe      -> VERIFICATION:- SUCCESSFUL
//   read_initial_through_static_ref_safe    -> VERIFICATION:- SUCCESSFUL
//   nested_write_then_read_safe             -> VERIFICATION:- SUCCESSFUL
//   nested_read_wrong_initial_must_fail     -> VERIFICATION:- FAILED (assertion)
//   nested_write_then_stale_read_must_fail  -> VERIFICATION:- FAILED (assertion)
//   plain_write_then_stale_read_must_fail   -> VERIFICATION:- FAILED (assertion)

#![allow(static_mut_refs)]

static mut FOO: &mut i32 = &mut 12;
static mut X: i32 = 12;

#[kani::proof]
fn read_initial_plain_static_mut_safe() {
    unsafe { assert!(X == 12) };
}

#[kani::proof]
fn read_initial_through_static_ref_safe() {
    unsafe { assert!(*FOO == 12) };
}

#[kani::proof]
fn nested_write_then_read_safe() {
    unsafe {
        *FOO = 13;
        assert!(*FOO == 13);
    }
}

#[kani::proof]
fn nested_read_wrong_initial_must_fail() {
    unsafe { assert!(*FOO == 13) };
}

#[kani::proof]
fn nested_write_then_stale_read_must_fail() {
    unsafe {
        *FOO = 13;
        assert!(*FOO == 12);
    }
}

#[kani::proof]
fn plain_write_then_stale_read_must_fail() {
    unsafe {
        X = 13;
        assert!(X == 12);
    }
}

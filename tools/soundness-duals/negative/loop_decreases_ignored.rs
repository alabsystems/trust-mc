// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z loop-contracts
//
// NEGATIVE PACK: `#[kani::loop_decreases]` shapes the BMC lane silently drops.
//
// Audit evidence: kani-middle/loop-decreases and kani-surface/attr-loop-decreases.
// The CHC lane fails closed on unsupported measures (codegen_function.rs
// failing VC); the default BMC lane has no such gate, so a struct-field or
// multi-dimensional (tuple) measure is dropped and upstream
// expected/loop-contract/fixme_decreases_struct_field.rs and
// fixme_multi_dim_decreases.rs scored as missed bugs on BMC (2026-09-08 corpus).
//
// The must-fail harnesses carry a measure that NEVER decreases, so the
// termination obligation is genuinely violated on the first iteration. The
// safe twins are the upstream fixme shapes with a correct measure: a proof is
// right, a fail-closed non-Genuine refusal is tolerated, a Genuine
// counterexample is a false failure.
//
// Oracle (per harness):
//   identity_measure_not_decreasing_must_fail    -> VERIFICATION:- FAILED (loop decreases)
//   struct_field_measure_not_decreasing_must_fail -> VERIFICATION:- FAILED (loop decreases)
//   multi_dim_measure_not_decreasing_must_fail   -> VERIFICATION:- FAILED (loop decreases)
//   struct_field_measure_decreasing_safe         -> NOT-GENUINE (SUCCESSFUL preferred)
//   multi_dim_measure_decreasing_safe            -> NOT-GENUINE (SUCCESSFUL preferred)

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

struct Counter {
    val: u8,
    steps: u8,
}

#[kani::proof]
fn identity_measure_not_decreasing_must_fail() {
    let x: u8 = 5;
    let mut k: u8 = 0;
    #[kani::loop_invariant(k <= 3 && x == 5)]
    #[kani::loop_decreases(x)]
    while k < 3 {
        k += 1;
    }
    assert!(k == 3);
}

#[kani::proof]
fn struct_field_measure_not_decreasing_must_fail() {
    let mut c = Counter { val: 5, steps: 0 };
    #[kani::loop_invariant(c.steps <= 3 && c.val == 5)]
    #[kani::loop_decreases(c.val)]
    while c.steps < 3 {
        c.steps += 1;
    }
    assert!(c.steps == 3);
}

#[kani::proof]
fn multi_dim_measure_not_decreasing_must_fail() {
    let n: u8 = 5;
    let i: u8 = 0;
    let j: u8 = 0;
    let mut k: u8 = 0;
    #[kani::loop_invariant(k <= 3 && i == 0 && j == 0)]
    #[kani::loop_decreases(n - i, n - j)]
    while k < 3 {
        k += 1;
    }
    assert!(k == 3);
}

#[kani::proof]
fn struct_field_measure_decreasing_safe() {
    let mut c = Counter { val: kani::any_where(|i| *i >= 1 && *i <= 20), steps: 0 };
    #[kani::loop_invariant(c.val >= 1)]
    #[kani::loop_decreases(c.val)]
    while c.val > 1 {
        c.val -= 1;
        c.steps = c.steps.wrapping_add(1);
    }
    assert!(c.val == 1);
}

#[kani::proof]
fn multi_dim_measure_decreasing_safe() {
    let n: u8 = kani::any_where(|i| *i >= 1 && *i <= 5);
    let mut i: u8 = 0;
    let mut j: u8 = 0;
    #[kani::loop_invariant(i <= n && j <= n)]
    #[kani::loop_decreases(n - i, n - j)]
    while i < n {
        if j < n {
            j += 1;
        } else {
            i += 1;
            j = 0;
        }
    }
    assert!(i == n);
}

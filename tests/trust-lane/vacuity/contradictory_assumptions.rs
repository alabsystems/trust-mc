// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// V4 vacuity, both lanes, both routes. A harness whose assumptions are
// contradictory verifies NOTHING: every check under them is unreachable, so a
// clean green proof there is fail-OPEN on the project's own default
// (`--allow-vacuous`'s help: a vacuous harness is a FAILURE unless relaxed).
//
// Measured before the CHC-side probe existed (parity-1 third review, finding
// 8.6): BMC reported `VERIFICATION:- VACUOUS` with every check
// `Status: UNREACHABLE`, and CHC reported `VERIFICATION:- SUCCESSFUL`,
// `[AY:PROOF] CHC verification: property proven`, `[AY:PROOF_QUALIFIERS:clean]`
// and every check `Status: SUCCESS` — the same source program, opposite
// verdicts. The gate keys on `classify_vacuity`, which looks for UNREACHABLE
// checks; the CHC lane never produced that shape because its compiler-side
// straight-line discharge decides reachability STRUCTURALLY and cannot see a
// semantic contradiction.
//
// Every `vac_*_vacuous` harness below asserts `1 + 1 == 3` under assumptions no
// value satisfies. It must never be SUCCESSFUL in either lane on either route.
// The reachable controls pin the other direction: the probe must not turn a
// real proof into a vacuity report.
#![allow(unused)]

// A NaN that is also greater than zero: IEEE says an unordered comparison is
// false for every NaN, so nothing satisfies both.
#[kani::proof]
fn vac_contradictory_nan_vacuous() {
    let x: f32 = kani::any();
    kani::assume(x.is_nan() && x > 0.0);
    assert!(1 + 1 == 3);
}

// The contradiction is only visible THROUGH the min/max relation: `x.max(1.0)`
// is at least 1.0 for every non-NaN x, so it can never be negative.
#[kani::proof]
fn vac_contradictory_relation_vacuous() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    let m = x.max(1.0);
    kani::assume(m < 0.0);
    assert!(1 + 1 == 3);
}

// The contradiction is only visible THROUGH the float-to-int cast: `NaN as i32`
// saturates to 0, never 5.
#[kani::proof]
fn vac_contradictory_cast_vacuous() {
    let x: f32 = kani::any();
    kani::assume(x.is_nan());
    kani::assume((x as i32) == 5);
    assert!(1 + 1 == 3);
}

// Plain arithmetic, no floats: the simplest shape of the same defect.
#[kani::proof]
fn vac_contradictory_int_vacuous() {
    let x: u8 = kani::any();
    kani::assume(x > 200);
    kani::assume(x < 100);
    assert!(1 + 1 == 3);
}

// The control: the same assumption SHAPE, satisfiable, and the property really
// holds. A vacuity probe that fired here would make every clamp proof vacuous.
#[kani::proof]
fn vac_reachable_holds() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    let m = x.max(1.0);
    kani::assume(m < 2.0);
    assert!(m >= 1.0 && m < 2.0);
}

// A second control with no floats in it at all.
#[kani::proof]
fn vac_reachable_int_holds() {
    let x: u8 = kani::any();
    kani::assume(x > 10);
    kani::assume(x < 20);
    assert!(x > 10 && x < 20);
}

// A reachable harness whose property is FALSE: the probe must not mask a real
// counterexample by re-statusing checks it did not decide.
#[kani::proof]
fn vac_reachable_but_false_refuted() {
    let x: u8 = kani::any();
    kani::assume(x > 10);
    kani::assume(x < 20);
    assert!(x > 15);
}

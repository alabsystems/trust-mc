// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `<[T; N]>::contains`, a stub, under a
//! declared unwind bound smaller than the std loop's trip count
//! (fix/chc-walker-fail-closed, repair round 4: the class of walker
//! fail-closed review 6 round 3 finding 6). CHC lane only: the BMC lane is
//! INCONCLUSIVE (UndecidedModel) on both rows on main and on the branch.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   u1_slice_contains_u2_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u1_slice_contains_u10_safe   -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. As `model_call_unwind_dual.rs`: the bug row verified
//! clean on main's CHC lane; the modelled call now states Kani's unwinding
//! assertion, uncertified (`codegen_call.rs`, `model_call_unwinding_check`),
//! and the safe row is the measured precision cost.

#[kani::proof]
#[kani::unwind(2)]
fn u1_slice_contains_u2_bug() {
    let x: u8 = kani::any();
    let a = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let _ = a.contains(&x);
}

#[kani::proof]
#[kani::unwind(10)]
fn u1_slice_contains_u10_safe() {
    let x: u8 = kani::any();
    let a = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let _ = a.contains(&x);
}

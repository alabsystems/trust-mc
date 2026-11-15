// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the trip-count bound of a modelled
//! integer `pow` under a declared unwind bound, at its boundary
//! (fix/chc-walker-fail-closed, repair round 4: the class of walker
//! fail-closed review 6 round 3 finding 6).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   b1_pow_e16_u4_bug            -> VERIFICATION:- FAILED  ('unwinding assertion loop 1')
//!   b1_pow_e16_u5_safe           -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. A modelled call whose callee may loop states Kani's
//! unwinding assertion as `bound < U ∨ t` (`codegen_call_model_unwind.rs`).
//! Exponentiation by squaring runs one pass per bit of the exponent and
//! leaves its `loop` from the middle of the last one, so its back edge is
//! taken `bit_length(exp) - 1` times: `exp = 16` (5 bits) fails under
//! `unwind(4)` and passes under `unwind(5)` (measured on Kani for exp in
//! 1..=32 and U in 1..=6, `probes/g1_pow_grid.rs`; the rule is stated as
//! `exp < 2^U`). CHC only: the BMC lane is INCONCLUSIVE (UndecidedModel) on
//! both rows on main and on the branch. The safe row is a false failure on
//! main's CHC lane too (a translation drop in `wrapping_pow`), so it guards
//! the bound only once that drop is gone; the bug row guards the check.

#[kani::proof]
#[kani::unwind(4)]
fn b1_pow_e16_u4_bug() {
    let x: i32 = kani::any();
    let e: u32 = kani::any();
    kani::assume(e == 16);
    let _ = x.wrapping_pow(e);
}

#[kani::proof]
#[kani::unwind(5)]
fn b1_pow_e16_u5_safe() {
    let x: i32 = kani::any();
    let e: u32 = kani::any();
    kani::assume(e == 16);
    let _ = x.wrapping_pow(e);
}

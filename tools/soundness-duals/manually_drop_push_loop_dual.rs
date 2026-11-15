// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PRECISION DUAL -- a harness loop pushing through `ManuallyDrop::deref_mut`
//! with no declared unwind, beside a cheap harness the same file must still
//! decide (fix/chc-walker-fail-closed, repair round 2, walker fail-closed
//! review 6 round 2 finding 5; the review's probe `rp10b_m15_nounwind.rs`,
//! promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3 with `--default-unwind 5`,
//! measured 2026-09-28; without a bound Kani does not terminate on the first
//! row, CBMC unwinding the range loop past 5,900 iterations):
//!   m15_push_cap_sym_nounwind_bug -> VERIFICATION:- FAILED  ('assertion failed: md.capacity() == 1')
//!   s1_scalar_deref_safe          -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. On the repair-round-1 bundle 8626027c the first
//! harness's translation finished, and the straightline prover
//! (`chc/straightline_proof.rs`) then re-applied every (rule, frame) firing
//! in every saturation round, without polling any deadline: the compile
//! timed out at 154 s (CompileTimeout) and took the file's other harnesses
//! with it; main decides the file in about 10 s. Each firing is now applied
//! once, and the prover declines past its own 5 s wall budget or the
//! translation deadline.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s manually_drop_push_loop_dual.rs

use std::mem::ManuallyDrop;

#[kani::proof]
fn m15_push_cap_sym_nounwind_bug() {
    let n: u8 = kani::any();
    kani::assume(n >= 1 && n <= 3);
    let mut md = ManuallyDrop::new(Vec::<u8>::with_capacity(1));
    for i in 0..n {
        md.push(i);
    }
    assert!(md.capacity() == 1);
}

#[kani::proof]
fn s1_scalar_deref_safe() {
    let x: u32 = kani::any();
    let md = ManuallyDrop::new(x);
    assert!(*md == x);
}

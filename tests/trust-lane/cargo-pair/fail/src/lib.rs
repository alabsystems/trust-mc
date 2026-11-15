// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 cargo pair, failing half. The same build script and proc-macro dependency,
//! with a sum limit of 150 that a = b = 99 reaches: a reachable user assertion.
//! A second harness outruns `#[kani::unwind(3)]`, so its unwinding assertion
//! fails; with `--no-unwinding-checks` it would report SUCCESSFUL, which is the
//! engine flag the smoke's wrapper case tries to smuggle in.
//! Expected: VERIFICATION:- FAILED for both harnesses.

#[cfg(not(pair_build_script_ran))]
compile_error!("the build script did not run");

include!(concat!(env!("OUT_DIR"), "/bound.rs"));
pair_macros::sum_limit!(150);

#[cfg(kani)]
mod verification {
    use super::{OPERAND_BOUND, SUM_LIMIT};

    #[kani::proof]
    fn bounded_add_reaches_the_macro_limit() {
        let a: u8 = kani::any();
        let b: u8 = kani::any();
        kani::assume(a < OPERAND_BOUND && b < OPERAND_BOUND);
        let sum = a + b;
        assert!(sum < SUM_LIMIT, "sum reaches the macro limit");
    }

    #[kani::proof]
    #[kani::unwind(3)]
    fn loop_runs_past_its_unwind_bound() {
        let mut i: u32 = 0;
        while i < 10 {
            i += 1;
        }
        assert!(i < 10, "the loop ran to 10");
    }
}

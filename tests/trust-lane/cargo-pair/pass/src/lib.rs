// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 cargo pair, passing half. The operand bound comes from the build script and
//! the sum limit from the proc-macro dependency, so no verdict exists unless both
//! host units were built and ran. Both operands are below 100, so the sum cannot
//! overflow and stays below the limit of 200.
//! Expected: VERIFICATION:- SUCCESSFUL.

#[cfg(not(pair_build_script_ran))]
compile_error!("the build script did not run");

include!(concat!(env!("OUT_DIR"), "/bound.rs"));
pair_macros::sum_limit!(200);

#[cfg(kani)]
mod verification {
    use super::{OPERAND_BOUND, SUM_LIMIT};

    #[kani::proof]
    fn bounded_add_is_below_the_macro_limit() {
        let a: u8 = kani::any();
        let b: u8 = kani::any();
        kani::assume(a < OPERAND_BOUND && b < OPERAND_BOUND);
        assert!(a + b < SUM_LIMIT);
    }
}

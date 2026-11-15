// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A loop-contract harness whose single lane FAILS, so the driver's two-lane
//! loop-contract retry is eligible for it (`loop_two_lane::harness_is_eligible`
//! reads the obligation messages out of the `.vc.json`).
//!
//! The invariant is perfectly inductive and still cannot carry the harness's
//! assertion — under the abstraction the normal loop exit stays reachable — so
//! the first lane reports FAILED. That is the case the two-lane retry exists
//! for, and the case the Trustc route cannot take: the lanes set engine
//! environment knobs on child drivers and this route carries no engine knob to
//! the engine. The smoke requires the route to say so BY NAME, and to leave the
//! single-lane verdict alone, rather than starting a lane it will refuse and
//! printing the child's refusal inside its own diagnostic.

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

fn find_five(arr: &[i32; 5]) -> Option<usize> {
    let mut lo: usize = 0;
    let mut hi: usize = arr.len();

    #[kani::loop_invariant(lo <= hi && hi <= arr.len())]
    #[kani::loop_decreases(hi - lo)]
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if arr[mid] == 5 {
            return Some(mid);
        } else if arr[mid] < 5 {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    None
}

#[kani::proof]
fn loop_contract_retry_harness() {
    let arr = [1, 3, 5, 7, 9];
    assert!(find_five(&arr) == Some(2));
}

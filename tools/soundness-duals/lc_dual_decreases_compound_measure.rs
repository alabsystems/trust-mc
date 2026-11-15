// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: -Z loop-contracts
//
// A `#[kani::loop_decreases]` measure the CHC lane does not encode.
//
// `hi - lo` lowers to a two-block closure (the subtraction's overflow Assert),
// which `instrument_loop_decreases` rejects (guard 6) unless
// TRUST_MC_COMPOUND_DECREASES=1. The register call then survives and CHC
// codegen substitutes a failing VC. That VC is a refusal, not a ranking
// counterexample, yet the CHC lane certified it [AY:CTREX_CAT:Genuine] while the
// BMC lane's identical stub records an unsupported-construct fallback and reports
// EncodingGap. tests/expected/loop-contract/decreases_binary_search.rs was a
// false positive that way (Kani: SUCCESSFUL).
//
// Oracles (each measured with the corpus-rev Kani, 4c0fce8c3, 2026-09-15):
//   compound_measure_binary_search_safe          SUCCESSFUL
//   compound_measure_not_decreasing_must_fail    FAILED ("Check variant decreases after step")
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

fn binary_search(arr: &[i32; 5], target: i32) -> Option<usize> {
    let mut lo: usize = 0;
    let mut hi: usize = arr.len();

    #[kani::loop_invariant(lo <= hi && hi <= arr.len())]
    #[kani::loop_decreases(hi - lo)]
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    None
}

#[kani::proof]
fn compound_measure_binary_search_safe() {
    let arr = [1, 3, 5, 7, 9];
    let result = binary_search(&arr, 5);
    assert!(result == Some(2));
}

#[kani::proof]
fn compound_measure_not_decreasing_must_fail() {
    let mut lo: usize = 0;
    let mut hi: usize = 4;
    #[kani::loop_invariant(lo <= hi && hi <= 8)]
    #[kani::loop_decreases(hi - lo)]
    while lo < hi && hi < 8 {
        lo = lo + 1;
        hi = hi + 1;
    }
    assert!(lo <= hi);
}

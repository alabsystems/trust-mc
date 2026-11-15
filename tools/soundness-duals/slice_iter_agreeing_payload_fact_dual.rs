// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A slice `for` loop under `#[kani::unwind]`: unwinding duplicates both the
// `Iterator::next` call `_39 = next(..)` and the payload copy
// `_42 = copy ((_39 as Some).0)` into every unwound body. The `next` stub's
// value fact on `_39` is its own payload slot variable, the same term for every
// producer, but `propagate_ref_metadata` dropped it for the duplicated
// producer, and the fix/collections2 guard then failed `*_42` closed.
//
// Measured 2026-09-15 on bundle-m3 (main 498d0c80f), CHC lane: every harness
// below recorded `deref_value_fact_dropped` and ended `[AY:CTREX_CAT:Unknown]`
// (kani/SwitchInt/main.rs: 3.4 s encoding_gap before the guard, 49 s unknown
// after it).
//
// Oracles, each confirmed with Kani 0.67.0:
//   safe_unwound_single_element_match           SUCCESSFUL -> NOT_GENUINE
//   safe_unwound_second_element_match           SUCCESSFUL -> NOT_GENUINE
//   safe_unwound_sum_of_elements                SUCCESSFUL -> NOT_GENUINE
//   bug_unwound_single_element_mismatch         FAILED
//   bug_unwound_sum_claims_first_element_twice  FAILED (a kept fact that read
//                                               a stale element would give 10)
//
// The fix keeps the fact when every producer agrees and the source cannot change
// under the copy (codegen_stmt_payload_value_fact.rs); ambiguous producers keep
// failing closed (slice_iter_unwound_payload_deref_dual.rs).

fn first_match(xs: &[i32], want: i32) -> i32 {
    for i in xs.iter() {
        if *i == want {
            return 1;
        }
    }
    2
}

#[kani::proof]
#[kani::unwind(2)]
fn safe_unwound_single_element_match() {
    assert!(first_match(&[99], 99) == 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_unwound_second_element_match() {
    assert!(first_match(&[5, 99], 99) == 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_unwound_sum_of_elements() {
    let a: &[i32] = &[5, 7];
    let mut sum = 0;
    for e in a {
        sum += *e;
    }
    assert!(sum == 12);
}

#[kani::proof]
#[kani::unwind(2)]
fn bug_unwound_single_element_mismatch() {
    assert!(first_match(&[98], 99) == 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_unwound_sum_claims_first_element_twice() {
    let a: &[i32] = &[5, 7];
    let mut sum = 0;
    for e in a {
        sum += *e;
    }
    assert!(sum == 10);
}

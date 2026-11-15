// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A slice `for` loop reads its element through the `Option<&T>` payload of the
// slice `Iterator::next` stub, which holds the ELEMENT, not an address.
// `*payload` resolves only through a `const_ref_values` fact. Loop unwinding
// gives `_11 = copy ((_5 as Some).0)` one producer per unwound copy, so that
// fact was dropped, and `*_11` became a Mem-level load at an "address" equal to
// the element's value: a memory cell no rule wrote.
//
// Measured 2026-09-15 on the fix/collections2 merge (CHC, dev-cli), once the
// kept `_6 = &mut _4` points-at edge let the stub run instead of failing closed:
//  * expected/loop-backedge/test.rs (Kani SUCCESSFUL) FAILED
//    `[AY:CTREX_CAT:Genuine]` on `assertion failed: e == 0`, and every safe
//    harness below did the same. Expectation NOT_GENUINE: a counterexample over
//    the unconstrained load may be reported, never certified.
//  * `bug_slice_for_element_claimed_zero` MUST FAIL: `[0, 1]` has a non-zero
//    element, so the fail-closed deref must not hide it.
//
// The fix records a reference whose value fact was dropped for an ambiguous
// producer, and a deref through it fails closed (translation drop,
// `deref_value_fact_dropped`), so a SAT result classifies EncodingGap.

#[kani::proof]
#[kani::unwind(3)]
fn safe_slice_for_by_pattern() {
    let a: &[i32] = &[0, 0];
    for &e in a {
        assert_eq!(e, 0);
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_slice_for_by_reference() {
    let a: &[i32] = &[0, 0];
    for e in a {
        assert_eq!(*e, 0);
    }
}

#[kani::proof]
#[kani::unwind(4)]
fn safe_slice_for_nonzero_elements() {
    let a: &[i32] = &[5, 7];
    for &e in a {
        assert!(e == 5 || e == 7);
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_loop_backedge_nested_range() {
    let a: &[i32] = &[0, 0];
    for &e in a {
        assert_eq!(e, 0);
        for i in e..1 {
            assert_eq!(i, 0);
        }
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_slice_for_element_claimed_zero() {
    let a: &[i32] = &[0, 1];
    for &e in a {
        assert_eq!(e, 0);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The LIVENESS boundary of the kept slice-iterator payload value fact
// (codegen_stmt_payload_value_fact.rs condition 4, and
// codegen_stmt_payload_value_liveness.rs).
//
// `for &e in a` reads the payload through a temp rustc brackets NOWHERE:
//
//     bb5: _10 = copy ((_5 as Some).0: &i32);   // the payload copy
//          _8  = copy (*_10);                   // the `&e` binding reads it
//
// so the storage-marker form of condition 4 killed nothing, the loop backedge
// carried the copy into the `next` call again, and the fact was dropped for
// every pattern-binding loop — `expected/loop-backedge/test.rs` and the four
// safe harnesses of slice_iter_unwound_payload_deref_dual.rs among them —
// although each unwound copy reads its own payload before the next call runs.
// `for e in a`, whose binding IS the copy and IS bracketed, kept it.
//
// The two shapes below are the two sides of the boundary:
//   * `pattern_binding_*`: the copy is DEAD at the next `next` call, so the fact
//     is kept and every obligation of the loop is PROVED. Measured 2026-09-18:
//     all six checks SUCCESS where the baseline engine returned UNKNOWN. The
//     verdict is still FAILED, because 2 residual translation drops
//     (`drop_fallback`, pre-existing and unrelated to the payload fact) DEMOTE
//     that proof -- so the expectation is NOT_GENUINE, not SUCCESSFUL.
//   * `payload_kept_across_next_*`: the payload reference is stored in a local
//     that outlives the call, so a carrier is LIVE at the producer and the fact
//     stays dropped — the deref fails closed and no counterexample over it may
//     be certified.
//
// Oracles, each confirmed with the corpus-rev Kani (see the gate manifest).

#[kani::proof]
#[kani::unwind(3)]
fn safe_pattern_binding_sums_elements() {
    let a: &[i32] = &[3, 4];
    let mut s = 0;
    for &e in a {
        s += e;
    }
    assert!(s == 7);
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_pattern_binding_sum_claims_wrong_total() {
    let a: &[i32] = &[3, 4];
    let mut s = 0;
    for &e in a {
        s += e;
    }
    // FALSE: 3 + 4 is 7.
    assert!(s == 8);
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_payload_kept_across_next_not_certified() {
    let a: &[i32] = &[0, 0];
    let mut it = a.iter();
    let mut kept: Option<&i32> = None;
    while let Some(e) = it.next() {
        if let Some(p) = kept {
            assert_eq!(*p, 0);
        }
        kept = Some(e);
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_payload_kept_across_next_claims_zero() {
    let a: &[i32] = &[5, 0];
    let mut it = a.iter();
    let mut kept: Option<&i32> = None;
    while let Some(e) = it.next() {
        // FALSE on the second iteration: the reference kept from the first one
        // points at 5.
        if let Some(p) = kept {
            assert_eq!(*p, 0);
        }
        kept = Some(e);
    }
}

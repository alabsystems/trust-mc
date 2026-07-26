// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Task #77 DUAL (b): the failing check is DATA-INDEPENDENT of the havoc.
//
// The harness makes the SAME unhandled indirect extern call as DUAL (a) — so it
// carries the identical `unhandled_calls` taint — but here the call's result is
// DISCARDED. The assertion that fails reads ONLY the raw symbolic input `x`,
// never the havocked return. The bug (x is unconstrained, so `x >= 100` is
// violable) is real regardless of what the approximation chose, so in principle
// this deserves a certified-Genuine counterexample.
//
// FINDING (Task #77): in the emitted CHC the discarded extern return is a
// normally-named, unconstrained variable that is INDISTINGUISHABLE from the
// constrained input `x`. The driver cannot prove the failing assertion's
// reachability avoids the freed var, so it cannot soundly certify this and it
// correctly stays OverApproximation. DUAL (a) and DUAL (b) are indistinguishable
// to every driver-side syntactic proxy — which is exactly why no sound driver-
// only certification exists. Recovery needs compiler-side plumbing of the freed
// var's SMT identity; see the Task #77 note in ctrex_classify.rs.
extern "C" {
    fn foreign(i: u32) -> u32;
}

fn call_on(input: u32, func: unsafe extern "C" fn(u32) -> u32) -> u32 {
    unsafe { func(input) }
}

#[kani::proof]
fn dual_independent() {
    let x: u32 = kani::any();
    // Havoc present (taints the harness) but its result is discarded.
    let _ = call_on(x, foreign);
    // This failure depends ONLY on the raw symbolic input x, not the havoc.
    assert!(x >= 100);
}

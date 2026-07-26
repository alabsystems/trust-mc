// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Task #77 DUAL (a): the failing check is DATA-DEPENDENT on a havocked value.
//
// `foreign` is passed as an `extern "C"` FUNCTION POINTER through `call_on`, so
// the indirect call trips the `unhandled_calls` sound approximation, which
// leaves the call's return value UNCONSTRAINED (a normally-named CHC var). The
// assertion reads that unconstrained return directly, so the counterexample
// (ret != x) is a pure artifact of the havoc — there is no real reachable bug.
// This MUST stay OverApproximation. Certifying it Genuine is UNSOUND (this is
// the trap the task forbids; it mirrors expected/foreign-function/ffi_ptr.rs).
extern "C" {
    fn foreign(i: u32) -> u32;
}

fn call_on(input: u32, func: unsafe extern "C" fn(u32) -> u32) -> u32 {
    unsafe { func(input) }
}

#[kani::proof]
fn dual_dependent() {
    let x: u32 = kani::any();
    // `call_on(x, foreign)` is the havocked (unconstrained) extern return.
    assert_eq!(call_on(x, foreign), x);
}

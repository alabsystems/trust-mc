// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! `hint::unreachable_unchecked` is kept as a Call by the inline pass and
//! routed to the PanicError stub: reaching it is UB, so it is an obligation.
//! Inlined, its `assert_unsafe_precondition!` expansion pulled
//! `panic_nounwind_fmt::runtime` / `Location::caller` into the harness and the
//! solver came back UNDECIDED on the trivially reachable case below.

#[kani::proof]
fn unreachable_unchecked_guarded_is_fine() {
    let x: u8 = kani::any();
    kani::assume(x < 3);
    if x == 3 {
        unsafe { std::hint::unreachable_unchecked() }
    }
    // A reachable check, so the harness is not vacuous (V4 gate).
    assert!(x < 3);
}

// Deliberately reachable (x == 3 is not assumed away) — must FAIL.
#[kani::proof]
fn unreachable_unchecked_reached_fails() {
    let x: u8 = kani::any();
    if x == 3 {
        unsafe { std::hint::unreachable_unchecked() }
    }
}

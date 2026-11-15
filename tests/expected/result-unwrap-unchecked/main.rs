// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! `Result::unwrap_unchecked` is MIR-inlined by the inline pass (no stub can
//! fire); its `Err` arm lowers to `hint::unreachable_unchecked`, which is now
//! a kept Call with a PanicError obligation. Before that the inlined
//! precondition-check machinery left an unsupported `Call terminator` and the
//! Err case was INCONCLUSIVE instead of a reported UB.

#[kani::proof]
fn unwrap_unchecked_on_ok() {
    let r: Result<u8, u8> = Ok(3);
    assert_eq!(unsafe { r.unwrap_unchecked() }, 3);
}

// Deliberately UB: `unwrap_unchecked` on `Err` — must FAIL.
#[kani::proof]
fn unwrap_unchecked_on_err_is_ub() {
    let r: Result<u8, u8> = Err(3);
    let _ = unsafe { r.unwrap_unchecked() };
}

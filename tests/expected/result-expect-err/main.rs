// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! `Result::expect_err` is kept as a Call by the inline pass and routed to the
//! ResultUnwrapErr stub, which extracts the Err payload AND records the
//! panic-on-Ok obligation. Inlined, the library body dragged `unwrap_failed`'s
//! Debug formatting into the harness: `Err(3u8).expect_err("x") == 3` was
//! demoted (`unconstrained_assignment=6`) and could never PROVE.

#[kani::proof]
fn expect_err_on_err_returns_payload() {
    let r: Result<u8, u8> = Err(3);
    assert_eq!(r.expect_err("expected Err"), 3);
}

#[kani::proof]
fn expect_err_symbolic_payload() {
    let e: u8 = kani::any();
    let r: Result<u8, u8> = Err(e);
    assert_eq!(r.expect_err("expected Err"), e);
}

// Deliberately broken: `expect_err` on `Ok` panics — must FAIL.
#[kani::proof]
fn expect_err_on_ok_panics() {
    let r: Result<u8, u8> = Ok(3);
    let _ = r.expect_err("expected Err");
}

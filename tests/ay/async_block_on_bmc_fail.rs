// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-verify-fail
// kani-expect: CTREX
//
// compile-flags: --edition 2021
// kani-flags: -Z async-lib
//
//! The broken twins of `async_block_on_bmc.rs` — discriminating controls in the
//! failing direction:
//!
//! * `awaited_value_broken` — the awaited value CAN be 10, so `y < 10` must be
//!   a genuine counterexample, never an unreachable (vacuously proved) check;
//! * `pending_forever_is_loud` — a future that never becomes Ready: the
//!   busy-poll loop is cut by the unwind bound and that cut must FAIL as an
//!   unwinding assertion, never be silently pruned into a proof.

async fn add_one(x: u8) -> u8 {
    x + 1
}

struct Never;

impl std::future::Future for Never {
    type Output = ();
    fn poll(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<()> {
        std::task::Poll::Pending
    }
}

#[kani::proof]
#[kani::unwind(2)]
async fn awaited_value_broken() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    let y = add_one(x).await;
    assert!(y < 10);
}

#[kani::proof]
#[kani::unwind(2)]
async fn pending_forever_is_loud() {
    Never.await;
}

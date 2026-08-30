// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
// compile-flags: --edition 2021
// kani-flags: -Z async-lib
//
//! BMC drives `kani::block_on` itself: the executor is MIR-inlined into the
//! harness, its busy-poll loop is unrolled under the unwind bound, and the
//! awaited assertion is a REACHABLE obligation of the harness (not vacuous).
//!
//! Before this landed the inline pass preserved every `block_on` call for the
//! CHC specializer, the DAG-only statement mini-inliner then refused the poll
//! LOOP, and every `async fn` harness bailed as an unsupported `Call
//! terminator` with zero obligations — `INCONCLUSIVE (no checks)`.
//!
//! The deliberately broken twin lives in `async_block_on_bmc_fail.rs`.

async fn add_one(x: u8) -> u8 {
    x + 1
}

/// Pending once, then Ready(7): the poll loop must genuinely iterate.
struct ReadyOnSecondPoll {
    polled: bool,
}

impl std::future::Future for ReadyOnSecondPoll {
    type Output = u8;
    fn poll(
        mut self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<u8> {
        if self.polled {
            std::task::Poll::Ready(7)
        } else {
            self.polled = true;
            std::task::Poll::Pending
        }
    }
}

#[kani::proof]
#[kani::unwind(2)]
async fn awaited_value_holds() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    let y = add_one(x).await;
    assert!(y < 11);
}

#[kani::proof]
#[kani::unwind(2)]
async fn ready_on_second_poll_holds() {
    let v = ReadyOnSecondPoll { polled: false }.await;
    assert!(v == 7);
}

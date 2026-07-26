// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// kani-flags: -Z loop-contracts

//! Check that `loop_decreases` is recognized but rejected until termination
//! semantics are implemented.

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn loop_decreases_unsupported() {
    let mut x: u8 = 3;

    #[kani::loop_decreases(x)]
    while x > 0 {
        x -= 1;
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: -Z loop-contracts
//
// The loop-contract retry must judge the harness it retries and no other.
//
// The retry runs a child driver per harness with `--harness <name>`, and the
// filter matches substrings. `skip_bug` is a substring of `skip_bug_twin_ok`,
// so before AY alignment review round 3 the child for `skip_bug` also checked
// the twin, and the parent read the twin's SUCCESSFUL line (and its obligation
// text) as the retry's own: `skip_bug` was printed SUCCESSFUL over its own
// counterexample, certified Genuine, in both lanes, on main's bundle and the
// branch alike. The child now gets `--exact`, and the parent accepts a child
// only if it checked exactly the harness being retried.
//
// Oracles (Kani 0.67.0, measured 2026-09-28):
//   skip_bug          MUST FAIL    (the loop is not entered, x stays 7)
//   skip_bug_twin_ok  NOT-GENUINE  (Kani SUCCESSFUL: same loop, no assertion)
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn skip_bug() {
    let mut x: u8 = 7;
    #[kani::loop_invariant(x != 7)]
    while x > 7 {
        x = 6;
    }
    assert!(x == 6);
}

#[kani::proof]
fn skip_bug_twin_ok() {
    let mut x: u8 = 7;
    #[kani::loop_invariant(x != 7)]
    while x > 7 {
        x = 6;
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Regression for a verifier CRASH, plus a must-fail twin.
//
// tests/expected/loop-contract/while_let_loop_for_slice.rs under
// `-Z loop-contracts` on the BMC lane aborted the compiler with
// `thread 'rustc' has overflowed its stack` (SIGABRT, measured 2026-09-13 and
// 2026-09-14): `ensure_derived_pointee_in_env` followed a `ref_pointees`
// chain that loops back on itself (`bytes = rest` re-points the slice
// reference at a sub-slice of its own pointee) and recursed without bound.
//
// Oracle: `trim_ascii_start_shape` is SUCCESSFUL under Kani; this file only
// requires it NOT to crash and never to be certified Genuine
// (`expected = NOT_GENUINE` in the manifest). `bug_after_loop_len_unchanged`
// MUST FAIL: when a[0] is ASCII whitespace the loop strips it, so the slice
// is shorter than the array.

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

#[kani::proof]
fn trim_ascii_start_shape() {
    let a: [u8; 10] = kani::any();
    let s = a.as_slice();
    let mut bytes = s;
    #[kani::loop_invariant(
            bytes.len() <= s.len() &&
            (bytes.len() == 0 || (&s[s.len()-bytes.len()..]).as_ptr() == bytes.as_ptr())
    )]
    while let [first, rest @ ..] = bytes {
        if first.is_ascii_whitespace() {
            bytes = rest;
        } else {
            break;
        }
    }
}

#[kani::proof]
fn bug_after_loop_len_unchanged() {
    let a: [u8; 10] = kani::any();
    let s = a.as_slice();
    let mut bytes = s;
    #[kani::loop_invariant(bytes.len() <= s.len())]
    while let [first, rest @ ..] = bytes {
        if first.is_ascii_whitespace() {
            bytes = rest;
        } else {
            break;
        }
    }
    assert!(bytes.len() == 10);
}

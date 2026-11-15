// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PRECISION DUAL (one file, decided as a whole) -- `any` / `all` / `find`
//! with a closure whose result folds to a constant, walked by the CHC
//! walker (fix/chc-walker-fail-closed, repair round 3, walker fail-closed
//! review 6 round 3 finding 3; the review's probes `q10_any_shapes.rs` and
//! `q6_closure_helpers.rs`'s `h02` / `h03` / `h15`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   a1_all_concrete_array_safe          -> VERIFICATION:- SUCCESSFUL
//!   a2_any_symbolic_elem_safe           -> VERIFICATION:- SUCCESSFUL
//!   a3_any_const_false_closure_safe     -> VERIFICATION:- SUCCESSFUL
//!   h02_iter_any_bug                    -> VERIFICATION:- FAILED  ('*v < 200')
//!   h02_iter_any_safe                   -> VERIFICATION:- SUCCESSFUL
//!   h03_iter_all_bug                    -> VERIFICATION:- FAILED  ('*v < 200')
//!   h15_find_bug                        -> VERIFICATION:- FAILED  ('**v < 200')
//!
//! MECHANISM UNDER TEST. The walker's loop replay refunds a concrete
//! iteration its fuel when the loop's exit test folds to "stay"
//! (`loop_replay.rs`, `refund_concrete_loop_iteration`). It treated any test
//! with an edge out of the loop as the exit test: in `any`'s loop the
//! closure's `if f(x) { return true }` folds to "stay" every pass while
//! `next()`'s test stays symbolic, so every pass was refunded, the replay ran
//! to the SwitchInt depth limit, and hashing its deferred checks as trees did
//! not finish in 600 s: a CompileTimeout that took every harness of the file
//! with it (main decides the file in 10 s). Only the header's own exit test
//! is refunded now; the deferred-check dedup is identity-first and
//! structural only for small terms; and an ordinary replay past 1,000,000
//! written-out nodes fails closed, as the raised and declared ones do.
#[inline(never)]
fn sink<T>(_v: T) {}

#[kani::proof]
fn a1_all_concrete_array_safe() {
    let a = [1u8, 2, 3];
    assert!(a.iter().all(|v| *v < 10));
}

#[kani::proof]
fn a2_any_symbolic_elem_safe() {
    let a = [1u8, 2, kani::any()];
    let r = a.iter().any(|v| *v == 1);
    assert!(r);
}

#[kani::proof]
fn a3_any_const_false_closure_safe() {
    let a = [1u8, 2, kani::any()];
    let r = a.iter().any(|_v| false);
    assert!(!r);
}

#[kani::proof]
fn h02_iter_any_bug() {
    let a = [1u8, 2, kani::any()];
    let r = a.iter().any(|v| {
        assert!(*v < 200);
        false
    });
    sink(r);
}

#[kani::proof]
fn h02_iter_any_safe() {
    let a = [1u8, 2, 3];
    let r = a.iter().any(|v| {
        assert!(*v < 200);
        false
    });
    assert!(!r);
}

#[kani::proof]
fn h03_iter_all_bug() {
    let a = [1u8, 2, kani::any()];
    let r = a.iter().all(|v| {
        assert!(*v < 200);
        true
    });
    sink(r);
}

#[kani::proof]
fn h15_find_bug() {
    let a = [1u8, 2, kani::any()];
    let r = a.iter().find(|v| {
        assert!(**v < 200);
        false
    });
    sink(r);
}

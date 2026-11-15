// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `skip` over an adapter under a
//! declared `#[kani::unwind(U)]`, with the reduction's value unread so the
//! only way to fail is Kani's unwinding assertion (fix/chc-walker-fail-closed,
//! repair round 3, walker fail-closed review 6 round 3 finding 10; the
//! review's probes `q3_sum_impls.rs` `t1` / `t2` / `t3` and
//! `q4_loop_passes.rs` `k1` / `k2`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   t1_skip_filter_unread_bug             -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   t1_skip_filter_unread_n3_safe         -> VERIFICATION:- SUCCESSFUL
//!   t2_skip_past_end_map_unread_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   t3_enumerate_skip_filter_unread_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   k1_skip_past_end_cloned_unread_bug    -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   k2_skip_past_end_copied_unread_safe   -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The reduction unwinding rule table
//! (`codegen_ay/reduce_loop_rule.rs`) gave `Skip<I>` the rule of `I`. But
//! `Skip::fold` first calls `I::nth`, and for `Filter`, `Map` or `Cloned`
//! that is a loop over the inner elements (`find`, or the default
//! `advance_by`) with its own unwinding assertion. `Skip<I>` takes `I`'s rule
//! now only when `I::nth` is index arithmetic (a slice iterator, an `array` /
//! `vec` `IntoIter`, and `Copied` / `Enumerate` of one); any other is the
//! unmeasured shape (the conservative rule). Every bug row fails on main too,
//! but only because an unrelated fail-closed fires (`iter_fold_advance_failed`):
//! the rows keep the rule honest when the adapter advance is modelled.
#[inline(never)]
fn sink<T>(_v: T) {}

#[kani::proof]
#[kani::unwind(4)]
fn t1_skip_filter_unread_bug() {
    let a = [1u8, 2, 3, 4];
    let s = a.iter().filter(|x| **x > 100).skip(1).fold(0u8, |acc, x| acc.wrapping_add(*x));
    sink(s);
    assert!(a[0] == 1);
}

#[kani::proof]
#[kani::unwind(4)]
fn t1_skip_filter_unread_n3_safe() {
    let a = [1u8, 2, 3];
    let s = a.iter().filter(|x| **x > 100).skip(1).fold(0u8, |acc, x| acc.wrapping_add(*x));
    sink(s);
    assert!(a[0] == 1);
}

#[kani::proof]
#[kani::unwind(4)]
fn t2_skip_past_end_map_unread_bug() {
    let a = [1u8, 2, 3, 4];
    let s = a.iter().map(|x| *x).skip(6).fold(0u8, |acc, x| acc.wrapping_add(x));
    sink(s);
    assert!(a[0] == 1);
}

#[kani::proof]
#[kani::unwind(4)]
fn t3_enumerate_skip_filter_unread_bug() {
    let a = [1u8, 2, 3, 4];
    let s = a
        .iter()
        .filter(|x| **x > 100)
        .skip(1)
        .enumerate()
        .fold(0usize, |acc, (i, _)| acc.wrapping_add(i));
    sink(s);
    assert!(a[0] == 1);
}

#[kani::proof]
#[kani::unwind(4)]
fn k1_skip_past_end_cloned_unread_bug() {
    let a = [1u8, 2, 3, 4];
    let s = a.iter().cloned().skip(6).fold(0u8, |acc, x| acc.wrapping_add(x));
    sink(s);
    assert!(a[0] == 1);
}

#[kani::proof]
#[kani::unwind(4)]
fn k2_skip_past_end_copied_unread_safe() {
    let a = [1u8, 2, 3, 4];
    let s = a.iter().copied().skip(6).fold(0u8, |acc, x| acc.wrapping_add(x));
    sink(s);
    assert!(a[0] == 1);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `sum` / `fold` under a declared
//! `#[kani::unwind(U)]`: Kani's unwinding assertion on the std loop the
//! reduction runs (fix/chc-walker-fail-closed, repair round 2, walker
//! fail-closed review 6 round 2 findings 1 and 8; the review's probes
//! `rp2_reduce_unwind.rs` and `rp10_more.rs`, promoted, with the boundary
//! rows that measured each receiver shape's rule).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   u1_sum_past_unwind_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u1_sum_within_unwind_safe     -> VERIFICATION:- SUCCESSFUL
//!   u2_fold_past_unwind_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u3_sum_nine_past_unwind_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u4_iter_sum_past_unwind_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   r1_slice_sum_n5_u5_safe       -> VERIFICATION:- SUCCESSFUL
//!   r2_slice_sum_n5_u4_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   r4_slice_sum_unused_u3_bug    -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   a1_into_fold_n4_u4_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   a2_into_for_n4_u4_bug         -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   a2_into_for_n3_u4_safe        -> VERIFICATION:- SUCCESSFUL
//!   m1_map_fold_n5_u4_bug         -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   m1_map_fold_n5_u5_safe        -> VERIFICATION:- SUCCESSFUL
//!   f1_filter_sum_safe            -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The statement path folds `sum` / `fold` over an
//! addressable iterator as an explicit chain of `bound` steps
//! (`codegen_call_iterator_adapter/fold_precise.rs`). Repair round 1 raised
//! the bound to an array's length `N`, which covered every element and made
//! the unreplayed-step check unreachable, and nothing stated Kani's
//! unwinding assertion on the std `fold` loop: `sum` over five elements under
//! `unwind(3)` verified clean where Kani fails (the `u*` / `r*` bug rows on
//! the repair-round-1 bundle 8626027c). Under a declared bound the chain now
//! stays at `U` steps and the loop's unwinding assertion is a check,
//! `unwinding assertion loop 0`, under the receiver's measured rule
//! (`codegen_ay/reduce_loop_rule.rs`): a slice iterator's do-while `fold`
//! (and `map` / `filter` / `copied` / `cloned` / `enumerate` / `skip` of one)
//! fails once more than `U` elements remain, an `array::IntoIter` or
//! `vec::IntoIter` once `U` remain (`a1`: N = U = 4 fails), any other shape
//! as the latter, uncertified. Without the precise chain (an adapter), the
//! check is uncertified under "the iterator is not empty", unless the
//! array's length bounds the count through the adapter (`m1`). The BMC
//! lane's element-wise unroll had the same hole on every bug row and states
//! the same assertion (`statement/collections/iter_adapters.rs`).
//!
//! `a2`: a `for` loop over the array's own `IntoIter` of at most eight
//! elements was straight-lined by the array-iterator pass
//! (`kani_middle/transform/array_iter.rs`) with no loop left for the bounded
//! unroll to check, a missed bug on main; under a declared bound the chain is
//! used only where the loop stays within it. `a1` (`fold` over the same
//! iterator) is inlined down to `PolymorphicIter::try_fold`, whose model
//! emits no check: INCONCLUSIVE (no checks) on the CHC lane, on main too.
//!
//! `f1_filter_sum_safe`: the chain decomposed an adapter through its `iter`
//! field and folded the INNER elements, unfiltered; its overflow was
//! certified Genuine on main. The chain now folds only a receiver that is
//! the element sequence.
//!
//! Note: `a.into_iter()` on an array is the slice iterator in this file's
//! edition (2015); `IntoIterator::into_iter(a)` is the array's own.
//!
//! Lane scope: CHC and BMC.
//!
//! Run: trust-mc-driver [--ay-chc] -Z unstable-options --harness-timeout=30s walker_reduce_unwind_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

#[kani::proof]
#[kani::unwind(3)]
fn u1_sum_past_unwind_bug() {
    let a: [u8; 5] = [1, 1, 1, 1, kani::any()];
    kani::assume(a[4] < 10);
    let s: u8 = a.iter().sum();
    assert!(s >= 4);
}

#[kani::proof]
#[kani::unwind(7)]
fn u1_sum_within_unwind_safe() {
    let a: [u8; 5] = [1, 1, 1, 1, kani::any()];
    kani::assume(a[4] < 10);
    let s: u8 = a.iter().sum();
    assert!(s >= 4);
}

#[kani::proof]
#[kani::unwind(3)]
fn u2_fold_past_unwind_bug() {
    let a: [u8; 5] = [1, 2, 3, 4, kani::any()];
    let s = a.iter().fold(0u8, |acc, x| acc.wrapping_add(*x));
    assert!(s.wrapping_sub(a[4]) == 10);
}

#[kani::proof]
#[kani::unwind(3)]
fn u3_sum_nine_past_unwind_bug() {
    let a: [u8; 9] = [1, 1, 1, 1, 1, 1, 1, 1, kani::any()];
    kani::assume(a[8] < 10);
    let s: u8 = a.iter().sum();
    sink(s);
}

#[kani::proof]
#[kani::unwind(4)]
fn u4_iter_sum_past_unwind_bug() {
    let a: [u16; 6] = [1, 2, 3, 4, 5, kani::any()];
    kani::assume(a[5] < 100);
    let s: u16 = a.iter().sum();
    assert!(s >= 15);
}

// Slice iterator, N == U: the do-while loop takes N - 1 back edges.
#[kani::proof]
#[kani::unwind(5)]
fn r1_slice_sum_n5_u5_safe() {
    let a: [u8; 5] = [1, 1, 1, 1, kani::any()];
    kani::assume(a[4] < 10);
    let s: u8 = a.iter().sum();
    assert!(s >= 4);
}

#[kani::proof]
#[kani::unwind(4)]
fn r2_slice_sum_n5_u4_bug() {
    let a: [u8; 5] = [1, 1, 1, 1, kani::any()];
    kani::assume(a[4] < 10);
    let s: u8 = a.iter().sum();
    assert!(s >= 4);
}

// Nothing reads the sum: only the unwinding assertion can fail.
#[kani::proof]
#[kani::unwind(3)]
fn r4_slice_sum_unused_u3_bug() {
    let a: [u8; 6] = [1, 1, 1, 1, 1, kani::any()];
    kani::assume(a[5] < 10);
    let s: u8 = a.iter().sum();
    sink(s);
}

// The array's own `IntoIter`: its loop tests before the body, so N == U fails.
#[kani::proof]
#[kani::unwind(4)]
fn a1_into_fold_n4_u4_bug() {
    let a: [u8; 4] = [1, 1, 1, 1];
    let s = IntoIterator::into_iter(a).fold(0u8, |acc, x| acc.wrapping_add(x));
    sink(s);
}

// A `for` loop over the array's own `IntoIter`: the array-iterator pass
// straight-lined it with no loop left to check (`ai_for_n4_u4_assert_bug`
// verified clean on main); under a declared bound it now keeps the loop
// unless the loop stays within the bound (N = 3 < U = 4).
#[kani::proof]
#[kani::unwind(4)]
fn a2_into_for_n4_u4_bug() {
    let a: [u8; 4] = [1, 1, 1, 1];
    let mut s = 0u8;
    for x in IntoIterator::into_iter(a) {
        s = s.wrapping_add(x);
    }
    assert!(s == 4);
}

#[kani::proof]
#[kani::unwind(4)]
fn a2_into_for_n3_u4_safe() {
    let a: [u8; 3] = [1, 1, 1];
    let mut s = 0u8;
    for x in IntoIterator::into_iter(a) {
        s = s.wrapping_add(x);
    }
    assert!(s == 3);
}

// `map` of a slice iterator: the chain does not fold it; the array's length
// bounds the count through the adapter.
#[kani::proof]
#[kani::unwind(4)]
fn m1_map_fold_n5_u4_bug() {
    let a: [u8; 5] = [1, 1, 1, 1, 1];
    let s = a.iter().map(|x| *x as u16).fold(0u16, |acc, x| acc.wrapping_add(x));
    sink(s);
}

#[kani::proof]
#[kani::unwind(5)]
fn m1_map_fold_n5_u5_safe() {
    let a: [u8; 5] = [1, 1, 1, 1, 1];
    let s = a.iter().map(|x| *x as u16).fold(0u16, |acc, x| acc.wrapping_add(x));
    sink(s);
}

// No declared bound: `filter` keeps 1 and 3; the inner elements overflow.
#[kani::proof]
fn f1_filter_sum_safe() {
    let a: [u8; 4] = [1, 200, 3, 200];
    let s: u8 = a.iter().filter(|x| **x < 100).sum();
    assert!(s == 4);
}

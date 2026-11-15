// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Closures an iterator stub does not run (AY alignment round 8, review
// round 5, findings 1 and 4).
//
// Both lanes stub `Iterator::next` of std's closure adapters and
// `Iterator::collect`, and the CHC lane stubs `Iterator::sum` and
// `Iterator::fold`. None of those stubs runs the closures the real call runs:
// a `Filter`'s predicate, a `Map`'s function, a `try_fold`'s closure. Every
// check inside them was dropped, and for a summand that carries no panic
// obligation of its own (`Saturating`, `Wrapping`, a float) nothing stood in
// for it. Measured before the fix, all Kani FAILED on the closure's own check
// with every other check holding: CHC proved the `Saturating`, `Wrapping` and
// `f32` filter sums, the filter `fold`, the bare `next()` on the filter and the
// `try_fold`; BMC proved the `next()` on the `Map`, the `Filter` and the
// `FilterMap`, and the `collect()` of the `Map`. No row of the sum-stub duals
// used `filter`, so the gate could not see it.
//
// Each stub now adds a conservative check, which can never be certified as a
// real counterexample, wherever a closure the call runs may carry an
// obligation (the obligation-free walk cannot certify it). A closure that only
// compares or calls obligation-free code costs nothing (`*_pure_*_safe`); one
// whose check holds is failed closed (`*_holds_safe`, known red: the
// disclosed cost of the rule).
//
// Oracles (Kani 0.67.0, measured 2026-10-15):
//   every `*_bug`   MUST FAIL
//   every `*_safe`  MUST be SUCCESSFUL
use std::num::{Saturating, Wrapping};

fn hold() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    assert!(x < 20);
}

#[kani::proof]
fn sat_filter_sum_pred_panics_bug() {
    hold();
    let a = [Saturating(3u8), Saturating(2)];
    let s: Saturating<u8> = a
        .iter()
        .filter(|x| {
            assert!(x.0 < 3, "filter check");
            true
        })
        .sum();
    let _ = s;
}

#[kani::proof]
fn sat_filter_sum_pred_overflows_bug() {
    hold();
    let a = [Saturating(1u8), Saturating(200), Saturating(3)];
    let s: Saturating<u8> = a.iter().filter(|x| x.0 * 2 > 1).sum();
    let _ = s;
}

#[kani::proof]
fn sat_filter_sum_pure_pred_safe() {
    hold();
    let a = [Saturating(1u8), Saturating(200), Saturating(3)];
    let s: Saturating<u8> = a.iter().filter(|x| x.0 > 1).sum();
    let _ = s;
}

#[kani::proof]
fn sat_filter_sum_pred_holds_safe() {
    hold();
    let a = [Saturating(1u8), Saturating(2)];
    let s: Saturating<u8> = a
        .iter()
        .filter(|x| {
            assert!(x.0 < 3, "filter check");
            true
        })
        .sum();
    let _ = s;
}

#[kani::proof]
fn wrap_filter_sum_pred_panics_bug() {
    hold();
    let a = [Wrapping(9u32), Wrapping(2)];
    let s: Wrapping<u32> = a
        .iter()
        .filter(|x| {
            assert!(x.0 != 9, "filter check");
            true
        })
        .sum();
    let _ = s;
}

#[kani::proof]
fn wrap_filter_sum_pure_pred_safe() {
    hold();
    let a = [Wrapping(9u32), Wrapping(2)];
    let s: Wrapping<u32> = a.iter().filter(|x| x.0 != 9).sum();
    let _ = s;
}

#[kani::proof]
fn f32_filter_sum_pred_panics_bug() {
    hold();
    let a = [1.0f32, 2.0, 3.0];
    let s: f32 = a
        .iter()
        .filter(|x| {
            assert!(**x < 2.5, "filter check");
            true
        })
        .sum();
    let _ = s;
}

#[kani::proof]
fn f32_filter_sum_pure_pred_safe() {
    hold();
    let a = [1.0f32, 2.0, 3.0];
    let s: f32 = a.iter().filter(|x| **x < 2.5).sum();
    let _ = s;
}

#[kani::proof]
fn filter_fold_pred_panics_bug() {
    hold();
    let a = [1u32, 2, 3];
    let s = a
        .iter()
        .filter(|x| {
            assert!(**x < 3, "filter check");
            true
        })
        .fold(0u32, |acc, x| acc.wrapping_add(*x));
    let _ = s;
}

#[kani::proof]
fn filter_fold_pure_pred_safe() {
    hold();
    let a = [1u32, 2, 3];
    let s = a.iter().filter(|x| **x < 3).fold(0u32, |acc, x| acc.wrapping_add(*x));
    let _ = s;
}

#[kani::proof]
fn try_fold_closure_panics_bug() {
    hold();
    let a = [1u8, 2, 3];
    let s: Option<u8> = a.iter().try_fold(0u8, |acc, x| {
        assert!(*x < 3, "try_fold check");
        acc.checked_add(*x)
    });
    let _ = s;
}

#[kani::proof]
#[kani::unwind(5)]
fn filter_next_pred_panics_bug() {
    hold();
    let a = [3u8, 2, 1];
    let mut it = a.iter().filter(|x| {
        assert!(**x < 3, "filter check");
        true
    });
    let first = it.next();
    let _ = first;
}

#[kani::proof]
#[kani::unwind(5)]
fn filter_next_pure_pred_safe() {
    hold();
    let a = [3u8, 2, 1];
    let mut it = a.iter().filter(|x| **x < 3);
    let first = it.next();
    let _ = first;
}

#[kani::proof]
#[kani::unwind(5)]
fn filter_next_pred_holds_safe() {
    hold();
    let a = [1u8, 2, 1];
    let mut it = a.iter().filter(|x| {
        assert!(**x < 3, "filter check");
        true
    });
    let first = it.next();
    let _ = first;
}

#[kani::proof]
#[kani::unwind(5)]
fn map_next_closure_panics_bug() {
    hold();
    let a = [3u8, 2, 1];
    let mut it = a.iter().map(|x| {
        assert!(*x < 3, "map check");
        *x
    });
    let first = it.next();
    let _ = first;
}

#[kani::proof]
#[kani::unwind(5)]
fn map_next_pure_closure_safe() {
    hold();
    let a = [3u8, 2, 1];
    let mut it = a.iter().map(|x| x.wrapping_add(1));
    let first = it.next();
    let _ = first;
}

#[kani::proof]
#[kani::unwind(5)]
fn filter_map_next_closure_panics_bug() {
    hold();
    let a = [3u8, 2, 1];
    let mut it = a.iter().filter_map(|x| {
        assert!(*x < 3, "filter_map check");
        Some(*x)
    });
    let first = it.next();
    let _ = first;
}

#[kani::proof]
#[kani::unwind(5)]
fn map_collect_closure_panics_bug() {
    hold();
    let a = [3u8, 2, 1];
    let v: Vec<u8> = a
        .iter()
        .map(|x| {
            assert!(*x < 3, "map check");
            *x
        })
        .collect();
    let _ = v.len();
}

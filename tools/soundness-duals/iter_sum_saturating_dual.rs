// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// `Iterator::sum` over std's `Saturating<uN>`, and the conservative rule for a
// `Sum` impl the stub does not model (AY alignment round 8, review round 4,
// findings 1 and 2).
//
// std's `Sum` for `Saturating<uN>` is `fold(Saturating(0), |a, b| a + b)`
// whose `+` is `uN::saturating_add` (core/src/iter/traits/accum.rs,
// `saturating_integer_sum_product!`, unsigned integers only): it cannot panic.
// Round 3 left it unclassified, so the CHC lane's new rule for an unmodelled
// impl fired whenever a harness reached the call, and the safe rows below
// that never read the sum, or read a sum that does not saturate, FAILED in
// CHC where main and Kani prove them. The other dual files expected only
// FAILED rows for unmodelled impls (a user impl, `Duration`, `Option<T>`
// beside a holding check), so the gate could not see that cost.
//
//   * Saturating sums, by reference and by value (through `map`), unread or
//     read, saturating or not, of 2 to 12 constant elements, of symbolic
//     elements, and of a symbolic-length slice.
//   * A Saturating sum beside a check that fails: the stub must not make the
//     path past the call infeasible.
//   * A user `Sum` impl that cannot panic, its value unread: the stub does not
//     encode a user impl's body, so it cannot tell this impl from one that
//     panics and fails it closed (known red, the disclosed cost of the rule).
//
// Oracles (Kani 0.67.0, measured 2026-10-14):
//   every `*_bug`   MUST FAIL
//   every `*_safe`  MUST be SUCCESSFUL
use std::num::Saturating;

fn hold() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    assert!(x < 20);
}

#[kani::proof]
fn sat_ref_sum_unread_safe() {
    let a = [Saturating(200u8), Saturating(100u8)];
    let s: Saturating<u8> = a.iter().sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn sat_map_sum_unread_safe() {
    let a = [200u8, 100u8];
    let s: Saturating<u8> = a.iter().map(|&x| Saturating(x)).sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn sat_small_value_safe() {
    let a = [Saturating(1u8), Saturating(2u8)];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == 3);
}

#[kani::proof]
fn sat_saturates_value_safe() {
    let a = [Saturating(200u8), Saturating(100u8)];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == u8::MAX);
}

#[kani::proof]
fn sat_wrapped_value_bug() {
    let a = [Saturating(200u8), Saturating(100u8)];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == 44);
}

#[kani::proof]
fn sat_u64_saturates_value_safe() {
    let a = [Saturating(u64::MAX), Saturating(1u64), Saturating(7u64)];
    let s: Saturating<u64> = a.iter().sum();
    assert!(s.0 == u64::MAX);
}

#[kani::proof]
fn sat_long_value_safe() {
    let a = [Saturating(1u32 << 30); 12];
    let s: Saturating<u32> = a.iter().sum();
    assert!(s.0 == u32::MAX);
}

#[kani::proof]
fn sat_long_value_bug() {
    let a = [Saturating(30u8); 12];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == 104);
}

#[kani::proof]
fn sat_map_value_safe() {
    let a = [200u8, 100u8];
    let s: Saturating<u8> = a.iter().map(|&x| Saturating(x)).sum();
    assert!(s.0 == u8::MAX);
}

#[kani::proof]
fn sat_symbolic_bounds_safe() {
    let a = [Saturating(kani::any::<u8>()), Saturating(kani::any::<u8>())];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 >= a[0].0 && s.0 >= a[1].0);
}

#[kani::proof]
fn sat_symbolic_not_wrapping_bug() {
    let a = [Saturating(kani::any::<u8>()), Saturating(kani::any::<u8>())];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == a[0].0.wrapping_add(a[1].0));
}

#[kani::proof]
fn sat_symbolic_len_unread_safe() {
    let a = [Saturating(200u8), Saturating(100u8), Saturating(1u8)];
    let n: usize = kani::any();
    kani::assume(n <= 3);
    let s: Saturating<u8> = a[..n].iter().sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn sat_sum_beside_failing_check_bug() {
    let a = [Saturating(200u8), Saturating(100u8)];
    let s: Saturating<u8> = a.iter().sum();
    let x: u8 = kani::any();
    assert!(x < 200);
    let _ = s;
}

#[derive(Clone, Copy)]
struct Weight(u32);

// A user `Sum` that takes the maximum and cannot panic.
impl<'a> core::iter::Sum<&'a Weight> for u32 {
    fn sum<I: Iterator<Item = &'a Weight>>(it: I) -> u32 {
        it.fold(0, |a, w| a.max(w.0))
    }
}

#[kani::proof]
fn user_impl_never_panics_unread_safe() {
    let v = [Weight(3), Weight(u32::MAX)];
    let s: u32 = v.iter().sum();
    hold();
    let _ = s;
}

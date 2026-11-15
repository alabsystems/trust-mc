// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// `Iterator::sum` stub, the shapes `iter_sum_dual.rs` could not see (AY
// alignment round 8, review round 3, findings 2, 3, 4 and 5). Its `*_safe`
// rows expect NOT_GENUINE, which a FAILED OverApproximation satisfies, so a
// safe program the stub stopped proving stayed green there. The safe rows here
// expect SUCCESSFUL in both lanes.
//
//   * A `Sum` impl the stub does not model (a user impl, `Duration`,
//     `Option<T>`) panics inside its own body. The harness carries a second,
//     holding check, so the no-checks gate cannot stand in for the lost panic.
//     The CHC lane used to havoc the value and emit no error rule: all three
//     were SUCCESSFUL where Kani fails.
//   * An integer sum longer than the CHC replay's default bound of 8 whose
//     length is static: the conservative overflow rule for the elements the
//     replay left unchecked made `[20u8; 12]` unprovable (main proved it, by
//     emitting no overflow check at all).
//   * Short constant sums: the replay's overflow check was a node the CHC
//     straight-line discharge does not fold, so a sum of `[20u8; 2]` that
//     main proved in milliseconds went to the solver and timed out under
//     load.
//   * A float sum over symbolic elements (BMC: exact `fp.add`).
//
// Oracles (Kani 0.67.0, measured 2026-10-14):
//   every `*_bug`   MUST FAIL
//   every `*_safe`  MUST be SUCCESSFUL
use std::time::Duration;

fn hold() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    assert!(x < 20);
}

#[derive(Clone, Copy)]
struct Small(u8);

// A user `Sum` whose body overflows: Kani fails "attempt to add with overflow".
impl<'a> core::iter::Sum<&'a Small> for u8 {
    fn sum<I: Iterator<Item = &'a Small>>(it: I) -> u8 {
        it.fold(0u8, |a, w| a + w.0)
    }
}

#[kani::proof]
fn user_impl_overflow_beside_check_bug() {
    let v = [Small(200), Small(100)];
    let s: u8 = v.iter().sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn duration_sum_overflow_beside_check_bug() {
    let s: Duration = [Duration::from_secs(u64::MAX), Duration::from_secs(1)].iter().sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn option_sum_overflow_beside_check_bug() {
    let s: Option<u8> = [Some(200u8), Some(100)].iter().copied().sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn long_constant_sum_unread_safe() {
    let s: u8 = [20u8; 12].iter().sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn long_constant_sum_value_safe() {
    let s: u8 = [20u8; 12].iter().sum();
    assert!(s == 240);
}

#[kani::proof]
fn long_constant_sum_overflow_bug() {
    let s: u8 = [30u8; 12].iter().sum();
    hold();
    let _ = s;
}

#[kani::proof]
fn short_constant_sum_value_safe() {
    let s: u8 = [20u8; 2].iter().sum();
    assert!(s == 40);
}

#[kani::proof]
fn short_signed_sum_value_safe() {
    let s: i8 = [100i8, -100, 100, -100].iter().sum();
    assert!(s == 0);
}

#[kani::proof]
fn short_signed_sum_dip_overflow_bug() {
    let s: i8 = [100i8, 100, -100, -100].iter().sum();
    assert!(s == 0);
}

#[kani::proof]
fn symbolic_elems_sum_safe() {
    let a: [u8; 3] = kani::any();
    kani::assume(a[0] < 80 && a[1] < 80 && a[2] < 80);
    let s: u8 = a.iter().sum();
    assert!(s < 240);
}

#[kani::proof]
fn symbolic_elems_sum_overflow_bug() {
    let a: [u8; 3] = kani::any();
    kani::assume(a[0] < 90 && a[1] < 90 && a[2] < 90);
    let s: u8 = a.iter().sum();
    let _ = s;
}

#[kani::proof]
fn symbolic_float_sum_bug() {
    let a: [f32; 2] = kani::any();
    kani::assume(a[0].is_finite() && a[1].is_finite());
    let s: f32 = a.iter().sum();
    assert!(s.is_finite());
}

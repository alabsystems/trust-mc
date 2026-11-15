// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// `Iterator::sum` and `Iterator::fold` stubs: the arithmetic is std's `Sum`
// impl for the call's Rust types, never a guess from the SMT sort.
//
// Before AY alignment review round 2 both lanes summed any bitvector-sorted
// destination with `bvadd`:
//   * a float sum was the INTEGER sum of the IEEE bit patterns, so
//     `f32_sum_to_inf_bug` was proved and `f32_sum_value_safe` was a Genuine
//     counterexample, in both lanes;
//   * std's integer `Sum` adds under `#[rustc_inherit_overflow_checks]`; the
//     stub wrapped silently, so `u8_sum_overflow_bug`, `u8_map_sum_overflow_bug`
//     and `long_array_sum_overflow_bug` were proved (BMC);
//   * a `Saturating` sum and a max-taking user `Sum` were proved where Kani
//     fails, and their safe twins were Genuine counterexamples (CHC);
//   * the same held inside a helper and a generic helper (`helper_*`,
//     `generic_*`), where the stub reads the monomorphised call;
//   * a sum or fold past the CHC replay bound, or over a symbolic length, was
//     havocked through a symbol the counterexample classifier never saw, so the
//     safe `long_array_*` and `symbolic_len_*` harnesses were Genuine
//     counterexamples (CHC).
// The empty float sum is `-0.0` (std folds from `-0.0`).
//
// Oracles (Kani 0.67.0, measured 2026-10-02, one harness at a time):
//   every `*_bug`   MUST FAIL
//   every `*_safe`  NOT-GENUINE (Kani SUCCESSFUL; the CHC lane, which has no
//                   FP theory, havocs a float sum and may fail it, but must
//                   not certify that failure). The integer `u8_sum_safe`,
//                   `long_array_sum_safe` and `helper_sum_safe` are proved in
//                   both lanes and expect SUCCESSFUL (AY alignment round 8,
//                   review round 3, finding 5), and so do
//                   `saturating_sum_safe` and `wrapping_sum_safe` (review
//                   round 4: both lanes sum `Saturating` and `Wrapping`
//                   exactly); `iter_sum_shapes_dual.rs` and
//                   `iter_sum_saturating_dual.rs` carry the shapes these rows
//                   could not see.
use std::num::{Saturating, Wrapping};

#[kani::proof]
fn f32_sum_to_inf_bug() {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    assert!(s.is_finite());
}

#[kani::proof]
fn f32_sum_to_inf_safe() {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    assert!(s.is_infinite());
}

#[kani::proof]
fn f32_sum_value_bug() {
    let s: f32 = [1.5f32, 2.25].iter().sum();
    assert!(s == 3.0);
}

#[kani::proof]
fn f32_sum_value_safe() {
    let s: f32 = [1.5f32, 2.25].iter().sum();
    assert!(s == 3.75);
}

#[kani::proof]
fn f64_rounding_bug() {
    let s: f64 = [0.1f64, 0.2].iter().sum();
    assert!(s == 0.3); // 0.30000000000000004
}

#[kani::proof]
fn f64_rounding_safe() {
    let s: f64 = [0.1f64, 0.2].iter().sum();
    assert!(s != 0.3);
}

#[kani::proof]
#[kani::unwind(2)]
fn f32_empty_sum_is_negative_zero_bug() {
    let a: [f32; 0] = [];
    let s: f32 = a.iter().sum();
    assert!(s.is_sign_positive());
}

#[kani::proof]
#[kani::unwind(2)]
fn f32_empty_sum_is_negative_zero_safe() {
    let a: [f32; 0] = [];
    let s: f32 = a.iter().sum();
    assert!(s == 0.0 && s.is_sign_negative());
}

#[kani::proof]
fn u8_sum_overflow_bug() {
    let s: u8 = [200u8, 100].iter().sum();
    assert!(s > 0);
}

#[kani::proof]
fn u8_sum_safe() {
    let s: u8 = [200u8, 50].iter().sum();
    assert!(s == 250);
}

#[kani::proof]
fn i8_sum_underflow_bug() {
    let s: i8 = [-100i8, -100].iter().sum();
    assert!(s < 0);
}

#[kani::proof]
fn u8_map_sum_overflow_bug() {
    let s: u8 = [100u8, 100, 100].iter().map(|x| *x).sum();
    assert!(s > 0);
}

#[kani::proof]
fn long_array_sum_overflow_bug() {
    let a = [30u8; 12];
    let s: u8 = a.iter().sum();
    assert!(s > 0);
}

#[kani::proof]
fn long_array_sum_safe() {
    let a = [1u32; 12];
    let s: u32 = a.iter().sum();
    assert!(s == 12);
}

#[kani::proof]
fn symbolic_len_sum_safe() {
    let n: usize = kani::any();
    kani::assume(n <= 12);
    let a = [1u32; 12];
    let s: u32 = a[..n].iter().sum();
    assert!(s as usize == n);
}

#[kani::proof]
fn saturating_sum_bug() {
    let a = [Saturating(200u8), Saturating(100u8)];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == 44);
}

#[kani::proof]
fn saturating_sum_safe() {
    let a = [Saturating(200u8), Saturating(100u8)];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == 255);
}

#[kani::proof]
fn wrapping_sum_bug() {
    let a = [Wrapping(200u8), Wrapping(100u8)];
    let s: Wrapping<u8> = a.iter().sum();
    assert!(s.0 == 255);
}

#[kani::proof]
fn wrapping_sum_safe() {
    let a = [Wrapping(200u8), Wrapping(100u8)];
    let s: Wrapping<u8> = a.iter().sum();
    assert!(s.0 == 44);
}

#[derive(Clone, Copy)]
struct Weight(u32);

// A user `Sum` that takes the maximum: the stubs must not add.
impl<'a> core::iter::Sum<&'a Weight> for u32 {
    fn sum<I: Iterator<Item = &'a Weight>>(it: I) -> u32 {
        it.fold(0, |a, w| a.max(w.0))
    }
}

#[kani::proof]
fn user_sum_impl_bug() {
    let v = [Weight(3), Weight(4)];
    let s: u32 = v.iter().sum();
    assert!(s == 7);
}

#[kani::proof]
fn user_sum_impl_safe() {
    let v = [Weight(3), Weight(4)];
    let s: u32 = v.iter().sum();
    assert!(s == 4);
}

#[kani::proof]
fn long_array_fold_bug() {
    let a = [1u32; 12];
    let s: u32 = a.iter().fold(0u32, |acc, x| acc.wrapping_add(*x));
    assert!(s == 11);
}

#[kani::proof]
fn long_array_fold_safe() {
    let a = [1u32; 12];
    let s: u32 = a.iter().fold(0u32, |acc, x| acc.wrapping_add(*x));
    assert!(s == 12);
}

#[kani::proof]
fn symbolic_len_fold_safe() {
    let n: usize = kani::any();
    kani::assume(n <= 12);
    let a = [1u32; 12];
    let s: u32 = a[..n].iter().fold(0u32, |acc, x| acc.wrapping_add(*x));
    assert!(s as usize == n);
}

fn total(v: &[u8]) -> u8 {
    v.iter().sum()
}

fn total_generic<T: Copy + core::iter::Sum<T>>(v: &[T]) -> T {
    v.iter().copied().sum()
}

#[kani::proof]
fn helper_sum_overflow_bug() {
    let s = total(&[200, 100]);
    assert!(s > 0);
}

#[kani::proof]
fn helper_sum_safe() {
    let s = total(&[200, 50]);
    assert!(s == 250);
}

#[kani::proof]
fn generic_f32_sum_bug() {
    let s = total_generic(&[f32::MAX, f32::MAX]);
    assert!(s.is_finite());
}

#[kani::proof]
fn generic_f32_sum_safe() {
    let s = total_generic(&[1.5f32, 2.25]);
    assert!(s == 3.75);
}

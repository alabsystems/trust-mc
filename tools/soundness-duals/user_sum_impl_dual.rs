// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `Iterator::sum` into a `Sum` impl
//! other than core's integer fold (fix/chc-walker-fail-closed, repair round
//! 3, walker fail-closed review 6 round 3 findings 1, 2 and 4; the review's
//! probes `q3_sum_impls.rs`, `q5_sum_first.rs` and `q9_std_sum_types.rs`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   x2_user_sum_max_slice_bug                -> VERIFICATION:- FAILED  ('m.0 == 9')
//!   x2_user_sum_max_slice_safe               -> VERIFICATION:- SUCCESSFUL
//!   x3_user_sum_wrapping_safe                -> VERIFICATION:- SUCCESSFUL
//!   x4_user_sum_for_loop_u3_bug              -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   x4_user_sum_for_loop_u4_safe             -> VERIFICATION:- SUCCESSFUL
//!   y1_user_sum_first_unread_u3_safe         -> VERIFICATION:- SUCCESSFUL
//!   y2_user_sum_first_value_u3_safe          -> VERIFICATION:- SUCCESSFUL
//!   y3_user_sum_first_value_nounwind_safe    -> VERIFICATION:- SUCCESSFUL
//!   p1_primitive_target_user_sum_bug         -> VERIFICATION:- FAILED  ('s == 9')
//!   p1_primitive_target_user_sum_safe        -> VERIFICATION:- SUCCESSFUL
//!   w1_wrapping_sum_safe                     -> VERIFICATION:- SUCCESSFUL
//!   w2_saturating_sum_bug                    -> VERIFICATION:- FAILED  ('s.0 == 44')
//!   w2_saturating_sum_safe                   -> VERIFICATION:- SUCCESSFUL
//!   w3_signed_sum_overflow_bug               -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!
//! MECHANISM UNDER TEST. The statement path and the BMC unroll modelled a
//! call of `Iterator::sum` by its NAME (`"sum" if path.contains("Iterator")`)
//! as checked integer addition over the receiver's elements, whatever `Sum`
//! impl the call runs: a user `impl Sum<&u8> for Mx` (max: `x2` verified
//! clean; first element: `y1` certified a false Genuine unwinding failure),
//! a user `impl Sum<&M> for u8` (`p1`), and std's `Wrapping` / `Saturating`
//! (`w1` failed "attempt to add with overflow"). Only core's impls are
//! modelled now (`codegen_ay/reduce_loop_rule.rs`, `iter_sum_model`):
//! primitive numbers with the checked step, `Wrapping` with `wrapping_add`,
//! `Saturating` with `saturating_add`. Any other impl is the code it is: one
//! that is a single `fold` is inlined into the harness, where the reduction
//! models replay its closure; any other is walked.
use std::iter::Sum;
use std::num::{Saturating, Wrapping};

#[inline(never)]
fn sink<T>(_v: T) {}

struct Mx(u8);
impl<'a> Sum<&'a u8> for Mx {
    fn sum<I: Iterator<Item = &'a u8>>(it: I) -> Mx {
        Mx(it.fold(0, |a, b| a.max(*b)))
    }
}

#[kani::proof]
fn x2_user_sum_max_slice_bug() {
    let m: Mx = [1u8, 5, 3].iter().sum();
    assert!(m.0 == 9);
}

#[kani::proof]
fn x2_user_sum_max_slice_safe() {
    let m: Mx = [1u8, 5, 3].iter().sum();
    assert!(m.0 == 5);
}

struct W8(u8);
impl<'a> Sum<&'a u8> for W8 {
    fn sum<I: Iterator<Item = &'a u8>>(it: I) -> W8 {
        W8(it.fold(0u8, |a, b| a.wrapping_add(*b)))
    }
}

#[kani::proof]
fn x3_user_sum_wrapping_safe() {
    let w: W8 = [200u8, 100, 0].iter().sum();
    assert!(w.0 == 44);
}

struct S8(u8);
impl<'a> Sum<&'a u8> for S8 {
    fn sum<I: Iterator<Item = &'a u8>>(it: I) -> S8 {
        let mut s = 0u8;
        for x in it {
            s = s.wrapping_add(*x);
        }
        S8(s)
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn x4_user_sum_for_loop_u3_bug() {
    let s: S8 = [1u8, 2, 3].iter().sum();
    assert!(s.0 == 6);
}

#[kani::proof]
#[kani::unwind(4)]
fn x4_user_sum_for_loop_u4_safe() {
    let s: S8 = [1u8, 2, 3].iter().sum();
    assert!(s.0 == 6);
}

struct First(u8);
impl<'a> Sum<&'a u8> for First {
    fn sum<I: Iterator<Item = &'a u8>>(mut it: I) -> First {
        First(*it.next().unwrap_or(&0))
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn y1_user_sum_first_unread_u3_safe() {
    let a = [1u8, 2, 3, 4, 5];
    let f: First = a.iter().sum();
    sink(f);
    assert!(a[0] == 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn y2_user_sum_first_value_u3_safe() {
    let a = [1u8, 2, 3, 4, 5];
    let f: First = a.iter().sum();
    assert!(f.0 == 1);
}

#[kani::proof]
fn y3_user_sum_first_value_nounwind_safe() {
    let a = [1u8, 2, 3, 4, 5];
    let f: First = a.iter().sum();
    assert!(f.0 == 1);
}

struct M(u8);
impl<'a> Sum<&'a M> for u8 {
    fn sum<I: Iterator<Item = &'a M>>(it: I) -> u8 {
        it.fold(0u8, |acc, m| if m.0 > acc { m.0 } else { acc })
    }
}

#[kani::proof]
fn p1_primitive_target_user_sum_bug() {
    let a = [M(1), M(5), M(3)];
    let s: u8 = a.iter().sum();
    assert!(s == 9);
}

#[kani::proof]
fn p1_primitive_target_user_sum_safe() {
    let a = [M(1), M(5), M(3)];
    let s: u8 = a.iter().sum();
    assert!(s == 5);
}

#[kani::proof]
fn w1_wrapping_sum_safe() {
    let a = [Wrapping(200u8), Wrapping(100u8), Wrapping(0u8)];
    let s: Wrapping<u8> = a.iter().sum();
    assert!(s.0 == 44);
}

#[kani::proof]
fn w2_saturating_sum_bug() {
    let a = [Saturating(200u8), Saturating(100u8), Saturating(0u8)];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == 44);
}

#[kani::proof]
fn w2_saturating_sum_safe() {
    let a = [Saturating(200u8), Saturating(100u8), Saturating(0u8)];
    let s: Saturating<u8> = a.iter().sum();
    assert!(s.0 == 255);
}

#[kani::proof]
fn w3_signed_sum_overflow_bug() {
    let a = [-100i8, -100, 0];
    let s: i8 = a.iter().sum();
    let _ = s;
}

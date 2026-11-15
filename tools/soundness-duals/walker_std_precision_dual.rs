// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PRECISION DUAL (false-failure tripwire) -- correct programs whose walked std
//! code carries the walker's new BinOp checks. Every harness is SAFE.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   safe_rev_one_step_direct     -> VERIFICATION:- SUCCESSFUL
//!   safe_rev_one_step_dyn_multi  -> VERIFICATION:- SUCCESSFUL
//!   safe_two_calls_dyn_multi     -> VERIFICATION:- SUCCESSFUL
//!   safe_mix_wrappers_dyn_multi  -> VERIFICATION:- SUCCESSFUL
//!   safe_user_div_rem_dyn        -> VERIFICATION:- SUCCESSFUL
//!   safe_nz_new_dyn_multi        -> VERIFICATION:- SUCCESSFUL
//!
//! WHAT IT GUARDS. The walker checks `unchecked_*` and Div/Rem BinOps in walked
//! bodies since 2026-09-23 (`inline_shared/rvalue_ub.rs`). On correct std code
//! that added three kinds of regression, measured by the 2026-09-23 precision
//! review on its probes r10, r7, r6 and r2:
//! * a lost GUARD: `(a..b).rev().next()` walks `Range::spec_next_back`, whose
//!   `self.start < self.end` comparison takes its reference arguments as
//!   addresses and is havocked, so `Step::backward_unchecked(end, 1)`'s
//!   `unchecked_sub` check fires on `end == 0`. Reading the referents back from
//!   the borrowed places (`comparison_arg_referent_value`, 2026-09-24) fixed
//!   the direct row but was unsound and was removed
//!   (walker_referent_read_dual.rs), so `safe_rev_one_step_direct` is a
//!   tracked false failure again. Core's `unchecked_*` wrappers are answered
//!   at the call without spending inline depth
//!   (`inline_unchecked_arith_wrapper_call`).
//! * BUDGET starvation: each walked check is its own CHC property; locally
//!   valid ones (`checked_sub`'s guarded subtraction, `wrapping_shl`'s masked
//!   distance) took 9-13 s each and six of them turned a proof UNKNOWN. The
//!   host now drops a check valid on its own, and an exact duplicate
//!   (`emit_deferred_inline_checks_at`), such as a user `a / b`'s MIR Assert and
//!   the walker's own divisor check.
//! * an untranslatable operand: `NonZero::new(b)`'s payload does not translate,
//!   so `a / d` fails closed (`safe_nz_new_dyn_multi`, tracked known-red).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_std_precision_dual.rs

use std::num::NonZero;

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait OneStep {
    fn run(&self, a: u8, b: u8) -> Option<u8>;
}
pub struct OA;
pub struct OB;
impl OneStep for OA {
    fn run(&self, a: u8, b: u8) -> Option<u8> {
        (a..b).rev().next()
    }
}
impl OneStep for OB {
    fn run(&self, a: u8, b: u8) -> Option<u8> {
        (a..b).next_back()
    }
}

pub trait Two {
    fn run(&self, a: u32, b: u32) -> u32;
}
pub struct TwoA;
pub struct TwoB;
impl Two for TwoA {
    fn run(&self, a: u32, b: u32) -> u32 {
        a.checked_sub(b).unwrap_or(0)
    }
}
impl Two for TwoB {
    fn run(&self, a: u32, b: u32) -> u32 {
        b.checked_sub(a).unwrap_or(0)
    }
}

pub trait Mix {
    fn run(&self, a: u32, b: u32, s: u32) -> u32;
}
pub struct MixA;
pub struct MixB;
impl Mix for MixA {
    fn run(&self, a: u32, b: u32, s: u32) -> u32 {
        let x = a.wrapping_shl(s);
        let y = b.wrapping_shr(s);
        let z = a.checked_sub(b).unwrap_or(0);
        let w = a.checked_div(b).unwrap_or(0);
        x ^ y ^ z ^ w
    }
}
impl Mix for MixB {
    fn run(&self, a: u32, b: u32, s: u32) -> u32 {
        let x = a.wrapping_shr(s);
        let y = b.wrapping_shl(s);
        let z = b.checked_sub(a).unwrap_or(1);
        let w = a.checked_rem(b).unwrap_or(1);
        x ^ y ^ z ^ w
    }
}

pub trait Divs {
    fn run(&self, a: i32, b: i32) -> i32;
}
pub struct DA;
pub struct DB;
impl Divs for DA {
    fn run(&self, a: i32, b: i32) -> i32 {
        a / b
    }
}
impl Divs for DB {
    fn run(&self, a: i32, b: i32) -> i32 {
        a % b
    }
}

pub trait NzNew {
    fn op(&self, a: u32, b: u32) -> u32;
}
pub struct NewA;
pub struct NewB;
impl NzNew for NewA {
    fn op(&self, a: u32, b: u32) -> u32 {
        match NonZero::new(b) {
            Some(d) => a / d,
            None => 0,
        }
    }
}
impl NzNew for NewB {
    fn op(&self, a: u32, b: u32) -> u32 {
        match NonZero::new(b) {
            Some(d) => a % d,
            None => 1,
        }
    }
}

#[kani::proof]
fn safe_rev_one_step_direct() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    sink((a..b).rev().next());
}

#[kani::proof]
fn safe_rev_one_step_dyn_multi() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn OneStep> = if kani::any() { Box::new(OA) } else { Box::new(OB) };
    sink(o.run(a, b));
}

#[kani::proof]
fn safe_two_calls_dyn_multi() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let t: Box<dyn Two> = if kani::any() { Box::new(TwoA) } else { Box::new(TwoB) };
    let q1 = t.run(a, b);
    let q2 = t.run(b, a);
    let q3 = t.run(q1, q2);
    sink(q3);
}

#[kani::proof]
fn safe_mix_wrappers_dyn_multi() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let s: u32 = kani::any();
    let o: Box<dyn Mix> = if kani::any() { Box::new(MixA) } else { Box::new(MixB) };
    sink(o.run(a, b, s));
}

#[kani::proof]
fn safe_user_div_rem_dyn() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    kani::assume(b > 0);
    let o: Box<dyn Divs> = if kani::any() { Box::new(DA) } else { Box::new(DB) };
    sink(o.run(a, b));
}

#[kani::proof]
fn safe_nz_new_dyn_multi() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let o: Box<dyn NzNew> = if kani::any() { Box::new(NewA) } else { Box::new(NewB) };
    sink(o.op(a, b));
}

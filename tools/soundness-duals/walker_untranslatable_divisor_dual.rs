// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire, both directions) -- a Div/Rem in a
//! walked dyn body whose divisor the CHC inline walker cannot translate.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_skipped_divisor_multi_impl       -> VERIFICATION:- FAILED  ('attempt to divide by zero', and the Rem impl's divisor-zero check)
//!   bug_skipped_divisor_single_impl_box  -> VERIFICATION:- FAILED  (same check)
//!   safe_skipped_divisor_multi_impl      -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The divisor is an array element read at a symbolic
//! index, which the walker skips (the local stays unpopulated), so the Div's
//! operand is untranslatable. The walker's BinOp checks
//! (`inline_shared/rvalue_ub.rs`) FAIL CLOSED there
//! (`inline_rvalue_ub_check_dropped`): before them the Div was a silent rvalue
//! skip and `bug_*` verified SUCCESSFUL clean (the 2026-09-23 precision review,
//! r12). The bug rows now FAIL (non-certified); the safe row, whose every
//! divisor is non-zero, is demoted the same way -- the precision cost of the
//! fail-close, tracked on its row. Reading the element is the precise fix and
//! is not done here.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_untranslatable_divisor_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, a: u8, i: u8) -> u8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let d = arr[(i % 4) as usize];
        sink(200 / d);
        a
    }
}
impl Op for ImplB {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 4, 5, 6];
        let d = arr[(i % 4) as usize];
        sink(200 % d);
        a
    }
}

#[kani::proof]
fn bug_skipped_divisor_multi_impl() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, i));
}

#[kani::proof]
fn bug_skipped_divisor_single_impl_box() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.op(a, i));
}

#[kani::proof]
fn safe_skipped_divisor_multi_impl() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a != 0);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, i));
}

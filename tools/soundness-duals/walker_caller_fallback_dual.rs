// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the statement-path models that take
//! over a call whose inline walk the fn-inline caller declined (its body is
//! over the walker's block budget): the struct-method passthrough, the struct
//! Vec accessor, and the iter-collect method.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_passthrough_assert       -> VERIFICATION:- FAILED  ("with_bump assertion")
//!   bug_passthrough_value        -> VERIFICATION:- FAILED  ("passthrough value")
//!   safe_passthrough_clean       -> VERIFICATION:- SUCCESSFUL
//!   bug_vec_accessor_assert      -> VERIFICATION:- FAILED  ("getter assertion")
//!   safe_vec_len_accessor        -> VERIFICATION:- SUCCESSFUL
//!   bug_collect_method_assert    -> VERIFICATION:- FAILED  ("collect method assertion")
//!
//! MECHANISM UNDER TEST (package round of fix/chc-walker-fail-closed, item c:
//! the callers of the inline walker, audited for what a failed walk turns
//! into). The wrapper chains leave the method call past the MIR inliner's
//! depth, so the statement path's fn-inline caller walks it, finds the body
//! over the walker's budget, and declines; a pattern model then claims the
//! call. Each model stated only its pattern and recorded nothing: the
//! passthrough sets the result EQUAL to the receiver (so a mutation is lost:
//! `bug_passthrough_value`) and drops the method's checks; the Vec accessor
//! states the matched access (not its bounds check, not the method's other
//! checks); the iter-collect model states the map/collect pattern. On main
//! c22e1022e the three `_assert` rows and bug_passthrough_value verified
//! SUCCESSFUL clean. FIXED: the passthrough always fails closed
//! (`struct_method_passthrough_unmodelled`); the accessor and collect models
//! fail closed when the method can fail for its caller
//! (`obligation_free_walk::callee_may_fail_for_caller`). The safe rows are
//! the other direction: a `len` accessor that cannot fail still verifies;
//! safe_passthrough_clean is the passthrough's precision cost (known-red
//! false failure: the model is not an over-approximation, so it never proves).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_caller_fallback_dual.rs

use std::collections::BTreeMap;

#[inline(never)]
fn sink<T>(_value: T) {}

#[inline(never)] fn g1(x: u8) -> u8 { x ^ 1 }
#[inline(never)] fn g2(x: u8) -> u8 { x ^ 2 }
#[inline(never)] fn g3(x: u8) -> u8 { x ^ 3 }
#[inline(never)] fn g4(x: u8) -> u8 { x ^ 4 }
#[inline(never)] fn g5(x: u8) -> u8 { x ^ 5 }
#[inline(never)] fn g6(x: u8) -> u8 { x ^ 6 }
#[inline(never)] fn g7(x: u8) -> u8 { x ^ 7 }
#[inline(never)] fn g8(x: u8) -> u8 { x ^ 8 }
#[inline(never)] fn g9(x: u8) -> u8 { x ^ 9 }
#[inline(never)] fn g10(x: u8) -> u8 { x ^ 10 }
#[inline(never)] fn g11(x: u8) -> u8 { x ^ 11 }
#[inline(never)] fn g12(x: u8) -> u8 { x ^ 12 }
#[inline(never)] fn g13(x: u8) -> u8 { x ^ 13 }
#[inline(never)] fn g14(x: u8) -> u8 { x ^ 14 }
#[inline(never)] fn g15(x: u8) -> u8 { x ^ 15 }
#[inline(never)] fn g16(x: u8) -> u8 { x ^ 16 }
#[inline(never)] fn g17(x: u8) -> u8 { x ^ 17 }
#[inline(never)] fn g18(x: u8) -> u8 { x ^ 18 }
#[inline(never)] fn g19(x: u8) -> u8 { x ^ 19 }
#[inline(never)] fn g20(x: u8) -> u8 { x ^ 20 }
#[inline(never)] fn g21(x: u8) -> u8 { x ^ 21 }
#[inline(never)] fn g22(x: u8) -> u8 { x ^ 22 }
#[inline(never)] fn g23(x: u8) -> u8 { x ^ 23 }
#[inline(never)] fn g24(x: u8) -> u8 { x ^ 24 }
#[inline(never)] fn g25(x: u8) -> u8 { x ^ 25 }
#[inline(never)] fn g26(x: u8) -> u8 { x ^ 26 }
#[inline(never)] fn g27(x: u8) -> u8 { x ^ 27 }
#[inline(never)] fn g28(x: u8) -> u8 { x ^ 28 }
#[inline(never)] fn g29(x: u8) -> u8 { x ^ 29 }
#[inline(never)] fn g30(x: u8) -> u8 { x ^ 30 }
#[inline(never)] fn g31(x: u8) -> u8 { x ^ 31 }
#[inline(never)] fn g32(x: u8) -> u8 { x ^ 32 }
#[inline(never)] fn g33(x: u8) -> u8 { x ^ 33 }
#[inline(never)] fn g34(x: u8) -> u8 { x ^ 34 }
#[inline(never)] fn g35(x: u8) -> u8 { x ^ 35 }
#[inline(never)] fn g36(x: u8) -> u8 { x ^ 36 }
#[inline(never)] fn g37(x: u8) -> u8 { x ^ 37 }
#[inline(never)] fn g38(x: u8) -> u8 { x ^ 38 }
#[inline(never)] fn g39(x: u8) -> u8 { x ^ 39 }
#[inline(never)] fn g40(x: u8) -> u8 { x ^ 40 }

#[derive(Clone)]
pub struct Reg {
    m: BTreeMap<u8, u8>,
    x: u8,
}

impl Reg {
    #[inline(never)]
    fn with_bump(&self) -> Reg {
        assert!(self.x != 100, "with_bump assertion");
        let x = self.x;
        let x = g1(x);
        let x = g2(x);
        let x = g3(x);
        let x = g4(x);
        let x = g5(x);
        let x = g6(x);
        let x = g7(x);
        let x = g8(x);
        let x = g9(x);
        let x = g10(x);
        let x = g11(x);
        let x = g12(x);
        let x = g13(x);
        let x = g14(x);
        let x = g15(x);
        let x = g16(x);
        let x = g17(x);
        let x = g18(x);
        let x = g19(x);
        let x = g20(x);
        let x = g21(x);
        let x = g22(x);
        let x = g23(x);
        let x = g24(x);
        let x = g25(x);
        let x = g26(x);
        let x = g27(x);
        let x = g28(x);
        let x = g29(x);
        let x = g30(x);
        let x = g31(x);
        let x = g32(x);
        let x = g33(x);
        let x = g34(x);
        let x = g35(x);
        let x = g36(x);
        let x = g37(x);
        let x = g38(x);
        let x = g39(x);
        let x = g40(x);
        let mut r = self.clone();
        r.x = x;
        r
    }

    #[inline(never)]
    fn with_same(&self) -> Reg {
        let x = self.x;
        let x = g1(x);
        let x = g2(x);
        let x = g3(x);
        let x = g4(x);
        let x = g5(x);
        let x = g6(x);
        let x = g7(x);
        let x = g8(x);
        let x = g9(x);
        let x = g10(x);
        let x = g11(x);
        let x = g12(x);
        let x = g13(x);
        let x = g14(x);
        let x = g15(x);
        let x = g16(x);
        let x = g17(x);
        let x = g18(x);
        let x = g19(x);
        let x = g20(x);
        let x = g21(x);
        let x = g22(x);
        let x = g23(x);
        let x = g24(x);
        let x = g25(x);
        let x = g26(x);
        let x = g27(x);
        let x = g28(x);
        let x = g29(x);
        let x = g30(x);
        let x = g31(x);
        let x = g32(x);
        let x = g33(x);
        let x = g34(x);
        let x = g35(x);
        let x = g36(x);
        let x = g37(x);
        let x = g38(x);
        let x = g39(x);
        let x = g40(x);
        sink(x);
        self.clone()
    }
}

pub struct Bag {
    v: Vec<u8>,
    x: u8,
}

impl Bag {
    #[inline(never)]
    fn get(&self, i: usize) -> u8 {
        assert!(i != 1, "getter assertion");
        let x = self.x;
        let x = g1(x);
        let x = g2(x);
        let x = g3(x);
        let x = g4(x);
        let x = g5(x);
        let x = g6(x);
        let x = g7(x);
        let x = g8(x);
        let x = g9(x);
        let x = g10(x);
        let x = g11(x);
        let x = g12(x);
        let x = g13(x);
        let x = g14(x);
        let x = g15(x);
        let x = g16(x);
        let x = g17(x);
        let x = g18(x);
        let x = g19(x);
        let x = g20(x);
        let x = g21(x);
        let x = g22(x);
        let x = g23(x);
        let x = g24(x);
        let x = g25(x);
        let x = g26(x);
        let x = g27(x);
        let x = g28(x);
        let x = g29(x);
        let x = g30(x);
        let x = g31(x);
        let x = g32(x);
        let x = g33(x);
        let x = g34(x);
        let x = g35(x);
        let x = g36(x);
        let x = g37(x);
        let x = g38(x);
        let x = g39(x);
        let x = g40(x);
        sink(x);
        self.v[i]
    }

    #[inline(never)]
    fn width(&self) -> usize {
        let x = self.x;
        let x = g1(x);
        let x = g2(x);
        let x = g3(x);
        let x = g4(x);
        let x = g5(x);
        let x = g6(x);
        let x = g7(x);
        let x = g8(x);
        let x = g9(x);
        let x = g10(x);
        let x = g11(x);
        let x = g12(x);
        let x = g13(x);
        let x = g14(x);
        let x = g15(x);
        let x = g16(x);
        let x = g17(x);
        let x = g18(x);
        let x = g19(x);
        let x = g20(x);
        let x = g21(x);
        let x = g22(x);
        let x = g23(x);
        let x = g24(x);
        let x = g25(x);
        let x = g26(x);
        let x = g27(x);
        let x = g28(x);
        let x = g29(x);
        let x = g30(x);
        let x = g31(x);
        let x = g32(x);
        let x = g33(x);
        let x = g34(x);
        let x = g35(x);
        let x = g36(x);
        let x = g37(x);
        let x = g38(x);
        let x = g39(x);
        let x = g40(x);
        sink(x);
        self.v.len()
    }

    #[inline(never)]
    fn doubled(&self) -> Vec<u8> {
        assert!(self.x != 100, "collect method assertion");
        let x = self.x;
        let x = g1(x);
        let x = g2(x);
        let x = g3(x);
        let x = g4(x);
        let x = g5(x);
        let x = g6(x);
        let x = g7(x);
        let x = g8(x);
        let x = g9(x);
        let x = g10(x);
        let x = g11(x);
        let x = g12(x);
        let x = g13(x);
        let x = g14(x);
        let x = g15(x);
        let x = g16(x);
        let x = g17(x);
        let x = g18(x);
        let x = g19(x);
        let x = g20(x);
        let x = g21(x);
        let x = g22(x);
        let x = g23(x);
        let x = g24(x);
        let x = g25(x);
        let x = g26(x);
        let x = g27(x);
        let x = g28(x);
        let x = g29(x);
        let x = g30(x);
        let x = g31(x);
        let x = g32(x);
        let x = g33(x);
        let x = g34(x);
        let x = g35(x);
        let x = g36(x);
        let x = g37(x);
        let x = g38(x);
        let x = g39(x);
        let x = g40(x);
        sink(x);
        self.v.iter().map(|a| a.wrapping_mul(2)).collect()
    }
}

#[inline(never)]
fn pa4(r: &Reg) -> Reg {
    Reg::with_bump(r)
}
#[inline(never)]
fn pa3(r: &Reg) -> Reg {
    pa4(r)
}
#[inline(never)]
fn pa2(r: &Reg) -> Reg {
    pa3(r)
}
#[inline(never)]
fn pa1(r: &Reg) -> Reg {
    pa2(r)
}
#[inline(never)]
fn pv3(r: &Reg) -> Reg {
    Reg::with_bump(r)
}
#[inline(never)]
fn pv2(r: &Reg) -> Reg {
    pv3(r)
}
#[inline(never)]
fn pv1(r: &Reg) -> Reg {
    pv2(r)
}
#[inline(never)]
fn ps4(r: &Reg) -> Reg {
    Reg::with_same(r)
}
#[inline(never)]
fn ps3(r: &Reg) -> Reg {
    ps4(r)
}
#[inline(never)]
fn ps2(r: &Reg) -> Reg {
    ps3(r)
}
#[inline(never)]
fn ps1(r: &Reg) -> Reg {
    ps2(r)
}
#[inline(never)]
fn ga3(b: &Bag, i: usize) -> u8 {
    Bag::get(b, i)
}
#[inline(never)]
fn ga2(b: &Bag, i: usize) -> u8 {
    ga3(b, i)
}
#[inline(never)]
fn ga1(b: &Bag, i: usize) -> u8 {
    ga2(b, i)
}
#[inline(never)]
fn gl3(b: &Bag) -> usize {
    Bag::width(b)
}
#[inline(never)]
fn gl2(b: &Bag) -> usize {
    gl3(b)
}
#[inline(never)]
fn gl1(b: &Bag) -> usize {
    gl2(b)
}
#[inline(never)]
fn cm4(b: &Bag) -> Vec<u8> {
    Bag::doubled(b)
}
#[inline(never)]
fn cm3(b: &Bag) -> Vec<u8> {
    cm4(b)
}
#[inline(never)]
fn cm2(b: &Bag) -> Vec<u8> {
    cm3(b)
}
#[inline(never)]
fn cm1(b: &Bag) -> Vec<u8> {
    cm2(b)
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_passthrough_assert() {
    let r = Reg { m: BTreeMap::new(), x: kani::any() };
    let s = pa1(&r);
    sink(s.x);
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_passthrough_value() {
    let x: u8 = kani::any();
    kani::assume(x < 50);
    let r = Reg { m: BTreeMap::new(), x };
    let s = pv1(&r);
    assert!(s.x == r.x, "passthrough value");
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_passthrough_clean() {
    let r = Reg { m: BTreeMap::new(), x: kani::any() };
    let s = ps1(&r);
    sink(s.x);
}

#[kani::proof]
#[kani::unwind(4)]
fn bug_vec_accessor_assert() {
    let b = Bag { v: vec![1, 2, 3], x: kani::any() };
    let i: usize = kani::any();
    kani::assume(i < 3);
    sink(ga1(&b, i));
}

#[kani::proof]
#[kani::unwind(4)]
fn safe_vec_len_accessor() {
    let b = Bag { v: vec![1, 2, 3], x: kani::any() };
    sink(gl1(&b));
}

#[kani::proof]
#[kani::unwind(4)]
fn bug_collect_method_assert() {
    let b = Bag { v: vec![1, 2], x: kani::any() };
    let w = cm1(&b);
    sink(w.len());
}

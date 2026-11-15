// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwires) -- the walker's fail-closed rules for
//! a value it cannot translate, triggered by float arithmetic
//! (fix/chc-walker-fail-closed, package round 2).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   fl_untranslatable_assert_bug    -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   fl_kani_assert_call_bug         -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   fl_bailed_arm_bug               -> VERIFICATION:- FAILED  ('boom')
//!   fl_divisor_bug                  -> VERIFICATION:- FAILED  ('attempt to divide by zero')
//!   fl_unsafe_callee_bug            -> VERIFICATION:- FAILED  ('Rust intrinsic assumption failed')
//!   fl_std_expect_bug               -> VERIFICATION:- FAILED  (Kani's placeholder for the expect message)
//!   fl_std_map_closure_bug          -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!
//! WHY THIS FILE. The duals of the first rounds (walker_untranslatable_assert_dual.rs,
//! walker_kani_assert_call_dual.rs, walker_bailed_branch_dual.rs,
//! walker_untranslatable_divisor_dual.rs, walker_get_unchecked_dual.rs,
//! walker_std_callee_own_panic_dual.rs, walker_std_callee_local_obligation_dual.rs)
//! reached each rule through an array element read at a symbolic index,
//! which the walker used to skip. Item (c) builds those arrays exactly, so
//! their bug rows now fail on the exact check instead and no longer exercise
//! the rule. The walker does not translate a float multiplication (the
//! `BinaryOp` skip, `rvalue_gap_BinaryOp_root_Mul`; a float operation carries
//! no check without `--nan-check`), so `v` / `o` below are values it has no
//! term for, and each row reaches the rule its comment names (a thread-local
//! static, tried first, added an untranslatable null-pointer check of its own
//! that masked the rule): an untranslatable `Assert` (Mechanism E), `kani::assert` hook (E
//! through a call), a SwitchInt arm it cannot finish whose region can fail
//! (C), a `Div` operand (the BinOp UB check), a havocked `unsafe` std callee
//! (B), a havocked safe std callee whose own body panics (B), and one handed
//! a closure of this crate with a check (B). Every row fails, never Genuine
//! for the first four; bug rows only (a safe twin cannot prove what the walker
//! cannot translate).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_mechanism_triggers_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

#[inline(never)]
fn boom(v: u8) -> u8 {
    if v == 100 {
        panic!("boom");
    }
    v
}

// Mechanism E: an overflow `Assert` over the untranslatable `v`.
pub trait TAssert {
    fn op(&self, a: u8, i: u8, f: f32) -> u8;
}
pub struct CAssert;
impl TAssert for CAssert {
    #[allow(unused_variables)]
    fn op(&self, a: u8, i: u8, f: f32) -> u8 {
        let v = (f * 2.0) as u8;
        sink(v + 200);
        a
    }
}
impl TAssert for Other {
    fn op(&self, a: u8, _i: u8, _f: f32) -> u8 {
        a
    }
}
#[kani::proof]
fn fl_untranslatable_assert_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: f32 = kani::any();
    let o: Box<dyn TAssert> = if kani::any() { Box::new(CAssert) } else { Box::new(Other) };
    sink(o.op(a, i, f));
}

// Mechanism E through a call: `assert!` lowers to the `kani::assert` hook.
pub trait THook {
    fn op(&self, a: u8, i: u8, f: f32) -> u8;
}
pub struct CHook;
impl THook for CHook {
    #[allow(unused_variables)]
    fn op(&self, a: u8, i: u8, f: f32) -> u8 {
        let v = (f * 2.0) as u8;
        assert!(v != 100);
        a
    }
}
impl THook for Other {
    fn op(&self, a: u8, _i: u8, _f: f32) -> u8 {
        a
    }
}
#[kani::proof]
fn fl_kani_assert_call_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: f32 = kani::any();
    let o: Box<dyn THook> = if kani::any() { Box::new(CHook) } else { Box::new(Other) };
    sink(o.op(a, i, f));
}

// Mechanism C: the `v > 50` SwitchInt cannot be translated, and the region
// its arm abandons reaches `boom`'s panic.
pub trait TArm {
    fn op(&self, a: u8, i: u8, f: f32) -> u8;
}
pub struct CArm;
impl TArm for CArm {
    #[allow(unused_variables)]
    fn op(&self, a: u8, i: u8, f: f32) -> u8 {
        if a > 10 {
            let v = (f * 2.0) as u8;
            if v > 50 { boom(v) } else { v }
        } else {
            a
        }
    }
}
impl TArm for Other {
    fn op(&self, a: u8, _i: u8, _f: f32) -> u8 {
        a
    }
}
#[kani::proof]
fn fl_bailed_arm_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: f32 = kani::any();
    let o: Box<dyn TArm> = if kani::any() { Box::new(CArm) } else { Box::new(Other) };
    sink(o.op(a, i, f));
}

// The BinOp UB check over an untranslatable divisor.
pub trait TDiv {
    fn op(&self, a: u8, i: u8, f: f32) -> u8;
}
pub struct CDiv;
impl TDiv for CDiv {
    #[allow(unused_variables)]
    fn op(&self, a: u8, i: u8, f: f32) -> u8 {
        let d = (f * 2.0) as u8;
        sink(200 / d);
        a
    }
}
impl TDiv for Other {
    fn op(&self, a: u8, _i: u8, _f: f32) -> u8 {
        a
    }
}
#[kani::proof]
fn fl_divisor_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: f32 = kani::any();
    let o: Box<dyn TDiv> = if kani::any() { Box::new(CDiv) } else { Box::new(Other) };
    sink(o.op(a, i, f));
}

// Mechanism B: an `unsafe` std callee whose slice argument does not
// translate (the array has an untranslatable element) is havocked.
pub trait TGu {
    fn op(&self, a: u8, i: u8, f: f32) -> u8;
}
pub struct CGu;
impl TGu for CGu {
    #[allow(unused_variables)]
    fn op(&self, a: u8, i: u8, f: f32) -> u8 {
        let arr = [(f * 2.0) as u8, 1, 2, 3];
        unsafe { *arr.get_unchecked(i as usize) }
    }
}
impl TGu for Other {
    fn op(&self, a: u8, _i: u8, _f: f32) -> u8 {
        a
    }
}
#[kani::proof]
fn fl_unsafe_callee_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: f32 = kani::any();
    let o: Box<dyn TGu> = if kani::any() { Box::new(CGu) } else { Box::new(Other) };
    sink(o.op(a, i, f));
}

// Mechanism B: a safe std callee whose own body panics on its argument.
pub trait TExpect {
    fn op(&self, a: u8, i: u8, f: f32) -> u8;
}
pub struct CExpect;
impl TExpect for CExpect {
    #[allow(unused_variables)]
    fn op(&self, a: u8, i: u8, f: f32) -> u8 {
        let arr = [None, Some(250u8), Some((f * 2.0) as u8)];
        let o = arr[(i % 3) as usize];
        sink(o.expect("none reached"));
        a
    }
}
impl TExpect for Other {
    fn op(&self, a: u8, _i: u8, _f: f32) -> u8 {
        a
    }
}
#[kani::proof]
fn fl_std_expect_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: f32 = kani::any();
    let o: Box<dyn TExpect> = if kani::any() { Box::new(CExpect) } else { Box::new(Other) };
    sink(o.op(a, i, f));
}

// Mechanism B: a safe std callee handed a closure of this crate with a check.
pub trait TMap {
    fn op(&self, a: u8, i: u8, f: f32) -> u8;
}
pub struct CMap;
impl TMap for CMap {
    #[allow(unused_variables)]
    fn op(&self, a: u8, i: u8, f: f32) -> u8 {
        let arr = [None, Some(250u8), Some((f * 2.0) as u8)];
        let o = arr[(i % 3) as usize];
        sink(o.map(|x| x + 200));
        a
    }
}
impl TMap for Other {
    fn op(&self, a: u8, _i: u8, _f: f32) -> u8 {
        a
    }
}
#[kani::proof]
fn fl_std_map_closure_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: f32 = kani::any();
    let o: Box<dyn TMap> = if kani::any() { Box::new(CMap) } else { Box::new(Other) };
    sink(o.op(a, i, f));
}

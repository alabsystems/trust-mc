// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a user assertion whose condition the
//! CHC inline walker cannot translate, reached as a CALL (Mechanism E through
//! `kani::assert`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_assert_value_method_multi   -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   bug_assert_value_method_single  -> VERIFICATION:- FAILED  (same)
//!   bug_kani_assert_multi           -> VERIFICATION:- FAILED  ('v must not be 100')
//!   bug_assert_ne_multi             -> VERIFICATION:- FAILED  ('assertion failed: v != 100' family)
//!   bug_assert_dyn_fn_closure       -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   bug_unit_method_bailed_arm      -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   safe_assert_value_method_multi  -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. trust-mc's `library/std` lowers `assert!`,
//! `assert_eq!` / `assert_ne!` and `kani::assert` to the `kani::assert` hook,
//! a CALL, not a MIR `Assert` terminator. `v` is an array element read at a
//! symbolic index, which the walker skips, so the hook's condition does not
//! translate. `kani_inline.rs` `handle_inline_kani_assert_call` returned
//! without recording anything, so every bug row verified SUCCESSFUL clean on
//! the a15de6272 base bundle and on the first cut of fix/chc-walker-fail-closed
//! (whose Mechanism E fix covered the `Assert` terminator only;
//! walker_untranslatable_assert_dual.rs uses `v + 200`, which never reached
//! the hook). FIXED in the review round: the assertion is recorded as a check
//! that fails wherever it is reached, never certified (`uncertified_check.rs`),
//! with the assertion's message, so the bug rows FAIL non-certified; the safe
//! row pays the precision cost until the walker builds the array exactly.
//! Promoted from the review probes rv_kassert.rs and rv_consumers.rs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_kani_assert_call_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;

// `assert!` in a value-returning method whose result does not read `v`.
pub trait T1 {
    fn op(&self, a: u8, i: u8) -> u8;
}
pub struct C1;
impl T1 for C1 {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        assert!(v != 100);
        a
    }
}
impl T1 for Other {
    fn op(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_assert_value_method_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn T1> = if kani::any() { Box::new(C1) } else { Box::new(Other) };
    sink(o.op(a, i));
}

#[kani::proof]
fn bug_assert_value_method_single() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn T1> = Box::new(C1);
    sink(o.op(a, i));
}

#[kani::proof]
fn safe_assert_value_method_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a != 100);
    let o: Box<dyn T1> = if kani::any() { Box::new(C1) } else { Box::new(Other) };
    sink(o.op(a, i));
}

// `kani::assert` directly.
pub trait T2 {
    fn op(&self, a: u8, i: u8) -> u8;
}
pub struct C2;
impl T2 for C2 {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        kani::assert(v != 100, "v must not be 100");
        a
    }
}
impl T2 for Other {
    fn op(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_kani_assert_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn T2> = if kani::any() { Box::new(C2) } else { Box::new(Other) };
    sink(o.op(a, i));
}

// `assert_ne!`.
pub trait T3 {
    fn op(&self, a: u8, i: u8) -> u8;
}
pub struct C3;
impl T3 for C3 {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        assert_ne!(v, 100);
        a
    }
}
impl T3 for Other {
    fn op(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_assert_ne_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn T3> = if kani::any() { Box::new(C3) } else { Box::new(Other) };
    sink(o.op(a, i));
}

// `assert!` reached through a `dyn Fn` closure (fn-trait dispatch).
#[kani::proof]
fn bug_assert_dyn_fn_closure() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let f: Box<dyn Fn(u8, u8) -> u8> = if kani::any() {
        Box::new(|a: u8, i: u8| {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            assert!(v != 100);
            a
        })
    } else {
        Box::new(|a: u8, _i: u8| a)
    };
    sink(f(a, i));
}

// A unit-returning method: `assert!` in an arm; nothing reads the result.
pub trait T4 {
    fn act(&self, a: u8, i: u8);
}
pub struct C4;
impl T4 for C4 {
    fn act(&self, a: u8, i: u8) {
        if a > 10 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            assert!(v != 100);
        }
    }
}
impl T4 for Other {
    fn act(&self, _a: u8, _i: u8) {}
}

#[kani::proof]
fn bug_unit_method_bailed_arm() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn T4> = if kani::any() { Box::new(C4) } else { Box::new(Other) };
    o.act(a, i);
}

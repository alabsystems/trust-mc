// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (KNOWN-RED missed-bug tracker) -- a `&dyn` / `Box<dyn>`
//! method body walked by the CHC INLINE WALKER that reads a place it reaches
//! through a DEREF: `*a` for a `&mut u8` parameter, `self.x` for a field of
//! `*self`.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_add_after_write_zero  -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_add_after_write_guard -> VERIFICATION:- FAILED  (same check)
//!   bug_add_param_no_write    -> VERIFICATION:- FAILED  (same check)
//!   bug_read_after_write      -> VERIFICATION:- FAILED  ('assertion failed: r == 0')
//!   safe_read_after_write     -> VERIFICATION:- SUCCESSFUL
//!   bug_field_read_after_write  -> VERIFICATION:- FAILED  ('assertion failed: r == 7')
//!   safe_field_read_after_write -> VERIFICATION:- SUCCESSFUL
//!   bug_add_after_write_fnptr -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow'; control)
//!   bug_write_reaches_caller  -> VERIFICATION:- FAILED  ('assertion failed: a == 7')
//!   safe_write_reaches_caller -> VERIFICATION:- SUCCESSFUL
//!   bug_second_param_field_lt -> VERIFICATION:- FAILED  ('start < end')
//!   bug_write_then_compare    -> VERIFICATION:- FAILED  ('compares the written value')
//!
//! MECHANISM (pre-existing, NOT fixed; main and the walker branch agree): the
//! dyn-dispatch walker records a write through a deref (`*a = 255`,
//! `self.x = 200`) only to the host memory model when
//! `apply_inline_projected_assign` declines and `try_inline_memory_store`
//! succeeds (`codegen_call_virtual_inline/statement_exec.rs`, projected-assign
//! path); `local_exprs` is not updated, so a later read of the place in the same
//! body sees the value from before the write (`self.x` after `self.x = 200`
//! reads the constructor's 7). A `*param` read does not see the CALLER's value
//! either: it reads as 0 whatever was passed, written or not
//! (`bug_add_param_no_write`, `a = 255`). Every walked check built on such a read
//! -- an `unchecked_*` check or an `assert!` -- tests the wrong value, and the
//! harness verifies SUCCESSFUL clean. The fn-pointer, direct-call and
//! `Box<dyn Fn>` closure routes read the written value (`bug_add_after_write_fnptr`
//! FAILS on the walker branch; it was SUCCESSFUL on main).
//!
//! Three more faces of the same deref read:
//! * a write through `*a` never reaches the CALLER (`bug_write_reaches_caller`);
//! * a field of a NON-FIRST reference parameter (`w.start` with `w` the second
//!   argument of a nested helper) has no self-field-map entry, and
//!   `resolve_projected_place` (`call/inline_shared/field_map_projection.rs`)
//!   unflattens the BV64 ADDRESS as the struct (`try_unflatten_bv_to_datatype`),
//!   so `w.start < w.end` compares pointer bits, always `0 < 0`
//!   (`bug_second_param_field_lt`);
//! * a field of the FIRST parameter is answered from the self-field snapshot
//!   taken at entry (`build_self_field_map`), so a comparison after
//!   `r.a = v` reads the old `a` (`bug_write_then_compare`).
//!
//! Promoted from the 2026-09-24 adversarial review (validity-prover lens,
//! cv_stale.rs / cv_stale2.rs; verifier probes rs_dyn.rs, rs_field.rs,
//! rs_disamb.rs and rs_mech.rs; referent lens a3_write_then_cmp.rs and
//! c3_controls.rs).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_dyn_deref_write_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait W {
    fn add_after_write(&self, a: &mut u8) -> u8;
    fn add_after_write_guard(&self, a: &mut u8, e: u8) -> u8;
    fn add_no_write(&self, a: &mut u8) -> u8;
    fn read_after_write(&self, a: &mut u8) -> u8;
    fn field(&mut self) -> u8;
    fn wr(&self, a: &mut u8);
    fn lt_second(&self, x: u8, w: &Window) -> bool;
}
pub struct Window {
    pub start: u8,
    pub end: u8,
}
pub struct Pair {
    pub a: u8,
    pub b: u8,
}
#[inline(never)]
fn lt_binop(_x: u8, w: &Window) -> bool {
    w.start < w.end
}
#[inline(never)]
fn direct_write_cmp(r: &mut Pair, v: u8) -> bool {
    r.a = v;
    PartialOrd::lt(&r.a, &r.b)
}
pub struct A {
    x: u8,
}
pub struct B {
    x: u8,
}
macro_rules! imp {
    ($t:ty) => {
        impl W for $t {
            fn add_after_write(&self, a: &mut u8) -> u8 {
                *a = 255;
                unsafe { (*a).unchecked_add(1) }
            }
            fn add_after_write_guard(&self, a: &mut u8, e: u8) -> u8 {
                if *a < e {
                    *a = 255;
                    unsafe { (*a).unchecked_add(1) }
                } else {
                    0
                }
            }
            fn add_no_write(&self, a: &mut u8) -> u8 {
                unsafe { (*a).unchecked_add(1) }
            }
            fn read_after_write(&self, a: &mut u8) -> u8 {
                *a = 200;
                *a
            }
            fn field(&mut self) -> u8 {
                self.x = 200;
                self.x
            }
            fn wr(&self, a: &mut u8) {
                *a = 200;
            }
            fn lt_second(&self, x: u8, w: &Window) -> bool {
                lt_binop(x, w)
            }
        }
    };
}
imp!(A);
imp!(B);

// The write-then-compare row keeps the review probe's own shape: a trait of
// its own over unit structs (in `W`, whose impls carry a field, the same body
// ran the solver out of budget instead).
pub trait WriteCmp {
    fn write_cmp(&self, p: &mut Pair, v: u8) -> bool;
}
pub struct CA;
pub struct CB;
impl WriteCmp for CA {
    fn write_cmp(&self, p: &mut Pair, v: u8) -> bool {
        direct_write_cmp(p, v)
    }
}
impl WriteCmp for CB {
    fn write_cmp(&self, p: &mut Pair, v: u8) -> bool {
        direct_write_cmp(p, v)
    }
}

fn pick(x: u8) -> Box<dyn W> {
    if kani::any() { Box::new(A { x }) } else { Box::new(B { x }) }
}

fn add_after(a: &mut u8) -> u8 {
    *a = 255;
    unsafe { (*a).unchecked_add(1) }
}
fn add_after_b(a: &mut u8) -> u8 {
    *a = 255;
    unsafe { (*a).unchecked_add(1) }
}

#[kani::proof]
fn bug_add_after_write_zero() {
    let mut a: u8 = 0;
    sink(pick(0).add_after_write(&mut a));
}

#[kani::proof]
fn bug_add_after_write_guard() {
    let mut a: u8 = kani::any();
    sink(pick(0).add_after_write_guard(&mut a, kani::any()));
}

#[kani::proof]
fn bug_add_param_no_write() {
    let mut a: u8 = 255;
    sink(pick(0).add_no_write(&mut a));
}

#[kani::proof]
fn bug_read_after_write() {
    let mut a: u8 = 0;
    let r = pick(0).read_after_write(&mut a);
    assert!(r == 0);
}

#[kani::proof]
fn safe_read_after_write() {
    let mut a: u8 = 0;
    let r = pick(0).read_after_write(&mut a);
    assert!(r == 200);
}

#[kani::proof]
fn bug_field_read_after_write() {
    let mut d = pick(7);
    let r = d.field();
    assert!(r == 7);
}

#[kani::proof]
fn safe_field_read_after_write() {
    let mut d = pick(7);
    let r = d.field();
    assert!(r == 200);
}

#[kani::proof]
fn bug_add_after_write_fnptr() {
    let mut a: u8 = 0;
    let f: fn(&mut u8) -> u8 = if kani::any() { add_after } else { add_after_b };
    sink(f(&mut a));
}

#[kani::proof]
fn bug_write_reaches_caller() {
    let mut a: u8 = 7;
    pick(0).wr(&mut a);
    assert!(a == 7);
}

#[kani::proof]
fn safe_write_reaches_caller() {
    let mut a: u8 = 7;
    pick(0).wr(&mut a);
    assert!(a == 200);
}

#[kani::proof]
fn bug_second_param_field_lt() {
    let w = Window { start: kani::any(), end: kani::any() };
    kani::assume(w.start < w.end);
    assert!(!pick(0).lt_second(0, &w), "start < end");
}

// After the write a = v >= b, so the comparison is false.
#[kani::proof]
fn bug_write_then_compare() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let v: u8 = kani::any();
    kani::assume(p.a < p.b);
    kani::assume(v >= p.b);
    let o: Box<dyn WriteCmp> = if kani::any() { Box::new(CA) } else { Box::new(CB) };
    let s = o.write_cmp(&mut p, v);
    assert!(s, "compares the written value");
}

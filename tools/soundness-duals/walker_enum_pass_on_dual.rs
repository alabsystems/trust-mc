// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a fieldless enum returned by a callee
//! the walker havocs, where the callee can PASS ON an invalid value its
//! caller forged (fix/chc-walker-fail-closed, repair round 2, walker
//! fail-closed review 6 round 2 finding 2; the review's probe
//! `rp1_forged_enum.rs`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   f1_forged_by_value_bug        -> VERIFICATION:- FAILED  ('unreachable code')
//!   f2_forged_by_ref_bug          -> VERIFICATION:- FAILED  ('unreachable code')
//!   f3_forged_receiver_field_bug  -> VERIFICATION:- FAILED  ('unreachable code')
//!   f1_valid_by_value_safe        -> VERIFICATION:- SUCCESSFUL
//!   f3_valid_receiver_field_safe  -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Repair round 1 assumed a nested-call havoc of a
//! fieldless enum holds a valid discriminant whenever the callee cannot
//! FORGE one (`obligation_free_walk::instance_may_forge_invalid_value`). That
//! walk counts a copy of an argument, or a read through `&E`, as building a
//! value of its own type, so a float helper returning its enum argument
//! handed back an invalid value the harness wrote through `*mut u8`, the
//! assumption pruned that execution, and Kani's "unreachable code" failure
//! verified clean (f1, f2 on the repair-round-1 bundle 8626027c). The
//! assumption now needs the call not to be able to pass one on
//! (`obligation_free_walk::call_may_return_invalid_value`): no argument whose
//! type can hold the enum, no constant reference to one anywhere the callee
//! reaches; an argument OF the enum's type, by value, joins the result's
//! possible values (`valid(h) or h == e`) instead.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_enum_pass_on_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum E3 {
    A = 0,
    B = 1,
    C = 2,
}

// A float helper the walker gives up on, which returns its enum argument on
// one path.
#[inline(never)]
fn pass_f(e: E3, x: f32) -> E3 {
    if x < 0.0 { e } else { E3::A }
}

// The same through a reference.
#[inline(never)]
fn get_f(e: &E3, x: f32) -> E3 {
    if x < 0.0 { *e } else { E3::A }
}

pub trait Fp {
    fn f(&self, e: E3, x: f32) -> u8;
}
pub struct Cv;
impl Fp for Cv {
    fn f(&self, e: E3, x: f32) -> u8 {
        match pass_f(e, x * 2.0) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }
}
pub struct Cr;
impl Fp for Cr {
    fn f(&self, e: E3, x: f32) -> u8 {
        match get_f(&e, x * 2.0) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }
}
impl Fp for Other {
    fn f(&self, _e: E3, _x: f32) -> u8 {
        2
    }
}

// The receiver holds the forged value.
pub struct Holder {
    e: E3,
}
pub trait Hf {
    fn f(&self, x: f32) -> u8;
}
impl Hf for Holder {
    fn f(&self, x: f32) -> u8 {
        match get_f(&self.e, x * 2.0) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }
}
impl Hf for Other {
    fn f(&self, _x: f32) -> u8 {
        2
    }
}

fn forged() -> E3 {
    let b: u8 = kani::any();
    let mut e = E3::A;
    unsafe {
        *(&mut e as *mut E3 as *mut u8) = b;
    }
    e
}

#[kani::proof]
fn f1_forged_by_value_bug() {
    let e = forged();
    let x: f32 = kani::any();
    let o: Box<dyn Fp> = if kani::any() { Box::new(Cv) } else { Box::new(Other) };
    sink(o.f(e, x));
}

#[kani::proof]
fn f2_forged_by_ref_bug() {
    let e = forged();
    let x: f32 = kani::any();
    let o: Box<dyn Fp> = if kani::any() { Box::new(Cr) } else { Box::new(Other) };
    sink(o.f(e, x));
}

#[kani::proof]
fn f3_forged_receiver_field_bug() {
    let e = forged();
    let x: f32 = kani::any();
    let o: Box<dyn Hf> = if kani::any() { Box::new(Holder { e }) } else { Box::new(Other) };
    sink(o.f(x));
}

// Safe twins: the same shapes with a valid enum.
#[kani::proof]
fn f1_valid_by_value_safe() {
    let k: u8 = kani::any();
    let e = if k == 0 { E3::A } else if k == 1 { E3::B } else { E3::C };
    let x: f32 = kani::any();
    let o: Box<dyn Fp> = if kani::any() { Box::new(Cv) } else { Box::new(Other) };
    let r = o.f(e, x);
    assert!(r >= 1 && r <= 3);
}

#[kani::proof]
fn f3_valid_receiver_field_safe() {
    let k: u8 = kani::any();
    let e = if k == 0 { E3::A } else if k == 1 { E3::B } else { E3::C };
    let x: f32 = kani::any();
    let o: Box<dyn Hf> = if kani::any() { Box::new(Holder { e }) } else { Box::new(Other) };
    let r = o.f(x);
    assert!(r >= 1 && r <= 3);
}

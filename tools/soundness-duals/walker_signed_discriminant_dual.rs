// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a walked `match` on an enum with a
//! negative discriminant (`std::cmp::Ordering::Less` is -1), and on a
//! fieldless enum returned by a callee the walker gives up on
//! (fix/chc-walker-fail-closed, repair round 1, walker fail-closed review 6
//! findings 2 and 3; the review's probes, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   s1_cmp_match_safe            -> VERIFICATION:- SUCCESSFUL
//!   s1_cmp_match_bug             -> VERIFICATION:- FAILED  ('assertion failed: r != 1')
//!   s2_const_less_safe           -> VERIFICATION:- SUCCESSFUL
//!   s3_less_value_bug            -> VERIFICATION:- FAILED  ('assertion failed: o.f(a, b) == 20')
//!   s3_less_value_safe           -> VERIFICATION:- SUCCESSFUL
//!   s4_less_panic_bug            -> VERIFICATION:- FAILED  ('less')
//!   s5_neg_repr_bug              -> VERIFICATION:- FAILED  ('assertion failed: r != 1')
//!   h1_havocked_enum_safe        -> VERIFICATION:- SUCCESSFUL
//!   h1_forged_enum_bug           -> VERIFICATION:- FAILED  ('invalid enum construction: value is not a valid discriminant for this enum')
//!
//! MECHANISM UNDER TEST. SwitchInt case values are the discriminant's bits
//! at the width of its type: `Ordering::Less`, an `i8` of -1, is case 255.
//! The walker holds an enum discriminant as a pointer-width term,
//! sign-extended for a signed repr (`inline_shared/discriminant.rs`), and
//! compared it against `bitvec_const(255, 64)`: no case matched. With the
//! exhaustive `otherwise` arm an "unreachable code" obligation (package
//! round 1 item d), every walked exhaustive `Ordering` match failed Genuine
//! on programs Kani proves (`s1_cmp_match_safe`, `s2_const_less_safe` on the
//! round-2 bundle 5d66fe32); on main an explicit `Less` arm was never selected,
//! so its value was never the result and a `Less => panic!()` arm's
//! obligation was vacuous (`s3_less_value_bug`, `s4_less_panic_bug` SUCCESSFUL
//! clean on main c22e1022e and on the round-2 bundle: missed bugs). The walker
//! now compares the discriminant at its type's width (`switchint.rs`
//! `switch_discriminant_at_type_width`), where the case values live.
//!
//! The `h1` rows: an enum returned by a float helper the walker havocs. The
//! havoc ranged over every bit pattern, so the exhaustive `otherwise` arm was
//! reachable on values no execution produces (`h1_havocked_enum_safe` FAILED
//! OverApproximation on the round-2 bundle; main proves it). The
//! havoc is now constrained to the enum's discriminants when the callee
//! cannot manufacture another value (no transmute, raw-pointer access, union
//! field or unreadable callee anywhere it reaches:
//! `obligation_free_walk::instance_may_forge_invalid_value`). Its bug twin
//! forges one through a transmute, which Kani reports at the transmute (the
//! walker at the match's exhaustive `otherwise`, "unreachable code").
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_signed_discriminant_dual.rs

use std::cmp::Ordering;

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

pub trait Cmp { fn f(&self, a: u8, b: u8) -> u8; }
impl Cmp for Other { fn f(&self, _a: u8, _b: u8) -> u8 { 20 } }

// An exhaustive match on `a.cmp(&b)`.
pub struct Exh;
impl Cmp for Exh {
    fn f(&self, a: u8, b: u8) -> u8 {
        match a.cmp(&b) {
            Ordering::Less => 1,
            Ordering::Equal => 2,
            Ordering::Greater => 3,
        }
    }
}
#[kani::proof]
fn s1_cmp_match_safe() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Cmp> = if kani::any() { Box::new(Exh) } else { Box::new(Other) };
    let r = o.f(a, b);
    assert!((r >= 1 && r <= 3) || r == 20);
}
#[kani::proof]
fn s1_cmp_match_bug() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Cmp> = if kani::any() { Box::new(Exh) } else { Box::new(Other) };
    let r = o.f(a, b);
    assert!(r != 1);
}

// A constant `Less`, folded.
pub struct Const;
impl Cmp for Const {
    fn f(&self, a: u8, _b: u8) -> u8 {
        let o = Ordering::Less;
        let base = match o {
            Ordering::Less => 10u8,
            Ordering::Equal => 20,
            Ordering::Greater => 30,
        };
        base.wrapping_add(a & 1)
    }
}
#[kani::proof]
fn s2_const_less_safe() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Cmp> = if kani::any() { Box::new(Const) } else { Box::new(Other) };
    let r = o.f(a, b);
    assert!(r == 10 || r == 11 || r == 20);
}

// An explicit `Less` arm, the rest `_`.
pub struct Val;
impl Cmp for Val {
    fn f(&self, a: u8, b: u8) -> u8 {
        match a.cmp(&b) {
            Ordering::Less => 10,
            _ => 20,
        }
    }
}
#[kani::proof]
fn s3_less_value_bug() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Cmp> = if kani::any() { Box::new(Val) } else { Box::new(Other) };
    assert!(o.f(a, b) == 20);
}
#[kani::proof]
fn s3_less_value_safe() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Cmp> = if kani::any() { Box::new(Val) } else { Box::new(Other) };
    let r = o.f(a, b);
    assert!(r == 10 || r == 20);
}

pub struct Pan;
impl Cmp for Pan {
    fn f(&self, a: u8, b: u8) -> u8 {
        match a.cmp(&b) {
            Ordering::Less => panic!("less"),
            _ => 20,
        }
    }
}
#[kani::proof]
fn s4_less_panic_bug() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Cmp> = if kani::any() { Box::new(Pan) } else { Box::new(Other) };
    sink(o.f(a, b));
}

// A `#[repr(i8)]` enum with a negative variant.
#[derive(Clone, Copy)]
#[repr(i8)]
pub enum N { M = -3, Z = 0, P = 7 }
pub trait Neg { fn f(&self, n: N) -> u8; }
impl Neg for Other { fn f(&self, _n: N) -> u8 { 2 } }
pub struct CN;
impl Neg for CN {
    fn f(&self, n: N) -> u8 {
        match n {
            N::M => 1,
            N::Z => 2,
            N::P => 3,
        }
    }
}
#[kani::proof]
fn s5_neg_repr_bug() {
    let n = if kani::any() { N::M } else if kani::any() { N::Z } else { N::P };
    let o: Box<dyn Neg> = if kani::any() { Box::new(CN) } else { Box::new(Other) };
    let r = o.f(n);
    assert!(r != 1);
}

// A fieldless enum from a callee the walker havocs (float arithmetic).
#[derive(Clone, Copy)]
pub enum E3 { A, B, C }
#[inline(never)]
fn classify_f(x: f32) -> E3 {
    if x < 0.0 { E3::A } else if x == 0.0 { E3::B } else { E3::C }
}
pub trait Fl { fn f(&self, x: f32) -> u8; }
impl Fl for Other { fn f(&self, _x: f32) -> u8 { 2 } }
pub struct C6;
impl Fl for C6 {
    fn f(&self, x: f32) -> u8 {
        match classify_f(x * 2.0) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }
}
#[kani::proof]
fn h1_havocked_enum_safe() {
    let x: f32 = kani::any();
    let o: Box<dyn Fl> = if kani::any() { Box::new(C6) } else { Box::new(Other) };
    let r = o.f(x);
    assert!(r >= 1 && r <= 3);
}

// The same shape with a callee that forges the enum from any byte.
#[inline(never)]
fn forge_f(x: f32) -> E3 {
    let b = (x * 2.0) as u8;
    unsafe { std::mem::transmute::<u8, E3>(b) }
}
// Its own trait, so the safe row's dispatch cannot reach it.
pub trait Fg { fn f(&self, x: f32) -> u8; }
impl Fg for Other { fn f(&self, _x: f32) -> u8 { 2 } }
pub struct C7;
impl Fg for C7 {
    fn f(&self, x: f32) -> u8 {
        match forge_f(x) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }
}
#[kani::proof]
fn h1_forged_enum_bug() {
    let x: f32 = kani::any();
    let o: Box<dyn Fg> = if kani::any() { Box::new(C7) } else { Box::new(Other) };
    sink(o.f(x));
}

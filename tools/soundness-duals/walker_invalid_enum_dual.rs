// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- an enum value with an invalid
//! discriminant, written through a raw pointer, matched in a body the CHC
//! inline walker walks.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_raw_write_in_harness_match_in_walk_multi   -> VERIFICATION:- FAILED  (unreachable code)
//!   safe_valid_unit_enum_match_multi               -> VERIFICATION:- SUCCESSFUL
//!   bug_raw_write_match_harness_body               -> VERIFICATION:- FAILED  (unreachable code; control)
//!   bug_transmute_in_walk_multi                    -> VERIFICATION:- FAILED  (invalid enum construction)
//!   bug_raw_write_match_in_walk_multi              -> VERIFICATION:- FAILED  (unreachable code)
//!   safe_raw_write_valid_match_in_walk_multi       -> VERIFICATION:- SUCCESSFUL
//!   bug_dt_raw_tag_write_in_harness_match_in_walk_multi -> VERIFICATION:- FAILED (unreachable code)
//!   bug_dt_raw_tag_write_harness_body              -> VERIFICATION:- FAILED  (unreachable code)
//!   bug_option_raw_tag_write_harness_body          -> VERIFICATION:- FAILED  (assertion failed: o.is_some())
//!
//! MECHANISM UNDER TEST. The walker kept the `otherwise` arm rustc adds to an
//! exhaustive enum `match` dead, on the argument that validity is checked where
//! a value is BUILT ("invalid enum construction"). That covers a transmute
//! (bug_transmute_in_walk_multi is FAILED Genuine on every bundle) but not a
//! raw byte write: a fieldless enum is a raw bitvector in the encoding and
//! keeps whatever bits were written. The harness writes `x` into `e` through a
//! `*mut u8` (the statement path models the write, and its own match fails:
//! the control), then a walked method matches `e`: on main c22e1022e
//! bug_raw_write_in_harness_match_in_walk_multi verified SUCCESSFUL clean.
//! FIXED in the package round of fix/chc-walker-fail-closed (item d): the
//! exemption holds only for a data-carrying enum (a datatype sort, every term
//! a variant); a fieldless enum's exhaustive `otherwise` is an "unreachable
//! code" obligation whose not-taken condition every valid discriminant
//! discharges (safe_valid_unit_enum_match_multi verifies).
//!
//! The walked-body raw writes (`_in_walk_` rows) are not modelled exactly and
//! fail closed on every bundle; their safe twin is a known-red false failure.
//!
//! KNOWN RED, statement path (not the walker's exemption): a raw write of an
//! invalid TAG into a data-carrying enum (`F`) decodes to a valid variant, and
//! a raw tag write into an `Option<u8>` (a flattened `(is_some, value)`
//! local) is lost to the type-indexed memory model, so both the harness-body
//! rows and the walked row verify SUCCESSFUL clean on main and on the branch.
//! They are marked known-red missed bugs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_invalid_enum_dual.rs

#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum E {
    A = 0,
    B = 1,
}

#[inline(never)]
fn classify(e: E) -> u8 {
    match e {
        E::A => 10,
        E::B => 20,
    }
}

// The raw write in the harness, the match in a walked method's callee.
pub trait T2 {
    fn run(&self, e: E) -> u8;
}
pub struct C2;
impl T2 for C2 {
    fn run(&self, e: E) -> u8 {
        classify(e)
    }
}
impl T2 for Other {
    fn run(&self, _e: E) -> u8 {
        0
    }
}

#[kani::proof]
fn bug_raw_write_in_harness_match_in_walk_multi() {
    let x: u8 = kani::any();
    let mut e = E::A;
    unsafe {
        *(&mut e as *mut E as *mut u8) = x;
    }
    let o: Box<dyn T2> = if kani::any() { Box::new(C2) } else { Box::new(Other) };
    sink(o.run(e));
}

// The other direction: a validly built fieldless enum matched in the walk.
#[kani::proof]
fn safe_valid_unit_enum_match_multi() {
    let x: u8 = kani::any();
    let e = if x > 5 { E::A } else { E::B };
    let o: Box<dyn T2> = if kani::any() { Box::new(C2) } else { Box::new(Other) };
    sink(o.run(e));
}

// Control: the same raw write and match in the harness body.
#[kani::proof]
fn bug_raw_write_match_harness_body() {
    let x: u8 = kani::any();
    let mut e = E::A;
    unsafe {
        *(&mut e as *mut E as *mut u8) = x;
    }
    sink(classify(e));
}

// A transmute in the walked method: checked where the value is built.
pub trait T3 {
    fn run(&self, x: u8) -> u8;
}
pub struct C3;
impl T3 for C3 {
    fn run(&self, x: u8) -> u8 {
        let e: E = unsafe { core::mem::transmute(x) };
        classify(e)
    }
}
impl T3 for Other {
    fn run(&self, x: u8) -> u8 {
        x
    }
}

#[kani::proof]
fn bug_transmute_in_walk_multi() {
    let x: u8 = kani::any();
    let o: Box<dyn T3> = if kani::any() { Box::new(C3) } else { Box::new(Other) };
    sink(o.run(x));
}

// The raw write and the match both inside the walked method.
pub trait T1 {
    fn run(&self, x: u8) -> u8;
}
pub struct C1;
impl T1 for C1 {
    fn run(&self, x: u8) -> u8 {
        let mut e = E::A;
        unsafe {
            *(&mut e as *mut E as *mut u8) = x;
        }
        match e {
            E::A => 10,
            E::B => 20,
        }
    }
}
impl T1 for Other {
    fn run(&self, x: u8) -> u8 {
        x
    }
}

#[kani::proof]
fn bug_raw_write_match_in_walk_multi() {
    let x: u8 = kani::any();
    let o: Box<dyn T1> = if kani::any() { Box::new(C1) } else { Box::new(Other) };
    sink(o.run(x));
}

#[kani::proof]
fn safe_raw_write_valid_match_in_walk_multi() {
    let x: u8 = kani::any();
    kani::assume(x <= 1);
    let o: Box<dyn T1> = if kani::any() { Box::new(C1) } else { Box::new(Other) };
    sink(o.run(x));
}

// Known red (statement path): an invalid tag written into a data-carrying enum.
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum F {
    A(u8) = 0,
    B = 1,
}

#[inline(never)]
fn classify_f(f: F) -> u8 {
    match f {
        F::A(v) => v,
        F::B => 20,
    }
}

pub trait T5 {
    fn run(&self, f: F) -> u8;
}
pub struct C5;
impl T5 for C5 {
    fn run(&self, f: F) -> u8 {
        classify_f(f)
    }
}
impl T5 for Other {
    fn run(&self, _f: F) -> u8 {
        0
    }
}

#[kani::proof]
fn bug_dt_raw_tag_write_in_harness_match_in_walk_multi() {
    let x: u8 = kani::any();
    let mut f = F::B;
    unsafe {
        *(&mut f as *mut F as *mut u8) = x;
    }
    let o: Box<dyn T5> = if kani::any() { Box::new(C5) } else { Box::new(Other) };
    sink(o.run(f));
}

#[kani::proof]
fn bug_dt_raw_tag_write_harness_body() {
    let x: u8 = kani::any();
    let mut f = F::B;
    unsafe {
        *(&mut f as *mut F as *mut u8) = x;
    }
    sink(classify_f(f));
}

// Known red (statement path): a tag byte written into an `Option<u8>`.
#[kani::proof]
fn bug_option_raw_tag_write_harness_body() {
    let x: u8 = kani::any();
    kani::assume(x <= 1);
    let mut o: Option<u8> = Some(5);
    unsafe {
        *(&mut o as *mut Option<u8> as *mut u8) = x;
    }
    assert!(o.is_some());
}

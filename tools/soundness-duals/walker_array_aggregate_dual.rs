// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- arrays a walked body builds
//! (fix/chc-walker-fail-closed, package round 2 item c).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   c_array_read_assert_safe      -> VERIFICATION:- SUCCESSFUL
//!   c_array_read_assert_bug       -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   c_option_array_read_safe      -> VERIFICATION:- SUCCESSFUL
//!   c_option_array_read_bug       -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   c_array_get_unchecked_safe    -> VERIFICATION:- SUCCESSFUL
//!   c_array_get_unchecked_bug     -> VERIFICATION:- FAILED  ('Rust intrinsic assumption failed')
//!   c_array_slice_len_safe        -> VERIFICATION:- SUCCESSFUL
//!   c_array_slice_len_bug         -> VERIFICATION:- FAILED  ('assertion failed: s == 2')
//!
//! MECHANISM UNDER TEST. `inline_aggregate.rs` built datatype sorts only, so
//! an array aggregate in a walked body was skipped and every read of it was
//! untranslatable: a check over it became an uncertified reach check (the
//! safe rows FAILED) and a call taking it was havocked. The walker now builds
//! the array exactly: the constant array of the first element with a store
//! per later one, at `translate_ty`'s sort (a flattenable datatype element
//! packed, and unpacked again by the `Index` read), and a slice view of it
//! carries the array's length (`subslice_len`), so `<[T]>::get_unchecked`
//! checks `i < N`. The bug rows FAIL on their check, Genuine; the first
//! round's bundle FAILS every row (the safe ones uncertified).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_array_aggregate_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

pub trait Read { fn read(&self, a: u8, i: u8) -> u8; }
pub struct C;
impl Read for C {
    fn read(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        assert!(v != 100);
        v
    }
}
impl Read for Other { fn read(&self, a: u8, _i: u8) -> u8 { a } }
#[kani::proof]
fn c_array_read_assert_safe() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a != 100);
    let o: Box<dyn Read> = if kani::any() { Box::new(C) } else { Box::new(Other) };
    sink(o.read(a, i));
}
#[kani::proof]
fn c_array_read_assert_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn Read> = if kani::any() { Box::new(C) } else { Box::new(Other) };
    sink(o.read(a, i));
}

pub trait ReadOpt { fn read(&self, a: u8, i: u8) -> u8; }
pub struct COpt;
impl ReadOpt for COpt {
    fn read(&self, a: u8, i: u8) -> u8 {
        let arr = [Some(a), None, Some(1), Some(2)];
        match arr[(i % 4) as usize] {
            Some(v) => {
                assert!(v != 100);
                v
            }
            None => 7,
        }
    }
}
impl ReadOpt for Other { fn read(&self, a: u8, _i: u8) -> u8 { a } }
#[kani::proof]
fn c_option_array_read_safe() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a != 100);
    let o: Box<dyn ReadOpt> = if kani::any() { Box::new(COpt) } else { Box::new(Other) };
    sink(o.read(a, i));
}
#[kani::proof]
fn c_option_array_read_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn ReadOpt> = if kani::any() { Box::new(COpt) } else { Box::new(Other) };
    sink(o.read(a, i));
}

pub trait Gu { fn gu(&self, a: u8, i: u8) -> u8; }
pub struct CGu;
pub struct CGuWide;
impl Gu for CGu {
    fn gu(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 20, 30, 40];
        unsafe { *arr.get_unchecked((i % 4) as usize) }
    }
}
impl Gu for CGuWide {
    fn gu(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 20, 30, 40];
        unsafe { *arr.get_unchecked((i % 8) as usize) }
    }
}
impl Gu for Other { fn gu(&self, a: u8, _i: u8) -> u8 { a } }
#[kani::proof]
fn c_array_get_unchecked_safe() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn Gu> = if kani::any() { Box::new(CGu) } else { Box::new(Other) };
    sink(o.gu(a, i));
}
#[kani::proof]
fn c_array_get_unchecked_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn Gu> = if kani::any() { Box::new(CGuWide) } else { Box::new(Other) };
    sink(o.gu(a, i));
}

pub trait Len { fn len3(&self, a: u8) -> usize; }
pub struct CLen;
impl Len for CLen {
    fn len3(&self, a: u8) -> usize {
        let arr = [a, a, a];
        let s: &[u8] = &arr;
        s.len()
    }
}
impl Len for Other { fn len3(&self, _a: u8) -> usize { 3 } }
#[kani::proof]
fn c_array_slice_len_safe() {
    let a: u8 = kani::any();
    let o: Box<dyn Len> = if kani::any() { Box::new(CLen) } else { Box::new(Other) };
    let s = o.len3(a);
    assert!(s == 3);
}
#[kani::proof]
fn c_array_slice_len_bug() {
    let a: u8 = kani::any();
    let o: Box<dyn Len> = if kani::any() { Box::new(CLen) } else { Box::new(Other) };
    let s = o.len3(a);
    assert!(s == 2);
}

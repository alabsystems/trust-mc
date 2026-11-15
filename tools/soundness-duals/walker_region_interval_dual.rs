// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the region a walked loop abandons when
//! it outruns the CHC walker's replay, holding checks that always hold or can
//! fail (fix/chc-walker-fail-closed, package round 2 item a).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   a_region_mod_index_safe    -> VERIFICATION:- SUCCESSFUL
//!   a_region_mod_index_bug     -> VERIFICATION:- FAILED  ('index out of bounds: the length is less than or equal to the given index')
//!   a_region_mask_widen_safe   -> VERIFICATION:- SUCCESSFUL
//!   a_region_overflow_bug      -> VERIFICATION:- FAILED  ('attempt to multiply with overflow')
//!
//! MECHANISM UNDER TEST. `n` is symbolic (below 20) and no unwind bound is
//! declared, so the walked `while j < n` outruns the replay's five passes and
//! the SwitchInt arm past them is abandoned. The region scan
//! (`uncertified_check::region_may_carry_obligation`) decides whether that
//! arm is an uncertified reach check. It used to count every `Assert`, so the
//! bounds check on `table[(j % 4) as usize]` (a four-element table) and the
//! overflow check of `(t as u16) + (j as u16)` (both below 256) made the safe
//! rows FAIL. A sound interval analysis over the body (`region_intervals.rs`:
//! constants, `Rem` / `BitAnd` by a constant, value-preserving casts, array
//! lengths, flow-insensitive over every assignment) now discharges them; the
//! twins, whose index reaches 4 (`j % 5`) and whose product can overflow
//! (`acc * 300`), keep the reach check and FAIL. The main bundle proves
//! `a_region_mod_index_bug` clean (the region's check was discarded with the
//! arm's havoc), the first round's bundle FAILS all four.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_region_interval_dual.rs

fn sink<T>(_v: T) {}

pub trait Run { fn run(&self, a: u8, n: u8) -> u8; }
pub struct Other;
impl Run for Other { fn run(&self, a: u8, _n: u8) -> u8 { a } }

pub struct Mod4;
impl Run for Mod4 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            acc = acc.wrapping_add(table[(j % 4) as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn a_region_mod_index_safe() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(Mod4) } else { Box::new(Other) };
    sink(o.run(a, n));
}

pub struct Mod5;
impl Run for Mod5 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            acc = acc.wrapping_add(table[(j % 5) as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn a_region_mod_index_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(Mod5) } else { Box::new(Other) };
    sink(o.run(a, n));
}

pub struct Mask;
impl Run for Mask {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [9u8; 8];
        let mut acc = 0u16;
        let mut j: u8 = 0;
        while j < n {
            let w = (acc as u8 & 0x7) as usize;
            acc = (table[w] as u16) + (j as u16);
            j = j.wrapping_add(1);
        }
        acc as u8
    }
}
#[kani::proof]
fn a_region_mask_widen_safe() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(Mask) } else { Box::new(Other) };
    sink(o.run(a, n));
}

pub struct Wide;
impl Run for Wide {
    fn run(&self, a: u8, n: u8) -> u8 {
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let t = (acc as u16) * 300;
            acc = (t >> 8) as u8;
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn a_region_overflow_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(Wide) } else { Box::new(Other) };
    sink(o.run(a, n));
}

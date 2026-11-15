// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS AND PRECISION DUAL, WHOLE FILE -- eight harnesses each walking
//! a loop through `dyn Run` under a host-assumed trip count, run as one file
//! (fix/chc-walker-fail-closed, repair round 2, walker fail-closed review 6
//! round 2 finding 7; the review's probe `rg_region.rs`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   g1_add_near_bound_bug     -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   g1s_add_at_bound_safe     -> VERIFICATION:- SUCCESSFUL
//!   g2_signed_rem_index_bug   -> VERIFICATION:- FAILED  ('index out of bounds: the length is less than or equal to the given index')
//!   g3_trunc_cast_index_bug   -> VERIFICATION:- FAILED  ('index out of bounds: the length is less than or equal to the given index')
//!   g4s_masked_shift_safe     -> VERIFICATION:- SUCCESSFUL
//!   g4_unmasked_shift_bug     -> VERIFICATION:- FAILED  ('attempt to shift left with overflow')
//!   g5_mul_bug                -> VERIFICATION:- SUCCESSFUL  (the name is historical: 15 * 17 fits)
//!   g6_div_zero_late_bug      -> VERIFICATION:- FAILED  ('attempt to divide by zero')
//!
//! MECHANISM UNDER TEST. The dyn universe holds every `Run` impl of the
//! file, so each harness walks nine bodies. Package round 2 raised each
//! walked loop's replay to the host's assumed bound (`n < 20`), capped at
//! the 16-pass ceiling: the loop stayed abandoned past it, its reach check
//! in place, and the raise bought only size. As one file, under load, one
//! harness's per-property batch overran into the driver's 365 s watchdog and
//! four harnesses were left undecided (repair-round-1 bundle 8626027c, twice;
//! main decides all eight in 92 s). The raise now applies only where the
//! raised replay can reach the loop's exit (`loop_replay.rs`,
//! `raise_covers`); `g3` then decides by the acyclic witness without a
//! per-property batch. `g6` is a missed bug on main.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_region_whole_file_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub trait Run { fn run(&self, a: u8, n: u8) -> u8; }
pub struct Other;
impl Run for Other { fn run(&self, a: u8, _n: u8) -> u8 { a } }

// g1: checked add near the bound: (j & 0x7f) + 129 overflows at j & 0x7f == 127.
pub struct G1;
impl Run for G1 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let t = (acc & 0x7f) + 129;
            acc = t.wrapping_add(j);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g1_add_near_bound_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G1) } else { Box::new(Other) };
    sink(o.run(a, n));
}
// g1s: + 128 cannot overflow.
pub struct G1s;
impl Run for G1s {
    fn run(&self, a: u8, n: u8) -> u8 {
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let t = (acc & 0x7f) + 128;
            acc = t.wrapping_add(j);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g1s_add_at_bound_safe() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G1s) } else { Box::new(Other) };
    sink(o.run(a, n));
}

// g2: signed remainder then cast: (acc as i8 % 4) as usize can be huge.
pub struct G2;
impl Run for G2 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let k = (acc as i8) % 4;
            acc = acc.wrapping_add(table[k as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g2_signed_rem_index_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G2) } else { Box::new(Other) };
    sink(o.run(a, n));
}

// g3: a truncating cast: (acc as u16 * 3) as u8 % 5 indexes a 4-table.
pub struct G3;
impl Run for G3 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let t = ((acc as u16).wrapping_mul(3) as u8) % 5;
            acc = acc.wrapping_add(table[t as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g3_trunc_cast_index_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G3) } else { Box::new(Other) };
    sink(o.run(a, n));
}

// g4: a shift by a masked distance into an 8-table (safe), and by an
// unmasked one (bug: shift overflow when acc >= 8).
pub struct G4s;
impl Run for G4s {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8; 8];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let d = acc & 7;
            let idx = (0xffu8 >> d) >> 5;
            acc = acc.wrapping_add(table[idx as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g4s_masked_shift_safe() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G4s) } else { Box::new(Other) };
    sink(o.run(a, n));
}
pub struct G4;
impl Run for G4 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let d = acc & 15;
            acc = acc.wrapping_add(1u8 << d);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g4_unmasked_shift_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G4) } else { Box::new(Other) };
    sink(o.run(a, n));
}

// g5: a checked mul whose operand interval is widened across iterations.
pub struct G5;
impl Run for G5 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let mut acc: u8 = a & 3;
        let mut j: u8 = 0;
        while j < n {
            acc = (acc & 0x0f) * 17;
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g5_mul_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G5) } else { Box::new(Other) };
    sink(o.run(a, n));
}
// g6: division by a value that can be zero only after many iterations.
pub struct G6;
impl Run for G6 {
    fn run(&self, a: u8, n: u8) -> u8 {
        let mut acc = a;
        let mut d: u8 = 20;
        let mut j: u8 = 0;
        while j < n {
            d = d.wrapping_sub(1);
            acc = acc / d;
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn g6_div_zero_late_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(G6) } else { Box::new(Other) };
    sink(o.run(a, n));
}

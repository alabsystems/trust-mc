// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS AND PRECISION DUAL -- std loops (`contains`, `position`, `max`)
//! and a float loop under a declared `#[kani::unwind(U)]`, in walked bodies
//! and in a harness body (fix/chc-walker-fail-closed, repair round 2, walker
//! fail-closed review 6 round 2 finding 6; the review's probe
//! `rp6_unwind_more.rs`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   fw_float_loop_u3_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   ct_contains_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   ps_position_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   mx_max_u3_bug          -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   ct_contains_u8_safe    -> VERIFICATION:- SUCCESSFUL
//!   mx_max_u8_safe         -> VERIFICATION:- SUCCESSFUL
//!   h_contains_u3_bug      -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   h_max_u3_bug           -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!
//! MECHANISM UNDER TEST. Under a declared bound the walker replays loops as
//! Kani passes them (package round 2 item b). A std loop walked that way
//! built terms AY refused ("datatype signature surface exceeds
//! copy/comparison work bound", the u8 safe rows: 545,843 nodes written out)
//! or could not decide in the harness's budget (the u3 bug rows timed out on
//! the round-2 and repair-round-1 bundles; main fails them in seconds), and
//! the whole file took 244 s against main's 2 s. A top-level walk under a
//! declared bound whose written-out result passes 200,000 nodes now fails
//! closed at once (`walker.rs`, `walker_declared_replay_too_large`). The u8
//! safe rows remain false failures, as on main (the walker's region scan
//! cannot show `contains` / `max` stay within the bound).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_std_loop_unwind_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;
pub trait Ut {
    fn run(&self, n: u32, x: f32) -> u32;
}
// A loop with float state: the walker gives up on float operations.
pub struct Fw;
impl Ut for Fw {
    fn run(&self, n: u32, x: f32) -> u32 {
        let mut i = 0u32;
        let mut y = x;
        while i < n {
            i += 1;
            y = y * 0.5;
        }
        if y < 0.0 { 1 } else { i }
    }
}
// `contains` over a six-element array.
pub struct Ct;
impl Ut for Ct {
    fn run(&self, n: u32, _x: f32) -> u32 {
        let arr = [1u32, 2, 3, 4, 5, 6];
        if arr.contains(&n) { 1 } else { 0 }
    }
}
// `position` over a six-element array.
pub struct Ps;
impl Ut for Ps {
    fn run(&self, n: u32, _x: f32) -> u32 {
        let arr = [1u32, 2, 3, 4, 5, 6];
        match arr.iter().position(|&v| v == n) {
            Some(p) => p as u32,
            None => 9,
        }
    }
}
// `max` over a six-element array.
pub struct Mx;
impl Ut for Mx {
    fn run(&self, n: u32, _x: f32) -> u32 {
        let arr = [1u32, n, 3, 4, 5, 6];
        match arr.iter().max() {
            Some(m) => *m,
            None => 0,
        }
    }
}
impl Ut for Other {
    fn run(&self, n: u32, _x: f32) -> u32 {
        n
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn fw_float_loop_u3_bug() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let x: f32 = kani::any();
    let o: Box<dyn Ut> = if kani::any() { Box::new(Fw) } else { Box::new(Other) };
    sink(o.run(n, x));
}

#[kani::proof]
#[kani::unwind(3)]
fn ct_contains_u3_bug() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let x: f32 = kani::any();
    let o: Box<dyn Ut> = if kani::any() { Box::new(Ct) } else { Box::new(Other) };
    sink(o.run(n, x));
}

#[kani::proof]
#[kani::unwind(3)]
fn ps_position_u3_bug() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let x: f32 = kani::any();
    let o: Box<dyn Ut> = if kani::any() { Box::new(Ps) } else { Box::new(Other) };
    sink(o.run(n, x));
}

#[kani::proof]
#[kani::unwind(3)]
fn mx_max_u3_bug() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let x: f32 = kani::any();
    let o: Box<dyn Ut> = if kani::any() { Box::new(Mx) } else { Box::new(Other) };
    sink(o.run(n, x));
}

#[kani::proof]
#[kani::unwind(8)]
fn ct_contains_u8_safe() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let x: f32 = kani::any();
    let o: Box<dyn Ut> = if kani::any() { Box::new(Ct) } else { Box::new(Other) };
    sink(o.run(n, x));
}

#[kani::proof]
#[kani::unwind(8)]
fn mx_max_u8_safe() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let x: f32 = kani::any();
    let o: Box<dyn Ut> = if kani::any() { Box::new(Mx) } else { Box::new(Other) };
    sink(o.run(n, x));
}

// The same std loops in the harness body (statement path).
#[kani::proof]
#[kani::unwind(3)]
fn h_contains_u3_bug() {
    let arr = [1u32, 2, 3, 4, 5, 6];
    let n: u32 = kani::any();
    sink(arr.contains(&n));
}
#[kani::proof]
#[kani::unwind(3)]
fn h_max_u3_bug() {
    let n: u32 = kani::any();
    let arr = [1u32, n, 3, 4, 5, 6];
    sink(arr.iter().max());
}

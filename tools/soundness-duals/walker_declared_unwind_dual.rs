// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- walked loops bounded by their caller:
//! a declared unwind bound, and constant bounds past the old refund cap
//! (fix/chc-walker-fail-closed, package round 2 item b).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   b_break_nested_call_unwind_bug   -> VERIFICATION:- FAILED  ('assertion failed: acc != 7')
//!   b_break_nested_call_unwind_safe  -> VERIFICATION:- SUCCESSFUL
//!   b_while_within_unwind_safe       -> VERIFICATION:- SUCCESSFUL
//!   b_while_past_unwind_bug          -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   b_const100_last_bug              -> VERIFICATION:- FAILED  ('assertion failed: acc != 7')
//!   b_const100_last_safe             -> VERIFICATION:- SUCCESSFUL
//!   b_const250_last_bug              -> VERIFICATION:- FAILED  ('assertion failed: acc != 7')
//!   b_const250_last_safe             -> VERIFICATION:- SUCCESSFUL
//!   b_assume_bound_safe              -> VERIFICATION:- SUCCESSFUL
//!   b_assume_bound_bug               -> VERIFICATION:- FAILED  ('assertion failed: acc != 7')
//!
//! Repair round 1 rows (walker fail-closed review 6, finding 4), the same
//! Kani, measured 2026-09-28, no flag:
//!   u_unwind17_past_bug              -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u_unwind19_past_bug              -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u_unwind19_within_safe           -> VERIFICATION:- SUCCESSFUL
//!   u_branchy_unwind6_past_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u_branchy_unwind6_within_safe    -> VERIFICATION:- SUCCESSFUL
//!   u_nested_big_loop_past_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u_nested_big_loop_within_safe    -> VERIFICATION:- SUCCESSFUL
//!
//! The walker records Kani's unwinding assertion exactly only where it
//! replays the pass past the bound. Where it ABANDONS the loop instead (an
//! arm past its SwitchInt depth limit of 16 nested branches, the 17th pass of
//! a `while` or sooner with branches in the body, or past its replay fuel
//! ceiling of 16 passes; or a whole nested callee it cannot enter), the pass
//! and the failure went with it: the abandoned region held no check the
//! walker would have recorded, so it was the value havoc, and the `_past_bug`
//! rows verified clean on main c22e1022e and on the round-2 bundle 5d66fe32
//! (missed bugs). Under a declared bound with unwinding assertions on, a loop
//! in the abandoned region, or in any callee it reaches, now counts as an
//! obligation (`uncertified_check::region_may_fail_unwinding_assertion`;
//! `terminator_exec::nested_callee_may_fail_unwinding_assertion` for the
//! havocked callee). The cost is a loop that stays within the bound but
//! outruns the replay: `u_unwind19_within_safe` (19 passes, 17 replayed) and
//! `u_nested_big_loop_within_safe` FAIL uncertified, known-red precision
//! rows. The branchy rows reach the depth limit on 2048 paths; the abandoned
//! arm's check is recorded once per edge and joined at the merges
//! (`inline_body::merge_keyed_arm_checks`), so the safe twin proves.
//!
//! The two assume rows declare no unwind bound, and Kani does not terminate on
//! a loop bounded only by an assumption, so their oracle ran with
//! `--default-unwind 12` (the loop needs at most eleven header passes under
//! `n <= 10`, and no unwinding assertion fails at 12); every other row ran
//! with no flag.
//!
//! MECHANISM UNDER TEST. Under `#[kani::unwind(U)]` Kani passes each loop
//! header at most `U` times per entry (two iterations pass under `unwind(3)`
//! and fail its unwinding assertion under `unwind(2)`, for `while`,
//! `loop { if .. break }` and `for`). The walker now replays exactly that
//! (`loop_replay.rs` `visit_loop_header`): the path that needs pass `U + 1`
//! records Kani's unwinding-assertion failure and ends, where it used to be
//! the abandoned-arm havoc whose freed value kept every counterexample of the
//! harness uncertified (`b_break_nested_call_unwind_bug`, the review's
//! `l_break_nested_call_bug`, is Genuine now) and where a path between `U`
//! and the old fuel floor of six passes verified without the unwinding
//! assertion Kani reports (`b_while_past_unwind_bug` was SUCCESSFUL clean on
//! main and on the first round's bundle). Constant loops replay past 69
//! iterations with an adaptive refund budget (`MAX_INLINE_CONCRETE_REPLAY_BLOCKS`):
//! the 100- and 250-iteration rows used to take the bailed arm and FAIL
//! uncertified whatever `x` was. Without a declared bound, the caller's
//! assumed bound on an argument (`kani::assume(n <= 10)`, read at the host
//! call) raises the replay, so the paths within it are replayed and the
//! abandoned arm past them is infeasible under the host's assumption:
//! `b_assume_bound_safe` FAILED uncertified on the first round's bundle
//! (the arm's reach check was reachable with n >= 6) and proves now. Its bug
//! twin, SUCCESSFUL clean on main (a missed bug), FAILS Genuine since the
//! panic-path fallbacks the host strips stopped counting against the
//! harness's identity accounting (`translate.rs`
//! `account_escaped_assert_fallbacks`).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_declared_unwind_dual.rs

fn sink<T>(_v: T) {}
pub struct Other;

#[inline(never)]
fn check_at(i: u8, acc: u8) {
    if i == 9 {
        assert!(acc != 7);
    }
}
pub trait TNest { fn run(&self, x: u8, n: u8) -> u8; }
pub struct CNest;
impl TNest for CNest {
    fn run(&self, x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        loop {
            if i == n {
                break;
            }
            check_at(i, acc);
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }
}
impl TNest for Other { fn run(&self, x: u8, _n: u8) -> u8 { x } }
#[kani::proof]
#[kani::unwind(12)]
fn b_break_nested_call_unwind_bug() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 10);
    let o: Box<dyn TNest> = if kani::any() { Box::new(CNest) } else { Box::new(Other) };
    sink(o.run(x, n));
}
#[kani::proof]
#[kani::unwind(12)]
fn b_break_nested_call_unwind_safe() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 10);
    kani::assume(x != 254);
    let o: Box<dyn TNest> = if kani::any() { Box::new(CNest) } else { Box::new(Other) };
    sink(o.run(x, n));
}

pub trait TWhile { fn run(&self, n: u8) -> u8; }
pub struct CWhile;
impl TWhile for CWhile {
    fn run(&self, n: u8) -> u8 {
        let mut i = 0u8;
        let mut acc = 0u8;
        while i < n { acc = acc.wrapping_add(i); i += 1; }
        acc
    }
}
impl TWhile for Other { fn run(&self, n: u8) -> u8 { n } }
// Two iterations under unwind(3): Kani passes.
#[kani::proof]
#[kani::unwind(3)]
fn b_while_within_unwind_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 2);
    let o: Box<dyn TWhile> = if kani::any() { Box::new(CWhile) } else { Box::new(Other) };
    sink(o.run(n));
}
// Three iterations under unwind(3): Kani fails the unwinding assertion.
#[kani::proof]
#[kani::unwind(3)]
fn b_while_past_unwind_bug() {
    let n: u8 = kani::any();
    kani::assume(n <= 3);
    let o: Box<dyn TWhile> = if kani::any() { Box::new(CWhile) } else { Box::new(Other) };
    sink(o.run(n));
}

pub trait TConst { fn run(&self, x: u8) -> u8; }
pub struct C100; pub struct C250;
impl TConst for C100 {
    fn run(&self, x: u8) -> u8 {
        let mut acc = x; let mut i: u16 = 0;
        while i < 100 { if i == 99 { assert!(acc != 7); } acc = acc.wrapping_add(1); i += 1; }
        acc
    }
}
impl TConst for C250 {
    fn run(&self, x: u8) -> u8 {
        let mut acc = x; let mut i: u16 = 0;
        while i < 250 { if i == 249 { assert!(acc != 7); } acc = acc.wrapping_add(1); i += 1; }
        acc
    }
}
impl TConst for Other { fn run(&self, x: u8) -> u8 { x } }
#[kani::proof]
fn b_const100_last_bug() {
    let x: u8 = kani::any();
    let o: Box<dyn TConst> = if kani::any() { Box::new(C100) } else { Box::new(Other) };
    sink(o.run(x));
}
#[kani::proof]
fn b_const100_last_safe() {
    let x: u8 = kani::any();
    kani::assume(x != 164);
    let o: Box<dyn TConst> = if kani::any() { Box::new(C100) } else { Box::new(Other) };
    sink(o.run(x));
}
#[kani::proof]
fn b_const250_last_bug() {
    let x: u8 = kani::any();
    let o: Box<dyn TConst> = if kani::any() { Box::new(C250) } else { Box::new(Other) };
    sink(o.run(x));
}
#[kani::proof]
fn b_const250_last_safe() {
    let x: u8 = kani::any();
    kani::assume(x != 14);
    let o: Box<dyn TConst> = if kani::any() { Box::new(C250) } else { Box::new(Other) };
    sink(o.run(x));
}

// Bounded only by the caller's assumption (no declared unwind).
#[inline(never)]
fn check_at_k(i: u8, acc: u8, k: u8) {
    if i == k {
        assert!(acc != 7);
    }
}
pub trait TAssume { fn run(&self, x: u8, n: u8, k: u8) -> u8; }
pub struct CAssume;
impl TAssume for CAssume {
    fn run(&self, x: u8, n: u8, k: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        loop {
            if i == n {
                break;
            }
            check_at_k(i, acc, k);
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }
}
impl TAssume for Other { fn run(&self, x: u8, _n: u8, _k: u8) -> u8 { x } }
#[kani::proof]
fn b_assume_bound_safe() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 10);
    kani::assume(x != 254);
    let o: Box<dyn TAssume> = if kani::any() { Box::new(CAssume) } else { Box::new(Other) };
    sink(o.run(x, n, 9));
}
#[kani::proof]
fn b_assume_bound_bug() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 10);
    let o: Box<dyn TAssume> = if kani::any() { Box::new(CAssume) } else { Box::new(Other) };
    sink(o.run(x, n, 9));
}

// Repair round 1 (review 6, finding 4): loops the walker abandons.
pub trait Spin { fn run(&self, n: u8) -> u8; }
pub struct CSpin;
impl Spin for CSpin {
    fn run(&self, n: u8) -> u8 {
        let mut acc: u8 = 0;
        let mut i: u8 = 0;
        while i < n {
            acc = acc.wrapping_add(i);
            i = i.wrapping_add(1);
        }
        acc
    }
}
impl Spin for Other { fn run(&self, n: u8) -> u8 { n } }
// n >= 17 needs pass 18: past the replay fuel ceiling, inside Kani's bound
// for n = 16.
#[kani::proof]
#[kani::unwind(17)]
fn u_unwind17_past_bug() {
    let n: u8 = kani::any();
    kani::assume(n <= 40);
    let o: Box<dyn Spin> = if kani::any() { Box::new(CSpin) } else { Box::new(Other) };
    sink(o.run(n));
}
#[kani::proof]
#[kani::unwind(19)]
fn u_unwind19_past_bug() {
    let n: u8 = kani::any();
    kani::assume(n <= 19);
    let o: Box<dyn Spin> = if kani::any() { Box::new(CSpin) } else { Box::new(Other) };
    sink(o.run(n));
}
#[kani::proof]
#[kani::unwind(19)]
fn u_unwind19_within_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 18);
    let o: Box<dyn Spin> = if kani::any() { Box::new(CSpin) } else { Box::new(Other) };
    sink(o.run(n));
}

// Two branches per iteration: the SwitchInt depth limit is reached on the
// sixth pass.
pub trait Branchy { fn run(&self, n: u8, m: u8) -> u8; }
pub struct CBr;
impl Branchy for CBr {
    fn run(&self, n: u8, m: u8) -> u8 {
        let mut acc: u8 = 0;
        let mut i: u8 = 0;
        while i < n {
            if acc & 1 == 0 { acc = acc.wrapping_add(m); } else { acc = acc.wrapping_mul(3); }
            if acc & 2 == 0 { acc = acc.wrapping_add(1); } else { acc = acc.wrapping_sub(m); }
            i = i.wrapping_add(1);
        }
        acc
    }
}
impl Branchy for Other { fn run(&self, n: u8, _m: u8) -> u8 { n } }
#[kani::proof]
#[kani::unwind(6)]
fn u_branchy_unwind6_past_bug() {
    let n: u8 = kani::any();
    let m: u8 = kani::any();
    kani::assume(n <= 12);
    let o: Box<dyn Branchy> = if kani::any() { Box::new(CBr) } else { Box::new(Other) };
    sink(o.run(n, m));
}
#[kani::proof]
#[kani::unwind(6)]
fn u_branchy_unwind6_within_safe() {
    let n: u8 = kani::any();
    let m: u8 = kani::any();
    kani::assume(n <= 5);
    let o: Box<dyn Branchy> = if kani::any() { Box::new(CBr) } else { Box::new(Other) };
    sink(o.run(n, m));
}

// A callee with more than 16 effective blocks around an obligation-free
// loop: the walker cannot enter it, and havocs the whole call.
#[inline(never)]
fn big_loop(n: u8, k: u8) -> u8 {
    let mut acc: u8 = 0;
    let mut i: u8 = 0;
    while i < n {
        acc = acc.wrapping_add(i);
        i = i.wrapping_add(1);
    }
    if k == 1 { acc = acc.wrapping_add(3); }
    if k == 2 { acc = acc.wrapping_mul(5); }
    if k == 3 { acc = acc.wrapping_sub(7); }
    if k == 4 { acc = acc.wrapping_add(11); }
    if k == 5 { acc = acc.wrapping_mul(13); }
    if k == 6 { acc = acc.wrapping_sub(17); }
    if k == 7 { acc = acc.wrapping_add(19); }
    if k == 8 { acc = acc.wrapping_mul(23); }
    if k == 9 { acc = acc.wrapping_sub(29); }
    acc
}
pub trait Big { fn run(&self, n: u8, k: u8) -> u8; }
pub struct CBig;
impl Big for CBig { fn run(&self, n: u8, k: u8) -> u8 { big_loop(n, k) } }
impl Big for Other { fn run(&self, n: u8, _k: u8) -> u8 { n } }
#[kani::proof]
#[kani::unwind(3)]
fn u_nested_big_loop_past_bug() {
    let n: u8 = kani::any();
    let k: u8 = kani::any();
    kani::assume(n <= 10);
    let o: Box<dyn Big> = if kani::any() { Box::new(CBig) } else { Box::new(Other) };
    sink(o.run(n, k));
}
#[kani::proof]
#[kani::unwind(12)]
fn u_nested_big_loop_within_safe() {
    let n: u8 = kani::any();
    let k: u8 = kani::any();
    kani::assume(n <= 10);
    let o: Box<dyn Big> = if kani::any() { Box::new(CBig) } else { Box::new(Other) };
    sink(o.run(n, k));
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the BMC lane's `collect` into a `Vec`
//! over a `map` chain on a concrete array, and its `sum` over `filter_map`
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 8, `closure_helper_obligation_dual.rs` `h05`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   fs1_filter_map_sum_bug   -> VERIFICATION:- FAILED  ('assertion failed: s == 6')
//!   fs1_filter_map_sum_safe  -> VERIFICATION:- SUCCESSFUL
//!   fs2_map_collect_len_bug  -> VERIFICATION:- FAILED  ('assertion failed: v[2] == 3')
//!   fs2_map_collect_len_safe -> VERIFICATION:- SUCCESSFUL
//!   fs3_map_collect_u3_safe  -> VERIFICATION:- SUCCESSFUL
//!   fs4_map_collect_u2_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!
//! MECHANISM UNDER TEST. Repair round 3 failed every BMC `collect` over a
//! value-changing adapter closed (`iter_collect_adapter_unmodeled`): main had
//! collected the unmapped elements and dropped the closure's checks. A `map`
//! chain over a concrete slice iterator is now collected element by element,
//! each closure replayed in order (`iter_adapters.rs`,
//! `try_collect_map_chain`), with the loop's unwinding rule
//! (`reduce_loop_rule`): three elements pass under `unwind(3)` and fail under
//! `unwind(2)`. `filter_map` is recorded as a `Map` stage too; the rule reads
//! the chain from the MIR type, so its `Option` elements are never collected
//! as values (the first cut proved `mc2_filter_map_collect_len_bug`).
//!
//! Lane scope: BMC and CHC.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s collect_map_chain_dual.rs

#[kani::proof]
fn fs1_filter_map_sum_bug() {
    let a = [1u8, 2, 3];
    let s: u8 = a.iter().filter_map(|x| if *x > 1 { Some(*x) } else { None }).sum();
    assert!(s == 6);
}
#[kani::proof]
fn fs1_filter_map_sum_safe() {
    let a = [1u8, 2, 3];
    let s: u8 = a.iter().filter_map(|x| if *x > 1 { Some(*x) } else { None }).sum();
    assert!(s == 5);
}
#[kani::proof]
fn fs2_map_collect_len_bug() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().map(|x| x + 1).collect();
    assert!(v[2] == 3);
}
#[kani::proof]
fn fs2_map_collect_len_safe() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().map(|x| x + 1).collect();
    assert!(v.len() == 3 && v[2] == 4);
}
#[kani::proof]
#[kani::unwind(3)]
fn fs3_map_collect_u3_safe() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().map(|x| x + 1).collect();
    assert!(v.len() == 3);
}
#[kani::proof]
#[kani::unwind(2)]
fn fs4_map_collect_u2_bug() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().map(|x| x + 1).collect();
    assert!(v.len() == 3);
}

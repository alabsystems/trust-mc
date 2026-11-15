// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `Vec::extend` from an iterator adapter
//! (fix/chc-walker-fail-closed, repair round 4: the class of walker fail-closed
//! review 6 round 3 finding 8, std-helper models that drop the obligations in
//! the user closure they are given).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   e1_extend_map_closure_bug        -> VERIFICATION:- FAILED  ('*x < 200')
//!   e1_extend_map_closure_safe       -> VERIFICATION:- SUCCESSFUL
//!   e2_extend_filter_len_bug         -> VERIFICATION:- FAILED  ('v.len() == 3')
//!   e2_extend_filter_len_safe        -> VERIFICATION:- SUCCESSFUL
//!   e3_extend_take_len_bug           -> VERIFICATION:- FAILED  ('v.len() == 4')
//!   e4_extend_range_map_value_bug    -> VERIFICATION:- FAILED  ('v[2] == 2')
//!   e4_extend_range_map_value_safe   -> VERIFICATION:- SUCCESSFUL
//!   e5_extend_copied_slice_bug       -> VERIFICATION:- FAILED  ('v.len() == 3')
//!   e5_extend_copied_slice_safe      -> VERIFICATION:- SUCCESSFUL
//!   e6_extend_copied_stale_len_bug   -> VERIFICATION:- FAILED  ('v.len() == 1')
//!   x1_extend_exclusive_range_len_bug  -> VERIFICATION:- FAILED  ('v.len() == 4')
//!   x1_extend_exclusive_range_len_safe -> VERIFICATION:- SUCCESSFUL
//!   x2_extend_inclusive_range_len_bug  -> VERIFICATION:- FAILED  ('v.len() == 3')
//!   x2_extend_inclusive_range_len_safe -> VERIFICATION:- SUCCESSFUL
//!   x3_extend_empty_exclusive_bug      -> VERIFICATION:- FAILED  ('v.len() == 2')
//!   x3_extend_empty_exclusive_safe     -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `<Vec as Extend>::extend` maps by name to the
//! slice-extend model, which reads only the sequence under the adapters: the
//! closure of `map` never ran (e1 clean on main's BMC lane, masked only by an
//! unrelated demotion on CHC), and a range under `map` was extended by the
//! range's own values (e4's safe twin certified Genuine on main's CHC lane).
//! An adapter source the models do not read fails closed on both lanes
//! (`reduce_loop_rule::extend_source_is_modelled`). And where the CHC model
//! could not resolve the source length it left the length UNWRITTEN, so it
//! kept the old value: e5's safe twin was certified Genuine and e6 verified;
//! the length is a fresh value no smaller than the old one now
//! (`codegen_call_vec_ops_len.rs`, `vec_extend_source_len_unresolved`).
//!
//! The range-extend model counted `start..end` as `end - start + 1` items
//! and `start..=end` as `end - start + 1` whatever the range's exhaustion
//! flag: x1 and x3 bug rows verified clean on main's CHC lane and their safe
//! twins were certified Genuine. An exclusive range now yields
//! `ite(start < end, end - start, 0)` items, an inclusive one
//! `ite(exhausted ∨ start > end, 0, end - start + 1)`; an inclusive range
//! whose exhaustion flag is unresolved fails closed
//! (`codegen_call_vec_ops_extend_range.rs`).

#[kani::proof]
fn e1_extend_map_closure_bug() {
    let a = [1u8, 2, kani::any()];
    let mut v: Vec<u8> = Vec::new();
    v.extend(a.iter().map(|x| {
        assert!(*x < 200);
        *x
    }));
}

#[kani::proof]
fn e1_extend_map_closure_safe() {
    let x: u8 = kani::any();
    kani::assume(x < 200);
    let a = [1u8, 2, x];
    let mut v: Vec<u8> = Vec::new();
    v.extend(a.iter().map(|x| {
        assert!(*x < 200);
        *x
    }));
    assert!(v.len() == 3);
}

#[kani::proof]
fn e2_extend_filter_len_bug() {
    let a = [1u8, 2, 3];
    let mut v: Vec<u8> = Vec::new();
    v.extend(a.iter().copied().filter(|x| *x > 1));
    assert!(v.len() == 3);
}

#[kani::proof]
fn e2_extend_filter_len_safe() {
    let a = [1u8, 2, 3];
    let mut v: Vec<u8> = Vec::new();
    v.extend(a.iter().copied().filter(|x| *x > 1));
    assert!(v.len() == 2);
}

#[kani::proof]
fn e3_extend_take_len_bug() {
    let a = [1u8, 2, 3];
    let mut v: Vec<u8> = vec![9];
    v.extend(a.iter().copied().take(1));
    assert!(v.len() == 4);
}

#[kani::proof]
fn e4_extend_range_map_value_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.extend((0..3u32).map(|x| x * 2));
    assert!(v[2] == 2);
}

#[kani::proof]
fn e4_extend_range_map_value_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.extend((0..3u32).map(|x| x * 2));
    assert!(v.len() == 3 && v[2] == 4);
}

#[kani::proof]
fn e5_extend_copied_slice_bug() {
    let a = [1u8, 2, 3];
    let mut v: Vec<u8> = vec![9];
    v.extend(a.iter().copied());
    assert!(v.len() == 3);
}

#[kani::proof]
fn e5_extend_copied_slice_safe() {
    let a = [1u8, 2, 3];
    let mut v: Vec<u8> = vec![9];
    v.extend(a.iter().copied());
    assert!(v.len() == 4);
}

#[kani::proof]
fn e6_extend_copied_stale_len_bug() {
    let a = [1u8, 2, 3];
    let mut v: Vec<u8> = vec![9];
    v.extend(a.iter().copied());
    assert!(v.len() == 1);
}

#[kani::proof]
fn x1_extend_exclusive_range_len_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..3u32);
    assert!(v.len() == 4);
}

#[kani::proof]
fn x1_extend_exclusive_range_len_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..3u32);
    assert!(v.len() == 3);
}

#[kani::proof]
fn x2_extend_inclusive_range_len_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..=3u32);
    assert!(v.len() == 3);
}

#[kani::proof]
fn x2_extend_inclusive_range_len_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..=3u32);
    assert!(v.len() == 4);
}

#[kani::proof]
fn x3_extend_empty_exclusive_bug() {
    let mut v: Vec<u32> = vec![7];
    v.extend(5..5u32);
    assert!(v.len() == 2);
}

#[kani::proof]
fn x3_extend_empty_exclusive_safe() {
    let mut v: Vec<u32> = vec![7];
    v.extend(5..5u32);
    assert!(v.len() == 1);
}

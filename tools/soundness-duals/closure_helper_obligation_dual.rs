// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the closure a std helper model runs on
//! the elements (fix/chc-walker-fail-closed, repair round 3, walker
//! fail-closed review 6 round 3 finding 8; the review's probe
//! `q6_closure_helpers.rs` `h05`, `h17`, `h18`, `h21`, with twins and value
//! rows).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28,
//! `--default-unwind 6` where the review took it):
//!   h17_retain_bug                          -> VERIFICATION:- FAILED  ('*x < 200')
//!   h17_retain_plain_safe                   -> VERIFICATION:- SUCCESSFUL
//!   h18_sort_by_key_bug                     -> VERIFICATION:- FAILED  ('*x < 200')
//!   h18_sort_by_key_plain_safe              -> VERIFICATION:- SUCCESSFUL
//!   h05_map_collect_bug                     -> VERIFICATION:- FAILED  ('*v < 200')
//!   h05_map_collect_safe                    -> VERIFICATION:- SUCCESSFUL
//!   h21_filter_map_collect_bug              -> VERIFICATION:- FAILED  ('*v < 200')
//!   mc1_map_collect_value_bug               -> VERIFICATION:- FAILED  ('v[0] == 1')
//!   mc1_map_collect_value_safe              -> VERIFICATION:- SUCCESSFUL
//!   mc2_filter_map_collect_len_bug          -> VERIFICATION:- FAILED  ('v.len() == 3')
//!   mc4_vec_into_iter_collect_identity_safe -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. CHC: `Vec::retain`, `dedup_by(_key)` and
//! `sort_by(_key)` constrain their result and never walk the closure, so an
//! `assert!` in it was dropped (`h17`, `h18` verified clean on main and the
//! branch). A closure that can carry an obligation now gets an uncertified
//! reach check wherever the call is reached (`codegen_call_vec.rs`,
//! `vec_closure_step_uncertified`). BMC: `collect` peeled one adapter and
//! returned the Vec underneath, so `map(..).collect()` collected the UNMAPPED
//! elements and never ran the closure (`h05`, `h21`, `mc1`, `mc2` verified
//! clean); a collect over an adapter that runs a closure or changes the
//! elements now fails closed (`statement/collections/iter.rs`,
//! `iter_collect_adapter_unmodeled`). `mc4`: CHC certified a false Genuine
//! index failure on main (an adapter symbol, finding 9).
#[inline(never)]
fn sink<T>(_v: T) {}

#[kani::proof]
fn h17_retain_bug() {
    let mut v = vec![1u8, 2, kani::any()];
    v.retain(|x| {
        assert!(*x < 200);
        true
    });
    sink(v);
}

#[kani::proof]
fn h17_retain_plain_safe() {
    let mut v = vec![1u8, 2, 3];
    v.retain(|x| *x > 1);
    sink(v);
}

#[kani::proof]
fn h18_sort_by_key_bug() {
    let mut v = vec![3u8, 1, kani::any()];
    v.sort_by_key(|x| {
        assert!(*x < 200);
        *x
    });
    sink(v);
}

#[kani::proof]
fn h18_sort_by_key_plain_safe() {
    let mut v = vec![3u8, 1, 2];
    v.sort_by_key(|x| *x);
    sink(v);
}

#[kani::proof]
fn h05_map_collect_bug() {
    let a = [1u8, 2, kani::any()];
    let v: Vec<u8> = a
        .iter()
        .map(|v| {
            assert!(*v < 200);
            *v
        })
        .collect();
    sink(v);
}

#[kani::proof]
fn h05_map_collect_safe() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a
        .iter()
        .map(|v| {
            assert!(*v < 200);
            *v
        })
        .collect();
    assert!(v.len() == 3);
}

#[kani::proof]
fn h21_filter_map_collect_bug() {
    let a = [1u8, 2, kani::any()];
    let v: Vec<u8> = a
        .iter()
        .filter_map(|v| {
            assert!(*v < 200);
            Some(*v)
        })
        .collect();
    sink(v);
}

#[kani::proof]
fn mc1_map_collect_value_bug() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().map(|x| x + 10).collect();
    assert!(v[0] == 1);
}

#[kani::proof]
fn mc1_map_collect_value_safe() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().map(|x| x + 10).collect();
    assert!(v[0] == 11);
}

#[kani::proof]
fn mc2_filter_map_collect_len_bug() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().filter_map(|x| if *x > 1 { Some(*x) } else { None }).collect();
    assert!(v.len() == 3);
}

#[kani::proof]
fn mc4_vec_into_iter_collect_identity_safe() {
    let a = vec![1u8, 2, 3];
    let v: Vec<u8> = a.into_iter().collect();
    assert!(v[0] == 1);
}

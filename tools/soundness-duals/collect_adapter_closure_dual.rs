// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `collect` over an adapter chain whose
//! `map` closure carries an `assert!` (fix/chc-walker-fail-closed, repair
//! round 4: the class of walker fail-closed review 6 round 3 finding 8, on
//! the CHC lane; the BMC half closed in repair round 3).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   c19_copied_map_collect_bug      -> VERIFICATION:- FAILED  ('x < 200')
//!   c19_copied_map_collect_safe     -> VERIFICATION:- SUCCESSFUL
//!   c20_enumerate_map_collect_bug   -> VERIFICATION:- FAILED  ('*x < 200')
//!   c25_rev_map_collect_bug         -> VERIFICATION:- FAILED  ('*x < 200')
//!   c26_take_map_collect_bug        -> VERIFICATION:- FAILED  ('*x < 200')
//!   c27_chain_map_collect_bug       -> VERIFICATION:- FAILED  ('*x < 200')
//!   c10_scan_collect_bug            -> VERIFICATION:- FAILED  ('*x < 200')
//!   c30_copied_collect_safe         -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The CHC collect model reads the length and data of
//! the sequence under the adapters and applies a `map` closure as a value (a
//! forall over the collected data); it never ran the closure's checks, and
//! over `rev`, `enumerate`, `take`, `chain` or `scan` it collected the wrong
//! sequence. Run one harness per file, every bug row verified clean on main;
//! in a file with other harnesses an unrelated type-sort demotion hid it. A
//! receiver chain other than `Copied` / `Cloned` over a slice or vec iterator,
//! or `Map` whose closure carries no obligation, now fails closed
//! (`codegen_call_iterator_adapter/collect.rs`,
//! `collect_receiver_is_modelled`).

#[kani::proof]
fn c19_copied_map_collect_bug() {
    let a = [1u8, 2, kani::any()];
    let v: Vec<u8> = a.iter().copied().map(|x| {
        assert!(x < 200);
        x
    }).collect();
    let _ = v;
}

#[kani::proof]
fn c19_copied_map_collect_safe() {
    let x: u8 = kani::any();
    kani::assume(x < 200);
    let a = [1u8, 2, x];
    let v: Vec<u8> = a.iter().copied().map(|x| {
        assert!(x < 200);
        x
    }).collect();
    assert!(v.len() == 3);
}

#[kani::proof]
fn c20_enumerate_map_collect_bug() {
    let a = [1u8, 2, kani::any()];
    let v: Vec<u8> = a.iter().enumerate().map(|(_, x)| {
        assert!(*x < 200);
        *x
    }).collect();
    let _ = v;
}

#[kani::proof]
fn c25_rev_map_collect_bug() {
    let a = [1u8, 2, kani::any()];
    let v: Vec<u8> = a.iter().rev().map(|x| {
        assert!(*x < 200);
        *x
    }).collect();
    let _ = v;
}

#[kani::proof]
fn c26_take_map_collect_bug() {
    let a = [kani::any::<u8>(), 2, 3];
    let v: Vec<u8> = a.iter().take(2).map(|x| {
        assert!(*x < 200);
        *x
    }).collect();
    let _ = v;
}

#[kani::proof]
fn c27_chain_map_collect_bug() {
    let a = [1u8, 2];
    let b = [kani::any::<u8>()];
    let v: Vec<u8> = a.iter().chain(b.iter()).map(|x| {
        assert!(*x < 200);
        *x
    }).collect();
    let _ = v;
}

#[kani::proof]
fn c10_scan_collect_bug() {
    let a = [1u8, 2, kani::any()];
    let v: Vec<u8> = a.iter().scan(0u8, |s, x| {
        assert!(*x < 200);
        *s = *x;
        Some(*s)
    }).collect();
    let _ = v;
}

#[kani::proof]
fn c30_copied_collect_safe() {
    let a = [1u8, 2, 3];
    let v: Vec<u8> = a.iter().copied().collect();
    assert!(v.len() == 3);
}

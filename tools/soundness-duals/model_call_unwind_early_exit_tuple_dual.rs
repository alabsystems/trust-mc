// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's comparison loops on a tuple
//! stop early, part by part (walker fail-closed review, round 2 of the repair
//! after the merge with main's Rule D, 2026-10-15, finding 5). The rows of
//! `model_call_unwind_early_exit_dual.rs` whose tuple type makes the CHC lane
//! fall back on a type sort for every harness of its crate.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-15):
//!   t1_tuple_arr_first_differs_u2_safe -> VERIFICATION:- SUCCESSFUL
//!   t2_tuple_arr_equal_u2_bug          -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   t3_tuple_scalar_differs_u2_safe    -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. A tuple compares its parts in turn and stops at the
//! first unequal one (`a.0 == b.0 && a.1 == b.1`), and an array part runs
//! Kani's `memcmp`, which returns at the first differing byte. The bound
//! counted the array's four bytes whatever the data, so t1 under `unwind(2)`
//! failed closed where main and Kani prove it. The check is now the
//! condition, read from the two values (`compare_reach`). t3's differing
//! scalar comes after the array, whose loop then runs to its end: it is the
//! array's own data that decides (t3 differs at byte 0 and passes).
//!
//! Lane scope: both.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s [--ay-chc] model_call_unwind_early_exit_tuple_dual.rs

#[kani::proof]
#[kani::unwind(2)]
fn t1_tuple_arr_first_differs_u2_safe() {
    let a = ([9u8, 2, 3, 4], 1u8);
    let b = ([1u8, 2, 3, 4], 1u8);
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn t2_tuple_arr_equal_u2_bug() {
    let a = ([1u8, 2, 3, 4], 1u8);
    let b = ([1u8, 2, 3, 4], 2u8);
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn t3_tuple_scalar_differs_u2_safe() {
    let a = ([9u8, 2, 3, 4], 1u8);
    let b = ([1u8, 2, 3, 4], 2u8);
    assert!(a != b);
}

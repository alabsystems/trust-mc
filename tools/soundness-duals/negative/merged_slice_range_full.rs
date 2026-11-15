// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `s[..]` on a slice reference chosen on a path takes each path's array.
//
// Found while repairing slice_len_range_full_safe.rs (2026-09-12). The BMC lane
// tracks one pointee per reference. For `let source = if c { &lhs } else { &rhs }`
// that entry names one arm's array and is poisoned at the join, and `&source[..]`
// splices the tracked array into the result's fat pointer. The result must take
// each path's own array and length, must see writes made before and after it, and
// must still fail closed where a path's referent is not a tracked array.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample
#![feature(slice_index_methods)]

use std::cell::Cell;

#[kani::proof]
fn merged_full_contents_safe() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full: &[u8] = &source[..];
    assert!(full[0] == if choose_lhs { 1 } else { 5 });
    assert!(full[3] == if choose_lhs { 4 } else { 8 });
}

#[kani::proof]
fn merged_full_first_arm_must_fail() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full: &[u8] = &source[..];
    assert!(full[0] == 1);
}

#[kani::proof]
fn merged_full_last_arm_must_fail() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full: &[u8] = &source[..];
    assert!(full[0] == 5);
}

#[kani::proof]
fn merged_full_lengths_safe() {
    let short = [1u8, 2, 3, 4];
    let long = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let choose_short: bool = kani::any();
    let source: &[u8] = if choose_short { &short } else { &long };
    let full: &[u8] = &source[..];
    assert!(full.len() == if choose_short { 4 } else { 8 });
    assert!(full[full.len() - 1] == if choose_short { 4 } else { 8 });
}

#[kani::proof]
fn merged_full_lengths_must_fail() {
    let short = [1u8, 2, 3, 4];
    let long = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let choose_short: bool = kani::any();
    let source: &[u8] = if choose_short { &short } else { &long };
    let full: &[u8] = &source[..];
    assert!(full.len() == 8);
}

#[kani::proof]
fn merged_full_short_arm_index_must_fail() {
    let short = [1u8, 2, 3, 4];
    let long = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let choose_short: bool = kani::any();
    let source: &[u8] = if choose_short { &short } else { &long };
    let full: &[u8] = &source[..];
    let at: usize = 5;
    assert!(at < full.len() && full[at] == 6);
}

#[kani::proof]
fn merged_full_written_arm_safe() {
    let mut lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    if choose_lhs {
        lhs[0] = 9;
    }
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full: &[u8] = &source[..];
    assert!(full[0] == if choose_lhs { 9 } else { 5 });
}

#[kani::proof]
fn merged_full_written_arm_must_fail() {
    let mut lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    if choose_lhs {
        lhs[0] = 9;
    }
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full: &[u8] = &source[..];
    assert!(full[0] != 9);
}

#[kani::proof]
fn merged_full_cell_set_before_slice_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let rhs = [Cell::new(5u8), Cell::new(6u8)];
    let choose_lhs: bool = kani::any();
    let source: &[Cell<u8>] = if choose_lhs { &lhs } else { &rhs };
    lhs[0].set(7);
    let full: &[Cell<u8>] = &source[..];
    assert!(full[0].get() == if choose_lhs { 7 } else { 5 });
}

#[kani::proof]
fn merged_full_cell_set_before_slice_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let rhs = [Cell::new(5u8), Cell::new(6u8)];
    let choose_lhs: bool = kani::any();
    let source: &[Cell<u8>] = if choose_lhs { &lhs } else { &rhs };
    lhs[0].set(7);
    let full: &[Cell<u8>] = &source[..];
    assert!(full[0].get() != 7);
}

#[kani::proof]
fn merged_full_cell_set_after_slice_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let rhs = [Cell::new(5u8), Cell::new(6u8)];
    let choose_lhs: bool = kani::any();
    let source: &[Cell<u8>] = if choose_lhs { &lhs } else { &rhs };
    let full: &[Cell<u8>] = &source[..];
    lhs[0].set(7);
    assert!(full[0].get() == if choose_lhs { 7 } else { 5 });
}

#[kani::proof]
fn merged_full_cell_set_after_slice_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let rhs = [Cell::new(5u8), Cell::new(6u8)];
    let choose_lhs: bool = kani::any();
    let source: &[Cell<u8>] = if choose_lhs { &lhs } else { &rhs };
    let full: &[Cell<u8>] = &source[..];
    lhs[0].set(7);
    assert!(full[0].get() != 7);
}

#[kani::proof]
fn single_full_cell_set_after_slice_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let source: &[Cell<u8>] = &lhs;
    let full: &[Cell<u8>] = &source[..];
    lhs[0].set(7);
    assert!(full[0].get() == 7);
}

#[kani::proof]
fn single_full_cell_set_after_slice_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let source: &[Cell<u8>] = &lhs;
    let full: &[Cell<u8>] = &source[..];
    lhs[0].set(7);
    assert!(full[0].get() == 1);
}

#[kani::proof]
fn merged_full_subslice_arm_safe() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs[1..] } else { &rhs };
    let full: &[u8] = &source[..];
    assert!(full.len() == if choose_lhs { 3 } else { 4 });
    assert!(full[0] == if choose_lhs { 2 } else { 5 });
}

#[kani::proof]
fn merged_full_subslice_arm_must_fail() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs[1..] } else { &rhs };
    let full: &[u8] = &source[..];
    assert!(full[0] == 5);
}

#[kani::proof]
fn merged_full_three_arms_safe() {
    let a = [1u8, 2];
    let b = [3u8, 4];
    let c = [5u8, 6];
    let pick: u8 = kani::any();
    let source: &[u8] = if pick == 0 {
        &a
    } else if pick == 1 {
        &b
    } else {
        &c
    };
    let full: &[u8] = &source[..];
    assert!(full[1] == if pick == 0 { 2 } else if pick == 1 { 4 } else { 6 });
}

#[kani::proof]
fn merged_full_three_arms_must_fail() {
    let a = [1u8, 2];
    let b = [3u8, 4];
    let c = [5u8, 6];
    let pick: u8 = kani::any();
    let source: &[u8] = if pick == 0 {
        &a
    } else if pick == 1 {
        &b
    } else {
        &c
    };
    let full: &[u8] = &source[..];
    assert!(pick >= 2 || full[1] == 2);
}

#[kani::proof]
fn merged_full_nested_join_safe() {
    let a = [1u8, 2];
    let b = [3u8, 4];
    let e = [5u8, 6];
    let c: bool = kani::any();
    let d: bool = kani::any();
    let inner: &[u8] = if c { &a } else { &b };
    let outer: &[u8] = if d { inner } else { &e };
    let full: &[u8] = &outer[..];
    assert!(full[0] == if d { if c { 1 } else { 3 } } else { 5 });
}

#[kani::proof]
fn merged_full_nested_join_must_fail() {
    let a = [1u8, 2];
    let b = [3u8, 4];
    let e = [5u8, 6];
    let c: bool = kani::any();
    let d: bool = kani::any();
    let inner: &[u8] = if c { &a } else { &b };
    let outer: &[u8] = if d { inner } else { &e };
    let full: &[u8] = &outer[..];
    assert!(!d || full[0] == 1);
}

#[kani::proof]
fn merged_full_later_join_safe() {
    let lhs = [1u8, 2];
    let rhs = [3u8, 4];
    let choose_lhs: bool = kani::any();
    let other: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let mut n = 0u8;
    if other {
        n = 1;
    }
    let full: &[u8] = &source[..];
    assert!(full[0] == if choose_lhs { 1 } else { 3 });
    assert!(n <= 1);
}

#[kani::proof]
fn merged_full_later_join_must_fail() {
    let lhs = [1u8, 2];
    let rhs = [3u8, 4];
    let choose_lhs: bool = kani::any();
    let other: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let mut n = 0u8;
    if other {
        n = 1;
    }
    let full: &[u8] = &source[..];
    assert!(n <= 1);
    assert!(full[0] == 1);
}

#[kani::proof]
fn merged_full_reassigned_in_branch_safe() {
    let lhs = [1u8, 2];
    let rhs = [3u8, 4];
    let switch: bool = kani::any();
    let mut source: &[u8] = &lhs;
    if switch {
        source = &rhs;
    }
    let full: &[u8] = &source[..];
    assert!(full[1] == if switch { 4 } else { 2 });
}

#[kani::proof]
fn merged_full_reassigned_in_branch_must_fail() {
    let lhs = [1u8, 2];
    let rhs = [3u8, 4];
    let switch: bool = kani::any();
    let mut source: &[u8] = &lhs;
    if switch {
        source = &rhs;
    }
    let full: &[u8] = &source[..];
    assert!(full[1] == 2);
}

#[kani::proof]
fn merged_exact_slice_index_contents_safe() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full =
        <std::ops::RangeFull as std::slice::SliceIndex<[u8]>>::index(std::ops::RangeFull, source);
    assert!(full[2] == if choose_lhs { 3 } else { 7 });
}

#[kani::proof]
fn merged_exact_slice_index_contents_must_fail() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full =
        <std::ops::RangeFull as std::slice::SliceIndex<[u8]>>::index(std::ops::RangeFull, source);
    assert!(full[2] == 7);
}

#[kani::proof]
fn merged_full_mut_write_safe() {
    let mut lhs = [1u8, 2];
    let mut rhs = [3u8, 4];
    let choose_lhs: bool = kani::any();
    {
        let source: &mut [u8] = if choose_lhs { &mut lhs } else { &mut rhs };
        let full: &mut [u8] = &mut source[..];
        full[0] = 9;
    }
    assert!(if choose_lhs { lhs[0] == 9 && rhs[0] == 3 } else { lhs[0] == 1 && rhs[0] == 9 });
}

#[kani::proof]
fn merged_full_mut_write_must_fail() {
    let mut lhs = [1u8, 2];
    let mut rhs = [3u8, 4];
    let choose_lhs: bool = kani::any();
    {
        let source: &mut [u8] = if choose_lhs { &mut lhs } else { &mut rhs };
        let full: &mut [u8] = &mut source[..];
        full[0] = 9;
    }
    assert!(lhs[0] == 1);
}

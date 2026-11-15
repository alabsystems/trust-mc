// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A constant-index store inside a loop, placed after the loop's bounds check,
// must keep every other lane of the array.
//
// Fragment composition frames the array into the store's segment with an
// identity, `(= a__mid_bb4 a)`, and stores into the frame var:
// `(= a__mid_bb5 (store a__mid_bb4 0 v))`. No relation application names
// `a__mid_bb4`, and `normalize_free_array_bases` used to treat every such var
// as free, rewriting the store to `(store (const 0) 0 v)`. That zeroed lane 1.
// On main the corrupted value was hidden: the loop head's disputed scalarizer
// column was padded with free `__pad_*` lanes (havoc), or the VC failed to
// parse. With the scalarizer keeping that column whole (147763f07) the zeroed
// lanes reached the straight-line discharge, and every bug_* below was
// reported SUCCESSFUL with PROOF_QUALIFIERS:clean. The pass now replaces a base
// only in a rule where it occurs solely as the innermost base of store chains.
//
// The zero base was already live on main: bug_in_loop_copy_lane1 was proved
// there, and main certified "Genuine" counterexamples for the true twins
// safe_loop_store_lane1_two and safe_const_lanes_loop_frame out of the zeroed
// and `__pad_*` havoc lanes. bug_in_loop_any_lane1 is the bug twin whose
// failure the fixed encoding certifies Genuine, which shows the bug path is live.
//
// Oracles, each confirmed with Kani 0.67.0 (kani-src at the corpus rev):
//   bug_loop_store_lane1_zero     FAILED
//   safe_loop_store_lane1_two     SUCCESSFUL
//   bug_loop_copy_then_store      FAILED
//   bug_loop_copy_symbolic        FAILED
//   bug_sym_read_lane1_zero       FAILED
//   bug_any_loop_store            FAILED
//   bug_in_loop_copy_lane1        FAILED
//   bug_in_loop_any_lane1         FAILED
//   safe_const_lanes_loop_frame   SUCCESSFUL

#[kani::proof]
fn bug_loop_store_lane1_zero() {
    let mut a = [1u8, 2];
    let mut i = 0;
    while i < 2 {
        a[0] = a[0].wrapping_add(1);
        i += 1;
    }
    assert!(a[1] == 0); // FALSE: a[1] == 2
}

#[kani::proof]
fn safe_loop_store_lane1_two() {
    let mut a = [1u8, 2];
    let mut i = 0;
    while i < 2 {
        a[0] = a[0].wrapping_add(1);
        i += 1;
    }
    assert!(a[1] == 2);
}

#[kani::proof]
fn bug_loop_copy_then_store() {
    let mut a = [7u8, 8];
    let mut b = [0u8, 0];
    let mut i = 0;
    while i < 2 {
        b = a;
        a[0] = a[0].wrapping_add(1);
        i += 1;
    }
    assert!(b[1] == 0); // FALSE: b[1] == 8
}

#[kani::proof]
fn bug_loop_copy_symbolic() {
    let x: u8 = kani::any();
    kani::assume(x != 0);
    let mut a = [7u8, x];
    let mut b = [0u8, 0];
    let mut i = 0;
    while i < 2 {
        b = a;
        a[0] = a[0].wrapping_add(1);
        i += 1;
    }
    assert!(b[1] == 0); // FALSE: b[1] == x != 0
}

#[kani::proof]
fn bug_sym_read_lane1_zero() {
    let j: usize = kani::any();
    kani::assume(j < 2);
    let mut a = [1u8, 2];
    let mut i = 0;
    let mut acc = 0u8;
    while i < 2 {
        acc = acc.wrapping_add(a[j]);
        a[0] = a[0].wrapping_add(1);
        i += 1;
    }
    let _ = acc;
    assert!(a[1] == 0); // FALSE: a[1] == 2
}

// The same shape with nondeterministic lanes: the frame var carries `a`'s
// havoc lane 1, which a zero base would pin to 0.
#[kani::proof]
fn bug_any_loop_store() {
    let mut a: [u8; 2] = kani::any();
    let mut i = 0;
    while i < 2 {
        a[0] = a[0].wrapping_add(1);
        i += 1;
    }
    assert!(a[1] == 0); // FALSE for a[1] != 0
}

#[kani::proof]
fn bug_in_loop_copy_lane1() {
    let mut a = [7u8, 8];
    let mut b = [0u8, 0];
    let mut i = 0;
    while i < 2 {
        a[0] = a[0].wrapping_add(1);
        b = a;
        assert!(b[1] != 8); // FALSE on the first iteration
        i += 1;
    }
}

#[kani::proof]
fn bug_in_loop_any_lane1() {
    let mut a: [u8; 2] = kani::any();
    kani::assume(a[1] == 5);
    let mut i = 0;
    while i < 2 {
        a[0] = a[0].wrapping_add(1);
        assert!(a[1] != 5); // FALSE on the first iteration
        i += 1;
    }
}

#[kani::proof]
fn safe_const_lanes_loop_frame() {
    let mut a = [1u32, 2, 3, 4];
    a[1] = 5;
    let mut i = 0;
    while i < 3 {
        a[0] = a[0].wrapping_add(a[1]);
        a[2] ^= a[3];
        i += 1;
    }
    assert!(a[1] == 5);
}

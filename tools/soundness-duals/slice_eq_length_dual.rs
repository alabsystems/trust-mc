// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- slice `==` compares the two lengths
//! and the elements below them, never the encodings around them
//! (fix/slice-eq-lengths, 2026-11-06).
//!
//! Oracle: Rust's `impl PartialEq for [T]` (`core/src/slice/cmp.rs`): two
//! slices are equal exactly when their lengths are equal and every element
//! below that length is. The `_bug` rows assert something Rust makes false,
//! so they must FAIL; the `_safe` rows assert something Rust makes true, so a
//! counterexample certified `[AY:CTREX_CAT:Genuine]` on them is a false
//! certificate.
//!
//! DEFECT UNDER TEST, measured on main 6daf9014a with the landing gate's
//! bundle (2026-11-06):
//!   - CHC, `a == b` on `&[i32]` from `[1, 2]` and `[1, 2, 0]`: SUCCESSFUL
//!     (a false proof). The `<&[T] as PartialEq>` wrapper reaches
//!     `SlicePartialEq` with operands loaded through `&&[T]`, which carry no
//!     slice length, so the lane compared the two referent element arrays
//!     with SMT `=`: both decode over a constant 0 default, and `[1, 2, 0]`
//!     equals `[1, 2]` on every index. `u8` elements too.
//!   - BMC and CHC, `b"ab"` against `b"ab\0"` as `&[u8]`: SUCCESSFUL on both
//!     lanes (promoted constants, both decoded over a constant default).
//!   - BMC and CHC, `a != b` on the same two slices: FAILED with a
//!     counterexample certified Genuine. The BMC lane compared the pointees
//!     (`get_value_through_ref` reads the whole `[i32; N]` SMT array, the
//!     length left behind in the wide reference), whose free tails make either
//!     answer possible.
//!   - BMC, `a == b` at two reference levels before MIR inlining
//!     (`statement::tests::dispatch::mir_string_slice_clone`): not built at
//!     all (`codegen_partial_eq_value` cannot read an unsized `[T]` two levels
//!     down).
//!
//! FIX: the CHC lane compares an array-holding referent datum only below two
//! constant lengths (`codegen_call_slice.rs::slice_eq_from_referent_data`);
//! the BMC lane reads each slice from its wide reference and states
//! `len_a == len_b && forall i < len_a . a[i] == b[i]`
//! (`comparison_eq.rs::slice_partial_eq`, `compare_loops::slice_view_eq`).
//!
//! Run: trust-mc-driver [--ay-chc] -Z unstable-options --harness-timeout=60s slice_eq_length_dual.rs

#[kani::proof]
fn len_differs_d2_claim_equal_bug() {
    let x = [1i32, 2];
    let y = [1i32, 2, 0];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    assert!(a == b);
}

#[kani::proof]
fn len_differs_d1_claim_equal_bug() {
    let x = [1i32, 2];
    let y = [1i32, 2, 0];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    assert!(*a == *b);
}

#[kani::proof]
fn len_differs_u8_d2_claim_equal_bug() {
    let x = [1u8, 2];
    let y = [1u8, 2, 0];
    let a: &[u8] = &x;
    let b: &[u8] = &y;
    assert!(a == b);
}

#[kani::proof]
fn equal_d2_claim_unequal_bug() {
    let x = [1i32, 2];
    let y = [1i32, 2];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    assert!(a != b);
}

#[kani::proof]
fn vec_capacity_d2_claim_unequal_bug() {
    let mut v: Vec<i32> = Vec::with_capacity(4);
    v.push(1);
    let mut w: Vec<i32> = Vec::with_capacity(8);
    w.push(1);
    assert!(v.as_slice() != w.as_slice());
}

#[kani::proof]
fn popped_tails_d2_claim_unequal_bug() {
    let mut v: Vec<i32> = Vec::with_capacity(2);
    v.push(1);
    v.push(2);
    v.pop();
    let mut w: Vec<i32> = Vec::with_capacity(2);
    w.push(1);
    w.push(3);
    w.pop();
    assert!(v.as_slice() != w.as_slice());
}

#[kani::proof]
fn len_differs_d2_safe() {
    let x = [1i32, 2];
    let y = [1i32, 2, 0];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    assert!(a != b);
}

#[kani::proof]
fn len_differs_d1_safe() {
    let x = [1i32, 2];
    let y = [1i32, 2, 0];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    assert!(*a != *b);
}

#[kani::proof]
fn equal_d2_safe() {
    let x = [1i32, 2];
    let y = [1i32, 2];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    assert!(a == b);
}

#[kani::proof]
fn equal_d1_safe() {
    let x = [1i32, 2];
    let y = [1i32, 2];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    assert!(*a == *b);
}

#[kani::proof]
fn byte_literals_len_differs_d2_claim_equal_bug() {
    let s: &[u8] = b"ab";
    let t: &[u8] = b"ab\0";
    assert!(s == t);
}

#[kani::proof]
fn byte_literals_len_differs_d2_safe() {
    let s: &[u8] = b"ab";
    let t: &[u8] = b"ab\0";
    assert!(s != t);
}

#[kani::proof]
fn symbolic_len_differs_d2_safe() {
    let x: [u8; 2] = kani::any();
    let y: [u8; 3] = kani::any();
    let a: &[u8] = &x;
    let b: &[u8] = &y;
    assert!(a != b);
}

#[kani::proof]
fn symbolic_equal_d2_safe() {
    let x: [u8; 2] = kani::any();
    let y = x;
    let a: &[u8] = &x;
    let b: &[u8] = &y;
    assert!(a == b);
}

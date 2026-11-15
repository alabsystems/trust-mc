// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: copy_nonoverlapping overlap on SEPARATELY DERIVED pointers.
//
// Audit evidence: soundness/copy-overlap-separately-derived-false-proof.
// The BMC lane printed a CLEAN SUCCESS for `&a[0]` vs `&mut a[1]`: the overlap
// obligation is skipped when src and dst do not peel to the same root
// (codegen_copy.rs `if src_root != dst_root { return; }`). The CHC lane decides
// disjointness by allocation id and fails the same harness correctly.
//
// Oracle (per harness):
//   overlap_projection_must_fail           -> VERIFICATION:- FAILED (memcpy src/dst overlap)
//   overlap_as_ptr_vs_projection_must_fail -> VERIFICATION:- FAILED (memcpy src/dst overlap)
//   overlap_slice_projections_must_fail    -> VERIFICATION:- FAILED (memcpy src/dst overlap)
//   overlap_same_root_control_must_fail    -> VERIFICATION:- FAILED (memcpy src/dst overlap)
//   disjoint_projection_same_array_safe    -> VERIFICATION:- SUCCESSFUL
//   disjoint_slices_two_arrays_safe        -> VERIFICATION:- SUCCESSFUL
//
// The must-fail harnesses are UB in real Rust (overlapping copy_nonoverlapping)
// and Kani reports `memcpy src/dst overlap` for each. The safe twins keep every
// pointer inside the provenance it was derived from, so they are not UB under
// Kani's object model or under Stacked Borrows.

use std::ptr::copy_nonoverlapping;

#[kani::proof]
fn overlap_projection_must_fail() {
    let mut a = [1u8, 2, 3, 4, 5];
    let p: *const u8 = &a[0];
    let q: *mut u8 = &mut a[1];
    unsafe { copy_nonoverlapping(p, q, 4) };
}

#[kani::proof]
fn overlap_as_ptr_vs_projection_must_fail() {
    let mut a = [1u8, 2, 3, 4, 5];
    let p = a.as_ptr();
    let q: *mut u8 = &mut a[1];
    unsafe { copy_nonoverlapping(p, q, 4) };
    assert!(a[1] == 1);
}

#[kani::proof]
fn overlap_slice_projections_must_fail() {
    let mut a = [1u8, 2, 3, 4, 5];
    let p = (&a[0..3]).as_ptr();
    let q = (&mut a[1..4]).as_mut_ptr();
    unsafe { copy_nonoverlapping(p, q, 3) };
}

#[kani::proof]
fn overlap_same_root_control_must_fail() {
    let mut a = [1u8, 2, 3, 4, 5];
    let p = a.as_mut_ptr();
    unsafe { copy_nonoverlapping(p, p.add(1), 4) };
}

#[kani::proof]
fn disjoint_projection_same_array_safe() {
    let mut a = [1u8, 2, 3, 4, 5];
    let p: *const u8 = &a[0];
    let q: *mut u8 = &mut a[2];
    unsafe { copy_nonoverlapping(p, q, 1) };
    assert!(a[2] == 1);
}

#[kani::proof]
fn disjoint_slices_two_arrays_safe() {
    let a = [1u8, 2, 3, 4, 5];
    let mut b = [0u8; 5];
    let p = (&a[0..4]).as_ptr();
    let q = (&mut b[1..5]).as_mut_ptr();
    unsafe { copy_nonoverlapping(p, q, 4) };
    assert!(b[1] == 1 && b[4] == 4);
}

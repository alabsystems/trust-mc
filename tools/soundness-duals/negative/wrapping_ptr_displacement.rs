// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: under-scaled pointer wrapping_sub / wrapping_add displacement.
//
// Audit evidence: soundness/wrapping-sub-underscaled-false-positives and
// soundness/wrapping-add-deref-unrecorded-approximation. The BMC lane lowers
// `ptr.wrapping_sub(n)` / `ptr.wrapping_add(n)` as UNSCALED byte arithmetic, so
// `a.as_ptr().add(4).wrapping_sub(1)` on `[i32; 4]` lands 1 byte (not 4) below
// one-past-end. On align-4 elements that invents misalignment and region
// failures on legal code (certified Genuine). On align-1 elements of size 2
// there is no alignment check to hide behind, and the wrong cell is read
// silently: that is the missed-bug direction the `_align1_` harnesses pin.
//
// Oracle (per harness):
//   wrapping_sub_last_elem_legal_safe          -> VERIFICATION:- SUCCESSFUL
//   wrapping_sub_copy_dst_legal_safe           -> VERIFICATION:- SUCCESSFUL
//   wrapping_sub_copy_overlap_must_fail        -> VERIFICATION:- FAILED (memcpy src/dst overlap)
//   wrapping_sub_before_start_deref_must_fail  -> VERIFICATION:- FAILED (out-of-bounds dereference)
//   wrapping_sub_align1_right_cell_safe        -> VERIFICATION:- SUCCESSFUL
//   wrapping_sub_align1_wrong_cell_must_fail   -> VERIFICATION:- FAILED (assertion)
//   wrapping_add_deref_legal_safe              -> VERIFICATION:- SUCCESSFUL
//   wrapping_add_align1_wrong_cell_must_fail   -> VERIFICATION:- FAILED (assertion)

#[kani::proof]
fn wrapping_sub_last_elem_legal_safe() {
    let a = [1i32, 2, 3, 4];
    let p = unsafe { a.as_ptr().add(4) }.wrapping_sub(1);
    let v = unsafe { *p };
    assert!(v == 4);
}

#[kani::proof]
fn wrapping_sub_copy_dst_legal_safe() {
    let a = [1i32, 2];
    let mut b = [0i32, 0, 0];
    let dst = unsafe { b.as_mut_ptr().add(2) }.wrapping_sub(2);
    unsafe { core::ptr::copy_nonoverlapping(a.as_ptr(), dst, 2) };
    assert!(b[0] == 1 && b[1] == 2);
}

#[kani::proof]
fn wrapping_sub_copy_overlap_must_fail() {
    let mut a = [1i32, 2, 3, 4];
    let dst = unsafe { a.as_mut_ptr().add(3) }.wrapping_sub(2); // == &mut a[1]
    let src = a.as_ptr();
    unsafe { core::ptr::copy_nonoverlapping(src, dst, 3) }; // a[0..3] vs a[1..4]: overlap
}

#[kani::proof]
fn wrapping_sub_before_start_deref_must_fail() {
    let a = [1i32, 2, 3, 4];
    let p = unsafe { a.as_ptr().add(2) }.wrapping_sub(3); // one element before a[0]
    let v = unsafe { *p };
    assert!(v == v);
}

#[kani::proof]
fn wrapping_sub_align1_right_cell_safe() {
    let a: [[u8; 2]; 4] = [[1, 2], [3, 4], [5, 6], [7, 8]];
    let q = unsafe { a.as_ptr().add(2) }.wrapping_sub(1); // == &a[1]
    let e = unsafe { *q };
    assert!(e[0] == 3 && e[1] == 4);
}

#[kani::proof]
fn wrapping_sub_align1_wrong_cell_must_fail() {
    let a: [[u8; 2]; 4] = [[1, 2], [3, 4], [5, 6], [7, 8]];
    let q = unsafe { a.as_ptr().add(2) }.wrapping_sub(1); // == &a[1] == [3, 4]
    let e = unsafe { *q };
    // FALSE: e[0] == 3. An unscaled displacement reads bytes 3..5 == [4, 5].
    assert!(e[0] == 4);
}

#[kani::proof]
fn wrapping_add_deref_legal_safe() {
    let a = [1i32, 2, 3, 4];
    let v = unsafe { *a.as_ptr().wrapping_add(3) };
    assert!(v == 4);
}

#[kani::proof]
fn wrapping_add_align1_wrong_cell_must_fail() {
    let a: [[u8; 2]; 4] = [[1, 2], [3, 4], [5, 6], [7, 8]];
    let q = a.as_ptr().wrapping_add(1); // == &a[1] == [3, 4]
    let e = unsafe { *q };
    // FALSE: e[0] == 3. An unscaled displacement reads bytes 1..3 == [2, 3].
    assert!(e[0] == 2);
}

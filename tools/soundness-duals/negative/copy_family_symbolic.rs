// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `ptr::copy` over overlapping regions (memmove, forward and
// backward), `ptr::copy_nonoverlapping` and `ptr::write_bytes` with a symbolic
// count, a symbolic destination offset, an overlapping `copy_nonoverlapping`
// (UB), and `copy_from_slice` into a sub-range.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-12) around
// 199da0500 (copy-family early returns demote) and f792edbae (a copy count
// constant on the current path takes the constant unroll).
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::ptr::{copy, copy_nonoverlapping, write_bytes};

#[kani::proof]
fn overlap_forward_copy_safe() {
    let mut a = [1u8, 2, 3, 4];
    unsafe { copy(a.as_ptr(), a.as_mut_ptr().add(1), 3) };
    assert!(a == [1, 1, 2, 3]);
}

#[kani::proof]
fn overlap_forward_copy_must_fail() {
    let mut a = [1u8, 2, 3, 4];
    unsafe { copy(a.as_ptr(), a.as_mut_ptr().add(1), 3) };
    assert!(a[3] == 4);
}

#[kani::proof]
fn overlap_backward_copy_safe() {
    let mut a = [1u8, 2, 3, 4];
    unsafe { copy(a.as_ptr().add(1), a.as_mut_ptr(), 3) };
    assert!(a == [2, 3, 4, 4]);
}

#[kani::proof]
fn overlap_backward_copy_must_fail() {
    let mut a = [1u8, 2, 3, 4];
    unsafe { copy(a.as_ptr().add(1), a.as_mut_ptr(), 3) };
    assert!(a[0] == 1);
}

#[kani::proof]
fn symbolic_count_copy_nonoverlapping_safe() {
    let src = [1u8, 2, 3, 4];
    let mut dst = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n <= 4);
    unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), n) };
    assert!(n == 0 || dst[0] == 1);
    assert!(n < 4 || dst[3] == 4);
}

#[kani::proof]
fn symbolic_count_copy_nonoverlapping_must_fail() {
    let src = [1u8, 2, 3, 4];
    let mut dst = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 4);
    unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), n) };
    assert!(dst[0] == 0);
}

#[kani::proof]
fn symbolic_count_copy_tail_untouched_safe() {
    let src = [1u8, 2, 3, 4];
    let mut dst = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n <= 2);
    unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), n) };
    assert!(dst[2] == 0 && dst[3] == 0);
}

#[kani::proof]
fn symbolic_count_copy_tail_untouched_must_fail() {
    let src = [1u8, 2, 3, 4];
    let mut dst = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n <= 2);
    unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), n) };
    assert!(dst[1] == 0);
}

#[kani::proof]
fn symbolic_count_write_bytes_safe() {
    let mut d = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n <= 4);
    unsafe { write_bytes(d.as_mut_ptr(), 0xAB, n) };
    assert!(n < 2 || d[1] == 0xAB);
    assert!(n > 3 || d[3] == 0);
}

#[kani::proof]
fn symbolic_count_write_bytes_must_fail() {
    let mut d = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 4);
    unsafe { write_bytes(d.as_mut_ptr(), 0xAB, n) };
    assert!(d[0] == 0);
}

#[kani::proof]
fn write_bytes_u32_symbolic_count_safe() {
    let mut d = [0u32; 2];
    let n: usize = kani::any();
    kani::assume(n <= 2);
    unsafe { write_bytes(d.as_mut_ptr(), 0xAB, n) };
    assert!(n == 0 || d[0] == 0xABAB_ABAB);
    assert!(n == 2 || d[1] == 0);
}

#[kani::proof]
fn write_bytes_u32_symbolic_count_must_fail() {
    let mut d = [0u32; 2];
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 2);
    unsafe { write_bytes(d.as_mut_ptr(), 0xAB, n) };
    assert!(d[0] == 0);
}

#[kani::proof]
fn overlapping_copy_nonoverlapping_must_fail() {
    // UB: the regions [0, 2) and [1, 3) overlap.
    let mut a = [1u8, 2, 3, 4];
    unsafe { copy_nonoverlapping(a.as_ptr(), a.as_mut_ptr().add(1), 2) };
    assert!(a[3] == 4);
}

#[kani::proof]
fn symbolic_offset_copy_within_safe() {
    let mut a = [1u8, 2, 3, 4];
    let k: usize = kani::any();
    kani::assume(k <= 2);
    unsafe { copy(a.as_ptr(), a.as_mut_ptr().add(k), 4 - k) };
    assert!(a[k] == 1);
}

#[kani::proof]
fn symbolic_offset_copy_within_must_fail() {
    let mut a = [1u8, 2, 3, 4];
    let k: usize = kani::any();
    kani::assume(k <= 2);
    unsafe { copy(a.as_ptr(), a.as_mut_ptr().add(k), 4 - k) };
    assert!(a[3] == 4);
}

#[kani::proof]
fn copy_from_slice_subrange_safe() {
    let mut d = [0u8; 4];
    d[1..3].copy_from_slice(&[7, 8]);
    assert!(d == [0, 7, 8, 0]);
}

#[kani::proof]
fn copy_from_slice_subrange_must_fail() {
    let mut d = [0u8; 4];
    d[1..3].copy_from_slice(&[7, 8]);
    assert!(d[1] == 0);
}

#[kani::proof]
fn symbolic_count_copy_then_read_source_safe() {
    let mut src = [1u8, 2, 3, 4];
    let mut dst = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n <= 4);
    unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), n) };
    src[0] = 9;
    assert!(src[0] == 9 && (n == 0 || dst[0] == 1));
}

#[kani::proof]
fn symbolic_count_copy_then_read_source_must_fail() {
    let mut src = [1u8, 2, 3, 4];
    let mut dst = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 4);
    unsafe { copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), n) };
    src[0] = 9;
    assert!(dst[0] == 9);
}

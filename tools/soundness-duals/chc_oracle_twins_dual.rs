// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: the evidence that the costs this branch keeps on the
// index-result and far-pointer rows are not regressions from a sound baseline
// (second review of round 9 of fix/chc-false-certificates, finding 6; docs
// chc-hole-fix-designs-2026-09-24.md, "False certificates: round 9 repair,
// second review").
// - Index results: main reads the ELEMENT an index stub returns as the
//   reference's address. chc_index_ref_address_dual.rs's safe rows are proved
//   on main only by their element values: the same programs with other values
//   (`safe_index_*` below) are certified false counterexamples on main.
//   `safe_vec_cell_set_then_get_with_local_cell` is the cell route's
//   counterpart of cell_register_review_dual.rs `safe_vec_cell_with_local_cell`.
// - Far pointers: corpus-rev Kani's answer depends on how CBMC simplified the
//   arithmetic, not on the program's meaning. `(a - b) / 16 == k` and
//   `a - b == k * 16` are SUCCESSFUL, `a.wrapping_sub(b) == k * 16` (the same
//   value, no overflow) is FAILED; equality of far pointers is modulo 2^48
//   under a symbolic count and over 64 bits under a literal one. Main's 64-bit
//   model proves every literal row and misses or falsely certifies the symbolic
//   ones; this branch fails every such observation closed (known-red false
//   failures here, no missed bug and no certificate).
use std::cell::Cell;
#[inline(never)]
fn addr_of_u8(r: &u8) -> usize { r as *const u8 as usize }

// index results: the same programs as the dual rows with other element values
#[kani::proof]
fn safe_index_deref_raw_zero_element() {
    let v = vec![0u8, 3, 4];
    let p = &v[0] as *const u8;
    assert!(unsafe { *p } == 0);
}
#[kani::proof]
fn safe_index_addr_nonnull_zero_element() {
    let v = vec![0u8, 3, 4];
    assert!(&v[0] as *const u8 as usize != 0);
}
#[kani::proof]
fn safe_index_addr_via_fn_other_values() {
    let v = vec![5u8, 2, 3];
    assert!(addr_of_u8(&v[1]) == addr_of_u8(&v[0]) + 1);
}
#[kani::proof]
fn safe_vec_cell_set_then_get_with_local_cell() {
    let a = Cell::new(3u32);
    let v = vec![Cell::new(0u32)];
    v[0].set(9);
    assert!(a.get() == 3 && v[0].get() == 9);
}
// far observations: Kani's answer for one address difference
#[kani::proof]
fn safe_far_addr_diff_div_form() {
    let v = [0u128; 10];
    let v_0: *const u128 = &v[0];
    let high_offset = usize::MAX / (size_of::<u128>() * 4);
    let v_wrap: *const u128 = v_0.wrapping_add(high_offset);
    let wrapped_offset = (v_wrap.addr() - v_0.addr()) / size_of::<u128>();
    assert_eq!(high_offset, wrapped_offset);
}
#[kani::proof]
fn bug_far_addr_diff_wrapping_sub_form() {
    let v = [0u128; 10];
    let v_0: *const u128 = &v[0];
    let high_offset = usize::MAX / (size_of::<u128>() * 4);
    let v_wrap: *const u128 = v_0.wrapping_add(high_offset);
    assert_eq!(v_wrap.addr().wrapping_sub(v_0.addr()), high_offset * size_of::<u128>());
}
#[kani::proof]
fn safe_far_addr_diff_sub_form() {
    let v = [0u128; 10];
    let v_0: *const u128 = &v[0];
    let high_offset = usize::MAX / (size_of::<u128>() * 4);
    let v_wrap: *const u128 = v_0.wrapping_add(high_offset);
    assert_eq!(v_wrap.addr() - v_0.addr(), high_offset * size_of::<u128>());
}
// far equality: a symbolic count against a literal one
#[kani::proof]
fn safe_far_eq_symbolic_count() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    assert!(p.wrapping_byte_add(k) == p);
}
#[kani::proof]
fn bug_far_eq_literal_count() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    assert!(p.wrapping_byte_add(1usize << 48) == p);
}
#[kani::proof]
fn bug_far_two_steps_symbolic_ne_or_equal_counts() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    let j: usize = kani::any();
    assert!(p.wrapping_byte_add(k) != p.wrapping_byte_add(j) || k == j);
}
#[kani::proof]
fn safe_far_two_steps_literal_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    assert!(p.wrapping_byte_add(1usize << 48) != p.wrapping_byte_add(0));
}
#[kani::proof]
fn bug_far_nonzero_offset_ne_symbolic() {
    let ptr: *const u8 = &0u8;
    let offset = kani::any_where(|v: &isize| *v != 0);
    let new_ptr = ptr.wrapping_byte_offset(offset);
    assert_ne!(ptr, new_ptr);
}
#[kani::proof]
fn safe_far_nonzero_offset_ne_literal_2p48() {
    let ptr: *const u8 = &0u8;
    let new_ptr = ptr.wrapping_byte_offset(1isize << 48);
    assert_ne!(ptr, new_ptr);
}

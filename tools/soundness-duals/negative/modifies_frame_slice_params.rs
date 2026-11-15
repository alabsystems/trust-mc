// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z function-contracts
//
// NEGATIVE PACK: a `#[kani::modifies(s)]` footprint that IS a slice or array
// parameter (`&mut [u32]`, `&mut [u8]`, `&mut [u32; N]`), written at a constant
// index, at a symbolic index guarded by `len()`, at `len() - 1`, by `iter_mut`, by
// `fill`, by `swap`, by `copy_from_slice`, by `split_at_mut`, and one element past
// the end of a footprint that names only the first element.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-13) after
// `slice_elem_symbolic_store_safe` (negative/modifies_frame_interior_raw.rs) was
// certified FAILED [AY:CTREX_CAT:Genuine] in the CHC lane on bundle edec8fd8a
// (7cf7fa252's address-range check), while BMC proved it.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (frame); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[kani::modifies(s)]
fn unsized_const_index(s: &mut [u32]) {
    s[2] = 1;
}

#[kani::proof_for_contract(unsized_const_index)]
fn unsized_const_index_safe() {
    let mut s = [0u32; 3];
    unsized_const_index(&mut s);
}

#[kani::modifies(s)]
fn unsized_index_zero(s: &mut [u32]) {
    s[0] = 1;
}

#[kani::proof_for_contract(unsized_index_zero)]
fn unsized_index_zero_safe() {
    let mut s = [0u32; 3];
    unsized_index_zero(&mut s);
}

#[kani::modifies(s)]
fn unsized_symbolic_guarded(s: &mut [u32], i: usize) {
    if i < s.len() {
        s[i] = 1;
    }
}

#[kani::proof_for_contract(unsized_symbolic_guarded)]
fn unsized_symbolic_guarded_safe() {
    let mut s = [0u32; 3];
    let i: usize = kani::any();
    unsized_symbolic_guarded(&mut s, i);
}

#[kani::modifies(s)]
fn unsized_symbolic_assumed(s: &mut [u32], i: usize) {
    s[i] = 1;
}

#[kani::proof_for_contract(unsized_symbolic_assumed)]
fn unsized_symbolic_assumed_safe() {
    let mut s = [0u32; 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    unsized_symbolic_assumed(&mut s, i);
}

#[kani::modifies(s)]
fn unsized_u8_symbolic_guarded(s: &mut [u8], i: usize) {
    if i < s.len() {
        s[i] = 1;
    }
}

#[kani::proof_for_contract(unsized_u8_symbolic_guarded)]
fn unsized_u8_symbolic_guarded_safe() {
    let mut s = [0u8; 4];
    let i: usize = kani::any();
    unsized_u8_symbolic_guarded(&mut s, i);
}

#[kani::modifies(s)]
fn sized_symbolic_guarded(s: &mut [u32; 3], i: usize) {
    if i < 3 {
        s[i] = 1;
    }
}

#[kani::proof_for_contract(sized_symbolic_guarded)]
fn sized_symbolic_guarded_safe() {
    let mut s = [0u32; 3];
    let i: usize = kani::any();
    sized_symbolic_guarded(&mut s, i);
}

#[kani::modifies(s)]
fn unsized_last(s: &mut [u32]) {
    let n = s.len();
    if n > 0 {
        s[n - 1] = 1;
    }
}

#[kani::proof_for_contract(unsized_last)]
fn unsized_last_safe() {
    let mut s = [0u32; 3];
    unsized_last(&mut s);
}

#[kani::modifies(s)]
fn unsized_iter_mut(s: &mut [u32]) {
    for x in s.iter_mut() {
        *x = 1;
    }
}

#[kani::proof_for_contract(unsized_iter_mut)]
#[kani::unwind(5)]
fn unsized_iter_mut_safe() {
    let mut s = [0u32; 3];
    unsized_iter_mut(&mut s);
}

#[kani::modifies(s)]
fn unsized_fill(s: &mut [u32]) {
    s.fill(1);
}

#[kani::proof_for_contract(unsized_fill)]
fn unsized_fill_safe() {
    let mut s = [0u32; 3];
    unsized_fill(&mut s);
}

#[kani::modifies(s)]
fn unsized_swap(s: &mut [u32]) {
    s.swap(0, 2);
}

#[kani::proof_for_contract(unsized_swap)]
fn unsized_swap_safe() {
    let mut s = [0u32, 1, 2];
    unsized_swap(&mut s);
}

#[kani::modifies(s)]
fn unsized_copy_from_slice(s: &mut [u32]) {
    s.copy_from_slice(&[7, 8, 9]);
}

#[kani::proof_for_contract(unsized_copy_from_slice)]
fn unsized_copy_from_slice_safe() {
    let mut s = [0u32; 3];
    unsized_copy_from_slice(&mut s);
}

#[kani::modifies(s)]
fn unsized_split_at_mut(s: &mut [u32]) {
    let (lo, hi) = s.split_at_mut(1);
    lo[0] = 1;
    hi[1] = 2;
}

#[kani::proof_for_contract(unsized_split_at_mut)]
fn unsized_split_at_mut_safe() {
    let mut s = [0u32; 3];
    unsized_split_at_mut(&mut s);
}

#[kani::modifies(&s[0])]
fn first_elem_only_outside(s: &mut [u32]) {
    s[1] = 1;
}

#[kani::proof_for_contract(first_elem_only_outside)]
fn first_elem_only_outside_must_fail() {
    let mut s = [0u32; 3];
    first_elem_only_outside(&mut s);
}

#[kani::modifies(&s[0])]
fn first_elem_only_inside(s: &mut [u32]) {
    s[0] = 1;
}

#[kani::proof_for_contract(first_elem_only_inside)]
fn first_elem_only_inside_safe() {
    let mut s = [0u32; 3];
    first_elem_only_inside(&mut s);
}

#[kani::modifies(s)]
fn unsized_past_end_must_panic(s: &mut [u32]) {
    s[3] = 1;
}

#[kani::proof_for_contract(unsized_past_end_must_panic)]
fn unsized_past_end_must_fail() {
    let mut s = [0u32; 3];
    unsized_past_end_must_panic(&mut s);
}

#[kani::modifies(a)]
fn other_slice_outside(a: &mut [u32], b: &mut [u32], i: usize) {
    if i < a.len() && i < b.len() {
        a[i] = 1;
        b[i] = 1;
    }
}

#[kani::proof_for_contract(other_slice_outside)]
fn other_slice_symbolic_must_fail() {
    let mut a = [0u32; 3];
    let mut b = [0u32; 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    other_slice_outside(&mut a, &mut b, i);
}

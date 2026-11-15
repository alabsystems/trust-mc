// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `&mut [T]` unsized from `&mut [T; N]`, then measured, indexed,
// reborrowed and passed on.
//
// Found while pinning the slice-view fixes of m3/soundness-fixes-2 (2026-09-12).
// Every `len()` and bounds check on a `&mut [T]` reborrows `*s` (`&raw const *s`
// for the metadata), and in the BMC lane that reborrow built its fat pointer
// from the REFERENT: an array local has no length of its own, so the length was
// a fresh symbol unrelated to `s`'s. Measured on bundle e18dbf853 (BMC):
// `let s: &mut [u8] = &mut [1u8, 2]; assert!(s.len() == 2)`, `s[0] = 9`,
// `&mut *s`, `&*s as *const [u8]` and the callee shape all FAILED with
// [AY:CTREX_CAT:Genuine]; the CHC lane proved every *_safe harness. The
// reborrow now carries the reborrowed pointer's own metadata
// (rvalue_address_of.rs).
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[kani::proof]
fn unsize_mut_len_safe() {
    let mut lhs = [1u8, 2];
    let source: &mut [u8] = &mut lhs;
    assert!(source.len() == 2);
}

#[kani::proof]
fn unsize_mut_len_must_fail() {
    let mut lhs = [1u8, 2];
    let source: &mut [u8] = &mut lhs;
    assert!(source.len() == 3);
}

#[kani::proof]
fn unsize_mut_read_safe() {
    let mut lhs = [1u8, 2];
    let source: &mut [u8] = &mut lhs;
    assert!(source[1] == 2);
}

#[kani::proof]
fn unsize_mut_read_must_fail() {
    let mut lhs = [1u8, 2];
    let source: &mut [u8] = &mut lhs;
    assert!(source[1] == 3);
}

#[kani::proof]
fn unsize_mut_write_safe() {
    let mut lhs = [1u8, 2];
    {
        let source: &mut [u8] = &mut lhs;
        source[0] = 9;
    }
    assert!(lhs[0] == 9 && lhs[1] == 2);
}

#[kani::proof]
fn unsize_mut_write_must_fail() {
    let mut lhs = [1u8, 2];
    {
        let source: &mut [u8] = &mut lhs;
        source[0] = 9;
    }
    assert!(lhs[0] == 1);
}

#[kani::proof]
fn unsize_mut_symbolic_index_safe() {
    let mut lhs = [1u8, 2, 3, 4];
    let i: usize = kani::any();
    kani::assume(i < 4);
    let source: &mut [u8] = &mut lhs;
    source[i] = 9;
    assert!(lhs[i] == 9);
}

#[kani::proof]
fn unsize_mut_symbolic_index_must_fail() {
    let mut lhs = [1u8, 2, 3, 4];
    let i: usize = kani::any();
    kani::assume(i < 4);
    let source: &mut [u8] = &mut lhs;
    source[i] = 9;
    assert!(lhs[0] == 1);
}

#[kani::proof]
fn unsize_mut_reborrow_write_safe() {
    let mut lhs = [1u8, 2];
    {
        let source: &mut [u8] = &mut lhs;
        let again: &mut [u8] = &mut *source;
        again[1] = 5;
    }
    assert!(lhs[1] == 5);
}

#[kani::proof]
fn unsize_mut_reborrow_write_must_fail() {
    let mut lhs = [1u8, 2];
    {
        let source: &mut [u8] = &mut lhs;
        let again: &mut [u8] = &mut *source;
        again[1] = 5;
    }
    assert!(lhs[1] == 2);
}

#[kani::proof]
fn unsize_mut_raw_meta_safe() {
    let mut lhs = [1u8, 2, 3];
    let source: &mut [u8] = &mut lhs;
    let p: *const [u8] = &*source;
    assert!(p.len() == 3);
}

#[kani::proof]
fn unsize_mut_raw_meta_must_fail() {
    let mut lhs = [1u8, 2, 3];
    let source: &mut [u8] = &mut lhs;
    let p: *const [u8] = &*source;
    assert!(p.len() == 2);
}

#[kani::proof]
fn unsize_mut_param_write_safe() {
    fn set_first(s: &mut [u8]) {
        s[0] = 9;
    }
    let mut lhs = [1u8, 2];
    set_first(&mut lhs);
    assert!(lhs[0] == 9);
}

#[kani::proof]
fn unsize_mut_param_write_must_fail() {
    fn set_first(s: &mut [u8]) {
        s[0] = 9;
    }
    let mut lhs = [1u8, 2];
    set_first(&mut lhs);
    assert!(lhs[0] == 1);
}

#[kani::proof]
fn unsize_shared_read_safe() {
    let lhs = [1u8, 2];
    let source: &[u8] = &lhs;
    assert!(source.len() == 2 && source[1] == 2);
}

#[kani::proof]
fn unsize_shared_read_must_fail() {
    let lhs = [1u8, 2];
    let source: &[u8] = &lhs;
    assert!(source[1] == 3);
}

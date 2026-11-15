// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a sub-slice `s[a..b]` / `s[a..]` with a NONZERO start reads the
// elements at `start + i`, not at `i`.
//
// Found by the adversarial review of m3/soundness-fixes-2 (2026-09-12). The BMC
// index stub `try_codegen_subslice_range_ref` (statement/slice.rs) built the
// sub-slice as a Vec datatype whose `fld_data` was the SOURCE array unshifted
// and whose `fld_len` was `end - start`, so `sub[i]` read `source[i]`. Measured
// on bundles 31793ccc3 (main) and edec8fd8a (BMC): `let s = &[1u8, 2, 3][1..3];
// assert!(s[0] == 1)` verified SUCCESSFUL and `assert!(s[0] == 2)` FAILED with
// CTREX_CAT:Genuine; the same through a `&[u8]` and through a callee parameter.
// The CHC lane was exact. `RangeTo` (`s[..b]`) was exact in both lanes.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

fn first(s: &[u8]) -> u8 {
    s[0]
}

#[kani::proof]
fn array_range_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.len() == 2 && s[0] == 2 && s[1] == 3);
}

#[kani::proof]
fn array_range_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s[0] == 1);
}

#[kani::proof]
fn array_range_from_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    assert!(s.len() == 3 && s[0] == 2 && s[2] == 4);
}

#[kani::proof]
fn array_range_from_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    assert!(s[0] == 1);
}

#[kani::proof]
fn array_range_to_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[..2];
    assert!(s.len() == 2 && s[0] == 1 && s[1] == 2);
}

#[kani::proof]
fn array_range_to_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[..2];
    assert!(s[1] == 3);
}

#[kani::proof]
fn unsized_range_read_safe() {
    let a = [1u8, 2, 3, 4];
    let src: &[u8] = &a;
    let s = &src[1..3];
    assert!(s.len() == 2 && s[0] == 2 && s[1] == 3);
}

#[kani::proof]
fn unsized_range_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let src: &[u8] = &a;
    let s = &src[1..3];
    assert!(s[0] == 1);
}

#[kani::proof]
fn unsized_range_from_read_safe() {
    let a = [1u8, 2, 3, 4];
    let src: &[u8] = &a;
    let s = &src[2..];
    assert!(s.len() == 2 && s[0] == 3 && s[1] == 4);
}

#[kani::proof]
fn unsized_range_from_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let src: &[u8] = &a;
    let s = &src[2..];
    assert!(s[0] == 1);
}

#[kani::proof]
fn vec_range_read_safe() {
    let v = vec![1u8, 2, 3, 4];
    let s = &v[1..3];
    assert!(s.len() == 2 && s[0] == 2 && s[1] == 3);
}

#[kani::proof]
fn vec_range_read_must_fail() {
    let v = vec![1u8, 2, 3, 4];
    let s = &v[1..3];
    assert!(s[0] == 1);
}

#[kani::proof]
fn vec_range_from_read_safe() {
    let v = vec![1u8, 2, 3, 4];
    let s = &v[2..];
    assert!(s.len() == 2 && s[0] == 3 && s[1] == 4);
}

#[kani::proof]
fn vec_range_from_read_must_fail() {
    let v = vec![1u8, 2, 3, 4];
    let s = &v[2..];
    assert!(s[0] == 1);
}

#[kani::proof]
fn range_param_read_safe() {
    let a = [1u8, 2, 3, 4];
    assert!(first(&a[1..3]) == 2);
}

#[kani::proof]
fn range_param_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    assert!(first(&a[1..3]) == 1);
}

#[kani::proof]
fn range_iter_sum_safe() {
    let a = [1u8, 2, 3, 4];
    let mut t = 0u32;
    for x in &a[2..] {
        t += *x as u32;
    }
    assert!(t == 7);
}

#[kani::proof]
fn range_iter_sum_must_fail() {
    let a = [1u8, 2, 3, 4];
    let mut t = 0u32;
    for x in &a[2..] {
        t += *x as u32;
    }
    assert!(t == 3);
}

#[kani::proof]
fn symbolic_start_range_read_safe() {
    let a = [1u8, 2, 3, 4];
    let k: usize = kani::any();
    kani::assume(k <= 2);
    let s = &a[k..k + 2];
    assert!(s.len() == 2 && s[0] == a[k] && s[1] == a[k + 1]);
}

#[kani::proof]
fn symbolic_start_range_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let k: usize = kani::any();
    kani::assume(k <= 2);
    let s = &a[k..k + 2];
    assert!(s[0] == 1);
}

#[kani::proof]
fn nested_range_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    let t = &s[1..];
    assert!(t.len() == 2 && t[0] == 3 && t[1] == 4);
}

#[kani::proof]
fn nested_range_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    let t = &s[1..];
    assert!(t[0] == 2);
}

#[kani::proof]
fn range_of_range_to_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    let t = &s[..2];
    assert!(t.len() == 2 && t[0] == 2 && t[1] == 3);
}

#[kani::proof]
fn range_of_range_to_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    let t = &s[..2];
    assert!(t[0] == 1);
}

#[kani::proof]
fn range_first_last_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.first() == Some(&2) && s.last() == Some(&3));
}

#[kani::proof]
fn range_first_last_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.first() == Some(&1));
}

#[kani::proof]
fn range_to_vec_safe() {
    let a = [1u8, 2, 3, 4];
    let t = a[1..3].to_vec();
    assert!(t.len() == 2 && t[0] == 2 && t[1] == 3);
}

#[kani::proof]
fn range_to_vec_must_fail() {
    let a = [1u8, 2, 3, 4];
    let t = a[1..3].to_vec();
    assert!(t[0] == 1);
}

#[kani::proof]
fn range_eq_safe() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..3] == [2u8, 3]);
}

#[kani::proof]
fn range_eq_must_fail() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..3] == [1u8, 2]);
}

#[kani::proof]
fn range_contains_safe() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..3].contains(&3) && !a[1..3].contains(&1));
}

#[kani::proof]
fn range_contains_must_fail() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..3].contains(&1));
}

#[kani::proof]
fn str_range_read_safe() {
    let s = "abcd";
    let t = &s[1..3];
    assert!(t == "bc");
}

#[kani::proof]
fn str_range_read_must_fail() {
    let s = "abcd";
    let t = &s[1..3];
    assert!(t == "ab");
}

#[kani::proof]
fn range_mut_read_back_safe() {
    let mut a = [1u8, 2, 3, 4];
    let s = &mut a[1..3];
    assert!(s[0] == 2 && s[1] == 3);
}

#[kani::proof]
fn range_mut_read_back_must_fail() {
    let mut a = [1u8, 2, 3, 4];
    let s = &mut a[1..3];
    assert!(s[0] == 1);
}

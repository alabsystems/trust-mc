// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: every library route that yields a sub-slice with a NONZERO start
// and then reads it: `split_at`, `split_first` / `split_last`, `get(a..b)`,
// `chunks`, `windows`, `rchunks`, `strip_prefix`, `iter().skip`, `iter().rev`,
// `as_ptr()` of `s[a..]`, a sub-slice as the SOURCE of `copy_from_slice` /
// `extend_from_slice` / `clone_from_slice`, `concat`, `starts_with`, `position`,
// `enumerate`, a 2-D row's sub-slice, `as_bytes()[a..]`, and `&a[1..][1..]`.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-13) beside
// negative/subslice_offsets.rs: the BMC index stub backs `s[a..b]` with the
// source array unshifted (statement/slice.rs, try_codegen_subslice_range_ref),
// so any route that reaches an element by `i` instead of `start + i` reads the
// wrong element and can certify a wrong value.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[kani::proof]
fn split_at_tail_read_safe() {
    let a = [1u8, 2, 3, 4];
    let (head, tail) = a.split_at(1);
    assert!(head.len() == 1 && tail.len() == 3 && tail[0] == 2 && tail[2] == 4);
}

#[kani::proof]
fn split_at_tail_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let (_head, tail) = a.split_at(1);
    assert!(tail[0] == 1);
}

#[kani::proof]
fn split_first_rest_read_safe() {
    let a = [1u8, 2, 3, 4];
    let (first, rest) = a.split_first().unwrap();
    assert!(*first == 1 && rest.len() == 3 && rest[0] == 2);
}

#[kani::proof]
fn split_first_rest_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let (_first, rest) = a.split_first().unwrap();
    assert!(rest[0] == 1);
}

#[kani::proof]
fn split_last_init_read_safe() {
    let a = [1u8, 2, 3, 4];
    let (last, init) = a.split_last().unwrap();
    assert!(*last == 4 && init.len() == 3 && init[2] == 3);
}

#[kani::proof]
fn split_last_init_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let (_last, init) = a.split_last().unwrap();
    assert!(init[2] == 4);
}

#[kani::proof]
fn get_range_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = a.get(1..3).unwrap();
    assert!(s.len() == 2 && s[0] == 2 && s[1] == 3);
}

#[kani::proof]
fn get_range_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = a.get(1..3).unwrap();
    assert!(s[0] == 1);
}

#[kani::proof]
fn chunks_second_read_safe() {
    let a = [1u8, 2, 3, 4];
    let c = a.chunks(2).nth(1).unwrap();
    assert!(c.len() == 2 && c[0] == 3 && c[1] == 4);
}

#[kani::proof]
fn chunks_second_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let c = a.chunks(2).nth(1).unwrap();
    assert!(c[0] == 1);
}

#[kani::proof]
fn windows_second_read_safe() {
    let a = [1u8, 2, 3, 4];
    let w = a.windows(2).nth(1).unwrap();
    assert!(w[0] == 2 && w[1] == 3);
}

#[kani::proof]
fn windows_second_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let w = a.windows(2).nth(1).unwrap();
    assert!(w[0] == 1);
}

#[kani::proof]
fn rchunks_first_read_safe() {
    let a = [1u8, 2, 3, 4];
    let c = a.rchunks(3).next().unwrap();
    assert!(c.len() == 3 && c[0] == 2 && c[2] == 4);
}

#[kani::proof]
fn rchunks_first_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let c = a.rchunks(3).next().unwrap();
    assert!(c[0] == 1);
}

#[kani::proof]
fn strip_prefix_read_safe() {
    let a = [1u8, 2, 3, 4];
    let rest = a.strip_prefix(&[1u8]).unwrap();
    assert!(rest.len() == 3 && rest[0] == 2);
}

#[kani::proof]
fn strip_prefix_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let rest = a.strip_prefix(&[1u8]).unwrap();
    assert!(rest[0] == 1);
}

#[kani::proof]
fn iter_skip_read_safe() {
    let a = [1u8, 2, 3, 4];
    let v = *a.iter().skip(1).next().unwrap();
    assert!(v == 2);
}

#[kani::proof]
fn iter_skip_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let v = *a.iter().skip(1).next().unwrap();
    assert!(v == 1);
}

#[kani::proof]
fn subslice_iter_rev_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    let v = *s.iter().rev().next().unwrap();
    assert!(v == 3);
}

#[kani::proof]
fn subslice_iter_rev_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    let v = *s.iter().rev().next().unwrap();
    assert!(v == 4);
}

#[kani::proof]
fn subslice_as_ptr_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    let v = unsafe { *s.as_ptr() };
    assert!(v == 2 && std::ptr::eq(s.as_ptr(), &a[1]));
}

#[kani::proof]
fn subslice_as_ptr_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    let v = unsafe { *s.as_ptr() };
    assert!(v == 1);
}

#[kani::proof]
fn subslice_as_ptr_eq_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..];
    assert!(std::ptr::eq(s.as_ptr(), &a[0]));
}

#[kani::proof]
fn copy_from_subslice_source_safe() {
    let a = [1u8, 2, 3, 4];
    let mut d = [0u8; 2];
    d.copy_from_slice(&a[1..3]);
    assert!(d == [2, 3]);
}

#[kani::proof]
fn copy_from_subslice_source_must_fail() {
    let a = [1u8, 2, 3, 4];
    let mut d = [0u8; 2];
    d.copy_from_slice(&a[1..3]);
    assert!(d[0] == 1);
}

#[kani::proof]
fn clone_from_subslice_source_safe() {
    let a = [1u8, 2, 3, 4];
    let mut d = [0u8; 2];
    d.clone_from_slice(&a[2..]);
    assert!(d == [3, 4]);
}

#[kani::proof]
fn clone_from_subslice_source_must_fail() {
    let a = [1u8, 2, 3, 4];
    let mut d = [0u8; 2];
    d.clone_from_slice(&a[2..]);
    assert!(d[0] == 1);
}

#[kani::proof]
fn extend_from_subslice_source_safe() {
    let a = [1u8, 2, 3, 4];
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&a[1..3]);
    assert!(v.len() == 2 && v[0] == 2 && v[1] == 3);
}

#[kani::proof]
fn extend_from_subslice_source_must_fail() {
    let a = [1u8, 2, 3, 4];
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&a[1..3]);
    assert!(v[0] == 1);
}

#[kani::proof]
fn subslice_starts_with_safe() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..].starts_with(&[2u8, 3]) && !a[1..].starts_with(&[1u8]));
}

#[kani::proof]
fn subslice_starts_with_must_fail() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..].starts_with(&[1u8, 2]));
}

#[kani::proof]
fn subslice_position_safe() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..].iter().position(|&x| x == 3) == Some(1));
}

#[kani::proof]
fn subslice_position_must_fail() {
    let a = [1u8, 2, 3, 4];
    assert!(a[1..].iter().position(|&x| x == 3) == Some(2));
}

#[kani::proof]
fn subslice_enumerate_safe() {
    let a = [1u8, 2, 3, 4];
    let mut ok = true;
    for (i, x) in a[1..].iter().enumerate() {
        ok &= *x as usize == i + 2;
    }
    assert!(ok);
}

#[kani::proof]
fn subslice_enumerate_must_fail() {
    let a = [1u8, 2, 3, 4];
    let mut ok = true;
    for (i, x) in a[1..].iter().enumerate() {
        ok &= *x as usize == i + 1;
    }
    assert!(ok);
}

#[kani::proof]
fn row_subslice_read_safe() {
    let g = [[1u8, 2, 3], [4u8, 5, 6]];
    let s = &g[1][1..];
    assert!(s.len() == 2 && s[0] == 5 && s[1] == 6);
}

#[kani::proof]
fn row_subslice_read_must_fail() {
    let g = [[1u8, 2, 3], [4u8, 5, 6]];
    let s = &g[1][1..];
    assert!(s[0] == 4);
}

#[kani::proof]
fn str_bytes_subslice_read_safe() {
    let s = "abcd";
    let b = &s.as_bytes()[1..];
    assert!(b.len() == 3 && b[0] == b'b' && b[2] == b'd');
}

#[kani::proof]
fn str_bytes_subslice_read_must_fail() {
    let s = "abcd";
    let b = &s.as_bytes()[1..];
    assert!(b[0] == b'a');
}

#[kani::proof]
fn chained_range_from_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..][1..];
    assert!(s.len() == 2 && s[0] == 3 && s[1] == 4);
}

#[kani::proof]
fn chained_range_from_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..][1..];
    assert!(s[0] == 2);
}

#[kani::proof]
fn subslice_symbolic_param_read_safe() {
    fn at(s: &[u8], i: usize) -> u8 {
        s[i]
    }
    let a = [1u8, 2, 3, 4];
    let k: usize = kani::any();
    kani::assume(k < 3);
    assert!(at(&a[1..], k) == a[k + 1]);
}

#[kani::proof]
fn subslice_symbolic_param_read_must_fail() {
    fn at(s: &[u8], i: usize) -> u8 {
        s[i]
    }
    let a = [1u8, 2, 3, 4];
    let k: usize = kani::any();
    kani::assume(k < 3);
    assert!(at(&a[1..], k) == a[k]);
}

#[kani::proof]
fn subslice_sum_via_fold_safe() {
    let a = [1u8, 2, 3, 4];
    let t: u32 = a[1..3].iter().fold(0u32, |acc, &x| acc + x as u32);
    assert!(t == 5);
}

#[kani::proof]
fn subslice_sum_via_fold_must_fail() {
    let a = [1u8, 2, 3, 4];
    let t: u32 = a[1..3].iter().fold(0u32, |acc, &x| acc + x as u32);
    assert!(t == 3);
}

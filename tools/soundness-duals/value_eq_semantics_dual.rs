// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- comparisons whose `==` or order is
//! not the comparison of their encodings: floats, references and pointer
//! wrappers, and hand-written `PartialEq` impls, inside arrays, slices,
//! `Vec`s, `Option`s and tuples (walker fail-closed review, round 3 of the
//! repair after the merge with main's Rule D, 2026-10-15, finding 3).
//!
//! Oracle (per harness, the corpus-rev Kani at ~/tmc-measure/kani-src,
//! measured 2026-10-15): the `_safe` rows are SUCCESSFUL and the `_bug` rows
//! FAILED, every one measured.
//!
//! MECHANISM UNDER TEST. Rust's `==` on floats is IEEE equality (`NaN !=
//! NaN`, `+0.0 == -0.0`), on a reference or a pointer wrapper it compares the
//! pointees, and a hand-written `PartialEq` is whatever its `eq` says. The
//! CHC lane's array, slice, `Vec` and `Option` comparisons and the inline
//! walker's datatype fast path compared the values' encodings for every
//! element type, and the BMC lane's `PartialEq` calls did too: on main and
//! the branch `[0.0f32] == [-0.0f32]`, `Some(0.0f32) == Some(-0.0)`, `[&x] ==
//! [&y]` with `x == y` and `[Parity(1)] == [Parity(3)]` failed with certified
//! counterexamples, and `[f32::NAN] == [f32::NAN]` verified clean; the order
//! of a float array was its bits' order (`[1.0f32] < [-1.0]` verified). Both
//! lanes now classify a comparison by its type
//! (`shared/compare_loops.rs`, `comparison_is_faithful`): one that compares
//! bits keeps every fast path; any other is built exactly from the values
//! (`rust_value_eq`: IEEE equality, element by element, through tuples,
//! `Option` and `Result`), else walked through its own body (CHC), else left
//! unconstrained under a recorded fallback (`codegen_call_cmp_semantic.rs`,
//! the inline walker's fast paths, `slice_contains.rs`; BMC
//! `comparison_eq.rs`).
//!
//! Lane scope: both.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s [--ay-chc] value_eq_semantics_dual.rs

use std::cmp::Ordering;

#[derive(PartialEq, Clone, Copy)]
struct P {
    x: f32,
    t: u8,
}

#[kani::proof]
fn fa_f64_array_signed_zero_eq_safe() {
    let s = [0.0f64, 2.0];
    let t = [-0.0f64, 2.0];
    assert!(s == t);
}

#[kani::proof]
fn fb_f64_array_signed_zero_ne_bug() {
    let s = [0.0f64, 2.0];
    let t = [-0.0f64, 2.0];
    assert!(s != t);
}

#[kani::proof]
fn fc_f32_self_nan_ne_safe() {
    let a = [f32::NAN, 1.0];
    assert!(a != a);
}

#[kani::proof]
fn fd_f32_self_nan_eq_bug() {
    let a = [f32::NAN, 1.0];
    assert!(a == a);
}

#[kani::proof]
fn fe_f32_slice_self_nan_ne_safe() {
    let a = [1.0f32, f32::NAN];
    assert!(a[..] != a[..]);
}

#[kani::proof]
fn ff_vec_f32_signed_zero_eq_safe() {
    let a = vec![0.0f32, 1.0];
    let b = vec![-0.0f32, 1.0];
    assert!(a == b);
}

#[kani::proof]
fn fg_vec_f32_nan_eq_bug() {
    let a = vec![f32::NAN];
    let b = vec![f32::NAN];
    assert!(a == b);
}

#[kani::proof]
fn fh_option_f32_signed_zero_eq_safe() {
    let a = Some(0.0f32);
    let b = Some(-0.0f32);
    assert!(a == b);
}

#[kani::proof]
fn fi_option_f32_nan_ne_safe() {
    let a = Some(f32::NAN);
    let b = Some(f32::NAN);
    assert!(a != b);
}

#[kani::proof]
fn fj_tuple_f32_signed_zero_eq_safe() {
    let a = (0.0f32, 1u8);
    let b = (-0.0f32, 1u8);
    assert!(a == b);
}

#[kani::proof]
fn fk_struct_f32_signed_zero_eq_safe() {
    let a = P { x: 0.0, t: 1 };
    let b = P { x: -0.0, t: 1 };
    assert!(a == b);
}

#[kani::proof]
fn fl_struct_f32_nan_eq_bug() {
    let a = P { x: f32::NAN, t: 1 };
    let b = P { x: f32::NAN, t: 1 };
    assert!(a == b);
}

#[kani::proof]
fn fm_nested_f32_array_signed_zero_eq_safe() {
    let a = [[0.0f32, 1.0], [2.0, 3.0]];
    let b = [[-0.0f32, 1.0], [2.0, 3.0]];
    assert!(a == b);
}

#[kani::proof]
fn fn_nested_f32_array_nan_eq_bug() {
    let a = [[f32::NAN, 1.0], [2.0, 3.0]];
    let b = [[f32::NAN, 1.0], [2.0, 3.0]];
    assert!(a == b);
}

#[kani::proof]
fn fo_struct_array_signed_zero_eq_safe() {
    let a = [P { x: 0.0, t: 1 }, P { x: 1.0, t: 2 }];
    let b = [P { x: -0.0, t: 1 }, P { x: 1.0, t: 2 }];
    assert!(a == b);
}

#[kani::proof]
fn fp_struct_array_nan_eq_bug() {
    let a = [P { x: f32::NAN, t: 1 }];
    let b = [P { x: f32::NAN, t: 1 }];
    assert!(a == b);
}

#[kani::proof]
fn fq_option_f32_array_signed_zero_eq_safe() {
    let a = Some([0.0f32, 1.0]);
    let b = Some([-0.0f32, 1.0]);
    assert!(a == b);
}

#[kani::proof]
fn fr_option_f32_array_nan_eq_bug() {
    let a = Some([f32::NAN, 1.0]);
    let b = Some([f32::NAN, 1.0]);
    assert!(a == b);
}

#[kani::proof]
fn fs_sym_f32_array_eq_bug() {
    // x may be NaN: [x] == [x] is false then.
    let x: f32 = kani::any();
    let a = [x, 1.0];
    let b = [x, 1.0];
    assert!(a == b);
}

#[kani::proof]
fn ft_sym_f32_array_not_nan_eq_safe() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    let a = [x, 1.0];
    let b = [x, 1.0];
    assert!(a == b);
}

#[kani::proof]
fn fu_sym_f32_zero_array_eq_safe() {
    // x == 0.0 admits -0.0, which still compares equal to 0.0.
    let x: f32 = kani::any();
    kani::assume(x == 0.0);
    let a = [x];
    let b = [0.0f32];
    assert!(a == b);
}

#[kani::proof]
fn fv_box_f32_array_signed_zero_eq_safe() {
    let a = Box::new([0.0f32, 1.0]);
    let b = Box::new([-0.0f32, 1.0]);
    assert!(a == b);
}

#[kani::proof]
fn fw_f32_slice_contains_signed_zero_safe() {
    let a = [0.0f32, 1.0];
    assert!(a.contains(&-0.0));
}

#[kani::proof]
fn fx_f32_slice_contains_nan_bug() {
    let a = [f32::NAN, 1.0];
    assert!(a.contains(&f32::NAN));
}

#[kani::proof]
fn fy_f32_array_vs_slice_signed_zero_eq_safe() {
    let a = [0.0f32, 1.0];
    let b = [-0.0f32, 1.0];
    let s: &[f32] = &b;
    assert!(a == *s);
}

#[kani::proof]
fn fz_tuple_f64_nan_ne_safe() {
    let a = (f64::NAN, 1u8);
    let b = (f64::NAN, 1u8);
    assert!(a != b);
}

#[kani::proof]
fn g1_f32_array_assert_eq_signed_zero_safe() {
    let a = [0.0f32, 1.0, 2.0];
    let b = [-0.0f32, 1.0, 2.0];
    assert_eq!(a, b);
}

#[kani::proof]
fn g2_f32_array_ne_nan_safe() {
    let a = [1.0f32, f32::NAN];
    let b = [1.0f32, f32::NAN];
    assert_ne!(a, b);
}

#[kani::proof]
fn g3_f32_vec_self_nan_ne_safe() {
    let a = vec![f32::NAN];
    assert!(a != a);
}

#[kani::proof]
fn g4_u32_array_eq_still_exact_bug() {
    let a = [1u32, 2];
    let b = [1u32, 3];
    assert!(a == b);
}

#[kani::proof]
fn g5_u32_array_eq_still_exact_safe() {
    let a = [1u32, 2];
    let b = [1u32, 2];
    assert!(a == b);
}

#[kani::proof]
fn p5f_f32_array_signed_zero_eq_safe() {
    let s = [0.0f32, 1.0];
    let t = [-0.0f32, 1.0];
    assert!(s == t);
}

#[kani::proof]
fn p5g_f32_array_nan_ne_safe() {
    let s = [f32::NAN, 1.0];
    let t = [f32::NAN, 1.0];
    assert!(s != t);
}

#[kani::proof]
fn p5h_f32_array_signed_zero_ne_bug() {
    let s = [0.0f32, 1.0];
    let t = [-0.0f32, 1.0];
    assert!(s != t);
}

#[kani::proof]
fn p5i_f32_array_nan_eq_bug() {
    let s = [f32::NAN, 1.0];
    let t = [f32::NAN, 1.0];
    assert!(s == t);
}

#[kani::proof]
fn p5j_f64_slice_signed_zero_eq_safe() {
    let a = [0.0f64, 1.0];
    let b = [-0.0f64, 1.0];
    assert!(a[..] == b[..]);
}

#[kani::proof]
fn p5k_f32_scalar_signed_zero_eq_safe() {
    let x = 0.0f32;
    let y = -0.0f32;
    assert!(x == y);
}

#[kani::proof]
fn p5l_vec_f32_nan_ne_safe() {
    let a = vec![f32::NAN];
    let b = vec![f32::NAN];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(3)]
fn p2m_f32_nan_first_u3_safe() {
    // NaN != NaN: the element loop returns at the first element.
    let s = [f32::NAN, 2.0, 3.0, 4.0];
    let t = [f32::NAN, 2.0, 3.0, 4.0];
    assert!(s != t);
}

#[derive(Clone, Copy)]
struct Parity(u8);

impl PartialEq for Parity {
    fn eq(&self, other: &Parity) -> bool {
        self.0 % 2 == other.0 % 2
    }
}

#[derive(Clone, Copy, PartialEq)]
struct Holds(Parity);

#[kani::proof]
fn ea_array_custom_eq_safe() {
    let a = [Parity(1), Parity(2)];
    let b = [Parity(3), Parity(4)];
    assert!(a == b);
}

#[kani::proof]
fn eb_array_custom_eq_bug() {
    let a = [Parity(1), Parity(2)];
    let b = [Parity(3), Parity(5)];
    assert!(a == b);
}

#[kani::proof]
fn ec_slice_custom_eq_safe() {
    let a = [Parity(1), Parity(2)];
    let b = [Parity(3), Parity(4)];
    assert!(a[..] == b[..]);
}

#[kani::proof]
fn ed_vec_custom_eq_safe() {
    let a = vec![Parity(1), Parity(2)];
    let b = vec![Parity(3), Parity(4)];
    assert!(a == b);
}

#[kani::proof]
fn ee_vec_custom_eq_bug() {
    let a = vec![Parity(1)];
    let b = vec![Parity(2)];
    assert!(a == b);
}

#[kani::proof]
fn ef_option_custom_eq_safe() {
    let a = Some(Parity(1));
    let b = Some(Parity(3));
    assert!(a == b);
}

#[kani::proof]
fn eg_derived_wrapper_custom_eq_safe() {
    let a = Holds(Parity(1));
    let b = Holds(Parity(3));
    assert!(a == b);
}

#[kani::proof]
fn eh_derived_wrapper_array_custom_eq_safe() {
    let a = [Holds(Parity(1)), Holds(Parity(2))];
    let b = [Holds(Parity(3)), Holds(Parity(4))];
    assert!(a == b);
}

#[kani::proof]
fn ei_tuple_custom_eq_safe() {
    let a = (Parity(1), 2u8);
    let b = (Parity(3), 2u8);
    assert!(a == b);
}

#[kani::proof]
fn ej_vec_custom_ne_safe() {
    let a = vec![Parity(1)];
    let b = vec![Parity(2)];
    assert!(a != b);
}

#[kani::proof]
fn ha_array_of_refs_eq_safe() {
    let x = 1u8;
    let y = 1u8;
    let a = [&x];
    let b = [&y];
    assert!(a == b);
}

#[kani::proof]
fn hb_array_of_refs_ne_bug() {
    let x = 1u8;
    let y = 1u8;
    let a = [&x];
    let b = [&y];
    assert!(a != b);
}

#[kani::proof]
fn hc_vec_of_vecs_eq_safe() {
    let a = vec![vec![1u8, 2]];
    let b = vec![vec![1u8, 2]];
    assert!(a == b);
}

#[kani::proof]
fn hd_vec_of_vecs_ne_bug() {
    let a = vec![vec![1u8, 2]];
    let b = vec![vec![1u8, 2]];
    assert!(a != b);
}

#[kani::proof]
fn he_vec_of_strs_eq_safe() {
    let s = String::from("ab");
    let a = vec![s.as_str()];
    let b = vec!["ab"];
    assert!(a == b);
}

#[kani::proof]
fn hf_slice_of_refs_eq_safe() {
    let x = 7u16;
    let y = 7u16;
    let a = [&x, &x];
    let b = [&y, &x];
    assert!(a[..] == b[..]);
}

#[kani::proof]
fn hg_vec_of_strings_eq_safe() {
    let a = vec![String::from("x")];
    let b = vec![String::from("x")];
    assert!(a == b);
}

#[kani::proof]
fn hh_vec_of_refs_ne_bug() {
    let x = 3u32;
    let y = 3u32;
    let a = vec![&x];
    let b = vec![&y];
    assert!(a != b);
}

#[kani::proof]
fn hi_option_box_eq_safe() {
    let a = Some(Box::new(5u8));
    let b = Some(Box::new(5u8));
    assert!(a == b);
}

#[kani::proof]
fn hj_array_of_boxes_ne_bug() {
    let a = [Box::new(5u8)];
    let b = [Box::new(5u8)];
    assert!(a != b);
}

#[inline(never)]
fn same<T: PartialEq>(a: T, b: T) -> bool {
    a == b
}

#[inline(never)]
fn less<T: PartialOrd>(a: T, b: T) -> bool {
    a < b
}

#[inline(never)]
fn order<T: PartialOrd>(a: T, b: T) -> Option<Ordering> {
    a.partial_cmp(&b)
}

#[kani::proof]
fn ga_generic_eq_signed_zero_safe() {
    assert!(same(0.0f32, -0.0f32));
}

#[kani::proof]
fn gb_generic_eq_nan_bug() {
    assert!(same(f32::NAN, f32::NAN));
}

#[kani::proof]
fn gc_generic_lt_negative_safe() {
    assert!(less(-1.0f32, 1.0f32));
}

#[kani::proof]
fn gd_generic_lt_negative_bug() {
    assert!(less(1.0f64, -1.0f64));
}

#[kani::proof]
fn ge_generic_lt_nan_safe() {
    assert!(!less(f32::NAN, 1.0f32));
}

#[kani::proof]
fn gf_generic_partial_cmp_nan_safe() {
    assert!(order(f32::NAN, 1.0f32).is_none());
}

#[kani::proof]
fn gg_array_lt_negative_safe() {
    assert!([-1.0f32, 0.0] < [1.0f32, 0.0]);
}

#[kani::proof]
fn gh_array_lt_negative_bug() {
    assert!([1.0f32, 0.0] < [-1.0f32, 0.0]);
}

#[kani::proof]
fn gi_slice_lt_negative_safe() {
    let a = [-2.0f64, 1.0];
    let b = [2.0f64, 1.0];
    assert!(a[..] < b[..]);
}

#[kani::proof]
fn gj_generic_eq_option_signed_zero_safe() {
    assert!(same(Some(0.0f64), Some(-0.0f64)));
}

#[kani::proof]
fn gk_generic_eq_tuple_nan_ne_safe() {
    assert!(!same((f32::NAN, 1u8), (f32::NAN, 1u8)));
}

#[kani::proof]
fn gl_float_max_by_partial_cmp_safe() {
    let a = [-3.0f32, -1.0, -2.0];
    let m = a.iter().copied().fold(f32::NEG_INFINITY, |acc, x| if x > acc { x } else { acc });
    assert!(m == -1.0);
}

#[kani::proof]
fn k1_vec_f32_not_eq_safe() {
    let a = vec![1.0f32];
    let b = vec![2.0f32];
    assert!(!(a[..] == b[..]));
}
#[kani::proof]
fn k2_arr_f32_slice_ne_safe() {
    let a = [1.0f32];
    let b = [2.0f32];
    assert!(a[..] != b[..]);
}
#[kani::proof]
fn k3_vec_f32_eq_bug() {
    let a = vec![1.0f32];
    let b = vec![2.0f32];
    assert!(a[..] == b[..]);
}
#[kani::proof]
fn k4_vec_f32_ne_bug() {
    let a = vec![1.0f32];
    let b = vec![1.0f32];
    assert!(a[..] != b[..]);
}

#[kani::proof]
fn i1_vec_nan_elem_is_nan_safe() {
    let a = vec![f32::NAN];
    assert!(a[0].is_nan());
}
#[kani::proof]
fn i2_vec_two_vals_ne_safe() {
    let a = vec![1.0f32];
    let b = vec![2.0f32];
    assert!(a != b);
}
#[kani::proof]
fn i3_vec_nan_ne_slices_safe() {
    let a = vec![f32::NAN];
    let b = vec![f32::NAN];
    assert!(a[..] != b[..]);
}
#[kani::proof]
fn i4_vec_nan_eq_not_safe() {
    let a = vec![f32::NAN];
    let b = vec![f32::NAN];
    assert!(!(a == b));
}
#[kani::proof]
fn i5_vec_u8_ne_safe() {
    let a = vec![1u8];
    let b = vec![2u8];
    assert!(a != b);
}

#[kani::proof]
fn m1_box_u32_array_eq_safe() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 2]);
    assert!(a == b);
}
#[kani::proof]
fn m2_box_u32_array_eq_bug() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 3]);
    assert!(a == b);
}
#[kani::proof]
fn m3_box_f32_array_eq_same_bits_safe() {
    let a = Box::new([1.0f32, 2.0]);
    let b = Box::new([1.0f32, 2.0]);
    assert!(a == b);
}
#[kani::proof]
fn m4_box_f32_array_read_safe() {
    let a = Box::new([0.0f32, 1.0]);
    assert!(a[1] == 1.0);
}

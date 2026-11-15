// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's comparison loops stop early,
//! and its unwinding assertion counts the passes they complete (walker
//! fail-closed review, round 2 of the repair after the merge with main's
//! Rule D, 2026-10-15, finding 5).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-15):
//! every harness is measured; a `_bug` name, or the `m2`, `m7`, `f2` and `f4`
//! rows, FAILED with `unwinding assertion loop 0`, every other harness is
//! SUCCESSFUL.
//!
//! MECHANISM UNDER TEST. `memcmp` (Kani's `raw_eq` / `compare_bytes`)
//! returns at the first differing byte, the element loop of a slice
//! comparison (floats, which are not bytewise-comparable, and any element that
//! is not) at the first differing element, and a `str`, slice or `Vec`
//! comparison runs no loop when the lengths differ. Each loop's assertion
//! fails exactly when it completes `U` passes: at least `U` units, the first
//! `U` of them equal (m1-m9, f1-f6, s1-s4 calibrate this; m2 and f2 fail,
//! m1 and f1 do not). Both lanes bounded the loops by the data-independent
//! unit count (and a float array by its bytes), so `[9u8, 2, 3, 4] != [1, 2,
//! 3, 4]` and `"abc" != "ab"` under `unwind(2)` were undecided or failed
//! where main and Kani prove them, as were `Some(S { a: [..] })` of a derived
//! `PartialEq` (an unknown part) and `[f32; 4]` arrays under `unwind(6)`. The
//! check is now the condition itself, read from the two compared values
//! (`shared/compare_loops.rs`, `compare_reach`; CHC
//! `model_call_compare_reach`, BMC `bmc_compare_unwinding_check`), and a
//! derived `PartialEq` compares its fields.
//!
//! A tuple `([u8; 4], u8)` makes the CHC lane fall back on a type sort for
//! every harness of the crate (on main too), so its rows are in
//! `model_call_unwind_early_exit_tuple_dual.rs`.
//!
//! Lane scope: both.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s [--ay-chc] model_call_unwind_early_exit_dual.rs

#[derive(PartialEq, Clone, Copy)]
struct S {
    a: [u8; 4],
}

#[kani::proof]
#[kani::unwind(2)]
fn m1_u8_diff_at1_u2() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 9, 3, 4];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn m2_u8_diff_at2_u2() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 9, 4];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(3)]
fn m3_u8_diff_at2_u3() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 9, 4];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(1)]
fn m4_u8_diff_at0_u1() {
    let a = [9u8, 2, 3, 4];
    let b = [1u8, 2, 3, 4];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(4)]
fn m5_u8_diff_at3_u4() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 3, 9];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(5)]
fn m6_u8_equal_u5() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 3, 4];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(4)]
fn m7_u8_equal_u4() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 3, 4];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(2)]
fn m8_u16_diff_hi_byte0_u2() {
    // element 0 differs in its high byte only: byte 0 equal, byte 1 differs
    let a = [0x0101u16, 2];
    let b = [0x0201u16, 2];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(3)]
fn m9_u16_diff_hi_byte0_u3() {
    let a = [0x0101u16, 2];
    let b = [0x0201u16, 2];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn f1_f32_diff_at1_u2() {
    let a = [1.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 9.0, 3.0, 4.0];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(1)]
fn f2_f32_diff_at1_u1() {
    let a = [1.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 9.0, 3.0, 4.0];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(1)]
fn f3_f32_diff_at0_u1() {
    let a = [9.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 2.0, 3.0, 4.0];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(4)]
fn f4_f32_equal_u4() {
    let a = [1.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 2.0, 3.0, 4.0];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(5)]
fn f5_f32_equal_u5() {
    let a = [1.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 2.0, 3.0, 4.0];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn f6_f32_diff_at2_u3() {
    let a = [1.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 2.0, 9.0, 4.0];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn s1_str_diff_at1_u2() {
    let a: &str = "abc";
    let b: &str = "axc";
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(1)]
fn s2_str_len_differs_u1() {
    let a: &str = "abc";
    let b: &str = "ab";
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(1)]
fn s3_str_diff_at0_u1() {
    let a: &str = "abc";
    let b: &str = "xbc";
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(3)]
fn s4_str_diff_at2_u3() {
    let a: &str = "abc";
    let b: &str = "abx";
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn l1_slice_u8_diff_at1_u2() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 9, 3, 4];
    assert!(a[..] != b[..]);
}

#[kani::proof]
#[kani::unwind(1)]
fn l2_slice_u8_len_differs_u1() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 3];
    assert!(a[..] != b[..]);
}

#[kani::proof]
#[kani::unwind(2)]
fn o1_opt_arr_diff_at1_u2() {
    let a = Some([1u8, 2, 3, 4]);
    let b = Some([1u8, 9, 3, 4]);
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(1)]
fn o2_opt_arr_none_u1() {
    let a: Option<[u8; 4]> = None;
    let b = Some([1u8, 2, 3, 4]);
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1a_arr_u8_first_differs_u2_safe() {
    let a = [9u8, 2, 3, 4];
    let b = [1u8, 2, 3, 4];
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1b_arr_u8_equal_u2_bug() {
    let a = [1u8, 2, 3, 4];
    let b = [1u8, 2, 3, 4];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1c_opt_arr_first_differs_u2_safe() {
    let a = Some([9u8, 2, 3, 4]);
    let b = Some([1u8, 2, 3, 4]);
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1d_opt_arr_one_none_u2_safe() {
    let a: Option<[u8; 4]> = None;
    let b = Some([1u8, 2, 3, 4]);
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1e_opt_str_len_differs_u2_safe() {
    let a = Some("abc");
    let b = Some("ab");
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1f_str_len_differs_u2_safe() {
    let a: &str = "abc";
    let b: &str = "ab";
    assert!(a != b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1g_sym_first_differs_u2_safe() {
    let a: [u8; 4] = kani::any();
    kani::assume(a[0] != 0);
    let b = [0u8; 4];
    assert!(a != b);
}


#[kani::proof]
#[kani::unwind(3)]
fn w2c_opt_struct_arr_u3_bug() {
    let a = Some(S { a: [1, 2, 3, 4] });
    let b = Some(S { a: [1, 2, 3, 4] });
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(6)]
fn w2d_opt_struct_arr_u6_safe() {
    let a = Some(S { a: [1, 2, 3, 4] });
    let b = Some(S { a: [1, 2, 3, 4] });
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(6)]
fn w2e_f32_arr4_u6_safe() {
    let a = [1.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 2.0, 3.0, 4.0];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn w2f_f32_arr4_u3_bug() {
    let a = [1.0f32, 2.0, 3.0, 4.0];
    let b = [1.0f32, 2.0, 3.0, 4.0];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(6)]
fn w2g_opt_f32_arr4_u6_safe() {
    let a = Some([1.0f32, 2.0, 3.0, 4.0]);
    let b = Some([1.0f32, 2.0, 3.0, 4.0]);
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn w2h_nested_arr_u3_bug() {
    let a = [[1u8, 2], [3, 4]];
    let b = [[1u8, 2], [3, 4]];
    assert!(a == b);
}

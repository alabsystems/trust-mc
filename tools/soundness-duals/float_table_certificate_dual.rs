// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// T1 review dual (fix/chc-row72-small, 2026-09-24). With the float-binop table
// an IDENTIFIED approximation, a counterexample that reads no table and comes
// before every table select replays on the cut system and is certified
// Genuine. That certificate is only as good as the rest of the encoding: any
// free value nobody recorded is certified with it.
//
// - `safe_*`: correct programs (upstream Kani 0.67 corpus-rev build:
//   VERIFICATION:- SUCCESSFUL). A promoted `&-0.0f32` used to leave its
//   object's memory cell and `obj_size` free (the float scalar was not
//   decoded), so a memory-safety check failed on a free size and, with a float
//   op anywhere later in the harness, was certified Genuine. The constant-key
//   harness is tests/expected/test6/main.rs's first assertion: the table read
//   at `1.0 + 1.0` was scalarized to a cell the cut first missed.
//   MUST NOT CERTIFY: SUCCESSFUL, or FAILED without [AY:CTREX_CAT:Genuine].
// - `bug_*`: the same shapes with a real failure (Kani FAILED), so a repair of
//   the safe twins cannot be a blinding. SUCCESSFUL is a missed bug.

#[inline(never)]
fn read_f32(r: &f32) -> f32 {
    *r
}

#[inline(never)]
fn read_f64s(r: &[f64; 2]) -> f64 {
    r[1]
}

#[kani::proof]
fn safe_promoted_f32_read() {
    let v = read_f32(&-0.0f32);
    assert!(v.to_bits() == 0x8000_0000, "reads -0.0");
}

#[kani::proof]
fn safe_promoted_f32_read_then_float() {
    let v = read_f32(&-0.0f32);
    assert!(v.to_bits() == 0x8000_0000, "reads -0.0");
    let q: f32 = kani::any();
    let t = q * 2.0;
    assert!(t == t || t.is_nan(), "reflexive or nan");
}

#[kani::proof]
fn safe_promoted_f64_array_read_then_float() {
    let v = read_f64s(&[1.5f64, -2.25]);
    assert!(v.to_bits() == (-2.25f64).to_bits(), "reads -2.25");
    let q: f64 = kani::any();
    let t = q + 1.0;
    assert!(t == t || t.is_nan(), "reflexive or nan");
}

#[kani::proof]
fn safe_total_cmp_then_float() {
    let a: f32 = kani::any();
    kani::assume(a == 0.0 && !a.is_sign_negative());
    assert!((-0.0f32).total_cmp(&a) == core::cmp::Ordering::Less, "total order -0 < +0");
    let q: f32 = kani::any();
    let t = q + 1.0;
    assert!(t == t || t.is_nan(), "reflexive or nan");
}

fn add(a: i32, b: f32) -> f32 {
    a as f32 + b
}

fn add2(a: i32, b: i32) -> f32 {
    add(a, b as f32)
}

#[kani::proof]
fn safe_constant_key_table_cell() {
    assert!(add2(1, 1) == 2.0, "1 + 1 = 2");
}

#[kani::proof]
fn bug_promoted_f32_read_wrong_bits() {
    let v = read_f32(&-0.0f32);
    let q: f32 = kani::any();
    let _t = q * 2.0;
    assert!(v.to_bits() == 0, "reads +0.0 (false)");
}

#[kani::proof]
fn bug_int_fail_after_float() {
    let q: f32 = kani::any();
    let _t = q + 1.0;
    let n: u8 = kani::any();
    assert!(n != 7, "n is never 7 (false)");
}

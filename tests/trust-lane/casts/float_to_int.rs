// Route dual: `as` casts from a bounded float to an integer. A Rust float-to-int `as` cast
// saturates and truncates; the BMC lane used to reinterpret the float's bits as the integer,
// so `m as usize <= 3` for `0.0 <= m <= 3.0` was FAILED with a counterexample certified
// `[AY:CTREX_CAT:Genuine]` (the second parity-1 review's probe). Main's `cast_float.rs` lowers
// the cast exactly through `build_float_to_int_saturating_expr`; these duals pin it on both
// routes and both lanes.

#[kani::proof]
fn cast_bounded_f32_usize_holds() {
    let m: f32 = kani::any();
    kani::assume(m >= 0.0 && m <= 3.0);
    let i = m as usize;
    assert!(i <= 3);
}

#[kani::proof]
fn cast_bounded_f32_usize_refuted() {
    let m: f32 = kani::any();
    kani::assume(m >= 0.0 && m <= 3.0);
    let i = m as usize;
    assert!(i <= 2);
}

#[kani::proof]
fn cast_clamped_chain_usize_holds() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    let m = x.max(0.0).min(3.0);
    let i = m as usize;
    assert!(i <= 3);
}

#[kani::proof]
fn cast_min_then_usize_holds() {
    let x: f32 = kani::any();
    kani::assume(x >= 0.0);
    let i = x.min(3.0) as usize;
    assert!(i <= 3);
}

#[kani::proof]
fn cast_max_then_usize_holds() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan() && x <= 3.0);
    let i = x.max(0.0) as usize;
    assert!(i <= 3);
}

#[kani::proof]
fn cast_result_as_index_in_bounds_holds() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    let i = x.max(0.0).min(3.0) as usize;
    let arr = [1u8, 2, 3, 4];
    assert!(arr[i] >= 1);
}

#[kani::proof]
fn cast_result_as_index_oob_refuted() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    let i = x.max(0.0).min(4.0) as usize;
    let arr = [1u8, 2, 3, 4];
    assert!(arr[i] >= 1);
}

#[kani::proof]
fn cast_negative_saturates_to_zero_holds() {
    let x: f32 = kani::any();
    kani::assume(x < 0.0);
    assert!(x as u8 == 0);
}

#[kani::proof]
fn cast_large_saturates_to_max_holds() {
    let x: f64 = kani::any();
    kani::assume(x >= 300.0);
    assert!(x as u8 == 255);
}

#[kani::proof]
fn cast_nan_is_zero_holds() {
    let x: f32 = kani::any();
    kani::assume(x.is_nan());
    assert!(x as i32 == 0);
}

#[kani::proof]
fn cast_truncates_toward_zero_holds() {
    let x: f32 = kani::any();
    kani::assume(x > -1.0 && x < 1.0);
    assert!(x as i32 == 0);
}

#[kani::proof]
fn cast_truncates_toward_zero_refuted() {
    let x: f32 = kani::any();
    kani::assume(x > 1.0 && x < 3.0);
    assert!(x as i32 == 1);
}

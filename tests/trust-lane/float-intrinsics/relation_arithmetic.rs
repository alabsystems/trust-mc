// Route dual: a `min` / `max` result (a relation result, either zero) used in further float
// arithmetic. In the CHC lane a symbolic float binop is a select from an uninterpreted table;
// before the parity-1 second repair that select recorded nothing, so a counterexample the
// solver built from an interpretation no FPU has was certified `[AY:CTREX_CAT:Genuine]` for
// each of the three `_holds` below, on both routes. The table select is now a recorded sound
// approximation (a counterexample over it is OverApproximation, a proof stays clean), and the
// zero-operand cases IEEE 754 determines are encoded exactly, so the `_holds` verify.

#[kani::proof]
fn arith_add_pz_sign_holds() {
    // +0 + +0 = +0 and -0 + +0 = +0 under round-to-nearest: determined for either zero.
    let m = 0.0f32.min(-0.0);
    assert!((m + 0.0).is_sign_positive());
}

#[kani::proof]
fn arith_add_pz_sign_refuted() {
    let m = 0.0f32.min(-0.0);
    assert!((m + 0.0).is_sign_negative());
}

#[kani::proof]
fn arith_recip_sign_unprovable() {
    // 1 / +0 = +inf, 1 / -0 = -inf: the sign follows the relation's choice.
    let m = 0.0f64.min(-0.0);
    assert!(1.0 / m > 0.0);
}

#[kani::proof]
fn arith_recip_infinite_holds() {
    let m = 0.0f64.min(-0.0);
    assert!((1.0 / m).is_infinite());
}

#[kani::proof]
fn arith_mul_neg_one_eq_zero_holds() {
    let m = (-0.0f32).max(0.0);
    assert!(m * -1.0 == 0.0);
}

#[kani::proof]
fn arith_mul_neg_one_sign_unprovable() {
    let m = (-0.0f32).max(0.0);
    assert!((m * -1.0).is_sign_negative());
}

#[kani::proof]
fn arith_sub_sign_unprovable() {
    // +0 - +0 = +0 but -0 - +0 = -0.
    let m = 0.0f64.max(-0.0);
    assert!((m - 0.0).is_sign_positive());
}

#[kani::proof]
fn arith_sub_zero_is_zero_holds() {
    let m = 0.0f64.max(-0.0);
    assert!(m - 0.0 == 0.0);
}

#[kani::proof]
fn arith_copysign_sign_unprovable() {
    let m = (-0.0f32).max(0.0);
    assert!(2.0f32.copysign(m) == 2.0);
}

#[kani::proof]
fn arith_copysign_magnitude_holds() {
    let m = (-0.0f32).max(0.0);
    assert!(2.0f32.copysign(m).abs() == 2.0);
}

// A symbolic non-zero operand: the result is the table's, so nothing about it is proved and
// nothing about it is certified.
#[kani::proof]
fn arith_sym_sum_sign_refuted() {
    let x: f32 = kani::any();
    kani::assume(x.is_finite() && x != 0.0);
    let m = 0.0f32.min(-0.0);
    assert!((x + m).is_sign_positive());
}

#[kani::proof]
fn arith_sym_sum_is_x_holds() {
    // x + ±0 = x for a finite non-zero x.
    let x: f32 = kani::any();
    kani::assume(x.is_finite() && x != 0.0);
    let m = 0.0f32.min(-0.0);
    assert!((x + m).to_bits() == x.to_bits());
}

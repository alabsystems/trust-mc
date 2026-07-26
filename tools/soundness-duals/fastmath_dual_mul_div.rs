// Op-coverage duals for the NaN-generation obligation (Kani --nan-check
// parity) through the NEW congruent float-binop lane. Operands are kept
// SYMBOLIC via kani::any + assume so they exercise the table lane, not
// const-fold. Every harness genuinely produces NaN, so each must be
// VERIFICATION FAILED (Mul: 0 * inf; Div: 0/0 and inf/inf — the `assume(x ==
// 0.0)` / `== INFINITY` patterns are NOT finite-assume shapes, and the
// divisors are not nonzero constants, so no obligation discharges).

#[kani::proof]
fn mul_nan() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x == 0.0);
    kani::assume(y == f32::INFINITY);
    let z = x * y;
    assert!(z == z || z != z);
}

#[kani::proof]
fn div_zero_zero() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x == 0.0);
    kani::assume(y == 0.0);
    let z = x / y;
    assert!(z == z || z != z);
}

#[kani::proof]
fn div_inf_inf() {
    let x: f32 = kani::any();
    let y: f32 = kani::any();
    kani::assume(x == f32::INFINITY);
    kani::assume(y == f32::INFINITY);
    let z = x / y;
    assert!(z == z || z != z);
}

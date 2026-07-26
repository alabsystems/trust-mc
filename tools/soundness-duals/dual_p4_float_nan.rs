// Dual for P4 fix 4 (float boundary axioms).
// ALL harnesses must FAIL:
// - NaN - NaN == NaN, and NaN == 0.0 is false: an UNGUARDED sub(x,x) = +0.0
//   axiom would falsely prove the first three.
// - The powf/sine duals guard the blessed math-axiom over-approximation:
//   the axioms must never PIN the result to a specific value.
#![feature(core_intrinsics)]

#[kani::proof]
fn dual_nan_sub_not_zero() {
    let a = f32::NAN;
    let d = a - a;
    // Real result: NaN != 0.0. This assert is WRONG and must FAIL.
    assert!(d == 0.0);
}

#[kani::proof]
fn dual_nan_sub_not_zero_f64() {
    let a = f64::NAN;
    let d = a - a;
    assert!(d == 0.0);
}

#[kani::proof]
fn dual_symbolic_nan_sub_not_zero() {
    // Symbolic lane: x - x with x possibly NaN/Inf must NOT prove == 0.0.
    let x: f32 = kani::any();
    let d = x - x;
    assert!(d == 0.0);
}

#[kani::proof]
fn dual_inf_sub_not_zero() {
    // Inf - Inf = NaN: the finite guard must exclude infinities too.
    let x: f32 = kani::any();
    kani::assume(x == f32::INFINITY);
    let d = x - x;
    assert!(d == 0.0);
}

#[kani::proof]
fn dual_powf_not_lower_bounded() {
    // x in (0,1): x^2 < 1.0 — the even-power axiom (result >= 0) must not
    // prove a lower bound of 1.0.
    let x: f32 = kani::any();
    kani::assume(x.is_normal());
    kani::assume(x > 0.0 && x < 1.0);
    let x2 = x.powf(2.0);
    assert!(x2 >= 1.0);
}

#[kani::proof]
fn dual_sine_not_pinned() {
    // The sin range axiom constrains [-1,1] only; asserting an exact value
    // must FAIL.
    let x: f32 = kani::any();
    kani::assume(x.is_finite());
    let sine = unsafe { std::intrinsics::sinf32(x) };
    assert!(sine == 1.0);
}

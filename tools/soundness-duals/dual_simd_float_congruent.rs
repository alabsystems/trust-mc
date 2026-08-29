// Copyright Andrew Yates. Apache-2.0 OR MIT
//
// kani-flags: --nan-check
// NOTE: `simd_float_div_congruent` fails ONLY through the NaN-generation
// obligation (0/0), which requires --nan-check. Without it the obligation is
// never emitted and this tripwire passes VACUOUSLY.
//
// Oracle (per harness):
//   simd_float_div_congruent -> VERIFICATION:- FAILED
//   simd_float_div_wrong_key -> VERIFICATION:- FAILED
//
// Soundness duals for the SIMD float congruent-table lanes
// (codegen_call_simd_ops.rs apply_simd_binop -> float_binop_chc_term).
//
// The congruent table makes `simd_div` lane i and the scalar `a[i] / b[i]`
// the SAME table select (equality discharges), but it must NOT equate
// DIFFERENT keys:
//   simd_float_div_congruent — FAILS (correctly): with unconstrained any()
//     floats the NaN-generation obligation is genuinely reachable (0/0), so
//     the harness fails that check under Kani semantics too; the assert itself
//     exercises the congruence path (lane select == scalar table term).
//   simd_float_div_wrong_key — MUST FAIL: lane == a mult-derived value is not
//     implied by congruence (the discriminating tripwire — a force-true
//     encoding would spuriously prove it).
#![feature(repr_simd, core_intrinsics)]

#[repr(simd)]
#[derive(Copy, Clone)]
struct F32x2([f32; 2]);

#[kani::proof]
fn simd_float_div_congruent() {
    let a0: f32 = kani::any();
    let a1: f32 = kani::any();
    let b0: f32 = kani::any();
    let b1: f32 = kani::any();
    let x = F32x2([a0, a1]);
    let y = F32x2([b0, b1]);
    let q = unsafe { std::intrinsics::simd::simd_div(x, y) };
    let lanes = unsafe { std::mem::transmute::<F32x2, [f32; 2]>(q) };
    assert!(lanes[0].to_bits() == (a0 / b0).to_bits());
    assert!(lanes[1].to_bits() == (a1 / b1).to_bits());
}

#[kani::proof]
fn simd_float_div_wrong_key() {
    let a0: f32 = kani::any();
    let b0: f32 = kani::any();
    let x = F32x2([a0, 0.0]);
    let y = F32x2([b0, 1.0]);
    let q = unsafe { std::intrinsics::simd::simd_div(x, y) };
    let lanes = unsafe { std::mem::transmute::<F32x2, [f32; 2]>(q) };
    // Division result equated against a MULTIPLICATION of the same operands:
    // different table keys — congruence must not prove this (and it is false
    // on real IEEE semantics for almost all inputs).
    assert!(lanes[0].to_bits() == (a0 * b0).to_bits());
}

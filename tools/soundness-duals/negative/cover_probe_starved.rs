// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: probes the per-harness budget can starve.
//
// Audit evidence: bmc-codegen/single-ctrex-reporting and kani-surface/lib-cover.
// The finding as stated was refuted: since 8f4946df8 the BMC driver re-queries
// every non-FAILURE violation flag on its own. The confirmed residual is what
// happens when that re-query is starved of budget. call_ay.rs keeps the first
// model's status for a `None` answer ("keep the model-based classification"),
// so a violable check the first model did not surface reads SUCCESS instead
// of UNDETERMINED. That is a check-level missed bug (R3) behind a FAILED
// verdict. Cover probes that run out of budget are rendered UNDETERMINED,
// which is honest; the cover harnesses pin that it stays so (R4).
//
// Oracle (per harness):
//   starved_violation_requery     -> VERIFICATION:- FAILED (assertion)
//       check "violable only by factoring the first semiprime"  -> FAILURE (UNDETERMINED tolerated)
//       check "violable only by factoring the second semiprime" -> FAILURE (UNDETERMINED tolerated)
//   cover_after_expensive_assert  -> VERIFICATION:- SUCCESSFUL
//       cover "easy cover after expensive assert" -> SATISFIED (UNDETERMINED tolerated)
//   expensive_cover_probe         -> VERIFICATION:- SUCCESSFUL
//       cover "factor a 62-bit semiprime"         -> SATISFIED (UNDETERMINED tolerated)
//   unsatisfiable_cover_control   -> VERIFICATION:- SUCCESSFUL
//       cover "contradictory cover"               -> UNSATISFIABLE (UNDETERMINED tolerated)
//
// The semiprimes are 2147483647 * 2147483629 and 2147483587 * 2147483579 (all
// four factors prime), so each factoring assertion is violable, but only by a
// model that factors a 62-bit product.

#[kani::proof]
fn starved_violation_requery() {
    let x: u8 = kani::any();
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    kani::assume(a > 1 && b > 1 && a < (1u64 << 32) && b < (1u64 << 32));
    // Cheap: the first model violates this one with x == 0.
    assert!(x != 0, "cheap violable assertion");
    // Each re-query needs a factorization; a starved probe must not read SUCCESS.
    assert!(a * b != 4611685975477714963u64, "violable only by factoring the first semiprime");
    assert!(a * b != 4611685739254517873u64, "violable only by factoring the second semiprime");
}

#[kani::proof]
fn cover_after_expensive_assert() {
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    // True for every input, but a 64-bit nonlinear query that eats the budget.
    assert!(a.wrapping_mul(b) == b.wrapping_mul(a));
    kani::cover!(a == 7, "easy cover after expensive assert");
}

#[kani::proof]
fn expensive_cover_probe() {
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    kani::assume(a > 1 && b > 1 && a < (1u64 << 32) && b < (1u64 << 32));
    assert!(a > 1);
    kani::cover!(a * b == 4611685975477714963u64, "factor a 62-bit semiprime");
}

#[kani::proof]
fn unsatisfiable_cover_control() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    assert!(a == a);
    kani::cover!(a < b && b < a, "contradictory cover");
}

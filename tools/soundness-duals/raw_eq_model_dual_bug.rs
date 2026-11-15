// `raw_eq` model — BUG twin.
//
// The no-blinding half of `raw_eq_model_dual_safe.rs`. Whatever is eventually
// done about the trustc route's certified false positive on
// `kani/Intrinsics/RawEq/main.rs` (`docs/t1-rows-2-exceedances.md`, unit 3), it
// must not be done by making the `raw_eq` model blind: a FALSE claim about
// `raw_eq` still has to be refuted.
//
// Every assertion here is FALSE. `VERIFICATION:- FAILED` is the only acceptable
// verdict; SUCCESSFUL is a missed bug and a P0.
//
// Shape taken from `kani/Intrinsics/RawEq/main.rs`.

#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::raw_eq;

#[kani::proof]
fn raw_eq_model_still_refutes_a_false_claim() {
    // FALSE: the two arrays differ in both bytes.
    let eq_array: bool = unsafe { raw_eq(&[13_u8, 42], &[42, 13]) };
    assert!(eq_array);
}

#[kani::proof]
fn raw_eq_model_still_refutes_a_false_inequality() {
    // FALSE: the two values are byte-identical.
    let ne_i32: bool = unsafe { raw_eq(&42_i32, &42) };
    assert!(!ne_i32);
}

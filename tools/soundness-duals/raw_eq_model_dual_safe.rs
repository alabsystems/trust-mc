// `raw_eq` model — SAFE twin.
//
// Every assertion here is a constant truth about `core::intrinsics::raw_eq`:
// equal byte patterns compare equal, different ones do not. Nothing can be
// disproved, and the engine must not certify a counterexample.
//
// Why it exists. `kani/Intrinsics/RawEq/main.rs` is one of the seven CHC units
// that report a CERTIFIED failure (`[AY:CTREX_CAT:Genuine]`,
// `assertion failed: raw_eq_array_true`) on the canonical-trustc route at Trust
// seal 8595 where the frozen-nightly route reports SUCCESSFUL — see
// `docs/t1-rows-2-exceedances.md`, unit 3. That difference is NOT explained:
// `raw_eq` is declared `#[rustc_intrinsic]` with NO body in BOTH toolchains'
// `core` (verified in the seal's own `library/core/src/intrinsics/mod.rs` and
// the frozen nightly's), so neither route has a library body to inline, and a
// guard that refused one anyway left the trustc output byte-identical.
//
// This dual pins the half that IS decided: on the lane the gate runs, the model
// must keep proving what is true. If a later change makes the trustc route agree
// by WEAKENING the `raw_eq` model, this twin and its bug twin catch it.
//
// Shape taken from `kani/Intrinsics/RawEq/main.rs`.

#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::raw_eq;

#[kani::proof]
fn raw_eq_true_claims_are_proved() {
    let eq_i32: bool = unsafe { raw_eq(&42_i32, &42) };
    assert!(eq_i32);

    let ne_i32: bool = unsafe { raw_eq(&4_i32, &2) };
    assert!(!ne_i32);

    let eq_char: bool = unsafe { raw_eq(&'a', &'a') };
    assert!(eq_char);

    let ne_char: bool = unsafe { raw_eq(&'a', &'A') };
    assert!(!ne_char);

    // The array arm is the one the trustc route refutes.
    let eq_array: bool = unsafe { raw_eq(&[13_u8, 42], &[13, 42]) };
    assert!(eq_array);

    let ne_array: bool = unsafe { raw_eq(&[13_u8, 42], &[42, 13]) };
    assert!(!ne_array);
}

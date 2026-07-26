// Copyright Andrew Yates. Apache-2.0 OR MIT
//
// Soundness duals for the Infallible wrapper-blob exclusion
// (codegen_types_adt.rs has_alloc_infra_arg: `Result<Infallible, E>` now takes
// the general enum datatype path instead of an opaque bv128 blob).
//
// The datatype must carry the REAL error payload:
//   infallible_result_err_correct — MUST SUCCEED: the Err value is 42.
//   infallible_result_err_wrong   — MUST FAIL (Genuine): 43 is not stored.

use std::convert::Infallible;

fn make_err() -> Result<Infallible, u32> {
    Err(42)
}

#[kani::proof]
fn infallible_result_err_correct() {
    match make_err() {
        Ok(_) => unreachable!(),
        Err(v) => assert!(v == 42),
    }
}

#[kani::proof]
fn infallible_result_err_wrong() {
    match make_err() {
        Ok(_) => unreachable!(),
        Err(v) => assert!(v == 43),
    }
}

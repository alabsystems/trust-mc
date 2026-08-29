// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verifies wrapping_pow CHC dispatch handler correctness.
//!
//! The wrapping_pow(2, exp) path is encoded as bvshl(1, exp) in codegen.
//! This cross-checks that encoding against the separate BinOp::Shl path
//! (which goes through MIR Shl → bvshl directly).
//! Part of #3186: pow/wrapping_pow CHC dispatch.

// kani-expect: PROOF
#[kani::proof]
fn test_wrapping_pow_i32() {
    let exp: u32 = kani::any();
    kani::assume(exp < 31);
    let result = 2_i32.wrapping_pow(exp);
    // Cross-path assertion: wrapping_pow(2, exp) must equal 1 << exp.
    // wrapping_pow goes through the CHC call dispatch (bvshl stub),
    // while `<<` goes through MIR BinOp::Shl (direct bvshl encoding).
    // If the wrapping_pow encoding is wrong, these paths will diverge.
    // Note: use raw `<<` not `wrapping_shl` — wrapping_shl is a method call
    // that may lack CHC dispatch, while `<<` is a MIR BinOp.
    let expected = 1_i32 << exp;
    assert!(result == expected);
}

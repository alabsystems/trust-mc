// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fast-math BinOp expression patterns and SSA definition patterns.
//!
//! Fast-math intrinsics (fadd_fast etc.) use the same BinOp codegen as normal
//! arithmetic, plus a finite check. Test the expression structure.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

/// Test fast-math addition produces BvAdd expression.
#[test]
fn test_fast_math_add_expression() {
    let lhs = Expr::bitvec_const(1.0f32.to_bits() as u64, 32);
    let rhs = Expr::bitvec_const(2.0f32.to_bits() as u64, 32);

    // Fast-math add is modeled as bitvec add (same as normal float in BV model)
    let result = lhs.bvadd(rhs);
    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert!(matches!(result.value(), ExprValue::BvAdd { .. }));
}

/// Test fast-math subtraction produces BvSub expression.
#[test]
fn test_fast_math_sub_expression() {
    let lhs = Expr::bitvec_const(3.0f32.to_bits() as u64, 32);
    let rhs = Expr::bitvec_const(1.0f32.to_bits() as u64, 32);

    let result = lhs.bvsub(rhs);
    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert!(matches!(result.value(), ExprValue::BvSub { .. }));
}

/// Test fast-math multiplication produces BvMul expression.
#[test]
fn test_fast_math_mul_expression() {
    let lhs = Expr::bitvec_const(2.0f32.to_bits() as u64, 32);
    let rhs = Expr::bitvec_const(3.0f32.to_bits() as u64, 32);

    let result = lhs.bvmul(rhs);
    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert!(matches!(result.value(), ExprValue::BvMul { .. }));
}

/// Test that fast-math BvAdd preserves operand values in the expression tree.
/// Verifies: both children of BvAdd are the original operand expressions.
#[test]
fn test_fast_math_add_preserves_operands() {
    let lhs = Expr::bitvec_const(1.0f32.to_bits() as u64, 32);
    let rhs = Expr::bitvec_const(2.0f32.to_bits() as u64, 32);

    let result = lhs.bvadd(rhs);
    assert_eq!(result.sort().bitvec_width(), Some(32));
    match result.value() {
        ExprValue::BvAdd(l, r) => {
            // Verify children are BitVecConst with correct IEEE 754 patterns
            match l.value() {
                ExprValue::BitVecConst { value, width } => {
                    assert_eq!(*width, 32);
                    assert_eq!(*value, BigInt::from(1.0f32.to_bits() as u128));
                }
                other => panic!("BvAdd lhs should be BitVecConst, got {other:?}"),
            }
            match r.value() {
                ExprValue::BitVecConst { value, width } => {
                    assert_eq!(*width, 32);
                    assert_eq!(*value, BigInt::from(2.0f32.to_bits() as u128));
                }
                other => panic!("BvAdd rhs should be BitVecConst, got {other:?}"),
            }
        }
        other => panic!("expected BvAdd, got {other:?}"),
    }
}

/// Test SSA definition pattern: dest_var == const_val produces an Eq node
/// with correct variable and constant children (the pattern codegen uses
/// for math constant folding assignments).
#[test]
fn test_ssa_def_pattern_for_const_fold() {
    let dest_sort = Sort::bitvec(32);
    let dest_var = Expr::var("f32_sqrt_result_v1", dest_sort);
    let const_val = Expr::bitvec_const(2.0f32.to_bits() as u128, 32);

    // The codegen asserts dest_var == const_val
    let eq = dest_var.eq(const_val);
    assert!(eq.sort().is_bool());

    // Verify Eq structure has the right children
    match eq.value() {
        ExprValue::Eq(lhs, rhs) => {
            // LHS should be the variable
            assert!(
                matches!(lhs.value(), ExprValue::Var { .. }),
                "Eq LHS should be a variable, got {:?}",
                lhs.value()
            );
            // RHS should be the constant 2.0f32 bit pattern
            match rhs.value() {
                ExprValue::BitVecConst { value, width } => {
                    assert_eq!(*width, 32);
                    assert_eq!(
                        *value,
                        BigInt::from(2.0f32.to_bits() as u128),
                        "Eq RHS should be IEEE 754 bits for 2.0f32"
                    );
                }
                other => panic!("Eq RHS should be BitVecConst, got {other:?}"),
            }
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

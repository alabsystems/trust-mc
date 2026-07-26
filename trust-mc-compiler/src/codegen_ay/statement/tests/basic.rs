// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Basic codegen unit tests.
//!
//! Tests for fundamental operations:
//! - Binary operations (add, sub, mul, div, rem)
//! - Overflow checks
//! - Type coercion (sign/zero extend, width matching)
//! - Bitwise operations (and, or, xor, not)
//! - Comparisons
//! - Casts (bool<->bitvec)
//! - Phi node conversions (BigInt/BigUint)
//!
//! Extracted from tests.rs per #1734.

use super::*;

const BITWISE_WIDTH_SOURCE: &str = r#"
pub fn bitwise_width_probe() {}
"#;

#[test]
fn test_binop_translation() {
    let lhs = Expr::bitvec_const(5, 32);
    let rhs = Expr::bitvec_const(3, 32);

    // Addition: returns bitvec of same width
    let add = lhs.clone().bvadd(rhs.clone());
    assert_eq!(add.sort().bitvec_width(), Some(32));
    assert!(matches!(add.value(), ExprValue::BvAdd(..)));

    // Subtraction: returns bitvec of same width
    let sub = lhs.clone().bvsub(rhs.clone());
    assert_eq!(sub.sort().bitvec_width(), Some(32));
    assert!(matches!(sub.value(), ExprValue::BvSub(..)));

    // Equality: returns boolean
    let eq = lhs.eq(rhs);
    assert!(eq.sort().is_bool());
    assert!(matches!(eq.value(), ExprValue::Eq(..)));
}

#[test]
fn test_overflow_check_expressions() {
    let lhs = Expr::bitvec_const(100, 32);
    let rhs = Expr::bitvec_const(50, 32);
    let add_no_overflow = lhs.clone().bvadd_no_overflow_signed(rhs.clone());
    assert!(add_no_overflow.sort().is_bool());
    let add_no_overflow = lhs.clone().bvadd_no_overflow_unsigned(rhs.clone());
    assert!(add_no_overflow.sort().is_bool());
    let sub_no_overflow = lhs.clone().bvsub_no_overflow_signed(rhs.clone());
    assert!(sub_no_overflow.sort().is_bool());
    let sub_no_underflow = lhs.clone().bvsub_no_underflow_unsigned(rhs.clone());
    assert!(sub_no_underflow.sort().is_bool());
    let mul_no_overflow = lhs.clone().bvmul_no_overflow_signed(rhs.clone());
    assert!(mul_no_overflow.sort().is_bool());
    let mul_no_overflow = lhs.clone().bvmul_no_overflow_unsigned(rhs);
    assert!(mul_no_overflow.sort().is_bool());
    let neg_no_overflow = lhs.bvneg_no_overflow();
    assert!(neg_no_overflow.sort().is_bool());
}

#[test]
fn test_coerce_to_width_typed_sign_extends() {
    let expr = Expr::bitvec_const(0xffu128, 8);
    let widened = StatementCodegen::coerce_to_width_typed(expr, 32, true);
    assert_eq!(widened.sort().bitvec_width(), Some(32));
    assert!(matches!(widened.value(), ExprValue::BvSignExtend { .. }));
}

#[test]
fn test_coerce_to_width_typed_zero_extends() {
    let expr = Expr::bitvec_const(0xffu128, 8);
    let widened = StatementCodegen::coerce_to_width_typed(expr, 32, false);
    assert_eq!(widened.sort().bitvec_width(), Some(32));
    assert!(matches!(widened.value(), ExprValue::BvZeroExtend { .. }));
}

#[test]
fn test_coerce_to_match_widths_typed_widens_rhs() {
    let lhs = Expr::bitvec_const(0u128, 32);
    let rhs = Expr::bitvec_const(0xffu128, 8);
    let (lhs_w, rhs_w) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, true);
    assert_eq!(lhs_w.sort().bitvec_width(), Some(32));
    assert_eq!(rhs_w.sort().bitvec_width(), Some(32));
    assert!(matches!(rhs_w.value(), ExprValue::BvSignExtend { .. }));
}

#[test]
fn test_shift_uses_logical_for_unsigned() {
    let lhs = Expr::bitvec_const(0xFFFFFFFFu128, 32);
    let rhs = Expr::bitvec_const(1u128, 32);
    let result_unsigned = lhs.clone().bvlshr(rhs.clone());
    assert!(matches!(result_unsigned.value(), ExprValue::BvLShr { .. }));
    let result_signed = lhs.bvashr(rhs);
    assert!(matches!(result_signed.value(), ExprValue::BvAShr { .. }));
}

#[test]
fn test_codegen_bitwise_coerces_widths() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(-1i128, 8);
        let rhs = Expr::bitvec_const(0x0fu128, 16);
        let expr = codegen.codegen_binop_typed(BinOp::BitAnd, lhs, rhs, Some(true));

        assert_eq!(expr.sort().bitvec_width(), Some(16));
        assert!(expr.to_string().contains("sign_extend"));
    });
}

#[test]
fn test_sort_consistency_datatype_vs_bitvec() {
    let tuple_sort =
        struct_sort("Tuple_bv32_bv32", [("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bitvec(32))]);
    let fld0 = Expr::bitvec_const(1u128, 32);
    let fld1 = Expr::bitvec_const(2u128, 32);
    let tuple_expr = Expr::datatype_constructor(
        "Tuple_bv32_bv32",
        "Tuple_bv32_bv32_mk",
        vec![fld0, fld1],
        tuple_sort,
    );
    assert!(tuple_expr.sort().is_datatype());
}

#[test]
fn test_phi_bigint_path_prefixed_datatype_converts_to_int_field() {
    // #927: Use test fixture with "BigInt" in name to trigger convert_expr_to_sort
    // detection logic (env.rs:295). The name must contain "BigInt" for the production
    // code path, but uses "test::" prefix to show it's not a real BigInt type.
    // Real BigInt has 2 fields (sign, data); this fixture models the abstraction.
    let bigint_sort = struct_sort("test::BigIntWrapper", [("data", Sort::int())]);
    let bigint_expr = Expr::var("big", bigint_sort);

    let converted = StatementCodegen::convert_expr_to_sort(bigint_expr, &Sort::int(), None);

    assert!(converted.sort().is_int());
    match converted.value() {
        ExprValue::DatatypeSelector { datatype_name, selector_name, .. } => {
            assert_eq!(datatype_name, "test::BigIntWrapper");
            assert_eq!(selector_name, "data");
        }
        other => panic!("expected DatatypeSelector, got {:?}", other),
    }
}

#[test]
fn test_phi_biguint_path_prefixed_datatype_converts_to_int_field() {
    // #927: Use test fixture with "BigUint" in name to trigger convert_expr_to_sort
    // detection logic (env.rs:295). The name must contain "BigUint" for the production
    // code path, but uses "test::" prefix to show it's not a real BigUint type.
    // Real BigUint has 1 field (data: Vec<u64>); this fixture models the abstraction.
    let biguint_sort = struct_sort("test::BigUintWrapper", [("data", Sort::int())]);
    let biguint_expr = Expr::var("big", biguint_sort);

    let converted = StatementCodegen::convert_expr_to_sort(biguint_expr, &Sort::int(), None);

    assert!(converted.sort().is_int());
    match converted.value() {
        ExprValue::DatatypeSelector { datatype_name, selector_name, .. } => {
            assert_eq!(datatype_name, "test::BigUintWrapper");
            assert_eq!(selector_name, "data");
        }
        other => panic!("expected DatatypeSelector, got {:?}", other),
    }
}

#[test]
fn test_truncation_preserves_low_bits() {
    let expr = Expr::bitvec_const(0x1234_5678u128, 32);
    let truncated = expr.extract(7, 0);
    assert_eq!(truncated.sort().bitvec_width(), Some(8));
}

#[test]
fn test_bool_to_bitvec_cast() {
    let bool_true = Expr::bool_const(true);
    let bool_false = Expr::bool_const(false);
    let bv_true = Expr::ite(bool_true, Expr::bitvec_const(1, 8), Expr::bitvec_const(0, 8));
    let bv_false = Expr::ite(bool_false, Expr::bitvec_const(1, 8), Expr::bitvec_const(0, 8));
    assert_eq!(bv_true.sort().bitvec_width(), Some(8));
    assert_eq!(bv_false.sort().bitvec_width(), Some(8));
}

#[test]
fn test_bitvec_to_bool_cast() {
    let expr = Expr::bitvec_const(5u128, 32);
    let zero = Expr::bitvec_const(0u128, 32);
    let result = expr.ne(zero);
    assert!(result.sort().is_bool());
}

#[test]
fn test_division_by_nonzero() {
    let lhs = Expr::bitvec_const(100u128, 32);
    let rhs = Expr::bitvec_const(7u128, 32);
    let udiv = lhs.clone().bvudiv(rhs.clone());
    let sdiv = lhs.bvsdiv(rhs);
    assert_eq!(udiv.sort().bitvec_width(), Some(32));
    assert_eq!(sdiv.sort().bitvec_width(), Some(32));
}

#[test]
fn test_remainder_operations() {
    let lhs = Expr::bitvec_const(100u128, 32);
    let rhs = Expr::bitvec_const(7u128, 32);
    let urem = lhs.clone().bvurem(rhs.clone());
    let srem = lhs.bvsrem(rhs);
    assert_eq!(urem.sort().bitvec_width(), Some(32));
    assert_eq!(srem.sort().bitvec_width(), Some(32));
}

#[test]
fn test_comparison_operations_return_bool() {
    let lhs = Expr::bitvec_const(10u128, 32);
    let rhs = Expr::bitvec_const(20u128, 32);
    assert!(lhs.clone().eq(rhs.clone()).sort().is_bool());
    assert!(lhs.clone().ne(rhs.clone()).sort().is_bool());
    assert!(lhs.clone().bvult(rhs.clone()).sort().is_bool());
    assert!(lhs.clone().bvule(rhs.clone()).sort().is_bool());
    assert!(lhs.clone().bvslt(rhs.clone()).sort().is_bool());
    assert!(lhs.bvsle(rhs).sort().is_bool());
}

#[test]
fn test_bitwise_operations_preserve_width() {
    let lhs = Expr::bitvec_const(0xF0F0u128, 16);
    let rhs = Expr::bitvec_const(0x0F0Fu128, 16);
    assert_eq!(lhs.clone().bvand(rhs.clone()).sort().bitvec_width(), Some(16));
    assert_eq!(lhs.clone().bvor(rhs.clone()).sort().bitvec_width(), Some(16));
    assert_eq!(lhs.bvxor(rhs).sort().bitvec_width(), Some(16));
}

#[test]
fn test_unary_negation() {
    let expr = Expr::bitvec_const(5u128, 32);
    let neg = expr.bvneg();
    assert_eq!(neg.sort().bitvec_width(), Some(32));
}

#[test]
fn test_bitwise_not_preserves_width() {
    let expr = Expr::bitvec_const(0xFFu128, 8);
    let not = expr.bvnot();
    assert_eq!(not.sort().bitvec_width(), Some(8));
}

// --- Tests for codegen_unop (via StatementCodegen) ---

#[test]
fn test_codegen_unop_not_bool() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bool_expr = Expr::bool_const(true);
        let result = codegen.codegen_unop(UnOp::Not, bool_expr);
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::Not(..)));
    });
}

#[test]
fn test_codegen_unop_not_bitvec() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_expr = Expr::bitvec_const(0xFFu128, 8);
        let result = codegen.codegen_unop(UnOp::Not, bv_expr);
        assert_eq!(result.sort().bitvec_width(), Some(8));
        assert!(matches!(result.value(), ExprValue::BvNot(..)));
    });
}

#[test]
fn test_codegen_unop_neg() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_expr = Expr::bitvec_const(42u128, 32);
        let result = codegen.codegen_unop(UnOp::Neg, bv_expr);
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvNeg(..)));
    });
}

// --- Tests for build_discriminant_ite_chain ---

#[test]
fn test_build_discriminant_ite_chain_two_constructors() {
    // Simulates Option<T>: None=0, Some=1
    let option_sort = enum_sort(
        "Option_bv32",
        [("Option_None", vec![]), ("Option_Some", vec![("value", Sort::bitvec(32))])],
    );

    // Create a None expression and test discriminant
    let none_expr =
        Expr::datatype_constructor("Option_bv32", "Option_None", vec![], option_sort.clone());

    // Get constructors from the sort
    if let ay_bindings::SortInner::Datatype(dt) = option_sort.inner() {
        let result =
            StatementCodegen::build_discriminant_ite_chain(&dt.name, &dt.constructors, &none_expr);
        // Result should be bv32 (discriminant width)
        assert_eq!(result.sort().bitvec_width(), Some(32));
        // Should be an ITE expression
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    } else {
        panic!("Expected Datatype sort for Option");
    }
}

// --- Tests for coerce_to_int_pair ---

#[test]
fn test_coerce_to_int_pair_both_int() {
    let lhs = Expr::int_const(42);
    let rhs = Expr::int_const(7);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    // Both already Int, should pass through unchanged
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
}

#[test]
fn test_coerce_to_int_pair_mixed_bv_int() {
    let lhs = Expr::bitvec_const(42u128, 32);
    let rhs = Expr::int_const(7);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    // lhs should be converted to Int, rhs passes through
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    assert!(matches!(l.value(), ExprValue::Bv2Int(..)));
}

#[test]
fn test_coerce_to_int_pair_mixed_int_bv() {
    let lhs = Expr::int_const(42);
    let rhs = Expr::bitvec_const(7u128, 64);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    // rhs should be converted to Int, lhs passes through
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    assert!(matches!(r.value(), ExprValue::Bv2Int(..)));
}

// =============================================================================
// codegen_binop_typed: arithmetic operations via StatementCodegen (Part of #2016)
// =============================================================================

#[test]
fn test_codegen_binop_add() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Add, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvAdd(..)));
    });
}

#[test]
fn test_codegen_binop_sub() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(10u128, 32);
        let rhs = Expr::bitvec_const(3u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Sub, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvSub(..)));
    });
}

#[test]
fn test_codegen_binop_mul() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(7u128, 32);
        let rhs = Expr::bitvec_const(6u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Mul, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvMul(..)));
    });
}

#[test]
fn test_codegen_binop_div_unsigned() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Div, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvUDiv(..)));
    });
}

#[test]
fn test_codegen_binop_div_signed() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Div, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvSDiv(..)));
    });
}

#[test]
fn test_codegen_binop_rem_unsigned() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(17u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Rem, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvURem(..)));
    });
}

#[test]
fn test_codegen_binop_rem_signed() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(17u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Rem, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvSRem(..)));
    });
}

// =============================================================================
// codegen_binop_typed: shift operations (Part of #2016)
// =============================================================================

#[test]
fn test_codegen_binop_shl() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(1u128, 32);
        let rhs = Expr::bitvec_const(4u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Shl, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvShl(..)));
    });
}

#[test]
fn test_codegen_binop_shr_unsigned() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xFF00u128, 32);
        let rhs = Expr::bitvec_const(8u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvLShr(..)));
    });
}

#[test]
fn test_codegen_binop_shr_signed() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xFF00u128, 32);
        let rhs = Expr::bitvec_const(8u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        // Signed shift → arithmetic right shift
        assert!(matches!(result.value(), ExprValue::BvAShr(..)));
    });
}

#[test]
fn test_codegen_binop_shl_mismatched_widths() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // MIR shift ops can have different-width operands (e.g., u32 << u8)
        let lhs = Expr::bitvec_const(1u128, 32);
        let rhs = Expr::bitvec_const(4u128, 8); // 8-bit shift amount
        let result = codegen.codegen_binop_typed(BinOp::Shl, lhs, rhs, Some(false));
        // Result width matches lhs (32-bit), rhs was coerced
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

// =============================================================================
// codegen_binop_typed: comparison operations (Part of #2016)
// =============================================================================

#[test]
fn test_codegen_binop_eq() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(42u128, 32);
        let rhs = Expr::bitvec_const(42u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Eq, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::Eq(..)));
    });
}

#[test]
fn test_codegen_binop_ne() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(42u128, 32);
        let rhs = Expr::bitvec_const(99u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Ne, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_codegen_binop_lt_unsigned() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Lt, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::BvULt(..)));
    });
}

#[test]
fn test_codegen_binop_lt_signed() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Lt, lhs, rhs, Some(true));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::BvSLt(..)));
    });
}

#[test]
fn test_codegen_binop_eq_mixed_int_bv() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // BigInt path: one Int, one BitVec → coerce both to Int
        let lhs = Expr::int_const(42);
        let rhs = Expr::bitvec_const(42u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Eq, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

// =============================================================================
// codegen_binop_typed: boolean bitwise operations (Part of #2016)
// =============================================================================

#[test]
fn test_codegen_binop_bitxor_bool() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(true);
        let rhs = Expr::bool_const(false);
        let result = codegen.codegen_binop_typed(BinOp::BitXor, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::Xor(..)));
    });
}

#[test]
fn test_codegen_binop_bitor_bool() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(true);
        let rhs = Expr::bool_const(false);
        let result = codegen.codegen_binop_typed(BinOp::BitOr, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::Or(..)));
    });
}

#[test]
fn test_codegen_binop_bitand_bool() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(true);
        let rhs = Expr::bool_const(false);
        let result = codegen.codegen_binop_typed(BinOp::BitAnd, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::And(..)));
    });
}

#[test]
fn test_codegen_binop_add_width_coercion() {
    with_test_ay_ctx_for_source(BITWISE_WIDTH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_width_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Mismatched widths: 8-bit + 16-bit → coerces to 16-bit
        let lhs = Expr::bitvec_const(5u128, 8);
        let rhs = Expr::bitvec_const(10u128, 16);
        let result = codegen.codegen_binop_typed(BinOp::Add, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(16));
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Signedness coverage for comparison codegen with `char` (unsigned) operands.
//!
//! `char` maps to `Some(false)` (unsigned) via `ty_signedness_shallow` (#2944).
//! These tests verify that char-vs-u16 comparisons use unsigned BV operations
//! (BvULt, BvZeroExtend) rather than signed ones.

use super::*;

const UNSIGNED_CHAR_COMPARISON_SOURCE: &str = r#"
pub fn mixed_scalar_probe(_a: char, _b: u16) -> bool {
    true
}
"#;

#[test]
fn test_codegen_ord_cmp_char_unsigned_uses_bvult() {
    with_test_ay_ctx_for_source(UNSIGNED_CHAR_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_scalar_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.operand_signedness(&local_operand(1)),
            Some(false),
            "char must be unsigned"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result =
            codegen.codegen_ord_cmp(&[local_operand(1), local_operand(2)], &dest, Some(26));
        assert_eq!(result, Some(26));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for ord_cmp unsigned path");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvULt(..))),
            "ord_cmp unsigned char must use BvULt, got {:?}",
            rhs.value()
        );
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvZeroExtend { .. })),
            "ord_cmp unsigned char should zero-extend narrower operand, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_partial_eq_char_unsigned_uses_zero_extend() {
    with_test_ay_ctx_for_source(UNSIGNED_CHAR_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_scalar_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.operand_signedness(&local_operand(1)),
            Some(false),
            "char must be unsigned"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result =
            codegen.codegen_partial_eq(&[local_operand(1), local_operand(2)], &dest, Some(27));
        assert_eq!(result, Some(27));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_eq unsigned path");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvZeroExtend { .. })),
            "partial_eq unsigned char should zero-extend narrower operand, got {:?}",
            rhs.value()
        );
        assert!(
            !expr_contains(&rhs, &|v| matches!(v, ExprValue::BvSignExtend { .. })),
            "partial_eq unsigned char must not sign-extend narrower operand, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_partial_ne_char_unsigned_uses_zero_extend() {
    with_test_ay_ctx_for_source(UNSIGNED_CHAR_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_scalar_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.operand_signedness(&local_operand(1)),
            Some(false),
            "char must be unsigned"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result =
            codegen.codegen_partial_ne(&[local_operand(1), local_operand(2)], &dest, Some(28));
        assert_eq!(result, Some(28));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_ne unsigned path");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvZeroExtend { .. })),
            "partial_ne unsigned char should zero-extend narrower operand, got {:?}",
            rhs.value()
        );
        assert!(
            !expr_contains(&rhs, &|v| matches!(v, ExprValue::BvSignExtend { .. })),
            "partial_ne unsigned char must not sign-extend narrower operand, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_partial_ord_cmp_char_unsigned_uses_bvult() {
    with_test_ay_ctx_for_source(UNSIGNED_CHAR_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_scalar_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.operand_signedness(&local_operand(1)),
            Some(false),
            "char must be unsigned"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_partial_ord_cmp(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(29),
            "lt",
        );
        assert_eq!(result, Some(29));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_ord unsigned path");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvULt(..))),
            "partial_ord lt unsigned char must use BvULt, got {:?}",
            rhs.value()
        );
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvZeroExtend { .. })),
            "partial_ord lt unsigned char should zero-extend narrower operand, got {:?}",
            rhs.value()
        );
    });
}

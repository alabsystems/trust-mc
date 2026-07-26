// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven array comparison regression tests.

use super::*;

const ARRAY_COMPARISON_SOURCE: &str = r#"
pub fn array_partial_ord_lt_probe(a: &[i32; 3], b: &[i32; 3]) -> bool {
    a < b
}

pub fn array_ord_cmp_probe(a: &[i32; 3], b: &[i32; 3]) -> core::cmp::Ordering {
    a.cmp(b)
}
"#;

fn ref_local_operand(local_idx: usize) -> Operand {
    Operand::Copy(Place { local: local_idx, projection: vec![] })
}

fn return_place() -> Place {
    Place { local: 0, projection: vec![] }
}

fn expr_contains(expr: &Expr, pred: &dyn Fn(&ExprValue) -> bool) -> bool {
    if pred(expr.value()) {
        return true;
    }
    match expr.value() {
        ExprValue::Not(inner) | ExprValue::BvNeg(inner) | ExprValue::BvNot(inner) => {
            expr_contains(inner, pred)
        }
        ExprValue::Eq(a, b)
        | ExprValue::BvULt(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b) => expr_contains(a, pred) || expr_contains(b, pred),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            expr_contains(cond, pred)
                || expr_contains(then_expr, pred)
                || expr_contains(else_expr, pred)
        }
        ExprValue::BvZeroExtend { expr: inner, .. }
        | ExprValue::BvSignExtend { expr: inner, .. }
        | ExprValue::BvExtract { expr: inner, .. } => expr_contains(inner, pred),
        _ => false,
    }
}

#[test]
fn test_mir_codegen_ord_cmp_array_uses_lexicographic_path() {
    with_test_ay_ctx_for_source(ARRAY_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_ord_cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(26);
        let before = codegen.ctx.program.commands().len();

        let result =
            codegen.codegen_ord_cmp(&[ref_local_operand(1), ref_local_operand(2)], &dest, target);

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "array ord_cmp should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "array ord_cmp destination should be Ordering discriminant bv32"
        );

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for array ord_cmp dest");
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::Ite { .. })),
            "array ord_cmp should use lexicographic ITE chain, got {:?}",
            rhs.value()
        );
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvSLt(..))),
            "array ord_cmp on i32 should use signed element comparison, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_codegen_partial_ord_array_lt_uses_lexicographic_path() {
    with_test_ay_ctx_for_source(ARRAY_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_partial_ord_lt_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(26);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_ord_cmp(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
            "lt",
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "array partial_ord lt should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "array partial_ord destination should be bool");

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for array partial_ord lt dest");
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::Ite { .. })),
            "array partial_ord should use lexicographic ITE chain, got {:?}",
            rhs.value()
        );
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvSLt(..))),
            "array partial_ord on i32 should use signed element comparison, got {:?}",
            rhs.value()
        );
    });
}

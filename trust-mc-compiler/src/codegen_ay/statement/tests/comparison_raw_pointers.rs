// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-backed raw-pointer `Ord::{min,max,clamp}` regressions for statement comparison lowering.

use super::*;

const RAW_POINTER_ORD_HELPER_SOURCE: &str = r#"
#![allow(ambiguous_wide_pointer_comparisons)]

pub fn raw_ptr_min_probe(a: *const u8, b: *const u8) -> *const u8 {
    a.min(b)
}

pub fn raw_ptr_max_probe(a: *const u8, b: *const u8) -> *const u8 {
    a.max(b)
}

pub fn raw_slice_ptr_clamp_probe(a: *const [u8], lo: *const [u8], hi: *const [u8]) -> *const [u8] {
    a.clamp(lo, hi)
}
"#;

fn return_place() -> Place {
    local_place(0)
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
fn test_mir_dispatch_ord_min_thin_raw_ptr_assigns_pointer_destination() {
    with_test_ay_ctx_for_source(RAW_POINTER_ORD_HELPER_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_min_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(26);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.dispatch_raw_eq_and_cmp(
            "core::cmp::Ord::min",
            &[local_operand(1), local_operand(2)],
            &dest,
            target,
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "Ord::min raw-pointer dispatch should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "thin raw-pointer min should preserve pointer-width bitvec sort"
        );

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for raw-pointer min");
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "raw-pointer min should lower to ITE selection, got {:?}",
            rhs.value()
        );
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvUGt(..))),
            "raw-pointer min should use unsigned pointer ordering, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_dispatch_ord_max_thin_raw_ptr_assigns_pointer_destination() {
    with_test_ay_ctx_for_source(RAW_POINTER_ORD_HELPER_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_max_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(27);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.dispatch_raw_eq_and_cmp(
            "core::cmp::Ord::max",
            &[local_operand(1), local_operand(2)],
            &dest,
            target,
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "Ord::max raw-pointer dispatch should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "thin raw-pointer max should preserve pointer-width bitvec sort"
        );

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for raw-pointer max");
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "raw-pointer max should lower to ITE selection, got {:?}",
            rhs.value()
        );
        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvULt(..))),
            "raw-pointer max should use unsigned pointer ordering, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_dispatch_ord_clamp_wide_raw_ptr_uses_ptr_and_len_selectors() {
    with_test_ay_ctx_for_source(RAW_POINTER_ORD_HELPER_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_slice_ptr_clamp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(28);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.dispatch_raw_eq_and_cmp(
            "core::cmp::Ord::clamp",
            &[local_operand(1), local_operand(2), local_operand(3)],
            &dest,
            target,
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "Ord::clamp wide raw-pointer dispatch should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(
            dest_expr.sort().datatype_name().is_some(),
            "wide raw-pointer clamp should preserve fat-pointer datatype sort"
        );

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for wide raw-pointer clamp");
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "wide raw-pointer clamp should lower to nested ITE selection, got {:?}",
            rhs.value()
        );
        let rhs_smt = format!("{rhs}");
        assert!(
            rhs_smt.contains("fld_ptr"),
            "wide raw-pointer clamp should compare fat-pointer data fields, got {rhs_smt}"
        );
        assert!(
            rhs_smt.contains("fld_len"),
            "wide raw-pointer clamp should compare fat-pointer metadata fields, got {rhs_smt}"
        );
    });
}

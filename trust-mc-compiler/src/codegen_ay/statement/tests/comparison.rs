// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven unit tests for comparison.rs — Ord::cmp, PartialEq/PartialOrd,
//! raw_eq, ZST detection, width coercion.
//!
//! Trivial tests that only constructed AY Expr/Sort values (ITE encoding
//! patterns, bvult/bvslt/bvule/bvsle/bvugt/bvsgt/bvuge/bvsge expressions,
//! eq/ne/bool_const assertions, int_lt/int_gt/int_bitvec_mix guard truth
//! tables, primitive clone sort checks) were removed per rule #2312 and #2482
//! because they did not exercise production codegen paths.
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

mod fallback_signedness;

/// Recursively check if an expression tree contains a node matching a predicate.
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

// ─── Bitvec width coercion for comparison ───────────────────────────

#[test]
fn test_coerce_widths_for_comparison_widens_narrower() {
    let lhs = Expr::bitvec_const(0xFFu128, 8);
    let rhs = Expr::bitvec_const(0x1234u128, 16);

    // Unsigned coercion: zero-extend narrower to wider
    let (lhs_c, rhs_c) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert_eq!(lhs_c.sort().bitvec_width(), Some(16));
    assert_eq!(rhs_c.sort().bitvec_width(), Some(16));
    assert!(matches!(lhs_c.value(), ExprValue::BvZeroExtend { .. }));
}

#[test]
fn test_coerce_widths_for_comparison_sign_extends_when_signed() {
    let lhs = Expr::bitvec_const(0xFFu128, 8); // -1 as i8
    let rhs = Expr::bitvec_const(0x0000u128, 16);

    // Signed coercion: sign-extend narrower to wider
    let (lhs_c, rhs_c) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, true);
    assert_eq!(lhs_c.sort().bitvec_width(), Some(16));
    assert_eq!(rhs_c.sort().bitvec_width(), Some(16));
    assert!(matches!(lhs_c.value(), ExprValue::BvSignExtend { .. }));
}

#[test]
fn test_coerce_widths_same_width_no_op() {
    let lhs = Expr::bitvec_const(5u128, 32);
    let rhs = Expr::bitvec_const(10u128, 32);

    let (lhs_c, rhs_c) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    // Same width: should pass through without extension
    assert_eq!(lhs_c.sort().bitvec_width(), Some(32));
    assert_eq!(rhs_c.sort().bitvec_width(), Some(32));
    // No sign/zero extend wrapper
    assert!(matches!(lhs_c.value(), ExprValue::BitVecConst { .. }));
    assert!(matches!(rhs_c.value(), ExprValue::BitVecConst { .. }));
}

// ─── ZST detection: is_zst_type via MIR context ────────────────────

const ZST_SOURCE: &str = r#"
pub struct Marker;

pub fn zst_probe(
    _marker: Marker,
    _unit: (),
    _arr0: [u8; 0],
    _arr_unit: [(); 5],
    _normal: [u8; 4],
    _u32val: u32,
) {}
"#;

#[test]
fn test_is_zst_type_unit() {
    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_probe");
        let body = instance.body().expect("function body");
        // _unit is Local 2 (after return place + marker arg)
        let unit_ty = body.locals()[2].ty;
        assert!(StatementCodegen::is_zst_type(unit_ty), "() should be ZST");
    });
}

#[test]
fn test_is_zst_type_fieldless_struct() {
    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_probe");
        let body = instance.body().expect("function body");
        // _marker is Local 1
        let marker_ty = body.locals()[1].ty;
        assert!(StatementCodegen::is_zst_type(marker_ty), "fieldless struct Marker should be ZST");
    });
}

#[test]
fn test_is_zst_type_zero_length_array() {
    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_probe");
        let body = instance.body().expect("function body");
        // _arr0 is Local 3: [u8; 0]
        let arr0_ty = body.locals()[3].ty;
        assert!(StatementCodegen::is_zst_type(arr0_ty), "[u8; 0] should be ZST");
    });
}

#[test]
fn test_is_zst_type_array_of_unit() {
    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_probe");
        let body = instance.body().expect("function body");
        // _arr_unit is Local 4: [(); 5]
        let arr_unit_ty = body.locals()[4].ty;
        assert!(
            StatementCodegen::is_zst_type(arr_unit_ty),
            "[(); 5] should be ZST (array of ZST elements)"
        );
    });
}

#[test]
fn test_is_zst_type_normal_array_is_not_zst() {
    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_probe");
        let body = instance.body().expect("function body");
        // _normal is Local 5: [u8; 4]
        let normal_ty = body.locals()[5].ty;
        assert!(!StatementCodegen::is_zst_type(normal_ty), "[u8; 4] should NOT be ZST");
    });
}

#[test]
fn test_is_zst_type_u32_is_not_zst() {
    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_probe");
        let body = instance.body().expect("function body");
        // _u32val is Local 6: u32
        let u32_ty = body.locals()[6].ty;
        assert!(!StatementCodegen::is_zst_type(u32_ty), "u32 should NOT be ZST");
    });
}

// ─── Coercion edge cases specific to comparison paths ───────────────

#[test]
fn test_coerce_widths_int_bitvec_mixed_converts_to_int() {
    let int_val = Expr::int_const(100);
    let bv_val = Expr::bitvec_const(50u128, 32);

    // When one is Int and the other is BitVec, coerce_to_match_widths_typed
    // should convert the BitVec to Int via bv2int
    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(int_val, bv_val, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    assert!(matches!(r.value(), ExprValue::Bv2Int(..)));
}

#[test]
fn test_partial_eq_different_width_bitvecs_coerce() {
    // When comparing bitvecs of different widths, the narrower is coerced.
    let narrow = Expr::bitvec_const(42u128, 8);
    let wide = Expr::bitvec_const(42u128, 16);

    let (l, r) = StatementCodegen::coerce_to_match_widths_typed(
        narrow, wide, false, // unsigned
    );

    // Both should have the same width after coercion
    assert_eq!(l.sort().bitvec_width(), r.sort().bitvec_width());
    // The wider width wins
    assert_eq!(l.sort().bitvec_width(), Some(16));
}

#[test]
fn test_partial_eq_signed_coercion_uses_sign_extend() {
    let narrow = Expr::bitvec_const(0xFEu128, 8); // -2 as i8
    let wide = Expr::bitvec_const(0xFFFEu128, 16); // -2 as i16

    let (l, _r) = StatementCodegen::coerce_to_match_widths_typed(
        narrow, wide, true, // signed
    );

    // Narrow should be sign-extended to 16 bits
    assert_eq!(l.sort().bitvec_width(), Some(16));
    assert!(matches!(l.value(), ExprValue::BvSignExtend { .. }));
}

// ─── is_zst_type standalone checks ──────────────────────────────────

#[test]
fn test_is_zst_type_never_type_via_mir() {
    // The Never type (!) is classified as ZST.
    // We test this through MIR since the type system is needed.
    const NEVER_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn never_probe() -> ! { loop {} }
    "#;

    with_test_ay_ctx_for_source(NEVER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "never_probe");
        let body = instance.body().expect("body");

        // Return type (local 0) should be ! (Never)
        let ret_ty = body.locals()[0].ty;
        let is_zst = StatementCodegen::is_zst_type(ret_ty);
        assert!(is_zst, "Never type should be ZST");
    });
}

// ─── MIR-driven comparison codegen entrypoints ──────────────────────

// These tests avoid relying on rustc preserving trait-call terminators in MIR.
// Instead, they initialize StatementCodegen from real MIR bodies (for local/ref types)
// and invoke comparison entrypoint methods directly with MIR operands.

const COMPARISON_ENTRYPOINT_SOURCE: &str = r#"
pub fn eq_probe(a: &u32, b: &u32) -> bool {
    a == b
}

pub fn ne_probe(a: &u32, b: &u32) -> bool {
    a != b
}

pub fn ord_cmp_probe(a: &u32, b: &u32) -> core::cmp::Ordering {
    a.cmp(b)
}

pub fn partial_ord_lt_probe(a: &i32, b: &i32) -> bool {
    a < b
}

pub fn partial_ord_le_probe(a: &u32, b: &u32) -> bool {
    a <= b
}

pub fn partial_ord_gt_probe(a: &i32, b: &i32) -> bool {
    a > b
}

pub fn partial_ord_ge_probe(a: &u32, b: &u32) -> bool {
    a >= b
}

pub fn clone_probe(a: &u32) -> u32 {
    *a
}

pub fn raw_eq_probe(a: &u32, b: &u32) -> bool {
    a == b
}
"#;

const COMPARISON_SORT_GUARD_SOURCE: &str = r#"
pub fn scalar_mismatch_probe(_a: u32, _b: bool) -> bool {
    true
}

pub fn bool_partial_ord_probe(_a: bool, _b: bool) -> bool {
    true
}
"#;

fn ref_local_operand(local_idx: usize) -> Operand {
    Operand::Copy(Place { local: Local::from(local_idx), projection: vec![] })
}

fn return_place() -> Place {
    Place { local: Local::from(0usize), projection: vec![] }
}

#[test]
fn test_mir_codegen_partial_eq_assigns_bool_destination() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "eq_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(11);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_eq(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "codegen_partial_eq should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "partial_eq destination should be bool");

        // Semantic: verify the computed value uses Eq (SMT equality)
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_eq dest");
        assert!(
            matches!(rhs.value(), ExprValue::Eq(..)),
            "partial_eq should produce Eq expression, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_codegen_partial_ne_assigns_bool_destination() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ne_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(12);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_ne(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "codegen_partial_ne should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "partial_ne destination should be bool");

        // Semantic: ne produces Not(Eq(..)) or Distinct(..)
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_ne dest");
        // ne() is lhs.ne(rhs) which is typically lhs.eq(rhs).not() = Not(Eq(..))
        let is_negated_eq = matches!(rhs.value(), ExprValue::Not(..))
            || matches!(rhs.value(), ExprValue::Distinct(..));
        assert!(
            is_negated_eq,
            "partial_ne should produce Not(Eq(..)) or Distinct(..), got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_codegen_ord_cmp_assigns_ordering_bitvec() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ord_cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(13);
        let before = codegen.ctx.program.commands().len();

        let result =
            codegen.codegen_ord_cmp(&[ref_local_operand(1), ref_local_operand(2)], &dest, target);

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "codegen_ord_cmp should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "ord_cmp destination should be Ordering discriminant bv32"
        );

        // Semantic: verify the ITE(lt, 0xFFFFFFFF, ITE(eq, 0x00, 0x01)) encoding
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for ord_cmp dest");
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "ord_cmp should produce outer ITE encoding, got {:?}",
            rhs.value()
        );
        // The outer ITE's then-branch should be the Less discriminant (0xFFFFFFFF as bv32)
        if let ExprValue::Ite { then_expr, else_expr, .. } = rhs.value() {
            assert_eq!(
                then_expr.sort().bitvec_width(),
                Some(32),
                "ITE then-branch (Less) should be bv32"
            );
            // Inner else-branch should also be an ITE for Equal/Greater
            assert!(
                matches!(else_expr.value(), ExprValue::Ite { .. }),
                "ord_cmp should have nested ITE for Equal/Greater, got {:?}",
                else_expr.value()
            );
        }
    });
}

#[test]
fn test_mir_codegen_partial_ord_lt_assigns_bool_destination() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "partial_ord_lt_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(14);
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
            "codegen_partial_ord_cmp should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "partial_ord destination should be bool");

        // Semantic: lt on i32 (signed) should produce BvSLt somewhere in the expression tree
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_ord lt dest");
        // The RHS should contain a signed comparison (BvSLt) since the probe uses &i32
        let has_signed_lt = expr_contains(&rhs, &|v| matches!(v, ExprValue::BvSLt(..)));
        assert!(
            has_signed_lt,
            "partial_ord lt on i32 should use BvSLt (signed), got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_codegen_raw_eq_assigns_bool_destination() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_eq_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(15);
        let before = codegen.ctx.program.commands().len();

        let result =
            codegen.codegen_raw_eq(&[ref_local_operand(1), ref_local_operand(2)], &dest, target);

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "codegen_raw_eq should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "raw_eq destination should be bool");

        // Semantic: raw_eq on u32 should produce Eq expression (SMT equality)
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for raw_eq dest");
        // raw_eq on non-ZST bitvecs uses eq after width coercion
        let has_eq = expr_contains(&rhs, &|v| matches!(v, ExprValue::Eq(..)));
        // May also be a Var (symbolic) if deref fails — but for u32 refs it should be Eq
        assert!(
            has_eq,
            "raw_eq on u32 references should produce Eq expression, got {:?}",
            rhs.value()
        );
    });
}

// ─── MIR-driven PartialOrd le/gt/ge (previously only "lt" was tested) ───

#[test]
fn test_mir_codegen_partial_ord_le_assigns_bool_destination() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "partial_ord_le_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(16);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_ord_cmp(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
            "le",
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "codegen_partial_ord_cmp(le) should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "partial_ord le destination should be bool");

        // Semantic: le on u32 (unsigned) should produce BvULe
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_ord le dest");
        let has_unsigned_le = expr_contains(&rhs, &|v| matches!(v, ExprValue::BvULe(..)));
        assert!(
            has_unsigned_le,
            "partial_ord le on u32 should use BvULe (unsigned), got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_codegen_partial_ord_gt_signed_assigns_bool_destination() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "partial_ord_gt_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(17);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_ord_cmp(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
            "gt",
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "codegen_partial_ord_cmp(gt) should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "partial_ord gt destination should be bool");

        // Semantic: gt on i32 (signed) should produce BvSGt
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_ord gt dest");
        let has_signed_gt = expr_contains(&rhs, &|v| matches!(v, ExprValue::BvSGt(..)));
        assert!(
            has_signed_gt,
            "partial_ord gt on i32 should use BvSGt (signed), got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_codegen_partial_ord_ge_assigns_bool_destination() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "partial_ord_ge_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(18);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_ord_cmp(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
            "ge",
        );

        assert_eq!(result, target);
        assert!(
            codegen.ctx.program.commands().len() > before,
            "codegen_partial_ord_cmp(ge) should emit SSA constraint"
        );

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "partial_ord ge destination should be bool");

        // Semantic: ge on u32 (unsigned) should produce BvUGe
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for partial_ord ge dest");
        let has_unsigned_ge = expr_contains(&rhs, &|v| matches!(v, ExprValue::BvUGe(..)));
        assert!(
            has_unsigned_ge,
            "partial_ord ge on u32 should use BvUGe (unsigned), got {:?}",
            rhs.value()
        );
    });
}

// ─── MIR-driven primitive clone ─────────────────────────────────────

#[test]
fn test_mir_codegen_primitive_clone_assigns_same_sort() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "clone_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(19);

        // clone takes &self, so arg is the reference parameter (local 1)
        let result = codegen.codegen_primitive_clone(&[ref_local_operand(1)], &dest, target);

        assert_eq!(result, target);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        // Clone of u32 should produce 32-bit bitvec (same as the source type)
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "primitive_clone of u32 should produce bv32"
        );
    });
}

// ─── MIR-driven ZST comparison through codegen entrypoints ─────────

const ZST_COMPARISON_SOURCE: &str = r#"
pub fn zst_eq_probe(a: &(), b: &()) -> bool {
    a == b
}

pub fn zst_ne_probe(a: &(), b: &()) -> bool {
    a != b
}
"#;

#[test]
fn test_mir_codegen_partial_eq_zst_returns_true() {
    with_test_ay_ctx_for_source(ZST_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_eq_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(20);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_eq(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
        );

        assert_eq!(result, target, "ZST eq should return target (not None)");

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "ZST eq destination should be bool");

        // Semantic: ZST eq should produce BoolConst(true) — not just any bool
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for ZST eq dest");
        assert!(
            matches!(rhs.value(), ExprValue::BoolConst(true)),
            "ZST eq should produce constant true, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_mir_codegen_partial_ne_zst_returns_false() {
    with_test_ay_ctx_for_source(ZST_COMPARISON_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "zst_ne_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(21);
        let before = codegen.ctx.program.commands().len();

        let result = codegen.codegen_partial_ne(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            target,
        );

        assert_eq!(result, target, "ZST ne should return target (not None)");

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool(), "ZST ne destination should be bool");

        // Semantic: ZST ne should produce BoolConst(false) — not just any bool
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr)
            .expect("should find SSA-defining assertion for ZST ne dest");
        assert!(
            matches!(rhs.value(), ExprValue::BoolConst(false)),
            "ZST ne should produce constant false, got {:?}",
            rhs.value()
        );
    });
}

// ─── MIR-driven partial_ord unknown op returns None ─────────────────

#[test]
fn test_mir_codegen_partial_ord_unknown_op_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "partial_ord_le_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();

        // Pass an invalid op string — should return None
        let result = codegen.codegen_partial_ord_cmp(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            Some(22),
            "invalid_op",
        );

        assert_eq!(result, None, "unknown op should return None");
    });
}

#[test]
fn test_codegen_partial_eq_nonref_mismatch_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_SORT_GUARD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "scalar_mismatch_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result = codegen.codegen_partial_eq(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            Some(23),
        );

        // u32 vs bool should fail the non-bitvec/non-int mismatch guard.
        assert_eq!(result, None, "partial_eq should reject u32 vs bool sort mismatch");
    });
}

#[test]
fn test_codegen_partial_ne_nonref_mismatch_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_SORT_GUARD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "scalar_mismatch_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result = codegen.codegen_partial_ne(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            Some(24),
        );

        // u32 vs bool should fail the non-bitvec/non-int mismatch guard.
        assert_eq!(result, None, "partial_ne should reject u32 vs bool sort mismatch");
    });
}

#[test]
fn test_codegen_partial_ord_cmp_bool_sorts_return_none() {
    with_test_ay_ctx_for_source(COMPARISON_SORT_GUARD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_partial_ord_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result = codegen.codegen_partial_ord_cmp(
            &[ref_local_operand(1), ref_local_operand(2)],
            &dest,
            Some(25),
            "lt",
        );

        // Bool+Bool is neither bitvec nor int; comparison helper should reject it.
        assert_eq!(result, None, "partial_ord_cmp should reject non-bitvec/int sort pairs");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Insufficient args guard tests (defensive paths)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_codegen_partial_eq_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "eq_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        // Pass only 1 arg instead of 2
        let result = codegen.codegen_partial_eq(&[ref_local_operand(1)], &dest, Some(10));
        assert_eq!(result, None, "partial_eq with <2 args should return None");
    });
}

#[test]
fn test_codegen_partial_ne_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ne_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result = codegen.codegen_partial_ne(&[ref_local_operand(1)], &dest, Some(10));
        assert_eq!(result, None, "partial_ne with <2 args should return None");
    });
}

#[test]
fn test_codegen_ord_cmp_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ord_cmp_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result = codegen.codegen_ord_cmp(&[ref_local_operand(1)], &dest, Some(10));
        assert_eq!(result, None, "ord_cmp with <2 args should return None");
    });
}

#[test]
fn test_codegen_partial_ord_cmp_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "partial_ord_lt_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result =
            codegen.codegen_partial_ord_cmp(&[ref_local_operand(1)], &dest, Some(10), "lt");
        assert_eq!(result, None, "partial_ord_cmp with <2 args should return None");
    });
}

#[test]
fn test_codegen_raw_eq_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_eq_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result = codegen.codegen_raw_eq(&[ref_local_operand(1)], &dest, Some(10));
        assert_eq!(result, None, "raw_eq with <2 args should return None");
    });
}

#[test]
fn test_codegen_primitive_clone_empty_args_returns_none() {
    with_test_ay_ctx_for_source(COMPARISON_ENTRYPOINT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "clone_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let result = codegen.codegen_primitive_clone(&[], &dest, Some(10));
        assert_eq!(result, None, "primitive_clone with 0 args should return None");
    });
}

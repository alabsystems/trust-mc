// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-backed tests for `rvalue_discriminant.rs` strategy resolution.
//!
//! These tests exercise strategy-specific behavior for `Rvalue::Discriminant`
//! and assert expression semantics (shape/value), not just that codegen returns
//! a value.

use super::*;

const CHECKED_ARITH_SOURCE: &str = r#"
pub fn checked_add_discriminant(x: u8, y: u8) -> u8 {
    let checked = x.checked_add(y);
    match checked {
        Some(_) => 1,
        None => 0,
    }
}
"#;

const BITVEC_DISCRIMINANT_SOURCE: &str = r#"
use core::ops::ControlFlow;

pub fn controlflow_discriminant(x: ControlFlow<u8, u8>) -> u8 {
    match x {
        ControlFlow::Continue(_) => 0,
        ControlFlow::Break(_) => 1,
    }
}

pub fn result_discriminant(x: Result<u8, u8>) -> u8 {
    match x {
        Ok(_) => 0,
        Err(_) => 1,
    }
}

pub fn option_discriminant(x: Option<u8>) -> u8 {
    match x {
        Some(_) => 1,
        None => 0,
    }
}

pub enum Color {
    Red,
    Green,
    Blue,
}

pub fn color_discriminant(c: Color) -> u8 {
    c as u8
}
"#;

const DATATYPE_DISCRIMINANT_SOURCE: &str = r#"
pub enum Probe {
    A,
    B,
    C,
}

pub fn probe_discriminant(p: Probe) -> u8 {
    match p {
        Probe::A => 0,
        Probe::B => 1,
        Probe::C => 2,
    }
}
"#;

const ALLOC_RESULT_SOURCE: &str = r#"
pub enum AllocError {
    Oom,
}

pub fn alloc_result_discriminant(r: Result<u8, AllocError>) -> u8 {
    match r {
        Ok(_) => 0,
        Err(_) => 1,
    }
}
"#;

const SINGLE_VARIANT_SOURCE: &str = r#"
pub enum Single {
    Only = 42,
}

pub fn single_variant_discriminant(x: Single) -> u32 {
    x as u32
}
"#;

const SYMBOLIC_FALLBACK_SOURCE: &str = r#"
pub enum Pair {
    A(u8),
    B(u8),
}

pub fn pair_discriminant(p: Pair) -> u8 {
    match p {
        Pair::A(_) => 0,
        Pair::B(_) => 1,
    }
}
"#;

const NON_ENUM_DISCRIMINANT_SOURCE: &str = r#"
#![allow(internal_features)]
#![feature(core_intrinsics)]

use std::intrinsics::discriminant_value;

pub enum MyError {
    Error1(i32),
    Error2(&'static str),
    Error3 { description: String, code: u32 },
}

pub fn non_enum_value_discriminant() -> u8 {
    discriminant_value(&2)
}

pub fn non_enum_ctor_discriminant() -> u8 {
    discriminant_value(&MyError::Error1)
}
"#;

fn find_discriminant_place(body: &rustc_public::mir::Body) -> Place {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                continue;
            };
            let Rvalue::Discriminant(place) = rvalue else {
                continue;
            };
            return place.clone();
        }
    }
    panic!("missing Rvalue::Discriminant in body");
}

fn assert_bitvec_const(expr: &Expr, expected: u128, width: u32) {
    match expr.value() {
        ExprValue::BitVecConst { value, width: actual_width } => {
            assert_eq!(*actual_width, width, "bitvec width mismatch");
            assert_eq!(
                value,
                &BigInt::from(expected),
                "bitvec constant mismatch: expected {expected}, got {value}"
            );
        }
        other => panic!("expected BitVecConst({expected}, {width}), got {other:?}"),
    }
}

fn expr_contains_datatype_tester(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::DatatypeTester { .. } => true,
        ExprValue::Ite { cond, then_expr, else_expr } => {
            expr_contains_datatype_tester(cond)
                || expr_contains_datatype_tester(then_expr)
                || expr_contains_datatype_tester(else_expr)
        }
        ExprValue::Not(inner) => expr_contains_datatype_tester(inner),
        ExprValue::And(args) | ExprValue::Or(args) | ExprValue::Distinct(args) => {
            args.iter().any(expr_contains_datatype_tester)
        }
        ExprValue::Eq(lhs, rhs) => {
            expr_contains_datatype_tester(lhs) || expr_contains_datatype_tester(rhs)
        }
        _ => false,
    }
}

fn expr_contains_bitvec_const(expr: &Expr, expected: u128, width: u32) -> bool {
    match expr.value() {
        ExprValue::BitVecConst { value, width: actual_width } => {
            *actual_width == width && *value == BigInt::from(expected)
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            expr_contains_bitvec_const(cond, expected, width)
                || expr_contains_bitvec_const(then_expr, expected, width)
                || expr_contains_bitvec_const(else_expr, expected, width)
        }
        ExprValue::Not(inner) => expr_contains_bitvec_const(inner, expected, width),
        ExprValue::And(args) | ExprValue::Or(args) | ExprValue::Distinct(args) => {
            args.iter().any(|arg| expr_contains_bitvec_const(arg, expected, width))
        }
        ExprValue::Eq(lhs, rhs) => {
            expr_contains_bitvec_const(lhs, expected, width)
                || expr_contains_bitvec_const(rhs, expected, width)
        }
        _ => false,
    }
}

#[test]
fn test_checked_arith_discriminant_from_overflow_field() {
    with_test_ay_ctx_for_source(CHECKED_ARITH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_add_discriminant");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = find_discriminant_place(&body);
        let base = codegen.ssa_base_name(&place);
        codegen.env_update(format!("{base}_field_1"), Expr::var("overflow_flag", Sort::bool()));

        let discr_expr = codegen
            .codegen_rvalue(&Rvalue::Discriminant(place))
            .expect("checked arithmetic discriminant expression");

        match discr_expr.value() {
            ExprValue::Ite { cond, then_expr, else_expr } => {
                match cond.value() {
                    ExprValue::Var { name } => assert_eq!(name, "overflow_flag"),
                    other => panic!("expected overflow var condition, got {other:?}"),
                }
                assert_bitvec_const(then_expr, 0, 32);
                assert_bitvec_const(else_expr, 1, 32);
            }
            other => panic!("expected ITE from overflow-bit fallback, got {other:?}"),
        }
    });
}

#[test]
fn test_bitvec_discriminant_controlflow_result_option_paths() {
    with_test_ay_ctx_for_source(BITVEC_DISCRIMINANT_SOURCE, |mut ctx| {
        // Post-#2462: bitvec-stored ControlFlow/Result/Option return symbolic
        // discriminant variables (not hardcoded constants). The solver explores
        // both variant paths.
        for fn_suffix in ["controlflow_discriminant", "result_discriminant", "option_discriminant"]
        {
            let instance = find_instance_by_suffix(&ctx, fn_suffix);
            let body = instance.body().expect("function body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            let place = local_place(1);
            let base = codegen.ssa_base_name(&place);
            codegen.env_update(
                base,
                Expr::var(format!("{fn_suffix}_encoded"), Sort::bitvec(POINTER_WIDTH)),
            );

            let discr_expr = codegen
                .codegen_rvalue(&Rvalue::Discriminant(place))
                .expect("bitvec discriminant should return symbolic var");
            match discr_expr.value() {
                ExprValue::Var { name } => {
                    assert!(
                        name.contains("bitvec_discr"),
                        "symbolic discriminant name should contain 'bitvec_discr', got {name}"
                    );
                }
                other => {
                    panic!("expected symbolic discriminant var for {fn_suffix}, got {other:?}")
                }
            }
            assert_eq!(
                discr_expr.sort().bitvec_width(),
                Some(POINTER_WIDTH),
                "symbolic discriminant width for {fn_suffix}"
            );
        }

        // Unit enum stored as bitvec should return the encoded bitvec value.
        let instance = find_instance_by_suffix(&ctx, "color_discriminant");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let place = local_place(1);
        let base = codegen.ssa_base_name(&place);
        codegen.env_update(base, Expr::bitvec_const(2, 32));
        let discr_expr = codegen
            .codegen_rvalue(&Rvalue::Discriminant(place))
            .expect("unit enum bitvec discriminant");
        assert_bitvec_const(&discr_expr, 2, 32);
    });
}

#[test]
fn test_datatype_discriminant_tester_paths_two_and_multi_variant() {
    with_test_ay_ctx_for_source(DATATYPE_DISCRIMINANT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_discriminant");
        let body = instance.body().expect("function body");
        let place = local_place(1);

        // Two-variant datatype path: None-like constructor tester -> ITE(None=0, Some=1).
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let base = codegen.ssa_base_name(&place);
        let two_variant_sort =
            enum_sort("OptionLike", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(8))])]);
        codegen.env_update(base, Expr::var("option_like", two_variant_sort));
        let two_variant_expr = codegen
            .codegen_rvalue(&Rvalue::Discriminant(place.clone()))
            .expect("two-variant datatype discriminant");
        match two_variant_expr.value() {
            ExprValue::Ite { cond, then_expr, else_expr } => {
                assert!(
                    expr_contains_datatype_tester(cond),
                    "two-variant path should use is-constructor tester"
                );
                assert_bitvec_const(then_expr, 0, 32);
                assert_bitvec_const(else_expr, 1, 32);
            }
            other => panic!("expected ITE from two-variant datatype path, got {other:?}"),
        }

        // Multi-variant datatype path: build_discriminant_ite_chain with tester conditions.
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let base = codegen.ssa_base_name(&place);
        let multi_variant_sort =
            enum_sort("Tri", [("A", Vec::<(&str, Sort)>::new()), ("B", vec![]), ("C", vec![])]);
        codegen.env_update(base, Expr::var("tri_enum", multi_variant_sort));
        let multi_variant_expr = codegen
            .codegen_rvalue(&Rvalue::Discriminant(place))
            .expect("multi-variant datatype discriminant");
        assert!(
            matches!(multi_variant_expr.value(), ExprValue::Ite { .. }),
            "multi-variant path should produce ITE chain, got {:?}",
            multi_variant_expr.value()
        );
        assert!(
            expr_contains_datatype_tester(&multi_variant_expr),
            "multi-variant path should contain datatype testers"
        );
        for expected in [0u128, 1u128, 2u128] {
            assert!(
                expr_contains_bitvec_const(&multi_variant_expr, expected, 32),
                "multi-variant path should encode discriminant constant {expected}"
            );
        }
    });
}

#[test]
fn test_alloc_result_forces_ok_discriminant_zero() {
    with_test_ay_ctx_for_source(ALLOC_RESULT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_result_discriminant");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = local_place(1);
        let base = codegen.ssa_base_name(&place);
        let alloc_error_sort =
            enum_sort("AllocError", [("AllocError", Vec::<(&str, Sort)>::new())]);
        let alloc_result_sort = enum_sort(
            "Result_AllocError",
            [("Ok", vec![("value", Sort::bitvec(8))]), ("Err", vec![("error", alloc_error_sort)])],
        );
        codegen.env_update(base, Expr::var("alloc_result", alloc_result_sort));

        let discr_expr = codegen
            .codegen_rvalue(&Rvalue::Discriminant(place))
            .expect("alloc Result discriminant");
        assert_bitvec_const(&discr_expr, 0, POINTER_WIDTH);
    });
}

#[test]
fn test_unit_enum_single_variant_uses_declared_discriminant() {
    with_test_ay_ctx_for_source(SINGLE_VARIANT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "single_variant_discriminant");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = local_place(1);
        let discr_expr = codegen
            .codegen_rvalue(&Rvalue::Discriminant(place))
            .expect("single-variant unit enum discriminant");
        assert_bitvec_const(&discr_expr, 42, 32);
    });
}

#[test]
fn test_discriminant_symbolic_fallback_declares_var_when_unresolved() {
    with_test_ay_ctx_for_source(SYMBOLIC_FALLBACK_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "pair_discriminant");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = local_place(1);
        let expected_name = format!("{}_discriminant", codegen.ssa_name(&place, false));
        let discr_expr = codegen
            .codegen_rvalue(&Rvalue::Discriminant(place))
            .expect("symbolic discriminant fallback");

        match discr_expr.value() {
            ExprValue::Var { name } => assert_eq!(name, &expected_name),
            other => panic!("expected symbolic discriminant var, got {other:?}"),
        }
        assert!(
            discr_expr.sort().is_bitvec(),
            "symbolic fallback discriminant should be bitvec, got {:?}",
            discr_expr.sort()
        );
        assert_eq!(
            discr_expr.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "symbolic fallback discriminant width"
        );
    });
}

#[test]
fn test_non_enum_discriminant_returns_zero() {
    with_test_ay_ctx_for_source(NON_ENUM_DISCRIMINANT_SOURCE, |mut ctx| {
        for fn_suffix in ["non_enum_value_discriminant", "non_enum_ctor_discriminant"] {
            let instance = find_instance_by_suffix(&ctx, fn_suffix);
            let body = instance.body().expect("function body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let place = find_discriminant_place(&body);
            let ty = place.ty(body.locals()).expect("discriminant place type");
            assert!(
                !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(_, _))),
                "{fn_suffix} should lower through a non-enum referent, got {:?}",
                ty
            );

            let discr_expr = codegen
                .codegen_rvalue(&Rvalue::Discriminant(place))
                .expect("non-enum discriminant expression");
            assert_bitvec_const(&discr_expr, 0, POINTER_WIDTH);
        }
    });
}

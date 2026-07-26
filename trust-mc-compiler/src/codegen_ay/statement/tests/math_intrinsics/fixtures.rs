// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared probe source and helper functions for math intrinsic tests.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

pub(crate) const MATH_PROBE_SOURCE: &str = r#"
pub fn math_f32_probe(x: f32) -> f32 { x }
pub fn math_f64_probe(x: f64) -> f64 { x }
pub fn math_f32_binary_probe(x: f32, _y: f32) -> f32 { x }
pub fn math_f64_binary_probe(x: f64, _y: f64) -> f64 { x }
pub fn math_f32_ternary_probe(x: f32, _y: f32, _z: f32) -> f32 { x }
pub fn math_f64_ternary_probe(x: f64, _y: f64, _z: f64) -> f64 { x }
"#;

pub(crate) fn seed_math_local(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    local_idx: usize,
    value: Expr,
) -> Operand {
    let fn_name =
        codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
    let base_name = format!("{}::local_{}", fn_name, local_idx);
    codegen.env_update(base_name, value);
    Operand::Copy(Place { local: local_idx, projection: vec![] })
}

pub(crate) fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

pub(crate) fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

pub(crate) fn latest_assignment_rhs(codegen: &StatementCodegen<'_, '_, '_>) -> Expr {
    let constraint = codegen
        .ctx
        .bmc_vc
        .constraints
        .last()
        .expect("expected assignment constraint after dispatch");
    match constraint.value() {
        ExprValue::Eq(_, rhs) => rhs.clone(),
        other => panic!("expected assignment equality constraint, got {other:?}"),
    }
}

pub(crate) fn assert_fp_to_ieee_bv_assignment(rhs: &Expr, expected_op: rustc_public::mir::BinOp) {
    let inner = match rhs.value() {
        ExprValue::FpToIeeeBv(inner) => inner,
        other => panic!("expected fp.to_ieee_bv assignment, got {other:?}"),
    };
    assert!(
        match expected_op {
            rustc_public::mir::BinOp::Add => matches!(inner.value(), ExprValue::FpAdd(_, _, _)),
            rustc_public::mir::BinOp::Sub => matches!(inner.value(), ExprValue::FpSub(_, _, _)),
            rustc_public::mir::BinOp::Mul => matches!(inner.value(), ExprValue::FpMul(_, _, _)),
            rustc_public::mir::BinOp::Div => matches!(inner.value(), ExprValue::FpDiv(_, _, _)),
            other => panic!("unsupported fast-math op in test helper: {other:?}"),
        },
        "expected fp.to_ieee_bv-wrapped {expected_op:?}, got {:?}",
        rhs.value()
    );
}

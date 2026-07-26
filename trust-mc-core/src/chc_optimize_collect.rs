// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Variable name collection from AY expression trees.
//!
//! Used by the dead-argument elimination pass (`chc_optimize`) to determine
//! which variables appear in real constraints (anchored) versus transfer edges.
//!
//! ## Soundness
//!
//! Every `ExprValue` variant that contains sub-expressions MUST be handled
//! explicitly. The final catch-all `_ => {}` exists only because `ExprValue`
//! is `#[non_exhaustive]`. If a new variant with sub-expressions falls through,
//! variables are silently dropped, potentially causing false dead-arg
//! classification and vacuous proofs.
//!
//! **Audit this file on every AY dependency bump.**

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue};

/// Recursively collects all `Var` names in an expression tree.
///
/// Dispatches to category-specific helpers to stay within function size limits.
pub(super) fn collect_var_names(expr: &Expr, out: &mut HashSet<String>) {
    match expr.value() {
        // Leaf nodes
        ExprValue::Var { name } => {
            out.insert(name.clone());
        }
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_) => {}

        // Unary operations
        ExprValue::Not(e)
        | ExprValue::BvNeg(e)
        | ExprValue::BvNot(e)
        | ExprValue::IntNeg(e)
        | ExprValue::RealNeg(e)
        | ExprValue::BvNegNoOverflow(e)
        | ExprValue::IntToReal(e)
        | ExprValue::RealToInt(e)
        | ExprValue::IsInt(e)
        | ExprValue::Bv2Int(e) => collect_var_names(e, out),

        ExprValue::Int2Bv(e, _)
        | ExprValue::BvZeroExtend { expr: e, .. }
        | ExprValue::BvSignExtend { expr: e, .. }
        | ExprValue::BvExtract { expr: e, .. }
        | ExprValue::ConstArray { value: e, .. } => collect_var_names(e, out),

        // Binary and compound operations
        _ => collect_var_names_compound(expr, out),
    }
}

/// Handles binary bitvector and overflow-detection expression variants.
fn collect_var_names_bv_binary(expr: &Expr, out: &mut HashSet<String>) -> bool {
    match expr.value() {
        ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvMul(a, b)
        | ExprValue::BvUDiv(a, b)
        | ExprValue::BvSDiv(a, b)
        | ExprValue::BvURem(a, b)
        | ExprValue::BvSRem(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvXor(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvULt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::BvConcat(a, b)
        | ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvAddNoOverflowSigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b)
        | ExprValue::BvSubNoOverflowSigned(a, b)
        | ExprValue::BvMulNoOverflowUnsigned(a, b)
        | ExprValue::BvMulNoOverflowSigned(a, b)
        | ExprValue::BvSdivNoOverflow(a, b) => {
            collect_var_names(a, out);
            collect_var_names(b, out);
            true
        }
        _ => false,
    }
}

/// Handles binary, n-ary, and structured expression variants.
fn collect_var_names_compound(expr: &Expr, out: &mut HashSet<String>) {
    // Try BV binary first.
    if collect_var_names_bv_binary(expr, out) {
        return;
    }

    match expr.value() {
        // Binary operations (integer, real, logic, equality)
        ExprValue::IntAdd(a, b)
        | ExprValue::IntSub(a, b)
        | ExprValue::IntMul(a, b)
        | ExprValue::IntDiv(a, b)
        | ExprValue::IntMod(a, b)
        | ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b)
        | ExprValue::RealAdd(a, b)
        | ExprValue::RealSub(a, b)
        | ExprValue::RealMul(a, b)
        | ExprValue::RealDiv(a, b)
        | ExprValue::RealLt(a, b)
        | ExprValue::RealLe(a, b)
        | ExprValue::RealGt(a, b)
        | ExprValue::RealGe(a, b)
        | ExprValue::Xor(a, b)
        | ExprValue::Implies(a, b)
        | ExprValue::Eq(a, b) => {
            collect_var_names(a, out);
            collect_var_names(b, out);
        }

        // N-ary operations
        ExprValue::And(exprs) | ExprValue::Or(exprs) | ExprValue::Distinct(exprs) => {
            for e in exprs {
                collect_var_names(e, out);
            }
        }

        // Structured expressions
        ExprValue::Ite { cond, then_expr, else_expr } => {
            collect_var_names(cond, out);
            collect_var_names(then_expr, out);
            collect_var_names(else_expr, out);
        }
        ExprValue::Select { array, index } => {
            collect_var_names(array, out);
            collect_var_names(index, out);
        }
        ExprValue::Store { array, index, value } => {
            collect_var_names(array, out);
            collect_var_names(index, out);
            collect_var_names(value, out);
        }

        // Datatype, quantifier, FP, and function expressions
        _ => collect_var_names_dt_quant(expr, out),
    }
}

/// Handles datatype, quantifier, and function application variants.
fn collect_var_names_dt_quant(expr: &Expr, out: &mut HashSet<String>) {
    match expr.value() {
        ExprValue::DatatypeConstructor { args, .. } | ExprValue::FuncApp { args, .. } => {
            for e in args {
                collect_var_names(e, out);
            }
        }
        ExprValue::DatatypeSelector { expr: e, .. } | ExprValue::DatatypeTester { expr: e, .. } => {
            collect_var_names(e, out);
        }
        ExprValue::Forall { body, triggers, .. } | ExprValue::Exists { body, triggers, .. } => {
            collect_var_names(body, out);
            for trigger_group in triggers {
                for e in trigger_group {
                    collect_var_names(e, out);
                }
            }
        }
        _ => collect_var_names_fp(expr, out),
    }
}

/// Handles floating-point expression variants.
///
/// Audit date: 2026-03-02. Covers all 27 FP variants from ay_bindings ExprValue.
/// If ay adds new FP variants, the final catch-all `_ => {}` in this function
/// will silently drop variables — review on every AY bump.
fn collect_var_names_fp(expr: &Expr, out: &mut HashSet<String>) {
    match expr.value() {
        // FP constants — no sub-expressions, no variables to collect.
        ExprValue::FpPlusInfinity { .. }
        | ExprValue::FpMinusInfinity { .. }
        | ExprValue::FpNaN { .. }
        | ExprValue::FpPlusZero { .. }
        | ExprValue::FpMinusZero { .. } => {}

        // FP unary operations — one sub-expression.
        ExprValue::FpAbs(e)
        | ExprValue::FpNeg(e)
        | ExprValue::FpIsNaN(e)
        | ExprValue::FpIsInfinite(e)
        | ExprValue::FpIsZero(e)
        | ExprValue::FpIsNormal(e)
        | ExprValue::FpIsSubnormal(e)
        | ExprValue::FpIsPositive(e)
        | ExprValue::FpIsNegative(e)
        | ExprValue::FpToReal(e) => collect_var_names(e, out),

        // FP unary with rounding mode or extra fields.
        ExprValue::FpSqrt(_, e)
        | ExprValue::FpRoundToIntegral(_, e)
        | ExprValue::FpToSbv(_, e, _)
        | ExprValue::FpToUbv(_, e, _) => collect_var_names(e, out),

        // FP binary operations — two sub-expressions.
        ExprValue::FpRem(a, b)
        | ExprValue::FpMin(a, b)
        | ExprValue::FpMax(a, b)
        | ExprValue::FpEq(a, b)
        | ExprValue::FpLt(a, b)
        | ExprValue::FpLe(a, b)
        | ExprValue::FpGt(a, b)
        | ExprValue::FpGe(a, b) => {
            collect_var_names(a, out);
            collect_var_names(b, out);
        }

        // FP binary with rounding mode.
        ExprValue::FpAdd(_, a, b)
        | ExprValue::FpSub(_, a, b)
        | ExprValue::FpMul(_, a, b)
        | ExprValue::FpDiv(_, a, b) => {
            collect_var_names(a, out);
            collect_var_names(b, out);
        }

        // FP ternary with rounding mode (fused multiply-add).
        ExprValue::FpFma(_, a, b, c) => {
            collect_var_names(a, out);
            collect_var_names(b, out);
            collect_var_names(c, out);
        }

        // SOUNDNESS GUARD: All currently known ExprValue variants with
        // sub-expressions are handled above. This catch-all exists because
        // ExprValue is #[non_exhaustive]. If a new variant with sub-expressions
        // is added and falls through here, variables will be silently dropped,
        // potentially causing false dead-arg classification.
        //
        // Mitigation: audit this match on every AY dependency bump.
        // Last audit: 2026-03-02 (113 variants, all covered).
        _ => {}
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Boolean simplification helpers for CHC assertion and assume guards.

use ay_bindings::{Expr, ExprValue};

pub(super) fn simplify_bool_expr(expr: Expr) -> Expr {
    match expr.value().clone() {
        ExprValue::BoolConst(_) | ExprValue::Var { .. } => expr,
        ExprValue::Not(inner) => {
            let inner = simplify_bool_expr(inner);
            match inner.value().clone() {
                ExprValue::BoolConst(value) => Expr::bool_const(!value),
                ExprValue::Not(grandchild) => simplify_bool_expr(grandchild),
                _ => inner.not(),
            }
        }
        ExprValue::Eq(lhs, rhs) => simplify_eq_bool(lhs, rhs),
        ExprValue::Ite { cond, then_expr, else_expr } if then_expr.sort().is_bool() => {
            let cond = simplify_bool_expr(cond);
            let then_expr = simplify_bool_expr(then_expr);
            let else_expr = simplify_bool_expr(else_expr);
            match (then_expr.value(), else_expr.value()) {
                (ExprValue::BoolConst(true), ExprValue::BoolConst(false)) => cond,
                (ExprValue::BoolConst(false), ExprValue::BoolConst(true)) => {
                    simplify_bool_expr(cond.not())
                }
                (ExprValue::BoolConst(t), ExprValue::BoolConst(e)) if t == e => {
                    Expr::bool_const(*t)
                }
                _ if then_expr == else_expr => then_expr,
                _ => Expr::ite(cond, then_expr, else_expr),
            }
        }
        _ => expr,
    }
}

fn simplify_eq_bool(lhs: Expr, rhs: Expr) -> Expr {
    if lhs == rhs {
        return Expr::bool_const(true);
    }

    if let Some(simplified) = simplify_bool_const_eq(&lhs, &rhs) {
        return simplified;
    }
    if let Some(simplified) = simplify_bool_const_eq(&rhs, &lhs) {
        return simplified;
    }
    if let Some(simplified) = simplify_bool_ite_flag_eq(&lhs, &rhs) {
        return simplified;
    }
    if let Some(simplified) = simplify_bool_ite_flag_eq(&rhs, &lhs) {
        return simplified;
    }

    let lhs = if lhs.sort().is_bool() { simplify_bool_expr(lhs) } else { lhs };
    let rhs = if rhs.sort().is_bool() { simplify_bool_expr(rhs) } else { rhs };
    if lhs == rhs { Expr::bool_const(true) } else { lhs.eq(rhs) }
}

fn simplify_bool_const_eq(expr: &Expr, maybe_const: &Expr) -> Option<Expr> {
    if !expr.sort().is_bool() {
        return None;
    }
    match maybe_const.value() {
        ExprValue::BoolConst(true) => Some(simplify_bool_expr(expr.clone())),
        ExprValue::BoolConst(false) => Some(simplify_bool_expr(expr.clone().not())),
        _ => None,
    }
}

fn simplify_bool_ite_flag_eq(ite_expr: &Expr, maybe_const: &Expr) -> Option<Expr> {
    let (const_width, const_value) = bitvec_const_zero_or_one(maybe_const)?;
    let ExprValue::Ite { cond, then_expr, else_expr } = ite_expr.value() else {
        return None;
    };
    let (then_width, then_value) = bitvec_const_zero_or_one(then_expr)?;
    let (else_width, else_value) = bitvec_const_zero_or_one(else_expr)?;
    if const_width != then_width || const_width != else_width || then_value == else_value {
        return None;
    }

    let cond = simplify_bool_expr(cond.clone());
    match (then_value, else_value, const_value) {
        (1, 0, 1) | (0, 1, 0) => Some(cond),
        (1, 0, 0) | (0, 1, 1) => Some(simplify_bool_expr(cond.not())),
        _ => None,
    }
}

fn bitvec_const_zero_or_one(expr: &Expr) -> Option<(u32, u8)> {
    let ExprValue::BitVecConst { value, width } = expr.value() else {
        return None;
    };
    if *value == 0u8.into() {
        Some((*width, 0))
    } else if *value == 1u8.into() {
        Some((*width, 1))
    } else {
        None
    }
}

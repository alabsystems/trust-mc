// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Equality refinements derived from inline `kani::assume` guards.

use std::collections::HashMap;

use ay_bindings::{Expr, ExprValue};

fn bool_const_value(expr: &Expr) -> Option<bool> {
    match expr.value() {
        ExprValue::BoolConst(value) => Some(*value),
        _ => None,
    }
}

pub(super) fn normalize_inline_bool_guard(expr: Expr) -> Expr {
    match expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            match (bool_const_value(&then_expr), bool_const_value(&else_expr)) {
                (Some(true), Some(false)) => cond.clone(),
                (Some(false), Some(true)) => cond.clone().not(),
                _ => expr,
            }
        }
        _ => expr,
    }
}

fn is_inline_refinement_value(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::BoolConst(_) | ExprValue::BitVecConst { .. } | ExprValue::IntConst(_)
    )
}

fn full_width_extract_base(expr: &Expr) -> Option<Expr> {
    let ExprValue::BvExtract { expr: inner, high, low } = expr.value() else {
        return None;
    };
    if *low == 0 && inner.sort().bitvec_width() == Some(*high + 1) {
        Some(inner.clone())
    } else {
        None
    }
}

fn inline_refinement_needle(expr: &Expr) -> Expr {
    full_width_extract_base(expr).unwrap_or_else(|| expr.clone())
}

fn zero_bitvec_const(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::BitVecConst { value, .. } if *value == 0u64.into()
    )
}

fn coerced_zero_refinement(coerced: &Expr, value: &Expr) -> Option<(Expr, Expr)> {
    if !zero_bitvec_const(value) {
        return None;
    }
    let inner = match coerced.value() {
        ExprValue::BvSignExtend { expr, .. } | ExprValue::BvZeroExtend { expr, .. } => expr,
        _ => return None,
    };
    let width = inner.sort().bitvec_width()?;
    Some((inline_refinement_needle(inner), Expr::bitvec_const(0u64, width)))
}

fn inline_assume_equality_refinement(guard: &Expr) -> Option<(Expr, Expr)> {
    let ExprValue::Eq(lhs, rhs) = guard.value() else {
        return None;
    };
    if is_inline_refinement_value(&rhs) {
        coerced_zero_refinement(lhs, rhs)
            .or_else(|| Some((inline_refinement_needle(lhs), rhs.clone())))
    } else if is_inline_refinement_value(&lhs) {
        coerced_zero_refinement(rhs, lhs)
            .or_else(|| Some((inline_refinement_needle(rhs), lhs.clone())))
    } else {
        None
    }
}

fn inline_assume_value_refinement(value: &Expr, guard: &Expr) -> Option<Expr> {
    match guard.value() {
        ExprValue::And(guards) => {
            guards.iter().find_map(|guard| inline_assume_value_refinement(value, guard))
        }
        _ => {
            let (needle, replacement) = inline_assume_equality_refinement(guard)?;
            (needle == *value && replacement.sort() == value.sort()).then_some(replacement)
        }
    }
}

pub(in crate::codegen_ay::chc::call::codegen_call_virtual_inline) fn refine_inline_value_from_assume(
    value: Expr,
    guard: &Expr,
) -> Expr {
    let guard = normalize_inline_bool_guard(guard.clone());
    inline_assume_value_refinement(&value, &guard).unwrap_or(value)
}

pub(super) fn apply_inline_assume_refinement(local_exprs: &mut HashMap<usize, Expr>, guard: &Expr) {
    let Some((needle, replacement)) = inline_assume_equality_refinement(guard) else {
        return;
    };
    for expr in local_exprs.values_mut() {
        if *expr == needle {
            *expr = replacement.clone();
        }
    }
}

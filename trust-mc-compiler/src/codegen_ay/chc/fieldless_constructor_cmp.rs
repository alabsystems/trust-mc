// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Equality folding for datatype values compared with fieldless constructors.

use ay_bindings::{Expr, ExprValue};

pub(in crate::codegen_ay::chc) fn try_fieldless_constructor_comparison(
    lhs: &Expr,
    rhs: &Expr,
    is_eq: bool,
) -> Option<Expr> {
    if let Some((datatype, constructor)) = fieldless_constructor_name(rhs) {
        let same_constructor = constructor_identity_guard(lhs, &datatype, &constructor)?;
        return Some(if is_eq { same_constructor } else { same_constructor.not() });
    }
    if let Some((datatype, constructor)) = fieldless_constructor_name(lhs) {
        let same_constructor = constructor_identity_guard(rhs, &datatype, &constructor)?;
        return Some(if is_eq { same_constructor } else { same_constructor.not() });
    }
    None
}

fn fieldless_constructor_name(expr: &Expr) -> Option<(String, String)> {
    match expr.value() {
        ExprValue::DatatypeConstructor { datatype_name, constructor_name, args }
            if args.is_empty() =>
        {
            Some((datatype_name.clone(), constructor_name.clone()))
        }
        ExprValue::FuncApp { name, args } if args.is_empty() => {
            let dt = expr.sort().datatype_sort()?;
            dt.constructors
                .iter()
                .any(|constructor| constructor.name == *name && constructor.fields.is_empty())
                .then(|| (dt.name.clone(), name.clone()))
        }
        _ => None,
    }
}

fn constructor_identity_guard(expr: &Expr, datatype: &str, constructor: &str) -> Option<Expr> {
    match expr.value() {
        ExprValue::DatatypeConstructor { datatype_name, constructor_name, .. } => {
            (datatype_name == datatype).then(|| Expr::bool_const(constructor_name == constructor))
        }
        ExprValue::FuncApp { name, args } if args.is_empty() => {
            let dt = expr.sort().datatype_sort()?;
            if dt.name != datatype {
                return None;
            }
            dt.constructors
                .iter()
                .any(|candidate| candidate.name == *name)
                .then(|| Expr::bool_const(name == constructor))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_guard = constructor_identity_guard(then_expr, datatype, constructor)?;
            let else_guard = constructor_identity_guard(else_expr, datatype, constructor)?;
            Some(simplify_bool_ite(cond.clone(), then_guard, else_guard))
        }
        _ => None,
    }
}

fn simplify_bool_ite(cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr {
    match (bool_const_value(&then_expr), bool_const_value(&else_expr)) {
        (Some(true), Some(false)) => cond,
        (Some(false), Some(true)) => cond.not(),
        (Some(true), Some(true)) => Expr::bool_const(true),
        (Some(false), Some(false)) => Expr::bool_const(false),
        _ => Expr::ite(cond, then_expr, else_expr),
    }
}

fn bool_const_value(expr: &Expr) -> Option<bool> {
    match expr.value() {
        ExprValue::BoolConst(value) => Some(*value),
        _ => None,
    }
}

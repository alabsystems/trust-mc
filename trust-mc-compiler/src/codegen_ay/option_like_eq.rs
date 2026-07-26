// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Option-like datatype equality lowering shared by BMC and CHC codegen.

use ay_bindings::{Expr, ExprValue, Sort};

#[derive(Clone)]
enum OptionLikeView {
    None,
    Some(Expr),
    Symbolic { is_some: Expr, payload: Expr },
}

pub(in crate::codegen_ay) fn option_like_datatype_eq(
    lhs: &Expr,
    rhs: &Expr,
    is_eq: bool,
) -> Option<Expr> {
    if lhs.sort() != rhs.sort() || !is_option_like_sort(lhs.sort()) {
        return None;
    }
    let lhs = option_like_view(lhs)?;
    let rhs = option_like_view(rhs)?;
    let eq = option_like_view_eq(lhs, rhs);
    Some(if is_eq { eq } else { eq.not() })
}

fn is_option_like_sort(sort: &Sort) -> bool {
    let Some(dt) = sort.datatype_sort() else {
        return false;
    };
    if dt.constructors.len() != 2 {
        return false;
    }
    let mut arities = dt.constructors.iter().map(|ctor| ctor.fields.len()).collect::<Vec<_>>();
    arities.sort_unstable();
    arities == [0, 1]
}

fn option_like_view(expr: &Expr) -> Option<OptionLikeView> {
    match expr.value() {
        ExprValue::DatatypeConstructor { args, .. } if args.is_empty() => {
            Some(OptionLikeView::None)
        }
        ExprValue::DatatypeConstructor { args, .. } if args.len() == 1 => {
            Some(OptionLikeView::Some(args[0].clone()))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_view = option_like_view(then_expr)?;
            let else_view = option_like_view(else_expr)?;
            match (then_view, else_view) {
                (OptionLikeView::Some(payload), OptionLikeView::None) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone(), payload })
                }
                (OptionLikeView::None, OptionLikeView::Some(payload)) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone().not(), payload })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn option_like_view_eq(lhs: OptionLikeView, rhs: OptionLikeView) -> Expr {
    match (lhs, rhs) {
        (OptionLikeView::None, OptionLikeView::None) => Expr::bool_const(true),
        (OptionLikeView::Some(lhs), OptionLikeView::Some(rhs)) => lhs.eq(rhs),
        (OptionLikeView::None, OptionLikeView::Some(_))
        | (OptionLikeView::Some(_), OptionLikeView::None) => Expr::bool_const(false),
        (OptionLikeView::Symbolic { is_some, payload }, OptionLikeView::Some(expected))
        | (OptionLikeView::Some(expected), OptionLikeView::Symbolic { is_some, payload }) => {
            is_some.and(payload.eq(expected))
        }
        (OptionLikeView::Symbolic { is_some, .. }, OptionLikeView::None)
        | (OptionLikeView::None, OptionLikeView::Symbolic { is_some, .. }) => is_some.not(),
        (
            OptionLikeView::Symbolic { is_some: lhs_is_some, payload: lhs_payload },
            OptionLikeView::Symbolic { is_some: rhs_is_some, payload: rhs_payload },
        ) => {
            let same_discriminant = lhs_is_some.clone().eq(rhs_is_some.clone());
            let same_payload_when_some =
                lhs_is_some.and(rhs_is_some).implies(lhs_payload.eq(rhs_payload));
            same_discriminant.and(same_payload_when_some)
        }
    }
}

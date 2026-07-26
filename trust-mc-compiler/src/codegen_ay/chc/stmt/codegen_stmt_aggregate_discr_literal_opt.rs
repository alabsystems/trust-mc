// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Part of #4290: literal Option-like ctor discriminant short-circuit.
//!
//! Extracted from `codegen_stmt_aggregate_discr_adt.rs` to keep that file
//! under the 500-line limit. See the caller in `translate_adt_discriminant`
//! (Option-like branch) for context.

use ay_bindings::{Expr, ExprValue};

use crate::codegen_ay::types::POINTER_WIDTH;

/// Part of #4290: Short-circuit discriminant emission for literal Option-like
/// constructors and ITE-over-constructors. Returns `Some(discr)` only when the
/// expression shape guarantees a constant (or cond-tagged constant) discriminant,
/// eliminating `(is C (C v))` tautologies that PDR fails to simplify during
/// projection. Returns `None` for symbolic / mixed / nested shapes so callers
/// fall through to the standard `is_constructor`-based emission.
///
/// Supported shapes:
/// - `Payload(_)` literal → `BV64(payload_idx)`
/// - `None_*` literal with matching datatype → `BV64(empty_idx)`
/// - `Ite(cond, Payload(_), None_*)` → `Ite(cond, BV64(payload_idx), BV64(empty_idx))`
/// - `Ite(cond, None_*, Payload(_))` → `Ite(cond, BV64(empty_idx), BV64(payload_idx))`
pub(super) fn literal_option_ctor_discr(
    value: &ExprValue,
    dt_name: &str,
    payload_ctor_name: &str,
    payload_idx: usize,
    empty_idx: usize,
) -> Option<Expr> {
    // Classify a literal constructor expression into its discriminant index.
    // Returns None when the expression is not a matching-DT constructor literal.
    fn classify(
        value: &ExprValue,
        dt_name: &str,
        payload_ctor_name: &str,
        payload_idx: usize,
        empty_idx: usize,
    ) -> Option<usize> {
        if let ExprValue::DatatypeConstructor { datatype_name, constructor_name, .. } = value {
            if datatype_name != dt_name {
                return None;
            }
            Some(if constructor_name == payload_ctor_name { payload_idx } else { empty_idx })
        } else {
            None
        }
    }

    match value {
        ExprValue::DatatypeConstructor { .. } => {
            let idx = classify(value, dt_name, payload_ctor_name, payload_idx, empty_idx)?;
            Some(Expr::bitvec_const(idx as u64, POINTER_WIDTH))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_idx =
                classify(then_expr.value(), dt_name, payload_ctor_name, payload_idx, empty_idx)?;
            let else_idx =
                classify(else_expr.value(), dt_name, payload_ctor_name, payload_idx, empty_idx)?;
            // If both branches collapse to the same discriminant, emit the constant.
            if then_idx == else_idx {
                return Some(Expr::bitvec_const(then_idx as u64, POINTER_WIDTH));
            }
            Some(Expr::ite(
                cond.clone(),
                Expr::bitvec_const(then_idx as u64, POINTER_WIDTH),
                Expr::bitvec_const(else_idx as u64, POINTER_WIDTH),
            ))
        }
        _ => None,
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Field-value coercion for inline ADT constructor applications.
//!
//! One implementation for the three inline aggregate paths
//! (`statement_exec_helpers::try_inline_adt_variant_assign_expr`,
//! `inline_shared::rvalue::inline_adt_variant_aggregate_to_expr`,
//! `inline_aggregate::inline_aggregate_to_expr`), which had drifted into three
//! copies whose last arm handed a value of ANY sort to
//! `Expr::datatype_constructor`. `ay_bindings::Expr::try_datatype_constructor`
//! checks only that the result sort is a datatype, never the argument sorts,
//! so an ill-sorted constructor survived to the emitted SMT and AY's parser
//! rejected the whole problem: kani/StorageMarkers/main.rs emitted
//! `(Some_Option_Handle_.._Edge (value_Option_LazyLeafHandle_marker_Dying ..))`,
//! a `LazyLeafHandle` where the constructor declares a `Handle`, and every
//! property of the harness came back `ChcParseError` with no solver run.
//!
//! A datatype-involved mismatch that no coercion repairs now DECLINES
//! (`None`): the caller records the gap and the assignment falls back to its
//! sound over-approximation instead of emitting a term whose meaning is
//! undefined. Two datatype sorts with the same NAME are the same SMT sort and
//! pass through (their in-memory definitions may differ in resolution depth).
//! Mismatches that involve no datatype keep their previous behaviour.

use ay_bindings::{Expr, Sort};
use tracing::debug;

use crate::codegen_ay::types::{
    SignExtension, coerce_bitvec_width, coerce_bool_to_unit_datatype, unflatten_bitvec_to_datatype,
};

/// Coerces `expr` to `field_sort` for use as a constructor argument, or
/// returns `None` when the sorts involve a datatype and cannot be reconciled.
#[must_use]
pub(in crate::codegen_ay::chc) fn coerce_inline_ctor_field(expr: Expr, field_sort: &Sort) -> Option<Expr> {
    let expr_sort = expr.sort().clone();
    if expr_sort == *field_sort {
        return Some(expr);
    }
    if expr_sort.is_bool() && field_sort.is_bitvec() {
        let width = field_sort.bitvec_width()?;
        return Some(Expr::ite(
            expr,
            Expr::bitvec_const(1u64, width),
            Expr::bitvec_const(0u64, width),
        ));
    }
    if expr_sort.is_bitvec() && field_sort.is_bool() {
        let width = expr_sort.bitvec_width()?;
        return Some(expr.ne(Expr::bitvec_const(0u64, width)));
    }
    if expr_sort.is_bitvec() && field_sort.is_bitvec() {
        return Some(match (expr_sort.bitvec_width(), field_sort.bitvec_width()) {
            (Some(src_w), Some(dst_w)) if src_w != dst_w => {
                coerce_bitvec_width(expr, dst_w, SignExtension::ZeroExtend)
            }
            _ => expr,
        });
    }
    if field_sort.is_datatype() {
        if let (Some(have), Some(want)) = (expr_sort.datatype_name(), field_sort.datatype_name())
            && have == want
        {
            return Some(expr);
        }
        // Part of #4090: ZST struct fields translate to Bool(true).
        if expr_sort.is_bool()
            && let Some(unit) = coerce_bool_to_unit_datatype(&expr, field_sort)
        {
            return Some(unit);
        }
        // Part of #3984: a BV-flattened callee local feeding a struct field.
        if expr_sort.is_bitvec()
            && let Some(unflattened) = unflatten_bitvec_to_datatype(&expr, field_sort)
        {
            return Some(unflattened);
        }
        debug!(
            have = ?expr_sort.datatype_name().unwrap_or("<non-datatype>"),
            want = ?field_sort.datatype_name(),
            "inline ctor field: datatype sort mismatch, declining"
        );
        return None;
    }
    if expr_sort.is_datatype() {
        debug!(
            have = ?expr_sort.datatype_name(),
            "inline ctor field: datatype value for a non-datatype field, declining"
        );
        return None;
    }
    Some(expr)
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;
    use ay_bindings::ExprValue;

    fn handle() -> Sort {
        Sort::struct_type("Handle_Edge", vec![("node".to_string(), Sort::bitvec(64))])
    }

    fn lazy_leaf_handle() -> Sort {
        Sort::enum_type(
            "LazyLeafHandle_marker_Dying",
            vec![
                ("Root_LazyLeafHandle".to_string(), vec![("Root_field_0".to_string(), Sort::bitvec(64))]),
                ("Edge_LazyLeafHandle".to_string(), vec![("Edge_field_0".to_string(), handle())]),
            ],
        )
    }

    #[test]
    fn equal_sorts_pass_through() {
        let x = Expr::var("x", handle());
        assert_eq!(coerce_inline_ctor_field(x.clone(), &handle()), Some(x));
    }

    /// The StorageMarkers shape: a `LazyLeafHandle` handed to a field declared
    /// `Handle`. Must decline, never reach `datatype_constructor`.
    #[test]
    fn different_datatype_declines() {
        let payload = Expr::var("payload", lazy_leaf_handle());
        assert_eq!(coerce_inline_ctor_field(payload, &handle()), None);
    }

    #[test]
    fn same_named_datatype_with_a_different_resolution_passes_through() {
        let shallow = Sort::struct_type("Handle_Edge", vec![("node".to_string(), Sort::uninterpreted("Ptr"))]);
        let x = Expr::var("x", shallow);
        let out = coerce_inline_ctor_field(x.clone(), &handle()).unwrap();
        assert_eq!(out, x);
    }

    #[test]
    fn datatype_value_for_a_bitvec_field_declines() {
        let x = Expr::var("x", handle());
        assert_eq!(coerce_inline_ctor_field(x, &Sort::bitvec(64)), None);
    }

    #[test]
    fn bitvec_that_cannot_be_unflattened_into_a_datatype_declines() {
        let x = Expr::var("x", Sort::bitvec(3));
        assert_eq!(coerce_inline_ctor_field(x, &lazy_leaf_handle()), None);
    }

    #[test]
    fn bool_into_non_unit_datatype_declines() {
        let b = Expr::var("b", Sort::bool());
        assert_eq!(coerce_inline_ctor_field(b, &lazy_leaf_handle()), None);
    }

    #[test]
    fn bool_and_bitvec_coercions_are_kept() {
        let b = Expr::var("b", Sort::bool());
        let as_bv = coerce_inline_ctor_field(b, &Sort::bitvec(8)).unwrap();
        assert_eq!(*as_bv.sort(), Sort::bitvec(8));
        assert!(matches!(as_bv.value(), ExprValue::Ite { .. }));

        let v = Expr::var("v", Sort::bitvec(8));
        let as_bool = coerce_inline_ctor_field(v.clone(), &Sort::bool()).unwrap();
        assert!(as_bool.sort().is_bool());

        let widened = coerce_inline_ctor_field(v, &Sort::bitvec(64)).unwrap();
        assert_eq!(*widened.sort(), Sort::bitvec(64));
    }

    /// Mismatches that involve no datatype are left exactly as before.
    #[test]
    fn non_datatype_mismatch_is_unchanged() {
        let i = Expr::var("i", Sort::int());
        assert_eq!(coerce_inline_ctor_field(i.clone(), &Sort::bitvec(64)), Some(i));
    }
}

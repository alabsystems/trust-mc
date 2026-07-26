// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! DT→DT fallback cast handler.
//!
//! When `coerce_datatype_structural` (in trust_mc-codegen-types) returns `None`
//! because field sorts are incompatible at the leaf level, this module
//! provides a more aggressive field-by-field coercion that handles
//! additional sort pairs: Bool↔BV, Int↔BV, and Array identity.
//!
//! Part of #3192: eliminates UnconstrainedAssignment for DT→DT cast
//! mismatches where the types are structurally compatible but field sorts
//! differ in ways that `coerce_datatype_structural` does not handle.

use ay_bindings::{Expr, Sort, SortInner};
use tracing::warn;

use crate::codegen_ay::types::SignExtension;

/// Try to coerce a single field expression from `src_sort` to `tgt_sort`.
///
/// Handles sort pairs that `coerce_datatype_structural` in types.rs does not:
/// - Bool → BV: `ite(expr, bv1(1), bv1(0))` then zero-extend to target width
/// - BV → Bool: `expr != 0`
/// - Int → BV: `int2bv(width)`
/// - BV → Int: `bv2int` (unsigned) or `bv2int_signed`
/// - Array identity: same index/element sorts but different Sort objects
///
/// Returns `None` if the sorts are genuinely incompatible.
pub(super) fn coerce_field_aggressive(
    field_expr: Expr,
    src_sort: &Sort,
    tgt_sort: &Sort,
    ext: SignExtension,
) -> Option<Expr> {
    // Same sort — identity (should be caught upstream, but defensive).
    if src_sort == tgt_sort {
        return Some(field_expr);
    }

    match (src_sort.inner(), tgt_sort.inner()) {
        // Bool → BV: encode as 0/1, then extend to target width.
        (SortInner::Bool, SortInner::BitVec(tb)) => {
            let bv1 =
                Expr::ite(field_expr, Expr::bitvec_const(1u64, 1), Expr::bitvec_const(0u64, 1));
            Some(if tb.width == 1 { bv1 } else { bv1.zero_extend(tb.width - 1) })
        }
        // BV → Bool: nonzero test.
        (SortInner::BitVec(sb), SortInner::Bool) => {
            Some(field_expr.ne(Expr::bitvec_const(0u64, sb.width)))
        }
        // Int → BV: modular conversion via int2bv.
        (SortInner::Int, SortInner::BitVec(tb)) => Some(field_expr.int2bv(tb.width)),
        // BV → Int: lift to integer, respecting signedness.
        (SortInner::BitVec(_), SortInner::Int) => Some(match ext {
            SignExtension::SignExtend => field_expr.bv2int_signed(),
            SignExtension::ZeroExtend => field_expr.bv2int(),
        }),
        // Array identity: same index and element sorts (catches cases where
        // Sort objects differ due to Arc identity but are structurally equal).
        (SortInner::Array(sa), SortInner::Array(ta))
            if sa.index_sort == ta.index_sort && sa.element_sort == ta.element_sort =>
        {
            Some(field_expr)
        }
        _ => None,
    }
}

/// Attempt DT→DT coercion with aggressive field-level sort conversion.
///
/// Called when `coerce_datatype_structural` returns `None`. This function
/// repeats the single-constructor, same-field-count check and applies
/// `coerce_field_aggressive` for field sorts that the structural coercer
/// cannot handle.
///
/// Returns `None` when:
/// - Either DT has != 1 constructor (multi-variant enum: genuinely hard)
/// - Field counts differ (genuinely incompatible)
/// - Any field sort pair is not coercible even with aggressive coercion
pub(super) fn coerce_dt_to_dt_fallback(
    rhs: Expr,
    src_dt: &ay_bindings::DatatypeSort,
    tgt_dt: &ay_bindings::DatatypeSort,
    out_sort: Sort,
    ext: SignExtension,
) -> Option<Expr> {
    // Only handle single-constructor DTs (structs/tuples).
    if src_dt.constructors.len() != 1 || tgt_dt.constructors.len() != 1 {
        return None;
    }
    let sc = src_dt.constructors.first()?;
    let tc = tgt_dt.constructors.first()?;

    // Field count must match.
    if sc.fields.len() != tc.fields.len() {
        return None;
    }

    let mut field_exprs = Vec::with_capacity(sc.fields.len());
    for (sf, tf) in sc.fields.iter().zip(tc.fields.iter()) {
        let extracted = rhs.clone().field_select(&*src_dt.name, &*sf.name, sf.sort.clone());
        if let Some(coerced) = coerce_field_aggressive(extracted, &sf.sort, &tf.sort, ext) {
            field_exprs.push(coerced);
        } else {
            // Field sorts are genuinely incompatible.
            warn!(
                src_field = %sf.name, tgt_field = %tf.name,
                src_sort = ?sf.sort, tgt_sort = ?tf.sort,
                "DT→DT fallback: incompatible field sorts"
            );
            return None;
        }
    }

    Some(Expr::datatype_constructor(&tgt_dt.name, &tc.name, field_exprs, out_sort))
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Lexicographic comparison for resolved slice backing arrays.

use ay_bindings::{Expr, ExprValue};

use super::super::SLICE_BACKING_REBASE_MAX_ELEMS;
use super::super::codegen_call_slice_helpers::ResolvedSliceBacking;
use crate::codegen_ay::stubs::StubKind;

/// Slice-backed comparison resolution.
///
/// `Unsupported` is fail-closed: callers must emit a sound fallback instead of
/// treating it like "no slice backing found" and trying legacy pointer paths.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) enum SliceBackingCmpResult {
    Precise(Expr),
    Unsupported,
}

impl SliceBackingCmpResult {
    pub(in crate::codegen_ay::chc) fn as_expr(&self) -> Option<&Expr> {
        match self {
            Self::Precise(expr) => Some(expr),
            Self::Unsupported => None,
        }
    }

    pub(in crate::codegen_ay::chc) fn is_unsupported(&self) -> bool {
        matches!(self, Self::Unsupported)
    }
}

pub(in crate::codegen_ay::chc) fn compute_slice_backing_cmp_result(
    stub: StubKind,
    lhs: &ResolvedSliceBacking,
    rhs: &ResolvedSliceBacking,
    is_signed: bool,
) -> SliceBackingCmpResult {
    compute_slice_backing_cmp_expr(stub, lhs, rhs, is_signed)
        .map(SliceBackingCmpResult::Precise)
        .unwrap_or(SliceBackingCmpResult::Unsupported)
}

pub(in crate::codegen_ay::chc) fn compute_optional_slice_backing_cmp_result(
    stub: StubKind,
    lhs: Option<&ResolvedSliceBacking>,
    rhs: Option<&ResolvedSliceBacking>,
    is_signed: bool,
) -> Option<SliceBackingCmpResult> {
    match (lhs, rhs) {
        (None, None) => None,
        (Some(lhs), Some(rhs)) => Some(compute_slice_backing_cmp_result(stub, lhs, rhs, is_signed)),
        (Some(_), None) | (None, Some(_)) => Some(SliceBackingCmpResult::Unsupported),
    }
}

fn compute_slice_backing_cmp_expr(
    stub: StubKind,
    lhs: &ResolvedSliceBacking,
    rhs: &ResolvedSliceBacking,
    is_signed: bool,
) -> Option<Expr> {
    if *lhs.data.as_expr().sort() != *rhs.data.as_expr().sort() {
        return None;
    }
    let arr = lhs.data.as_expr().sort().array_sort()?;
    if !arr.element_sort.is_bitvec() {
        return None;
    }
    let lhs_len = concrete_usize(lhs.len.as_expr())?;
    let rhs_len = concrete_usize(rhs.len.as_expr())?;
    let min_len = lhs_len.min(rhs_len);
    if min_len > SLICE_BACKING_REBASE_MAX_ELEMS
        || lhs_len.max(rhs_len) > SLICE_BACKING_REBASE_MAX_ELEMS
    {
        return None;
    }

    match stub {
        StubKind::PrimitivePartialEqEq | StubKind::PrimitivePartialEqNe => {
            let is_eq = stub == StubKind::PrimitivePartialEqEq;
            let eq = build_slice_eq(lhs, rhs, lhs_len, rhs_len)?;
            Some(if is_eq { eq } else { eq.not() })
        }
        StubKind::OrdCmp => build_slice_lexicographic_cmp(lhs, rhs, min_len, is_signed),
        StubKind::PrimitivePartialOrdLt
        | StubKind::PrimitivePartialOrdLe
        | StubKind::PrimitivePartialOrdGt
        | StubKind::PrimitivePartialOrdGe => {
            let cmp = build_slice_lexicographic_cmp(lhs, rhs, min_len, is_signed)?;
            let less = Expr::bitvec_const(-1i128, 32);
            let greater = Expr::bitvec_const(1, 32);
            Some(match stub {
                StubKind::PrimitivePartialOrdLt => cmp.eq(less),
                StubKind::PrimitivePartialOrdLe => cmp.ne(greater),
                StubKind::PrimitivePartialOrdGt => cmp.eq(greater),
                StubKind::PrimitivePartialOrdGe => cmp.ne(less),
                _ => return None,
            })
        }
        _ => None,
    }
}

pub(in crate::codegen_ay::chc) fn compute_optional_slice_backing_method_cmp_result(
    method: &str,
    lhs: Option<&ResolvedSliceBacking>,
    rhs: Option<&ResolvedSliceBacking>,
    is_signed: bool,
) -> Option<SliceBackingCmpResult> {
    match (lhs, rhs) {
        (None, None) => None,
        (Some(lhs), Some(rhs)) => {
            Some(compute_slice_backing_method_cmp_result(method, lhs, rhs, is_signed))
        }
        (Some(_), None) | (None, Some(_)) => Some(SliceBackingCmpResult::Unsupported),
    }
}

fn compute_slice_backing_method_cmp_result(
    method: &str,
    lhs: &ResolvedSliceBacking,
    rhs: &ResolvedSliceBacking,
    is_signed: bool,
) -> SliceBackingCmpResult {
    let stub = match method {
        "cmp" | "partial_cmp" => StubKind::OrdCmp,
        "eq" => StubKind::PrimitivePartialEqEq,
        "ne" => StubKind::PrimitivePartialEqNe,
        "lt" => StubKind::PrimitivePartialOrdLt,
        "le" => StubKind::PrimitivePartialOrdLe,
        "gt" => StubKind::PrimitivePartialOrdGt,
        "ge" => StubKind::PrimitivePartialOrdGe,
        _ => return SliceBackingCmpResult::Unsupported,
    };
    compute_slice_backing_cmp_result(stub, lhs, rhs, is_signed)
}

fn build_slice_eq(
    lhs: &ResolvedSliceBacking,
    rhs: &ResolvedSliceBacking,
    lhs_len: usize,
    rhs_len: usize,
) -> Option<Expr> {
    if lhs_len != rhs_len {
        return Some(Expr::bool_const(false));
    }
    let mut result = lhs.len.as_expr().clone().eq(rhs.len.as_expr().clone());
    for i in 0..lhs_len {
        let l = select_slice_elem(lhs, i)?;
        let r = select_slice_elem(rhs, i)?;
        result = result.and(l.eq(r));
    }
    Some(result)
}

fn build_slice_lexicographic_cmp(
    lhs: &ResolvedSliceBacking,
    rhs: &ResolvedSliceBacking,
    min_len: usize,
    is_signed: bool,
) -> Option<Expr> {
    let neg1 = Expr::bitvec_const(-1i128, 32);
    let zero = Expr::bitvec_const(0, 32);
    let pos1 = Expr::bitvec_const(1, 32);
    let len_lt = lhs.len.as_expr().clone().bvult(rhs.len.as_expr().clone());
    let len_eq = lhs.len.as_expr().clone().eq(rhs.len.as_expr().clone());
    let mut result = Expr::ite(len_lt, neg1.clone(), Expr::ite(len_eq, zero, pos1.clone()));

    for i in (0..min_len).rev() {
        let l = select_slice_elem(lhs, i)?;
        let r = select_slice_elem(rhs, i)?;
        let lt = if is_signed { l.clone().bvslt(r.clone()) } else { l.clone().bvult(r.clone()) };
        let gt = if is_signed { l.bvsgt(r) } else { l.bvugt(r) };
        result = Expr::ite(lt, neg1.clone(), Expr::ite(gt, pos1.clone(), result));
    }

    Some(result)
}

fn select_slice_elem(slice: &ResolvedSliceBacking, logical_index: usize) -> Option<Expr> {
    slice.data.as_expr().sort().array_sort()?;
    let offset = slice.offset.as_expr();
    let idx = Expr::bitvec_const(logical_index as u64, offset.sort().bitvec_width()?);
    let src_idx = if logical_index == 0 { offset.clone() } else { offset.clone().bvadd(idx) };
    Some(slice.data.as_expr().clone().select(src_idx))
}

fn concrete_usize(expr: &Expr) -> Option<usize> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => usize::try_from(value.clone()).ok(),
        ExprValue::BvAdd(lhs, rhs) => {
            let lhs = concrete_usize(lhs)?;
            let rhs = concrete_usize(rhs)?;
            let sum = lhs.checked_add(rhs)?;
            if fits_bitvec_width(sum, expr.sort().bitvec_width()?) { Some(sum) } else { None }
        }
        ExprValue::BvSub(lhs, rhs) => {
            let lhs = concrete_usize(lhs)?;
            let rhs = concrete_usize(rhs)?;
            let diff = lhs.checked_sub(rhs)?;
            if fits_bitvec_width(diff, expr.sort().bitvec_width()?) { Some(diff) } else { None }
        }
        ExprValue::BvExtract { high, low, expr: inner } => {
            if let ExprValue::BitVecConst { value, .. } = inner.value() {
                let shifted = value >> (*low as usize);
                let width = high - low + 1;
                let mask = (num_bigint::BigInt::from(1) << (width as usize)) - 1;
                let extracted = shifted & mask;
                u64::try_from(&extracted).ok().map(|v| v as usize)
            } else {
                None
            }
        }
        ExprValue::BvZeroExtend { expr: inner, .. }
        | ExprValue::BvSignExtend { expr: inner, .. } => concrete_usize(inner),
        _ => None,
    }
}

fn fits_bitvec_width(value: usize, width: u32) -> bool {
    if width as usize >= usize::BITS as usize { true } else { value < (1usize << width) }
}

#[cfg(test)]
mod tests {
    use ay_bindings::Sort;

    use super::*;
    use crate::codegen_ay::provenance::Val;
    use crate::codegen_ay::types::POINTER_WIDTH;

    fn backing(name: &str, len: Expr, offset: Expr) -> ResolvedSliceBacking {
        let data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
        ResolvedSliceBacking {
            data: Val::of_value(Expr::var(name, data_sort)),
            len: Val::of_value(len),
            offset: Val::of_value(offset),
        }
    }

    #[test]
    fn slice_backing_cmp_fails_closed_for_symbolic_len() {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let lhs = backing("lhs", Expr::var("n", Sort::bitvec(POINTER_WIDTH)), zero.clone());
        let rhs = backing("rhs", Expr::bitvec_const(2u64, POINTER_WIDTH), zero);

        let result = compute_slice_backing_cmp_result(StubKind::OrdCmp, &lhs, &rhs, false);

        assert!(matches!(result, SliceBackingCmpResult::Unsupported));
    }

    #[test]
    fn optional_slice_backing_cmp_distinguishes_one_sided_backing() {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let lhs = backing("lhs", Expr::bitvec_const(2u64, POINTER_WIDTH), zero);

        let one_sided =
            compute_optional_slice_backing_cmp_result(StubKind::OrdCmp, Some(&lhs), None, false);
        let no_backing =
            compute_optional_slice_backing_cmp_result(StubKind::OrdCmp, None, None, false);

        assert!(matches!(one_sided, Some(SliceBackingCmpResult::Unsupported)));
        assert!(no_backing.is_none());
    }

    #[test]
    fn slice_backing_cmp_folds_simple_arithmetic_lengths_with_nonzero_offsets() {
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let two = Expr::bitvec_const(2u64, POINTER_WIDTH);
        let lhs_len = Expr::bitvec_const(4u64, POINTER_WIDTH).bvsub(one.clone());
        let rhs_len = one.clone().bvadd(two.clone());
        let lhs = backing("lhs", lhs_len, one);
        let rhs = backing("rhs", rhs_len, two);

        assert!(matches!(
            compute_slice_backing_cmp_result(StubKind::OrdCmp, &lhs, &rhs, false),
            SliceBackingCmpResult::Precise(_)
        ));
    }
}

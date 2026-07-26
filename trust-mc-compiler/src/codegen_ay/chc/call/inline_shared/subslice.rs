// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Subslice projection helpers for inline body translators.
//!
//! Extracted from `place.rs` per 500-line file limit.
//! Part of #3188: Subslice read and write paths for the inline walker.

use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, TyKind};

use super::super::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Extract the element type from an array or slice MIR type.
pub(super) fn array_element_ty(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    match ctx.resolve_body_ty(ty).kind() {
        TyKind::RigidTy(RigidTy::Array(elem, _)) | TyKind::RigidTy(RigidTy::Slice(elem)) => {
            Some(ctx.resolve_body_ty(elem))
        }
        _ => None,
    }
}

/// Part of #3188: Apply a Subslice projection to an inline expression.
/// Identity (from=0, to=0, from_end=true) passes through. Bounded ranges build
/// a shifted Array. `known_len` enables `from_end=true` recovery when the
/// compile-time array length is available from the MIR type.
pub(super) fn apply_inline_subslice(
    current: &Expr,
    from: u64,
    to: u64,
    from_end: bool,
    known_len: Option<u64>,
) -> Option<Expr> {
    // from_end=true: array[from..len-to]. from=0,to=0 → full array (identity).
    // from_end=false: array[from..to]. from=0,to=0 → empty slice (NOT identity).
    if from == 0 && to == 0 && from_end {
        return Some(current.clone());
    }
    if !current.sort().is_array() {
        return None;
    }
    let (start, end) = if from_end {
        // from_end=true: array[from..len-to]. Recover with known compile-time length.
        let len = known_len?;
        (from as usize, (len - to) as usize)
    } else {
        (from as usize, to as usize)
    };
    if end <= start {
        return None;
    }
    let arr = current.sort().array_sort()?;
    let elem_sort = arr.element_sort.clone();
    let default_elem = if elem_sort.is_bitvec() {
        Expr::bitvec_const(0u64, elem_sort.bitvec_width().unwrap_or(POINTER_WIDTH))
    } else if elem_sort.is_bool() {
        Expr::bool_const(false)
    } else {
        return None;
    };
    let mut result = Expr::const_array(ay_bindings::Sort::bitvec(POINTER_WIDTH), default_elem);
    for i in 0..(end - start) {
        let src_idx = Expr::bitvec_const((start + i) as u128, POINTER_WIDTH);
        let dst_idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
        let elem = current.clone().select(src_idx);
        result = result.store(dst_idx, elem);
    }
    Some(result)
}

/// Part of #3188: Subslice write — copy elements from `rhs` array into
/// positions `[start..end)` of the target array. Used by
/// `update_inline_value_expr` in `projected_assign.rs`.
pub(in crate::codegen_ay) fn apply_inline_subslice_write(
    ctx: &ChcCtx<'_, '_>,
    current: Expr,
    current_ty: rustc_public::ty::Ty,
    from: u64,
    to: u64,
    from_end: bool,
    rhs: Expr,
) -> Option<Expr> {
    if !current.sort().is_array() {
        return None;
    }
    let (start, end) = if from_end {
        let len = match ctx.resolve_body_ty(current_ty).kind() {
            TyKind::RigidTy(RigidTy::Array(_, len_const)) => len_const.eval_target_usize().ok()?,
            _ => return None,
        };
        (from as usize, (len - to) as usize)
    } else {
        (from as usize, to as usize)
    };
    if end <= start {
        return None;
    }
    let signed = array_element_ty(ctx, current_ty)
        .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
        .unwrap_or(false);
    let mut result = current;
    for i in 0..(end - start) {
        let src_idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
        let dst_idx = Expr::bitvec_const((start + i) as u128, POINTER_WIDTH);
        let elem = rhs.clone().select(src_idx);
        let elem = ChcCtx::coerce_store_value(result.sort(), elem, signed, &ctx.diagnostics);
        result = result.store(dst_idx, elem);
    }
    Some(result)
}

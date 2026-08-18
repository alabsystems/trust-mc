// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer and float helper functions for inline rvalue translation.
//!
//! Extracted from `rvalue.rs` to keep it under the 500-line limit.
//! Part of #4050: RawPtr aggregate + BinOp::Offset support.

use ay_bindings::{Expr, SortInner};
use rustc_public::mir::{BinOp, LocalDecl, Operand};
use rustc_public::ty::{RigidTy, TyKind, UintTy};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::PlaceResolver;
use super::place::inline_operand_to_expr;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Route a float BinaryOp through FP theory (arithmetic) or IEEE 754
/// sign-aware comparison helpers. Part of #3839.
///
/// Previously, the inline translator passed `is_float=false` to
/// `translate_binop`, routing all float BinOps through BV integer
/// arithmetic (bvsub, bvadd, etc.) which gives wrong results on
/// IEEE 754 bit patterns. This caused 30+ math intrinsic harnesses
/// to be UNKNOWN because assertion functions like
/// `(sqrt(4.0) - 2.0).abs() <= EPSILON` produced garbage.
pub(super) fn inline_float_binop(op: BinOp, lhs: Expr, rhs: Expr, width: u32) -> Option<Expr> {
    use crate::codegen_ay::float_arithmetic::{bv_float_binop_chc, is_float_arithmetic_op};
    use crate::codegen_ay::float_compare::{
        bv_float_cmp, bv_float_eq, bv_float_ge, bv_float_gt, bv_float_le, bv_float_lt, bv_float_ne,
    };

    // Float arithmetic (Add, Sub, Mul, Div, Rem) → CHC-safe encoding.
    // Part of #3839: uses constant-fold for concrete, BV int for symbolic.
    if is_float_arithmetic_op(op) {
        return bv_float_binop_chc(op, lhs, rhs, width);
    }

    // Float comparisons → IEEE 754 sign-aware helpers.
    // Part of #3798: Eq/Ne use bv_float_eq/ne (not raw BV equality) so that
    // NaN self-comparison works correctly (is_nan() lowers to `self != self`).
    match op {
        BinOp::Lt => Some(bv_float_lt(&lhs, &rhs, width)),
        BinOp::Le => Some(bv_float_le(&lhs, &rhs, width)),
        BinOp::Gt => Some(bv_float_gt(&lhs, &rhs, width)),
        BinOp::Ge => Some(bv_float_ge(&lhs, &rhs, width)),
        BinOp::Cmp => Some(bv_float_cmp(&lhs, &rhs, width)),
        BinOp::Eq => Some(bv_float_eq(&lhs, &rhs, width)),
        BinOp::Ne => Some(bv_float_ne(&lhs, &rhs, width)),
        // Bitwise ops on float BVs (rare but possible): fall through to
        // the integer BV path which is correct for bitwise operations.
        _ => None,
    }
}

/// Translate `BinOp::Offset` (pointer arithmetic) in the inline context.
///
/// Part of #4050: Vec internals use `ptr.offset(n)` extensively. Without this,
/// every pointer offset fails → the pointer local isn't populated → all
/// downstream operations cascade to gaps.
///
/// Mirrors `translate_pointer_offset_with_modified` from `codegen_stmt_rvalue_offset.rs`.
pub(super) fn inline_pointer_offset<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    ptr_expr: Expr,
    count_expr: Expr,
    lhs_ty: rustc_public::ty::Ty,
) -> Option<Expr> {
    use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width};

    // Coerce operands to BV64 if needed (Int-lifted or narrower BV).
    let ptr = if ptr_expr.sort().is_int() {
        ptr_expr.int2bv(POINTER_WIDTH)
    } else if ptr_expr.sort().is_bitvec() {
        coerce_bitvec_width(ptr_expr, POINTER_WIDTH, SignExtension::ZeroExtend)
    } else {
        return None;
    };
    let count = if count_expr.sort().is_int() {
        count_expr.int2bv(POINTER_WIDTH)
    } else if count_expr.sort().is_bitvec() {
        // Offset counts are signed (isize).
        coerce_bitvec_width(count_expr, POINTER_WIDTH, SignExtension::SignExtend)
    } else {
        return None;
    };

    // Determine pointee size from the LHS pointer type.
    let pointee_size: u64 = match lhs_ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(inner, _)) | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
            ctx.get_type_size(inner).unwrap_or(1) as u64
        }
        _ => 1,
    };

    let byte_offset = if pointee_size == 1 {
        count
    } else {
        count.bvmul(Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH))
    };

    // Split-add keeps the obj_id lane intact (mirrors the stmt path, #3921):
    // whole-width bvadd smears a symbolic count across the id bits, and the
    // eventual deref's heap bounds check gets dropped for non-foldable obj_ids.
    Some(crate::codegen_ay::chc::pointer_step::step_split_pointer(ptr, byte_offset).result)
}

/// Coerce an expression to pointer width (BV64) for RawPtr aggregate construction.
///
/// Part of #4050: mirrors the main codegen's coercion in `codegen_stmt_aggregate.rs`.
pub(super) fn inline_coerce_to_ptr(expr: Expr) -> Expr {
    use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width};

    match expr.sort().inner() {
        ay_bindings::SortInner::BitVec(bv) if bv.width == POINTER_WIDTH => expr,
        ay_bindings::SortInner::BitVec(_) => {
            coerce_bitvec_width(expr, POINTER_WIDTH, SignExtension::ZeroExtend)
        }
        ay_bindings::SortInner::Int => expr.int2bv(POINTER_WIDTH),
        ay_bindings::SortInner::Bool => {
            // Unit metadata for thin pointers — should not normally be the data ptr.
            Expr::bitvec_const(0u64, POINTER_WIDTH)
        }
        _ => expr,
    }
}

/// Part of #4050: Coerce a single-field Datatype wrapper to its inner BV.
///
/// Types like `UsizeNoHighBit(BV64)` are single-constructor, single-field DTs
/// wrapping a BV. When these appear as BinOp operands alongside a raw BV, the
/// sort mismatch causes `binop_to_expr` to fail. Unwrap to the inner BV so
/// the comparison/arithmetic proceeds on matching sorts.
pub(super) fn coerce_dt_wrapper_to_bv(expr: Expr) -> Expr {
    if let ay_bindings::SortInner::Datatype(dt) = expr.sort().inner() {
        if dt.constructors.len() == 1 {
            let cons = &dt.constructors[0];
            if cons.fields.len() == 1 && cons.fields[0].sort.is_bitvec() {
                let dt_name = dt.name.clone();
                let field_name = cons.fields[0].name.clone();
                let field_sort = cons.fields[0].sort.clone();
                return expr.field_select(&dt_name, &field_name, field_sort);
            }
        }
    }
    expr
}

/// Lexicographic `(data, metadata)` comparison of two wide-pointer operands.
///
/// Wave 4 of the address-vs-value conversion. The double-width test below is
/// the handler's applicability gate — "is this the wide-pointer lane?" — and
/// stays. What is deleted is the assumption that followed it: that bits 127..64
/// of a double-width operand ARE metadata. `coerce_bitvec_width_safe` widens
/// thin pointers into exactly this slot, so that assumption compared extension
/// padding as if it were a slice length or vtable id.
///
/// `PtrRepr` reports metadata only for a genuine `Fat`, which leaves three
/// cases:
///
/// * **both fat** — unchanged: address lane first, metadata as tie-break;
/// * **neither fat** — both are widened thin pointers, so there is no
///   tie-break: the address lane decides alone. For a zero- or sign-extension
///   the high halves were equal whenever the low halves were, so this is the
///   same predicate the old code built, minus the padding terms;
/// * **mixed** — one real length against another's padding. Nothing honest to
///   compare, so decline and let the caller's generic lane handle it.
pub(super) fn try_translate_inline_wide_pointer_binop(
    op: BinOp,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<Expr> {
    if lhs.sort().bitvec_width() != Some(2 * POINTER_WIDTH)
        || rhs.sort().bitvec_width() != Some(2 * POINTER_WIDTH)
    {
        return None;
    }
    let (lhs_data, lhs_meta) = PtrRepr::classify(lhs)?.into_parts();
    let (rhs_data, rhs_meta) = PtrRepr::classify(rhs)?.into_parts();
    let meta = match (lhs_meta, rhs_meta) {
        (Some(lhs_meta), Some(rhs_meta)) => Some((lhs_meta.into_expr(), rhs_meta.into_expr())),
        (None, None) => None,
        _ => return None,
    };
    let (lhs_data, rhs_data) = (lhs_data.into_expr(), rhs_data.into_expr());
    let data_eq = lhs_data.clone().eq(rhs_data.clone());
    let meta_eq = meta.as_ref().map(|(l, r)| l.clone().eq(r.clone()));
    match op {
        BinOp::Eq => Some(match meta_eq {
            Some(meta_eq) => data_eq.and(meta_eq),
            None => data_eq,
        }),
        BinOp::Ne => Some(
            match meta_eq {
                Some(meta_eq) => data_eq.and(meta_eq),
                None => data_eq,
            }
            .not(),
        ),
        BinOp::Lt => {
            let data_lt = lhs_data.bvult(rhs_data);
            Some(match meta {
                Some((lhs_meta, rhs_meta)) => data_lt.or(data_eq.and(lhs_meta.bvult(rhs_meta))),
                None => data_lt,
            })
        }
        BinOp::Le => {
            let data_lt = lhs_data.bvult(rhs_data);
            Some(match meta {
                // `<=` on the metadata is vacuously true when there is none, so
                // the tie-break degenerates to plain address equality.
                Some((lhs_meta, rhs_meta)) => data_lt.or(data_eq.and(lhs_meta.bvule(rhs_meta))),
                None => data_lt.or(data_eq),
            })
        }
        BinOp::Gt => {
            let data_gt = rhs_data.bvult(lhs_data);
            Some(match meta {
                Some((lhs_meta, rhs_meta)) => data_gt.or(data_eq.and(rhs_meta.bvult(lhs_meta))),
                None => data_gt,
            })
        }
        BinOp::Ge => {
            let data_gt = rhs_data.bvult(lhs_data);
            Some(match meta {
                Some((lhs_meta, rhs_meta)) => data_gt.or(data_eq.and(rhs_meta.bvule(lhs_meta))),
                None => data_gt.or(data_eq),
            })
        }
        BinOp::Cmp => {
            let data_lt = lhs_data.clone().bvult(rhs_data.clone());
            let data_gt = rhs_data.bvult(lhs_data);
            // No metadata means no tie to break: equal addresses compare equal.
            let meta_cmp = match (meta, meta_eq) {
                (Some((lhs_meta, rhs_meta)), Some(meta_eq)) => Expr::ite(
                    lhs_meta.bvult(rhs_meta),
                    Expr::bitvec_const(-1i128, 32),
                    Expr::ite(meta_eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
                ),
                _ => Expr::bitvec_const(0, 32),
            };
            Some(Expr::ite(
                data_lt,
                Expr::bitvec_const(-1i128, 32),
                Expr::ite(data_gt, Expr::bitvec_const(1, 32), meta_cmp),
            ))
        }
        _ => None,
    }
}

fn copy_inline_subslice_metadata(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: Option<usize>,
    src_local: usize,
) {
    let Some(dest_local) = dest_local else { return };
    if let Some(len) = ctx.ref_resolution.subslice_len.get(&src_local).cloned() {
        ctx.ref_resolution.subslice_len.insert(dest_local, len);
    }
    if let Some(offset) = ctx.ref_resolution.subslice_offset.get(&src_local).cloned() {
        ctx.ref_resolution.subslice_offset.insert(dest_local, offset);
    }
}

pub(super) fn preserve_inline_subslice_metadata_from_operand(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: Option<usize>,
    operand: &Operand,
) {
    let (Operand::Copy(src) | Operand::Move(src)) = operand else {
        return;
    };
    if src.projection.is_empty() {
        copy_inline_subslice_metadata(ctx, dest_local, src.local);
    }
}

pub(super) fn preserve_inline_subslice_metadata_from_place(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: Option<usize>,
    place_local: usize,
) {
    copy_inline_subslice_metadata(ctx, dest_local, place_local);
}

pub(super) fn seed_inline_raw_ptr_metadata<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    dest_local: Option<usize>,
    operands: &[Operand],
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) {
    let Some(dest_local) = dest_local else { return };
    if operands.len() <= 1 {
        return;
    }
    let Ok(meta_ty) = operands[1].ty(locals) else {
        return;
    };
    if !matches!(meta_ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))) {
        return;
    }
    let Some(len_expr) = inline_operand_to_expr(ctx, &operands[1], local_exprs, resolver, locals)
    else {
        return;
    };
    ctx.ref_resolution.subslice_len.insert(dest_local, len_expr);
    debug!(dest = dest_local, "inline RawPtr aggregate: seeded subslice_len from metadata operand");
}

pub(super) fn translate_inline_ptr_metadata<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    operand: &Operand,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let ty = operand.ty(locals).ok()?;
    let is_wide = match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
        | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
            matches!(
                pointee.kind(),
                TyKind::RigidTy(RigidTy::Slice(_))
                    | TyKind::RigidTy(RigidTy::Str)
                    | TyKind::RigidTy(RigidTy::Dynamic(..))
            ) || pointee.layout().ok().is_some_and(|layout| layout.shape().is_unsized())
        }
        _ => false,
    };
    if !is_wide {
        return Some(Expr::bitvec_const(0, POINTER_WIDTH));
    }

    if let Operand::Copy(place) | Operand::Move(place) = operand
        && let Some(len_expr) = ctx.ref_resolution.subslice_len.get(&place.local)
    {
        debug!(local = place.local, "inline PtrMetadata: resolved from subslice_len");
        return Some(len_expr.clone());
    }

    if let Some(expr) = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals) {
        // `is_wide` above established from the MIR TYPE that this operand has
        // metadata; what shape the TERM has is a separate question, and the
        // width test that used to answer it here read bits 127..64 of any
        // double-width term as the length. For a thin pointer that
        // `coerce_bitvec_width_safe` widened into a bv128 slot those bits are
        // zero-extension padding, so the "length" was a fabricated 0 — which
        // makes every bounds obligation over it trivially satisfiable.
        // `PtrRepr` hands back metadata for a genuine `Fat` only; the widened
        // shape declines and falls through to the `fld_len` lane and then to
        // `translate_ptr_metadata`, which are the honest producers.
        match PtrRepr::classify(&expr) {
            Some(PtrRepr::Thin(_)) => {
                debug!("inline PtrMetadata: BV64 — returning 0 (thin pointer)");
                return Some(Expr::bitvec_const(0, POINTER_WIDTH));
            }
            Some(repr) => {
                if let Some(meta) = repr.into_metadata() {
                    debug!("inline PtrMetadata: BV128 metadata half");
                    return Some(meta.into_expr());
                }
                debug!("inline PtrMetadata: widened thin pointer — no metadata to read");
            }
            None => {}
        }
        let sort = expr.sort().clone();
        if let SortInner::Datatype(dt) = sort.inner()
            && let Some(cons) = dt.constructors.first()
            && cons.fields.iter().any(|field| &*field.name == "fld_len")
        {
            debug!("inline PtrMetadata: DT fld_len extraction");
            let dt_name = dt.name.clone();
            return Some(expr.field_select(
                &dt_name,
                "fld_len",
                crate::codegen_ay::types::ptr_sort(),
            ));
        }
    }

    let empty = std::collections::HashSet::new();
    ctx.translate_ptr_metadata(operand, &empty).map(|meta| meta.into_expr())
}

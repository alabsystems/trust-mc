// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Cast expression translation for inline body translators.
//!
//! Extracted from rvalue.rs to stay under the 500-line limit.

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use ay_bindings::Expr;
use rustc_public::mir::{CastKind, LocalDecl, Operand, PointerCoercion};
use tracing::debug;

use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};
use rustc_public::ty::{FloatTy, IntTy, RigidTy, TyKind, UintTy};
use std::collections::HashMap;

use super::super::ChcCtx;
use super::super::codegen_call_cmp_string::float_to_int_saturating::build_float_to_int_saturating_expr;
use super::super::codegen_types::CodegenTypes;
use super::PlaceResolver;
use super::place::inline_operand_to_expr;
use crate::codegen_ay::chc::heap::stack_address::{
    cast_exposes_address, transmute_makes_pointer_from_integer,
};
use crate::codegen_ay::chc::stmt::codegen_stmt_transmute_layout::AggregateTransmute;

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width, ty_to_bv_width, unflatten_bitvec_to_datatype,
};

/// Design 4 B: `concat(N, addr)` for an array-to-slice unsize of a thin
/// operand into a wide slice slot, or `None` to stay on the width cast.
fn inline_pack_array_unsize_len(
    ctx: &ChcCtx<'_, '_>,
    inner: &Expr,
    operand: &Operand,
    target_ty: &rustc_public::ty::Ty,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let target = ctx.resolve_body_ty(*target_ty);
    if PtrSlot::of_sort(&ChcCtx::translate_ty(target)?) != Some(PtrSlot::Fat) {
        return None;
    }
    let src_ty = ctx.resolve_body_ty(operand.ty(locals).ok()?);
    let len = ChcCtx::extract_array_len_from_ref(src_ty)?;
    let PtrRepr::Thin(addr) = PtrRepr::classify(inner)? else {
        return None;
    };
    debug!(len, "inline: array-to-slice unsize packs its length (design 4 B)");
    PtrRepr::from_declared_roles(
        addr,
        Val::of_value(Expr::bitvec_const(len as u128, POINTER_WIDTH)),
    )
    .into_packed()
}

/// The array-to-slice unsize of an array carried as its VALUE (an inline
/// walk's `&[T; N]` is the array's term, not an address): the term has no
/// metadata half to pack, so `N` is recorded against the term
/// (`ChcCtx::inline_array_value_slice_lens`) for the walker's `PtrMetadata`.
/// A term recorded with two different lengths answers nothing.
fn note_array_value_slice_len(
    ctx: &mut ChcCtx<'_, '_>,
    inner: &Expr,
    operand: &Operand,
    target_ty: &rustc_public::ty::Ty,
    locals: &[LocalDecl],
) {
    if !inner.sort().is_array() {
        return;
    }
    let target = ctx.resolve_body_ty(*target_ty);
    let target_is_slice_ptr = match target.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
            matches!(ctx.resolve_body_ty(pointee).kind(), TyKind::RigidTy(RigidTy::Slice(_)))
        }
        _ => false,
    };
    if !target_is_slice_ptr {
        return;
    }
    let Some(src_ty) = operand.ty(locals).ok().map(|ty| ctx.resolve_body_ty(ty)) else { return };
    let Some(len) = ChcCtx::extract_array_len_from_ref(src_ty) else { return };
    let entry = ctx.inline_array_value_slice_lens.entry(inner.clone()).or_insert(Some(len));
    if *entry != Some(len) {
        debug!(len, "inline: one array term unsized at two lengths — no slice length");
        *entry = None;
    } else {
        debug!(len, "inline: array value unsized to a slice — length recorded");
    }
}

pub(super) fn inline_cast_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    kind: &CastKind,
    operand: &Operand,
    target_ty: &rustc_public::ty::Ty,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    #[cfg(all(trust_toolchain, version("1.101")))]
    if matches!(kind, CastKind::BoxDerefTransmute) {
        // This cast additionally requires its input to be a valid Box. This
        // value-only API has no channel for the required validity checks:
        // preserving the pointer bits would silently drop the obligation.
        // The statement walk has a separate checked operation returning both
        // the value and its deferred checks atomically. It must not use this
        // value-only API even when the carrier shape is supported.
        ctx.record_sound_fallback_reason("box_deref_validity_unmodeled");
        return None;
    }
    let scalar_reference =
        operand.ty(locals).ok().is_some_and(|ty| ctx.readonly_scalar_pointee(ty).is_some());
    if matches!(kind, CastKind::Transmute)
        && ctx.readonly_value(operand).is_some()
        && !ctx.inline_walk_operand_is_address(operand)
    {
        // A typed field read does not certify the native bytes of its tuple
        // or closure carrier, even when its logical sort is one address wide.
        ctx.record_sound_fallback_reason("readonly_ref_address_cast_unmodeled");
        return None;
    }
    if scalar_reference
        && !ctx.inline_walk_operand_is_address(operand)
        && (matches!(kind, CastKind::Transmute)
            || matches!(
                ctx.resolve_body_ty(*target_ty).kind(),
                TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..))
            )
            || operand
                .ty(locals)
                .ok()
                .is_some_and(|source| cast_exposes_address(kind, source, *target_ty)))
    {
        ctx.record_sound_fallback_reason("readonly_ref_address_cast_unmodeled");
        return None;
    }
    // A function pointer reified inside a walked body is the target's
    // identity, as on the host (design 3, D1: `call/fn_ptr_targets.rs`). The
    // operand is a zero-sized function item or closure, so its own term says
    // nothing about which function it is.
    if let CastKind::PointerCoercion(
        PointerCoercion::ReifyFnPointer { .. } | PointerCoercion::ClosureFnPointer(_),
    ) = kind
    {
        let ty = ctx.resolve_body_ty(operand.ty(locals).ok()?);
        return Some(ctx.fn_ptr_value_for_reified_ty(ty));
    }
    let numeric_float_cast =
        matches!(kind, CastKind::IntToFloat | CastKind::FloatToInt | CastKind::FloatToFloat);
    let Some(inner) = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals) else {
        if numeric_float_cast {
            ctx.record_sound_fallback_reason("inline_float_operation_unmodeled");
        }
        return None;
    };
    // A pointer-to-integer cast or transmute reads the address (heap/stack_address.rs).
    if let Ok(src_ty) = operand.ty(locals)
        && cast_exposes_address(kind, src_ty, *target_ty)
        && ty_to_bv_width(*target_ty) == Some(64)
    {
        return Some(ctx.ptr_to_int_value(inner));
    }
    // An integer cast or transmuted to a thin pointer takes the one
    // integer-to-pointer rule of the host path (cast_dispatch.rs): the identity
    // whose address it is (`ChcCtx::int_to_ptr_value`), and the object it names
    // invalidated (`invalidate_int_to_ptr_object`: exact for the null object,
    // fail-closed for any other). Passed through as bits, the integer was read
    // as an identity term, so `without_provenance(1 << 40).addr()` came back
    // through the address view as another value.
    let int_to_ptr = match kind {
        CastKind::PointerWithExposedProvenance => operand.ty(locals).is_ok_and(|src_ty| {
            matches!(
                ctx.resolve_body_ty(src_ty).kind(),
                TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))
            )
        }),
        CastKind::Transmute => operand.ty(locals).is_ok_and(|src_ty| {
            transmute_makes_pointer_from_integer(
                kind,
                ctx.resolve_body_ty(src_ty),
                ctx.resolve_body_ty(*target_ty),
            )
        }),
        _ => false,
    };
    if int_to_ptr
        && inner.sort().bitvec_width() == Some(64)
        && ty_to_bv_width(*target_ty) == Some(64)
    {
        let result = ctx.int_to_ptr_value(inner);
        if !ctx.int_lift
            && let Some((obj_id, _offset)) = ctx.split_pointer(&result)
        {
            ctx.invalidate_int_to_ptr_object(obj_id, Some(operand));
            debug!("inline: invalidated obj_valid for an integer-to-pointer cast");
        }
        return Some(result);
    }
    if matches!(kind, CastKind::Transmute)
        && operand
            .ty(locals)
            .ok()
            .is_some_and(|source| ctx.native_dyn_transmute_needs_bytes(source, *target_ty))
    {
        ctx.record_sound_fallback_reason("native_dyn_pointer_bytes_unmodeled");
        return None;
    }
    // A multi-field struct or tuple facing a bitvector is reinterpreted in
    // MEMORY order, or havocked; the unflatten below is declaration-order
    // MSB-first and transposes the words (codegen_stmt_transmute_layout.rs).
    if matches!(kind, CastKind::Transmute)
        && let Ok(src_ty) = operand.ty(locals)
    {
        match ctx.transmute_aggregate_memory_order(&inner, src_ty, *target_ty) {
            AggregateTransmute::NotApplicable => {}
            AggregateTransmute::Precise(reinterpreted) => {
                if let Some(sort) = ChcCtx::translate_ty(ctx.resolve_body_ty(*target_ty))
                    && sort.is_datatype()
                {
                    ctx.declare_datatype_sort_if_needed(&sort);
                }
                return Some(reinterpreted);
            }
            AggregateTransmute::Unsupported(why) => {
                debug!(why, "inline: aggregate transmute layout not modeled; fresh value");
                let sort = ChcCtx::translate_ty(ctx.resolve_body_ty(*target_ty))?;
                let booked = ctx.record_sound_fallback_reason("transmute_layout_fallback");
                return Some(Havoc::booked(
                    booked,
                    crate::codegen_ay::chc::chc_fresh_name("__transmute_layout_nondet"),
                    sort,
                ));
            }
        }
    }
    // Numeric float casts are terminal: an unsupported type, representation
    // or helper result must never reach the integer width-coercion tail below.
    if numeric_float_cast {
        let result = (|| {
            match kind {
                CastKind::IntToFloat => {
                    let source_ty = ctx.resolve_body_ty(operand.ty(locals).ok()?);
                    if !matches!(
                        source_ty.kind(),
                        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))
                    ) || inner.sort().bitvec_width() != ty_to_bv_width(source_ty)
                    {
                        return None;
                    }
                    let target_float_width = match ctx.resolve_body_ty(*target_ty).kind() {
                        TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => 32,
                        TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => 64,
                        _ => return None,
                    };
                    let signed = ty_signedness_shallow(source_ty)?;
                    return crate::codegen_ay::float_arithmetic::int_to_float_bv_pure(
                        inner.clone(),
                        signed,
                        target_float_width,
                    )
                    .or_else(|| {
                        crate::codegen_ay::float_arithmetic::int_to_float_bv(
                            inner,
                            signed,
                            target_float_width,
                        )
                    });
                }
                CastKind::FloatToInt => {
                    let source_ty = ctx.resolve_body_ty(operand.ty(locals).ok()?);
                    if !matches!(source_ty.kind(), TyKind::RigidTy(RigidTy::Float(_)))
                        || inner.sort().bitvec_width() != ty_to_bv_width(source_ty)
                    {
                        return None;
                    }
                    let (width, signed) = match ctx.resolve_body_ty(*target_ty).kind() {
                        TyKind::RigidTy(RigidTy::Int(i)) => (
                            match i {
                                IntTy::I8 => 8,
                                IntTy::I16 => 16,
                                IntTy::I32 => 32,
                                IntTy::I64 => 64,
                                IntTy::I128 => 128,
                                IntTy::Isize => POINTER_WIDTH,
                            },
                            true,
                        ),
                        TyKind::RigidTy(RigidTy::Uint(u)) => (
                            match u {
                                UintTy::U8 => 8,
                                UintTy::U16 => 16,
                                UintTy::U32 => 32,
                                UintTy::U64 => 64,
                                UintTy::U128 => 128,
                                UintTy::Usize => POINTER_WIDTH,
                            },
                            false,
                        ),
                        _ => return None,
                    };
                    return build_float_to_int_saturating_expr(&inner, width, signed).or_else(
                        || {
                            crate::codegen_ay::float_arithmetic::float_to_int_saturating_bv(
                                inner, width, signed,
                            )
                        },
                    );
                }
                CastKind::FloatToFloat => {
                    let source_ty = ctx.resolve_body_ty(operand.ty(locals).ok()?);
                    let target_ty = ctx.resolve_body_ty(*target_ty);
                    // A same-type cast is an exact identity even for a float
                    // format whose numeric conversions are not implemented.
                    // The type equality is essential: equal widths alone do
                    // not justify reinterpreting one numeric type as another.
                    if matches!(source_ty.kind(), TyKind::RigidTy(RigidTy::Float(_)))
                        && source_ty == target_ty
                    {
                        let width = ty_to_bv_width(source_ty)?;
                        return (inner.sort().bitvec_width() == Some(width)).then_some(inner);
                    }
                    let source_width = match source_ty.kind() {
                        TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => 32,
                        TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => 64,
                        _ => return None,
                    };
                    let target_width = match target_ty.kind() {
                        TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => 32,
                        TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => 64,
                        _ => return None,
                    };
                    if inner.sort().bitvec_width() != Some(source_width) {
                        return None;
                    }
                    // Try pure BV first (CHC-safe), then FP theory fallback. Part of #3870.
                    return crate::codegen_ay::float_arithmetic::float_to_float_bv_pure(
                        inner.clone(),
                        source_width,
                        target_width,
                    )
                    .or_else(|| {
                        crate::codegen_ay::float_arithmetic::float_to_float_bv(
                            inner,
                            source_width,
                            target_width,
                        )
                    });
                }
                _ => None,
            }
        })();
        if result.is_none() {
            // Some expression-only callers skip declined assignments. Booking
            // here prevents their stale bindings from yielding a clean verdict.
            ctx.record_sound_fallback_reason("inline_float_operation_unmodeled");
        }
        return result;
    }
    // Design 4 B: the walker's array-to-slice unsize writes the source's
    // compile-time length into the metadata half, as the statement path does.
    // The width coercion below zero-extends the thin operand, which a reader of
    // the wide value takes as length 0.
    if matches!(kind, CastKind::PointerCoercion(PointerCoercion::Unsize))
        && let Some(packed) = inline_pack_array_unsize_len(ctx, &inner, operand, target_ty, locals)
    {
        return Some(packed);
    }
    if matches!(kind, CastKind::PointerCoercion(PointerCoercion::Unsize)) {
        note_array_value_slice_len(ctx, &inner, operand, target_ty, locals);
    }
    if inner.sort().is_bitvec() {
        if let Some(target_sort) = ChcCtx::translate_ty(*target_ty)
            && target_sort.is_datatype()
            && let Some(rebuilt) = unflatten_bitvec_to_datatype(&inner, &target_sort)
        {
            ctx.declare_datatype_sort_if_needed(&target_sort);
            return Some(rebuilt);
        }

        let Some(target_width) = (match target_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(_, _) | RigidTy::Ref(_, _, _)) => {
                ChcCtx::translate_ty(*target_ty).and_then(|sort| sort.bitvec_width())
            }
            _ => ty_to_bv_width(*target_ty),
        }) else {
            return Some(inner);
        };
        if let Some(src_width) = inner.sort().bitvec_width()
            && src_width != target_width
        {
            let signed = operand.ty(locals).ok().and_then(ty_signedness_shallow).unwrap_or(false);
            return Some(coerce_bitvec_width(
                inner,
                target_width,
                SignExtension::for_signedness(signed),
            ));
        }
    }
    // Datatype→BV coercion for pointer casts in inlined bodies.
    if inner.sort().is_datatype()
        && matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)))
    {
        if let Some(p) = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&inner) {
            // A pointer CAST writes this term into the destination local as its
            // datum, so the tag ends at the crossing.
            return Some(p.into_expr());
        }
    }
    Some(inner)
}

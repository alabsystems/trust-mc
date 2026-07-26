// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Cast expression translation for inline body translators.
//!
//! Extracted from rvalue.rs to stay under the 500-line limit.

use ay_bindings::Expr;
use rustc_public::mir::{CastKind, LocalDecl, Operand};
use rustc_public::ty::{FloatTy, IntTy, RigidTy, TyKind, UintTy};
use std::collections::HashMap;

use super::super::ChcCtx;
use super::super::codegen_call_cmp_string::float_to_int_saturating::build_float_to_int_saturating_expr;
use super::super::codegen_types::CodegenTypes;
use super::PlaceResolver;
use super::place::inline_operand_to_expr;

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width, ty_to_bv_width, unflatten_bitvec_to_datatype,
};

pub(super) fn inline_cast_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    kind: &CastKind,
    operand: &Operand,
    target_ty: &rustc_public::ty::Ty,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let inner = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals)?;
    if inner.sort().is_bitvec() {
        match kind {
            CastKind::IntToFloat => {
                let target_float_width = match target_ty.kind() {
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => Some(32u32),
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => Some(64),
                    _ => None,
                };
                if let Some(fw) = target_float_width {
                    let signed =
                        operand.ty(locals).ok().and_then(ty_signedness_shallow).unwrap_or(false);
                    return crate::codegen_ay::float_arithmetic::int_to_float_bv_pure(
                        inner.clone(),
                        signed,
                        fw,
                    )
                    .or_else(|| {
                        crate::codegen_ay::float_arithmetic::int_to_float_bv(inner, signed, fw)
                    });
                }
            }
            CastKind::FloatToInt => {
                let width_signed = match target_ty.kind() {
                    TyKind::RigidTy(RigidTy::Int(i)) => Some(match i {
                        IntTy::I8 => (8u32, true),
                        IntTy::I16 => (16, true),
                        IntTy::I32 => (32, true),
                        IntTy::I64 => (64, true),
                        IntTy::I128 => (128, true),
                        IntTy::Isize => (POINTER_WIDTH, true),
                    }),
                    TyKind::RigidTy(RigidTy::Uint(u)) => Some(match u {
                        UintTy::U8 => (8u32, false),
                        UintTy::U16 => (16, false),
                        UintTy::U32 => (32, false),
                        UintTy::U64 => (64, false),
                        UintTy::U128 => (128, false),
                        UintTy::Usize => (POINTER_WIDTH, false),
                    }),
                    _ => None,
                };
                if let Some((tw, signed)) = width_signed {
                    return build_float_to_int_saturating_expr(&inner, tw, signed).or_else(|| {
                        crate::codegen_ay::float_arithmetic::float_to_int_saturating_bv(
                            inner, tw, signed,
                        )
                    });
                }
            }
            CastKind::FloatToFloat => {
                let src_float_width = match operand.ty(locals).ok().map(|t| t.kind()) {
                    Some(TyKind::RigidTy(RigidTy::Float(FloatTy::F32))) => Some(32u32),
                    Some(TyKind::RigidTy(RigidTy::Float(FloatTy::F64))) => Some(64),
                    _ => None,
                };
                let target_float_width = match target_ty.kind() {
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => Some(32u32),
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => Some(64),
                    _ => None,
                };
                if let (Some(sw), Some(tw)) = (src_float_width, target_float_width) {
                    // Try pure BV first (CHC-safe), then FP theory fallback. Part of #3870.
                    return crate::codegen_ay::float_arithmetic::float_to_float_bv_pure(
                        inner.clone(),
                        sw,
                        tw,
                    )
                    .or_else(|| {
                        crate::codegen_ay::float_arithmetic::float_to_float_bv(inner, sw, tw)
                    });
                }
            }
            _ => {}
        }
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
            return Some(p);
        }
    }
    Some(inner)
}

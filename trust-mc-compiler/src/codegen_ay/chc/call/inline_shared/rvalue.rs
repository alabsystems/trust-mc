// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Rvalue translation for inline body translators, extracted from `inline_shared/mod.rs`.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::{AggregateKind, BinOp, LocalDecl, Operand, ProjectionElem, Rvalue, UnOp};
#[cfg(not(trust_toolchain))]
use rustc_public::mir::{NullOp, RuntimeChecks};
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, TyKind, UintTy};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_expr_signedness::infer_inline_binop_signedness;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_aggregate::inline_aggregate_to_expr;
use super::super::quantifier_encoding::QuantifierEncoding;
use super::place::{inline_operand_to_expr, resolve_place};
use super::rvalue_cast::inline_cast_to_expr;
use super::{PlaceResolver, discriminant};
use crate::codegen_ay::chc::heap::stack_address::is_relational_ptr_op;

use crate::codegen_ay::chc::stmt::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width, ptr_sort, ty_to_bv_width,
};
use crate::rustc_public_bridge::IndexedVal;

/// Translate a MIR Rvalue to a AY Expr within an inline body context.
/// Unified across closure, virtual, and quantifier inline translators.
/// Place resolution is dispatched through `resolver`.
/// Part of #3241.
pub(in crate::codegen_ay) fn inline_rvalue_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    rvalue: &Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
    dest_local: Option<usize>,
) -> Option<Expr> {
    match rvalue {
        Rvalue::BinaryOp(op, lhs, rhs) => {
            if matches!(
                op,
                BinOp::Eq
                    | BinOp::Ne
                    | BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge
                    | BinOp::Cmp
                    | BinOp::Offset
            ) && [lhs, rhs].iter().any(|operand| {
                operand.ty(locals).ok().is_some_and(|ty| ctx.readonly_scalar_pointee(ty).is_some())
                    && !ctx.inline_walk_operand_is_address(operand)
            }) {
                ctx.record_sound_fallback_reason("inline_reference_address_observation_unmodeled");
            }
            let l = inline_operand_to_expr(ctx, lhs, local_exprs, resolver, locals)?;
            let r = inline_operand_to_expr(ctx, rhs, local_exprs, resolver, locals)?;
            let lhs_ty = lhs.ty(locals).ok()?;
            // Part of #4050: route pointer offset before the generic width check.
            if matches!(op, BinOp::Offset) {
                return inline_pointer_offset(ctx, l, r, lhs_ty);
            }
            // Part of #4050: coerce single-field DT wrappers (e.g. UsizeNoHighBit) to BV.
            let l = coerce_dt_wrapper_to_bv(l);
            let r = coerce_dt_wrapper_to_bv(r);
            let int_bv_width = match ty_to_bv_width(lhs_ty) {
                Some(width) => width,
                None if matches!(
                    op,
                    BinOp::Lt
                        | BinOp::Le
                        | BinOp::Ge
                        | BinOp::Gt
                        | BinOp::Cmp
                        | BinOp::Eq
                        | BinOp::Ne
                ) =>
                {
                    // Part of #4030: wide raw-pointer comparisons still use pointer width here.
                    POINTER_WIDTH
                }
                None => return None,
            };
            let is_float = matches!(lhs_ty.kind(), TyKind::RigidTy(RigidTy::Float(_)));
            // Part of #3839: route float BinOps through FP theory instead of BV arithmetic.
            if is_float && l.sort().is_bitvec() {
                return inline_float_binop(*op, l, r, int_bv_width);
            }
            // Relational comparison of raw pointers: unordered across
            // allocations (heap/stack_address.rs).
            let (l, r) = if is_relational_ptr_op(*op)
                && matches!(lhs_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
            {
                ctx.ptr_order_operands(l, r)
            } else {
                (l, r)
            };
            // `==` / `!=` of raw pointers: the fail-closed far pointer
            // observation (heap/stack_address.rs `note_ptr_equality`).
            if matches!(op, BinOp::Eq | BinOp::Ne)
                && matches!(lhs_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
            {
                ctx.note_raw_pointer_equality(&l, &r, None);
            }
            if let Some(result) = try_translate_inline_wide_pointer_binop(*op, &l, &r) {
                return Some(result);
            }
            let signed = infer_inline_binop_signedness(*op, lhs, rhs, locals, dest_local);
            ctx.binop_to_expr(*op, l, r, signed, int_bv_width)
        }
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            // Part of #2440: proper (result, overflow) Datatype tuple, not bare scalar.
            let l = inline_operand_to_expr(ctx, lhs, local_exprs, resolver, locals)?;
            let r = inline_operand_to_expr(ctx, rhs, local_exprs, resolver, locals)?;
            let signed = infer_inline_binop_signedness(*op, lhs, rhs, locals, dest_local);
            let is_signed = signed.unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback_for_binop(
                    *op,
                    "inline_rvalue_to_expr::CheckedBinaryOp",
                )
            });
            let int_bv_width = ty_to_bv_width(lhs.ty(locals).ok()?)?;
            ctx.translate_checked_binop(*op, l, r, is_signed, int_bv_width)
        }
        Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
            translate_inline_ptr_metadata(ctx, operand, local_exprs, resolver, locals)
        }
        Rvalue::UnaryOp(UnOp::Not, operand) => {
            let inner = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals)?;
            if inner.sort().is_bool() {
                Some(inner.not())
            } else if inner.sort().is_bitvec() {
                Some(inner.bvnot())
            } else if inner.sort().is_int() {
                // Int-lifted locals need BV round-trip for bitwise NOT.
                // Part of #3043, #3055, #3243.
                let int_bv_width = ty_to_bv_width(operand.ty(locals).ok()?)?;
                let is_signed =
                    operand.ty(locals).ok().and_then(ty_signedness_shallow).unwrap_or(false);
                let bv_result = inner.int2bv(int_bv_width).bvnot();
                Some(if is_signed { bv_result.bv2int_signed() } else { bv_result.bv2int() })
            } else {
                None
            }
        }
        Rvalue::UnaryOp(UnOp::Neg, operand) => {
            let operand_ty = ctx.resolve_body_ty(operand.ty(locals).ok()?);
            if matches!(operand_ty.kind(), TyKind::RigidTy(RigidTy::Float(_))) {
                let result = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals)
                    .and_then(|inner| {
                        let width = ty_to_bv_width(operand_ty)?;
                        crate::codegen_ay::float_arithmetic::bv_float_neg(inner, width)
                    });
                if result.is_none() {
                    ctx.record_sound_fallback_reason("inline_float_operation_unmodeled");
                }
                return result;
            }
            let inner = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals)?;
            if inner.sort().is_int() {
                Some(inner.int_neg())
            } else if inner.sort().is_bitvec() {
                let w = inner.sort().bitvec_width()?;
                Some(Expr::bitvec_const(0u64, w).bvsub(inner))
            } else {
                None
            }
        }
        Rvalue::Use(operand, ..) => {
            preserve_inline_subslice_metadata_from_operand(ctx, dest_local, operand);
            inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals)
        }
        // Preserve address identity for ref-like rvalues rooted at an existing pointer local.
        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
            if place.ty(locals).ok().is_some_and(|ty| ctx.readonly_scalar_pointee(ty).is_some()) {
                ctx.record_sound_fallback_reason("readonly_ref_carrier_address_unmodeled");
                return None;
            }
            preserve_inline_subslice_metadata_from_place(ctx, dest_local, place.local);
            // The inline walker's expression map is still untyped, so the
            // Address / Transparent distinction is dropped here rather than
            // resolved — see `InlineRefExpr`. The walker's statement executor
            // reads the lane back to tag the destination as address-bound
            // (F2, `inline_walk_guard.rs`).
            let resolved =
                super::place::inline_ref_place_to_expr(ctx, local_exprs, place, resolver, locals);
            if matches!(rvalue, Rvalue::AddressOf(..))
                && matches!(&resolved, Some(super::place::InlineRefExpr::Transparent(_)))
                && !(matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                    && (ctx.inline_walk_local_is_address(place.local)
                        || locals.get(place.local).is_some_and(|decl| {
                            matches!(
                                ctx.resolve_body_ty(decl.ty).kind(),
                                TyKind::RigidTy(RigidTy::RawPtr(..))
                            )
                        })))
            {
                ctx.record_sound_fallback_reason("inline_reference_raw_address_unmodeled");
                return None;
            }
            ctx.last_inline_ref_was_address =
                matches!(resolved, Some(super::place::InlineRefExpr::Address(_)));
            resolved.map(super::place::InlineRefExpr::into_expr)
        }
        Rvalue::CopyForDeref(place) => resolve_place(ctx, local_exprs, place, resolver, locals),
        Rvalue::Discriminant(place) => {
            let current = resolve_place(ctx, local_exprs, place, resolver, locals)?;
            discriminant::inline_discriminant_expr(
                ctx,
                ctx.resolve_body_ty(place.ty(locals).ok()?),
                current,
            )
        }
        Rvalue::Cast(kind, operand, target_ty) => {
            preserve_inline_subslice_metadata_from_operand(ctx, dest_local, operand);
            inline_cast_to_expr(ctx, kind, operand, target_ty, local_exprs, resolver, locals)
        }
        Rvalue::Len(place) => inline_len_to_expr(ctx, place, local_exprs, resolver, locals),
        // Part of #3889: Zero-operand Aggregate for enum unit variants like Option::None.
        // Route through inline_aggregate_to_expr which constructs the Datatype with
        // the correct variant constructor and zero fields.
        Rvalue::Aggregate(kind, operands) if operands.is_empty() => {
            inline_adt_variant_aggregate_to_expr(
                ctx,
                kind,
                operands,
                local_exprs,
                resolver,
                locals,
                dest_local,
            )
            .or_else(|| {
                inline_aggregate_to_expr(
                    ctx,
                    kind,
                    operands,
                    local_exprs,
                    resolver,
                    locals,
                    dest_local,
                )
            })
            .or_else(|| {
                // Part of zst_param fix: ZST aggregates (e.g. `struct Void;`)
                // are encoded as Bool sort, not Datatype. The DT handlers above
                // return None for Bool. Emit the canonical ZST sentinel so
                // downstream fn-ptr calls see populated local_exprs.
                let dest_ty = dest_local.and_then(|l| locals.get(l)).map(|ld| ld.ty)?;
                let sort = ChcCtx::translate_ty(dest_ty)?;
                if sort.is_bool() {
                    debug!("inline: zero-operand Aggregate -> Bool ZST sentinel");
                    Some(Expr::bool_const(true))
                } else {
                    None
                }
            })
        }
        // Part of #3901, #3348: single-payload enum variants such as Some(value),
        // Ok(value), and Err(value) must preserve their constructor when the
        // destination sort is a Datatype. Fall back to passthrough for wrapper
        // structs/newtypes whose destination sort is not Datatype.
        Rvalue::Aggregate(kind, operands) if operands.len() == 1 => {
            inline_adt_variant_aggregate_to_expr(
                ctx,
                kind,
                operands,
                local_exprs,
                resolver,
                locals,
                dest_local,
            )
            .or_else(|| {
                inline_aggregate_to_expr(
                    ctx,
                    kind,
                    operands,
                    local_exprs,
                    resolver,
                    locals,
                    dest_local,
                )
            })
            .or_else(|| {
                // Tuple translation owns its representation/address checks.
                // Its refusal must not become an untyped operand pass-through.
                if matches!(kind, AggregateKind::Tuple) {
                    None
                } else {
                    inline_operand_to_expr(ctx, &operands[0], local_exprs, resolver, locals)
                }
            })
        }
        // Part of #4050/#4163: keep the data pointer expression but preserve raw-pointer len
        // metadata in `subslice_len`.
        Rvalue::Aggregate(AggregateKind::RawPtr(_, _), operands) if !operands.is_empty() => {
            seed_inline_raw_ptr_metadata(ctx, dest_local, operands, local_exprs, resolver, locals);
            let data_expr =
                inline_operand_to_expr(ctx, &operands[0], local_exprs, resolver, locals)?;
            let data_ptr = inline_coerce_to_ptr(data_expr);
            // A data "pointer" that is not a bitvector (an array value a walked
            // body built as a store chain, reached through `slice::from_raw_parts`
            // in std's `contains`) has no address to pack: the walk declines the
            // aggregate. It used to reach `concat` below and panic ("concat
            // requires BitVec sorts"), taking the compilation with it (walker
            // fail-closed review 6 round 2, found by the finding 6 unit test).
            data_ptr.sort().bitvec_width()?;
            // When metadata is usize (fat pointer), construct BV128 = len.concat(data_ptr)
            // so metadata survives array store/load round-trips and pointer casts.
            if operands.len() > 1 {
                if let Ok(meta_ty) = operands[1].ty(locals) {
                    if matches!(meta_ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))) {
                        if let Some(len_expr) =
                            inline_operand_to_expr(ctx, &operands[1], local_exprs, resolver, locals)
                        {
                            let len_bv = coerce_bitvec_width(
                                len_expr,
                                POINTER_WIDTH,
                                SignExtension::ZeroExtend,
                            );
                            debug!("inline RawPtr aggregate: BV128 fat pointer (len ++ data_ptr)");
                            return Some(len_bv.concat(data_ptr));
                        }
                    }
                }
            }
            Some(data_ptr)
        }
        // Part of #3561: Multi-field Aggregate construction for structs/tuples.
        // Translates `SolverState { scopes, scope_len, trail_len, next_var }` etc.
        // into a AY Datatype constructor expression.
        Rvalue::Aggregate(kind, operands) if operands.len() > 1 => {
            inline_adt_variant_aggregate_to_expr(
                ctx,
                kind,
                operands,
                local_exprs,
                resolver,
                locals,
                dest_local,
            )
            .or_else(|| {
                inline_aggregate_to_expr(
                    ctx,
                    kind,
                    operands,
                    local_exprs,
                    resolver,
                    locals,
                    dest_local,
                )
            })
        }
        // Part of #3561: Array initialization [value; count] → AY const_array.
        Rvalue::Repeat(operand, len_const) => {
            let elem = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals)?;
            let _len = len_const.eval_target_usize().ok()?;
            Some(Expr::const_array(crate::codegen_ay::types::ptr_sort(), elem))
        }
        // Part of #3188: NullaryOp runtime-check constants (ub_checks, etc.).
        #[cfg(not(trust_toolchain))]
        Rvalue::NullaryOp(null_op) => match null_op {
            NullOp::RuntimeChecks(RuntimeChecks::UbChecks) => Some(Expr::bool_const(
                crate::rustc_compat::runtime_checks_value(&RuntimeChecks::UbChecks),
            )),
            NullOp::RuntimeChecks(RuntimeChecks::ContractChecks) => Some(Expr::bool_const(true)),
            NullOp::RuntimeChecks(RuntimeChecks::OverflowChecks) => Some(Expr::bool_const(false)),
        },
        // Trust: user-ADT reborrowing has no CHC encoding (see
        // `trust_reborrow`). Unlike the silent `_` arm below, record the
        // fail-close reason before bailing.
        #[cfg(trust_toolchain)]
        Rvalue::Reborrow(..) => {
            ctx.record_reborrow_unsupported("inline_rvalue_to_expr");
            None
        }
        _ => {
            // external enum: Rvalue
            debug!("inline: unsupported rvalue {:?}", rvalue);
            None
        }
    }
}

fn inline_len_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    place: &rustc_public::mir::Place,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    // Part of #3323 Phase 3: enable inlining of functions using Len
    // (e.g., slice::is_empty). For fixed-size arrays [T; N], return
    // compile-time constant.
    let ty = place.ty(locals).ok()?;
    if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = ty.kind() {
        if let Ok(len) = const_len.eval_target_usize() {
            debug!(?place, len, "inline: Rvalue::Len on array — compile-time length");
            return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
        }
    }
    // Part of #3188: Try to resolve Len from Vec/Slice Datatype fld_len.
    // Resolve the place to an expression via the inline resolver, then
    // extract fld_len if the expression has a Datatype sort with that field.
    if let Some(expr) = resolve_place(ctx, local_exprs, place, resolver, locals) {
        use ay_bindings::SortInner;
        let sort = expr.sort();
        if let SortInner::Datatype(dt) = sort.inner() {
            if let Some(ctor) = dt.constructors.first() {
                if ctor.fields.iter().any(|f| &*f.name == "fld_len") {
                    let dt_name = dt.name.clone();
                    debug!(
                        ?place,
                        %dt_name,
                        "inline: Rvalue::Len — extracted fld_len from Datatype"
                    );
                    return Some(expr.field_select(&dt_name, "fld_len", ptr_sort()));
                }
            }
        }
    }
    debug!("inline: Rvalue::Len on non-array type — cannot resolve in inline context");
    None
}

fn inline_adt_variant_aggregate_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    kind: &AggregateKind,
    operands: &[Operand],
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
    dest_local: Option<usize>,
) -> Option<Expr> {
    let AggregateKind::Adt(_, variant, _, _, _) = kind else {
        return None;
    };

    let dest_ty = dest_local.and_then(|l| locals.get(l)).map(|ld| ld.ty)?;
    let sort = ChcCtx::translate_ty(dest_ty)?;

    if operands.is_empty()
        && let AggregateKind::Adt(def, variant, _, _, _) = kind
        && def.kind() == AdtKind::Enum
        && def.variants().iter().all(|variant| variant.fields().is_empty())
        && let Some(width) = sort.bitvec_width()
    {
        let internal_def = rustc_internal::internal(ctx.tcx, *def);
        let variant_idx = InternalVariantIdx::from_usize(variant.to_index());
        let discr = internal_def.discriminant_for_variant(ctx.tcx, variant_idx);
        let discriminant_val = sign_extend_discr_val(discr.val, discr.ty, ctx.tcx, width);
        debug!(
            variant_index = variant.to_index(),
            discriminant_val, width, "inline ADT aggregate: unit enum -> bitvec discriminant"
        );
        return Some(Expr::bitvec_const(discriminant_val, width));
    }

    let dt = sort.datatype_sort()?;
    let cons = dt.constructors.get(variant.to_index())?;

    if cons.fields.len() != operands.len() {
        return None;
    }

    // Translate operands ONCE — `inline_operand_to_expr` declares pending vars.
    let mut operand_exprs = Vec::with_capacity(operands.len());
    for op in operands {
        operand_exprs.push(inline_operand_to_expr(ctx, op, local_exprs, resolver, locals)?);
    }

    // TRANSPARENT WRAPPER PASS-THROUGH — see the twin guard in
    // `inline_aggregate::inline_aggregate_to_expr`. `translate_ty` collapses
    // `MaybeUninit<T>` / `ManuallyDrop<T>` / `#[repr(transparent)]` newtypes
    // onto the PAYLOAD's sort, so the aggregate that builds the wrapper is
    // already holding a value of the destination sort and must hand it back
    // unchanged. Running it through the field loop instead re-wraps it in the
    // payload's own constructor (`AscII_mk(<AscII>)`), an ill-sorted term that
    // only aborts much later, in whatever consumer finally believes the
    // declared field sort (#3312 raw_ptr: `Expr::extract` on a Datatype).
    // A real one-field struct never matches: its field sort is a strict
    // component of its own sort.
    if operand_exprs.len() == 1 && *operand_exprs[0].sort() == sort {
        debug!(dt_name = %dt.name, "inline ADT aggregate: transparent wrapper, passing payload through");
        return operand_exprs.pop();
    }

    let mut field_values = Vec::with_capacity(operands.len());
    for (i, expr) in operand_exprs.into_iter().enumerate() {
        // A datatype-involved sort mismatch declines instead of emitting an
        // ill-sorted constructor that AY's parser rejects (see `ctor_field`).
        let Some(coerced) = super::ctor_field::coerce_inline_ctor_field(expr, &cons.fields[i].sort)
        else {
            ctx.record_aggregate_gap("inline_ctor_field_sort_mismatch");
            return None;
        };
        field_values.push(coerced);
    }

    // Part of #3984: Declare callee-body DT sorts not in caller's state variables.
    ctx.declare_datatype_sort_if_needed(&sort);
    // Declines a field-sort mismatch instead of panicking (see the helper).
    checked_inline_variant_constructor(&dt.name, &cons.name, field_values, sort.clone())
}

/// The constructor application when every field's sort matches the declaration.
///
/// ay ad07c5cc63 checks each argument sort against the datatype declaration, and
/// `datatype_constructor` panics on a mismatch. A field none of the coercions
/// could bring to its declared sort is not a value of this constructor, so the
/// aggregate declines, as it does for an untranslatable operand. The panic took
/// down the whole harness into the `chc_codegen_error` fallback, whose forced
/// counterexample was certified Genuine: expected/derive-bounded-arbitrary/enum.rs
/// (the `BoundedArbitrary` payload of `Enum::B(Vec<T>, usize)` built inside
/// `bounded_any`) FAILED on a program Kani verifies.
pub(in crate::codegen_ay::chc) fn checked_inline_variant_constructor(
    dt_name: &str,
    cons_name: &str,
    field_values: Vec<Expr>,
    sort: ay_bindings::Sort,
) -> Option<Expr> {
    match Expr::try_datatype_constructor(dt_name, cons_name, field_values.clone(), sort) {
        Ok(expr) => Some(expr),
        Err(error) => {
            debug!(
                dt_name,
                cons_name,
                field_sorts = ?field_values.iter().map(|f| f.sort().to_string()).collect::<Vec<_>>(),
                ?error,
                "inline ADT aggregate: field sorts do not match the constructor; declining"
            );
            None
        }
    }
}

// Pointer, fat-pointer, float, and sort-coercion helpers extracted to rvalue_ptr.rs.
use super::rvalue_ptr::{
    coerce_dt_wrapper_to_bv, inline_coerce_to_ptr, inline_float_binop, inline_pointer_offset,
    preserve_inline_subslice_metadata_from_operand, preserve_inline_subslice_metadata_from_place,
    seed_inline_raw_ptr_metadata, translate_inline_ptr_metadata,
    try_translate_inline_wide_pointer_binop,
};

#[cfg(test)]
mod constructor_decline_tests {
    use super::checked_inline_variant_constructor;
    use ay_bindings::{Expr, Sort};

    fn guard_like_sort() -> Sort {
        // `core::array::Guard { array_mut: &mut [MaybeUninit<T>], initialized: usize }`
        // as translate_ty declares it: a BV128 fat pointer and a usize.
        Sort::struct_type(
            "Guard_probe",
            [("array_mut", Sort::bitvec(128)), ("initialized", Sort::bitvec(64))],
        )
    }

    #[test]
    fn matching_field_sorts_build_the_aggregate() {
        let sort = guard_like_sort();
        let fields = vec![Expr::bitvec_const(0u64, 128), Expr::bitvec_const(0u64, 64)];
        let built = checked_inline_variant_constructor(
            "Guard_probe",
            "Guard_probe_mk",
            fields,
            sort.clone(),
        );
        assert!(built.is_some_and(|e| *e.sort() == sort));
    }

    /// The walker hands a reference over as its REFERENT; a memory array where
    /// the constructor declares a fat pointer must decline, not panic in ay.
    #[test]
    fn referent_array_for_fat_pointer_field_declines() {
        let sort = guard_like_sort();
        let referent =
            Expr::var("guard_probe_referent", Sort::array(Sort::bitvec(64), Sort::bitvec(16)));
        let fields = vec![referent, Expr::bitvec_const(0u64, 64)];
        assert!(
            checked_inline_variant_constructor("Guard_probe", "Guard_probe_mk", fields, sort)
                .is_none()
        );
    }
}

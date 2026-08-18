// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Discriminant and ADT variant assignment helpers for inline statement execution.
//!
//! Extracted from statement_exec.rs for 500-line file-size compliance.
//! Part of #4206.

use ay_bindings::{Expr, ExprValue, SortInner};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::{AggregateKind, LocalDecl};
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, TyKind, VariantIdx};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::{
    PlaceResolver, inline_coroutine_discriminant_expr, inline_operand_to_expr, resolve_place,
};
use super::super::stubs_option_helpers::{OptionHelpers, option_value_sort};
use crate::codegen_ay::chc::stmt::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width};
use crate::rustc_public_bridge::IndexedVal;

pub(super) fn try_inline_unit_enum_discriminant_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    resolver: &PlaceResolver<'_>,
    place: &rustc_public::mir::Place,
    local_exprs: &HashMap<usize, Expr>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let current = resolve_place(ctx, local_exprs, place, resolver, locals)?;
    let ty = ctx.resolve_body_ty(place.ty(locals).ok()?);

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Coroutine(..)) => inline_coroutine_discriminant_expr(current),
        TyKind::RigidTy(RigidTy::Adt(def, _))
            if def.kind() == AdtKind::Enum
                && def.variants().iter().all(|variant| variant.fields().is_empty()) =>
        {
            use rustc_public::abi::IntegerType;

            let width = current.sort().bitvec_width()?;
            let is_signed = {
                let int_ty = def.repr().int.unwrap_or(IntegerType::Pointer { is_signed: true });
                matches!(
                    int_ty,
                    IntegerType::Fixed { is_signed: true, .. }
                        | IntegerType::Pointer { is_signed: true }
                )
            };

            Some(match width.cmp(&crate::codegen_ay::types::POINTER_WIDTH) {
                std::cmp::Ordering::Equal => current,
                std::cmp::Ordering::Less if is_signed => {
                    current.sign_extend(crate::codegen_ay::types::POINTER_WIDTH - width)
                }
                std::cmp::Ordering::Less => {
                    current.zero_extend(crate::codegen_ay::types::POINTER_WIDTH - width)
                }
                std::cmp::Ordering::Greater => {
                    current.extract(crate::codegen_ay::types::POINTER_WIDTH - 1, 0)
                }
            })
        }
        // Part of #3994: Multi-variant ADT enums with payload fields.
        // BV-flattened enums are reconstructed as a concatenated BV (tag || payload).
        // Extract the tag from MSB, map to discriminant values via ITE chain.
        // Datatype-encoded enums use is_constructor checks.
        TyKind::RigidTy(RigidTy::Adt(def, _))
            if def.kind() == AdtKind::Enum && def.variants().len() >= 2 =>
        {
            let variants = def.variants();
            let num_variants = variants.len();
            let pw = crate::codegen_ay::types::POINTER_WIDTH;
            let d = |v: u64| Expr::bitvec_const(v, pw);

            let idef = rustc_internal::internal(ctx.tcx, def);
            let discr_for = |i: usize| -> u64 {
                let disc =
                    idef.discriminant_for_variant(ctx.tcx, InternalVariantIdx::from_usize(i));
                crate::codegen_ay::chc::stmt::codegen_stmt_aggregate_adt::sign_extend_discr_val(
                    disc.val, disc.ty, ctx.tcx, pw,
                ) as u64
            };

            // Case A: Datatype-encoded enum -- use is_constructor ITE chain.
            if current.sort().is_datatype() {
                if let Some(dt_name) = current.sort().datatype_name() {
                    let sort_ctor_names: Vec<String> =
                        if let SortInner::Datatype(dt) = current.sort().inner() {
                            dt.constructors.iter().map(|c| c.name.clone()).collect()
                        } else {
                            return None;
                        };

                    // Part of #4290: Short-circuit literal datatype constructors
                    // and ITE-over-constructors to avoid `(is C (C v))` tautology
                    // that AY fails to simplify during PDR projection. The
                    // slice-first stub builds `ite(is_nonempty, Some(x), None)`
                    // for Option<&T>, and the following discriminant extraction
                    // would otherwise emit `ite(is-None(ite-over-ctors), 0, 1)`,
                    // defeating PDR's invariant synthesis on Option<&()>.
                    if let Some(discr) =
                        literal_ctor_discr(&current, dt_name, &sort_ctor_names, &discr_for)
                    {
                        debug!(num_variants, "inline discriminant: literal ctor fast-path (#4290)");
                        return Some(discr);
                    }

                    let last_discr = discr_for(num_variants - 1);
                    let mut result = d(last_discr);
                    for i in (0..num_variants - 1).rev() {
                        let ctor_name = &sort_ctor_names[i];
                        let is_variant = current.clone().is_constructor(dt_name, ctor_name.clone());
                        result = Expr::ite(is_variant, d(discr_for(i)), result);
                    }
                    debug!(
                        num_variants,
                        "inline discriminant: multi-variant Datatype ITE chain (#3994)"
                    );
                    return Some(result);
                }
            }

            // Case B: BV-flattened enum -- tag is in the MSB of the concat'd BV.
            if let Some(total_width) = current.sort().bitvec_width() {
                // enum_tag_bits: 1 bit for <=2 variants, ceil(log2(n)) for more.
                let tag_bits: u32 =
                    if num_variants <= 2 { 1 } else { (num_variants as f64).log2().ceil() as u32 };
                if total_width > tag_bits {
                    let tag = current.extract(total_width - 1, total_width - tag_bits);
                    // 2-variant enum: tag is 1 bit (Bool-like).
                    if num_variants == 2 {
                        let cond = tag.eq(Expr::bitvec_const(1u64, tag_bits));
                        debug!("inline discriminant: BV-flattened 2-variant tag extract (#3994)");
                        return Some(Expr::ite(cond, d(discr_for(1)), d(discr_for(0))));
                    }
                    // 3+ variants: ITE chain on tag value.
                    let last_discr = discr_for(num_variants - 1);
                    let mut result = d(last_discr);
                    for i in (0..num_variants - 1).rev() {
                        let cond = tag.clone().eq(Expr::bitvec_const(i as u64, tag_bits));
                        result = Expr::ite(cond, d(discr_for(i)), result);
                    }
                    debug!(
                        num_variants,
                        tag_bits,
                        total_width,
                        "inline discriminant: BV-flattened multi-variant tag extract (#3994)"
                    );
                    return Some(result);
                }
            }

            // Case C: Bool tag from flattened 2-variant enum (e.g., Option-like).
            if current.sort().is_bool() && num_variants == 2 {
                debug!("inline discriminant: Bool-tagged 2-variant enum (#3994)");
                return Some(Expr::ite(current, d(discr_for(1)), d(discr_for(0))));
            }

            None
        }
        _ => None,
    }
}

pub(super) fn try_inline_adt_variant_assign_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    rvalue: &rustc_public::mir::Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
    dest_local: Option<usize>,
) -> Option<Expr> {
    let rustc_public::mir::Rvalue::Aggregate(AggregateKind::Adt(_, variant, _, _, _), operands) =
        rvalue
    else {
        return None;
    };

    // Part of #3955: resolve body-local type so opaque async destinations
    // produce the correct sort (avoids Coroutine->bv64 mismatch).
    let dest_ty =
        dest_local.and_then(|local| locals.get(local)).map(|decl| ctx.resolve_body_ty(decl.ty))?;
    let sort = ChcCtx::translate_ty(dest_ty)?;

    if operands.is_empty()
        && let rustc_public::mir::Rvalue::Aggregate(AggregateKind::Adt(def, variant, _, _, _), _) =
            rvalue
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
    for operand in operands {
        let Some(expr) = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals) else {
            if let Some(tag_expr) = try_inline_bool_tag_set_discriminant_expr(dest_ty, *variant) {
                debug!(
                    variant_index = variant.to_index(),
                    "inline ADT aggregate: payload unresolved, preserving Bool tag"
                );
                return Some(tag_expr);
            }
            return None;
        };
        operand_exprs.push(expr);
    }

    // TRANSPARENT WRAPPER PASS-THROUGH.
    //
    // `translate_ty` collapses payload-shaped wrappers — `MaybeUninit<T>`,
    // `ManuallyDrop<T>`, `#[repr(transparent)]` newtypes — onto the sort of the
    // PAYLOAD, so the aggregate that BUILDS the wrapper (`_0 =
    // MaybeUninit::<AscII> { value: move _2 }`, whose one operand is already an
    // `AscII`) is holding a value of the destination sort and has to hand it
    // back unchanged. Matching it against the payload's own field list instead
    // re-wraps it as `AscII_mk(<AscII>)`, whose argument sort contradicts the
    // declared `fld_inner: BitVec 8`. Nothing rejects that at construction: it
    // survives until a consumer believes the declared sort — for #3312's
    // `raw_ptr` that is `reinterpret_fixed_layout_expr`, which selects
    // `fld_inner`, gets the datatype straight back from ay's
    // selector-over-constructor fold, and aborts codegen inside
    // `Expr::extract`.
    //
    // A genuine one-field struct or enum variant can never match: its field
    // sort is a strict component of its own sort.
    if operand_exprs.len() == 1 && *operand_exprs[0].sort() == sort {
        debug!(
            dt_name = %dt.name,
            "inline ADT aggregate: transparent wrapper, passing payload through"
        );
        return operand_exprs.pop();
    }

    let mut field_values = Vec::with_capacity(operands.len());
    for (i, expr) in operand_exprs.into_iter().enumerate() {
        let field_sort = &cons.fields[i].sort;
        let coerced = if *expr.sort() == *field_sort {
            expr
        } else if expr.sort().is_bool() && field_sort.is_bitvec() {
            let width = field_sort.bitvec_width()?;
            Expr::ite(expr, Expr::bitvec_const(1u64, width), Expr::bitvec_const(0u64, width))
        } else if expr.sort().is_bitvec() && field_sort.is_bool() {
            let width = expr.sort().bitvec_width()?;
            expr.ne(Expr::bitvec_const(0u64, width))
        } else if expr.sort().is_bitvec() && field_sort.is_bitvec() {
            if let (Some(src_w), Some(dst_w)) =
                (expr.sort().bitvec_width(), field_sort.bitvec_width())
            {
                if src_w != dst_w {
                    coerce_bitvec_width(expr, dst_w, SignExtension::ZeroExtend)
                } else {
                    expr
                }
            } else {
                expr
            }
        } else if expr.sort().is_bool() && field_sort.is_datatype() {
            // Part of #4090: Bool->Datatype coercion for ZST struct fields
            // (e.g., CharTryFromError(()) encoded as Datatype with 1 Bool field).
            // ZST constants translate to Bool(true) but the enum constructor
            // expects the wrapped Datatype sort.
            use crate::codegen_ay::types::coerce_bool_to_unit_datatype;
            if let Some(unit_expr) = coerce_bool_to_unit_datatype(&expr, field_sort) {
                unit_expr
            } else {
                expr
            }
        } else if expr.sort().is_bitvec() && field_sort.is_datatype() {
            // Part of #3984: BV->DT reconstruction for inline aggregate fields.
            // When a callee-body local was BV-flattened but the DT constructor
            // expects a struct-sorted field (e.g., NonCopyWrapper from BV32),
            // reconstruct the struct from the BV bits.
            use crate::codegen_ay::types::unflatten_bitvec_to_datatype;
            if let Some(unflattened) = unflatten_bitvec_to_datatype(&expr, field_sort) {
                unflattened
            } else {
                expr
            }
        } else {
            expr
        };
        field_values.push(coerced);
    }

    // Part of #3984: The DT sort must be declared to Z3 before any
    // is_constructor/field_select/datatype_constructor expressions reference it.
    // Inline body locals are from the callee's MIR, so their DTs are not in the
    // caller's state variables or flattened_local_field_count.
    ctx.declare_datatype_sort_if_needed(&sort);

    Some(Expr::datatype_constructor(&dt.name, &cons.name, field_values, sort.clone()))
}

pub(super) fn try_inline_bool_tag_set_discriminant_expr(
    ty: rustc_public::ty::Ty,
    variant_index: VariantIdx,
) -> Option<Expr> {
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
        return None;
    };
    if def.kind() != AdtKind::Enum {
        return None;
    }
    let variants = def.variants();
    if variants.len() != 2 {
        return None;
    }

    // Match the flattened Option-like Bool convention used by CHC state vars:
    // when one variant carries no payload and the other does, `true` denotes
    // the payload-carrying variant.
    let true_variant =
        if variants[0].fields().is_empty() && !variants[1].fields().is_empty() { 1 } else { 0 };
    let false_variant = 1 - true_variant;
    let ctor_idx = variant_index.to_index();
    if ctor_idx == true_variant {
        Some(Expr::bool_const(true))
    } else if ctor_idx == false_variant {
        Some(Expr::bool_const(false))
    } else {
        None
    }
}

pub(super) fn try_inline_set_discriminant_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    ty: rustc_public::ty::Ty,
    variant_index: VariantIdx,
    current: Option<&Expr>,
) -> Option<Expr> {
    try_inline_option_like_set_discriminant_expr(ctx, ty, variant_index, current)
        .or_else(|| try_inline_bool_tag_set_discriminant_expr(ty, variant_index))
}

fn try_inline_option_like_set_discriminant_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    ty: rustc_public::ty::Ty,
    variant_index: VariantIdx,
    current: Option<&Expr>,
) -> Option<Expr> {
    let ty = ctx.resolve_body_ty(ty);
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
        return None;
    };
    if def.kind() != AdtKind::Enum {
        return None;
    }
    let variants = def.variants();
    if variants.len() != 2 {
        return None;
    }
    let empty_idx = variants.iter().position(|variant| variant.fields().is_empty())?;
    let payload_idx = variants.iter().position(|variant| !variant.fields().is_empty())?;
    if empty_idx == payload_idx {
        return None;
    }

    let option_sort = ChcCtx::translate_ty(ty)?;
    if !option_sort.is_datatype() {
        return None;
    }
    ctx.declare_datatype_sort_if_needed(&option_sort);

    match variant_index.to_index() {
        idx if idx == empty_idx => ctx.make_none_expr_for_option(&option_sort),
        idx if idx == payload_idx => {
            let payload_sort = option_value_sort(&option_sort)?;
            let payload = current
                .cloned()
                .and_then(|expr| ctx.option_unwrap_value_on_some_path(expr))
                .filter(|expr| expr.sort() == &payload_sort)
                .unwrap_or_else(|| {
                    super::super::declare_pending_var(
                        super::super::chc_fresh_name("__inline_set_discriminant_payload"),
                        payload_sort.clone(),
                    )
                });
            ctx.make_some_expr_for_option(payload, &option_sort)
        }
        _ => None,
    }
}

/// Part of #4290: Short-circuit discriminant emission for literal datatype
/// constructors and ITE-over-constructors. Returns `Some(discr)` only when the
/// expression shape guarantees a constant (or cond-tagged constant) discriminant,
/// eliminating `(is C (C v))` tautologies that PDR fails to simplify during
/// projection. Returns `None` for symbolic / mixed / nested shapes so callers
/// fall through to the standard `is_constructor`-based emission.
fn literal_ctor_discr(
    current: &Expr,
    dt_name: &str,
    sort_ctor_names: &[String],
    discr_for: &dyn Fn(usize) -> u64,
) -> Option<Expr> {
    fn classify(value: &ExprValue, dt_name: &str, sort_ctor_names: &[String]) -> Option<usize> {
        if let ExprValue::DatatypeConstructor { datatype_name, constructor_name, .. } = value {
            if datatype_name != dt_name {
                return None;
            }
            sort_ctor_names.iter().position(|n| n == constructor_name)
        } else {
            None
        }
    }

    let pw = crate::codegen_ay::types::POINTER_WIDTH;
    let d = |v: u64| Expr::bitvec_const(v, pw);

    match current.value() {
        ExprValue::DatatypeConstructor { .. } => {
            let idx = classify(current.value(), dt_name, sort_ctor_names)?;
            Some(d(discr_for(idx)))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_idx = classify(then_expr.value(), dt_name, sort_ctor_names)?;
            let else_idx = classify(else_expr.value(), dt_name, sort_ctor_names)?;
            if then_idx == else_idx {
                return Some(d(discr_for(then_idx)));
            }
            Some(Expr::ite(cond.clone(), d(discr_for(then_idx)), d(discr_for(else_idx))))
        }
        _ => None,
    }
}

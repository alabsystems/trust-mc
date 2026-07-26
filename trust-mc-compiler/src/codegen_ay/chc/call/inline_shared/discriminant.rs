// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline discriminant extraction helpers.
//!
//! Part of #3886: nested inline bodies must support enum discriminants, not
//! just coroutine discriminants, so destructor assertions like
//! `self.0.is_some()` remain reachable on cleanup paths.

use ay_bindings::{Expr, ExprValue, SortInner};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};

use super::super::ChcCtx;
use super::inline_coroutine_discriminant_expr;
use crate::codegen_ay::chc::decl::codegen_decl_state_vars_enum_layout::unit_aware_multi_ctor_enum_layout;
use crate::codegen_ay::chc::stmt::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::POINTER_WIDTH;

pub(in crate::codegen_ay) fn inline_discriminant_expr(
    ctx: &mut ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
    value: Expr,
) -> Option<Expr> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Coroutine(..)) => inline_coroutine_discriminant_expr(value),
        TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Enum => {
            translate_enum_discriminant(ctx, def, ty, value)
        }
        _ => Some(Expr::bitvec_const(0u64, POINTER_WIDTH)),
    }
}

fn translate_enum_discriminant(
    ctx: &mut ChcCtx<'_, '_>,
    def: rustc_public::ty::AdtDef,
    ty: rustc_public::ty::Ty,
    value: Expr,
) -> Option<Expr> {
    let variants = def.variants();
    if variants.is_empty() {
        return Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
    }
    if variants.len() == 1 {
        return Some(enum_discriminant_const(ctx, def, 0));
    }

    if variants.iter().all(|variant| variant.fields().is_empty()) {
        return normalize_enum_scalar(def, value);
    }

    if variants.len() == 2 {
        let v0_fields = variants[0].fields().len();
        let v1_fields = variants[1].fields().len();

        if (v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0) {
            let payload_idx = if v0_fields > 0 { 0 } else { 1 };
            let empty_idx = 1 - payload_idx;
            let value_sort = value.sort().clone();

            // Part of #4290: Short-circuit literal Option-like constructors and
            // ITE-over-constructors to avoid `(is C (C v))` tautology that AY
            // fails to simplify during PDR projection. Emits the discriminant
            // as a constant (or cond-tagged constant) when the value shape is
            // known statically.
            if let SortInner::Datatype(dt) = value_sort.inner() {
                let dt_name = dt.name.clone();
                let payload_ctor_name =
                    dt.constructors.iter().find(|c| !c.fields.is_empty()).map(|c| c.name.clone());
                if let Some(payload_ctor_name) = payload_ctor_name {
                    if let Some(discr) = literal_option_ctor_discr(
                        ctx,
                        def,
                        value.value(),
                        &dt_name,
                        &payload_ctor_name,
                        payload_idx,
                        empty_idx,
                    ) {
                        return Some(discr);
                    }
                }
            }

            let has_payload = match value_sort.inner() {
                SortInner::Datatype(dt) => {
                    let dt_name = dt.name.clone();
                    let is_struct = dt.constructors.len() == 1
                        && dt.constructors[0].fields.len() == 2
                        && dt.constructors[0].fields[0].name == "is_some";
                    if is_struct {
                        value.field_select(&dt_name, "is_some", ay_bindings::Sort::bool())
                    } else {
                        let ctor_name = dt
                            .constructors
                            .iter()
                            .find(|ctor| !ctor.fields.is_empty())?
                            .name
                            .clone();
                        value.is_constructor(&dt_name, ctor_name)
                    }
                }
                _ if value_sort.is_bool() => value,
                _ => {
                    let width = value_sort.bitvec_width()?;
                    value.ne(Expr::bitvec_const(0u64, width))
                }
            };
            return Some(Expr::ite(
                has_payload,
                enum_discriminant_const(ctx, def, payload_idx),
                enum_discriminant_const(ctx, def, empty_idx),
            ));
        }

        if value.sort().is_bool() {
            return Some(Expr::ite(
                value,
                enum_discriminant_const(ctx, def, 1),
                enum_discriminant_const(ctx, def, 0),
            ));
        }
    }

    if let SortInner::Datatype(dt) = value.sort().inner() {
        let dt_name = dt.name.clone();
        let last_idx = variants.len() - 1;
        let mut result = enum_discriminant_const(ctx, def, last_idx);
        for idx in (0..last_idx).rev() {
            let ctor_name = dt.constructors.get(idx)?.name.clone();
            let is_variant = value.clone().is_constructor(&dt_name, ctor_name);
            result = Expr::ite(is_variant, enum_discriminant_const(ctx, def, idx), result);
        }
        return Some(result);
    }

    // Part of #3994: BV-flattened multi-ctor enum discriminant extraction.
    // When the value is a concatenated BV (tag ++ payload), extract the high
    // tag bits and map them to discriminant values via an ITE chain.
    // Without this, normalize_enum_scalar treats the whole BV (including
    // payload bits) as a discriminant, producing wrong comparisons in
    // inlined PartialEq::eq bodies.
    if value.sort().is_bitvec() {
        if let Some((layout, _)) = unit_aware_multi_ctor_enum_layout(ctx, ty) {
            let total_width = value.sort().bitvec_width()?;
            let tag_bits = layout.tag_bits;
            let tag = if total_width == tag_bits {
                value
            } else {
                value.extract(total_width - 1, total_width - tag_bits)
            };
            let last_idx = layout.num_constructors - 1;
            let mut result = enum_discriminant_const(ctx, def, last_idx);
            for idx in (0..last_idx).rev() {
                let cond = tag.clone().eq(Expr::bitvec_const(idx as u64, tag_bits));
                result = Expr::ite(cond, enum_discriminant_const(ctx, def, idx), result);
            }
            return Some(result);
        }
    }

    normalize_enum_scalar(def, value)
}

fn enum_discriminant_const(
    ctx: &ChcCtx<'_, '_>,
    def: rustc_public::ty::AdtDef,
    variant_idx: usize,
) -> Expr {
    let internal_def = rustc_internal::internal(ctx.tcx, def);
    let discr =
        internal_def.discriminant_for_variant(ctx.tcx, InternalVariantIdx::from_usize(variant_idx));
    Expr::bitvec_const(
        sign_extend_discr_val(discr.val, discr.ty, ctx.tcx, POINTER_WIDTH),
        POINTER_WIDTH,
    )
}

fn normalize_enum_scalar(def: rustc_public::ty::AdtDef, value: Expr) -> Option<Expr> {
    use rustc_public::abi::IntegerType;

    let width = value.sort().bitvec_width()?;
    let is_signed = {
        let int_ty = def.repr().int.unwrap_or(IntegerType::Pointer { is_signed: true });
        matches!(
            int_ty,
            IntegerType::Fixed { is_signed: true, .. } | IntegerType::Pointer { is_signed: true }
        )
    };

    Some(match width.cmp(&POINTER_WIDTH) {
        std::cmp::Ordering::Equal => value,
        std::cmp::Ordering::Less if is_signed => value.sign_extend(POINTER_WIDTH - width),
        std::cmp::Ordering::Less => value.zero_extend(POINTER_WIDTH - width),
        std::cmp::Ordering::Greater => value.extract(POINTER_WIDTH - 1, 0),
    })
}

/// Part of #4290: Short-circuit discriminant emission for literal Option-like
/// constructors and ITE-over-constructors. Returns `Some(discr)` only when the
/// expression shape guarantees a constant (or cond-tagged constant) discriminant,
/// eliminating `(is C (C v))` tautologies that PDR fails to simplify during
/// projection. Returns `None` for symbolic / mixed / nested shapes so callers
/// fall through to the standard `is_constructor`-based emission.
fn literal_option_ctor_discr(
    ctx: &mut ChcCtx<'_, '_>,
    def: rustc_public::ty::AdtDef,
    value: &ExprValue,
    dt_name: &str,
    payload_ctor_name: &str,
    payload_idx: usize,
    empty_idx: usize,
) -> Option<Expr> {
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
            Some(enum_discriminant_const(ctx, def, idx))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_idx =
                classify(then_expr.value(), dt_name, payload_ctor_name, payload_idx, empty_idx)?;
            let else_idx =
                classify(else_expr.value(), dt_name, payload_ctor_name, payload_idx, empty_idx)?;
            if then_idx == else_idx {
                return Some(enum_discriminant_const(ctx, def, then_idx));
            }
            Some(Expr::ite(
                cond.clone(),
                enum_discriminant_const(ctx, def, then_idx),
                enum_discriminant_const(ctx, def, else_idx),
            ))
        }
        _ => None,
    }
}

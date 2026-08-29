// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! RangeBounds::contains stub for CHC codegen.
//!
//! Intercepts `<Range<T> as RangeBounds<T>>::contains` and similar calls,
//! replacing the `P_inf_` uninterpreted function with a direct BV comparison.
//! Without this stub, PDR must synthesize what `contains(ptr, ptr)` means
//! from two opaque BV64 pointers — which it typically cannot, causing UNKNOWN.
//!
//! Part of #2183: OverApproximation CTREX reduction, Strategy 2 Tier E.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_rules::CodegenRules;
use crate::codegen_ay::shared::SignednessFallbackKind;

/// Detect if a callee path is a `RangeBounds::contains` call.
///
/// Matches patterns like:
/// - `std::ops::RangeBounds::contains`
/// - `<std::ops::Range<T> as std::ops::RangeBounds<T>>::contains`
/// - `<core::ops::range::RangeInclusive<T> as ...>::contains`
pub(in crate::codegen_ay::chc) fn detect_range_contains(path: &str) -> bool {
    // Must contain "contains" as the method name
    if !path.ends_with("::contains") && !path.contains("::contains<") {
        return false;
    }
    // Must be on a RangeBounds-related type.
    //
    // The `RangeInclusive` arm closes a handler-boundary gap: the MIR inline
    // pass REFUSES to inline `RangeInclusive::contains`
    // (`handler_boundaries::is_handler_backed_range_contains`) precisely so this
    // handler can lower it in value semantics — but the inherent method's
    // monomorphized path is `std::ops::RangeInclusive::<Idx>::contains`, which
    // matches neither "RangeBounds" nor the fully-qualified "ops::range::Range".
    // The call therefore reached no handler at all and fell through to a fresh
    // symbolic bool. This predicate now accepts exactly the set the inline pass
    // preserves for it.
    path.contains("RangeBounds")
        || path.contains("RangeInclusive")
        || path.contains("ops::range::Range")
}

/// Whether the range is inclusive (RangeInclusive) vs exclusive (Range).
///
/// Checks both the callee path and the receiver type. The callee path may be
/// the trait method `std::ops::RangeBounds::contains` which doesn't indicate
/// inclusivity. Fall back to checking the receiver argument type.
fn is_range_inclusive_from_args(
    path: &str,
    ctx: &ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};

    if path.contains("RangeInclusive") {
        return true;
    }
    // Part of #3470: Check receiver type for RangeInclusive.
    // When the callee is the trait method `RangeBounds::contains`, the path
    // doesn't contain "RangeInclusive". Check the first argument's type
    // (which is &RangeInclusive<T> or &Range<T>).
    if let Some(arg) = args.first() {
        if let Ok(arg_ty) = arg.ty(ctx.body.locals()) {
            let inner_ty = match arg_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some(inner),
                _ => None,
            };
            if let Some(inner) = inner_ty {
                if let TyKind::RigidTy(RigidTy::Adt(def, _)) = inner.kind() {
                    if def.trimmed_name().contains("RangeInclusive") {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Try to codegen a `RangeBounds::contains` call as a direct BV/Int comparison.
///
/// For `Range<T>::contains(&self, &item)`: `start <= item && item < end`
/// For `RangeInclusive<T>::contains(&self, &item)`:
/// `start <= item && item <= end && !exhausted`
///
/// The `!exhausted` conjunct is the `RangeBounds for RangeInclusive` end bound:
/// an exhausted `RangeInclusive` reports `Excluded(&end)`, so `(0..=0)` that has
/// been iterated to completion does NOT contain 0. Mirrors the BMC lowering in
/// `statement/dispatch/array_cmp/range_contains.rs`.
pub(in crate::codegen_ay::chc) fn try_codegen_range_contains(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    callee_path: &str,
) -> bool {
    let dest_local: usize = dcx.destination.local;
    let modified_locals = dcx.modified_locals;
    let inclusive = is_range_inclusive_from_args(callee_path, ctx, dcx.args);

    // Strategy: resolve the range's start/end fields and the item value.
    // The range is passed as &Range<T> (args[0]) and item as &T (args[1]).
    //
    // For flattened Range locals: find the underlying local via ref_targets,
    // then read the two consecutive state variables (fld0=start, fld1=end).
    // For Datatype Range: extract fld_start and fld_end.
    // For the item: use resolve_ref_or_const_referent.

    let (start_expr, end_expr, exhausted_expr) = match resolve_range_fields(ctx, dcx) {
        Some(fields) => fields,
        None => {
            debug!(
                bb_idx = dcx.bb_idx,
                "range_contains: could not resolve range fields, falling through"
            );
            return false;
        }
    };

    let item_expr = match ctx.resolve_ref_or_const_referent(&dcx.args[1], modified_locals) {
        Some(expr) => expr,
        None => {
            debug!(bb_idx = dcx.bb_idx, "range_contains: could not resolve item, falling through");
            return false;
        }
    };

    // Determine signedness from the item type.
    let is_signed = if item_expr.sort().is_bitvec() {
        super::super::codegen_expr_signedness::arg_signedness_or_fallback(
            &dcx.args[1],
            ctx.body.locals(),
            "range_contains",
            SignednessFallbackKind::Comparison,
        )
    } else {
        false
    };

    // Build: start <= item
    let lower_bound = build_le(&start_expr, &item_expr, is_signed);
    // Build: item < end (exclusive) or item <= end (inclusive)
    let upper_bound = if inclusive {
        build_le(&item_expr, &end_expr, is_signed)
    } else {
        build_lt(&item_expr, &end_expr, is_signed)
    };

    let result = match (lower_bound, upper_bound) {
        (Some(lower), Some(upper)) => lower.and(upper),
        (Some(bound), None) | (None, Some(bound)) => bound,
        (None, None) => {
            debug!(
                bb_idx = dcx.bb_idx,
                "range_contains: could not build comparison, falling through"
            );
            return false;
        }
    };

    // `RangeInclusive` carries an `exhausted` flag; once the iterator has run
    // past the end the range reports an EXCLUDED end bound and contains nothing
    // at `end`. Without this conjunct the lowering over-approximates
    // `contains` on a consumed range.
    let result = match exhausted_expr {
        Some(exhausted) if inclusive && exhausted.sort().is_bool() => result.and(exhausted.not()),
        _ => result,
    };

    // Constrain destination to the boolean result.
    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        let eq = ctx.make_coerced_eq_constraint(
            &dest_var,
            result,
            dest_var.sort(),
            dest_local,
            "range_contains",
        );
        let extra: Vec<Expr> = eq.into_iter().collect();
        let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            extra,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            inclusive, "range_contains: emitted direct BV comparison (Part of #2183)"
        );
        true
    } else {
        false
    }
}

/// Resolve the Range's start, end and (for `RangeInclusive`) `exhausted`
/// fields from the first argument.
///
/// Handles two cases:
/// 1. Flattened Range local: args[0] is a reference to a local that has been
///    flattened into consecutive state variables (start at idx, end at idx+1,
///    and for `RangeInclusive` `exhausted` at idx+2).
/// 2. Datatype Range: args[0] resolves to a Datatype with
///    fld_start/fld_end (+ optional fld_exhausted).
fn resolve_range_fields(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<(Expr, Expr, Option<Expr>)> {
    let modified_locals = dcx.modified_locals;

    // Try flattened Range first: find the underlying local via ref_targets.
    //
    // The `flattened_tuple_locals` guard is load-bearing: `base_idx + 1` is the
    // NEXT LOCAL's slot unless this local really was decomposed into consecutive
    // per-field slots. Without the guard an unflattened (single Datatype slot)
    // range read a neighbouring local as its `end` bound.
    if let Some(range_local) = resolve_ref_local(&dcx.args[0], ctx)
        && ctx.flatten.flattened_tuple_locals.contains(&range_local)
    {
        let base_idx = ctx.state_var_mgr.try_state_idx_for_local(range_local)?;
        // Flattened Range has two consecutive state vars: start at base_idx, end at base_idx+1.
        let state_vars = &ctx.state_var_mgr.output_state_vars;
        if base_idx + 1 < state_vars.len() {
            let field_count =
                ctx.flatten.flattened_local_field_count.get(&range_local).copied().unwrap_or(2);
            let use_out = modified_locals.contains(&range_local);
            let slot = |idx: usize| -> Option<Expr> {
                let vars = if use_out {
                    &ctx.state_var_mgr.output_state_vars
                } else {
                    &ctx.state_var_mgr.state_vars
                };
                vars.get(idx).map(|(name, sort)| Expr::var(&**name, sort.clone()))
            };

            let start = slot(base_idx)?;
            let end = slot(base_idx + 1)?;
            // `RangeInclusive<T>` for scalar `T` flattens to exactly 3 slots
            // whose third is the Bool `exhausted` flag. Any other shape (a
            // `Range` of a struct element, say) can also put a Bool leaf at
            // slot 2 without it meaning "exhausted", so the local's own TYPE
            // has to say so.
            let exhausted = if field_count == 3 && local_ty_is_range_inclusive(ctx, range_local) {
                slot(base_idx + 2).filter(|e| e.sort().is_bool())
            } else {
                None
            };

            debug!(
                range_local,
                base_idx,
                field_count,
                has_exhausted = exhausted.is_some(),
                "range_contains: resolved flattened Range fields"
            );
            return Some((start, end, exhausted));
        }
    }

    // Try Datatype resolution: resolve the reference and extract fields.
    if let Some(range_expr) = ctx.resolve_ref_or_const_referent(&dcx.args[0], modified_locals)
        && let ay_bindings::SortInner::Datatype(dt) = range_expr.sort().inner()
        && let Some(cons) = dt.constructors.first()
    {
        let field = |name: &str| cons.fields.iter().find(|f| f.name == name).cloned();
        if let (Some(start_field), Some(end_field)) = (field("fld_start"), field("fld_end")) {
            let dt_name = dt.name.clone();
            let start = range_expr.clone().field_select(
                &dt_name,
                &start_field.name,
                start_field.sort.clone(),
            );
            let end =
                range_expr.clone().field_select(&dt_name, &end_field.name, end_field.sort.clone());
            // `RangeInclusive_T` declares a third Bool field `fld_exhausted`.
            let exhausted = field("fld_exhausted")
                .filter(|f| f.sort.is_bool())
                .map(|f| range_expr.clone().field_select(&dt_name, &f.name, f.sort.clone()));
            debug!(
                has_exhausted = exhausted.is_some(),
                "range_contains: resolved Datatype Range fields ({})", dt_name
            );
            return Some((start, end, exhausted));
        }
    }

    None
}

/// Whether a MIR local's own type is `RangeInclusive<_>` — the only shape whose
/// flattened slot 2 is the `exhausted` flag.
fn local_ty_is_range_inclusive(ctx: &ChcCtx<'_, '_>, local: usize) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};

    let Some(decl) = ctx.body.locals().get(local) else { return false };
    matches!(
        decl.ty.kind(),
        TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name().contains("RangeInclusive")
    )
}

/// Resolve a reference operand to the underlying MIR local index.
fn resolve_ref_local(arg: &rustc_public::mir::Operand, ctx: &ChcCtx<'_, '_>) -> Option<usize> {
    match arg {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            // The operand is a local — check if it's a reference to another local.
            ctx.ref_resolution.ref_targets.get(&place.local).map(|t| t.local)
        }
        _ => None,
    }
}

/// Build a `<=` comparison for BV or Int sorts.
fn build_le(lhs: &Expr, rhs: &Expr, is_signed: bool) -> Option<Expr> {
    if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
        Some(if is_signed {
            lhs.clone().bvsle(rhs.clone())
        } else {
            lhs.clone().bvule(rhs.clone())
        })
    } else if lhs.sort().is_int() && rhs.sort().is_int() {
        Some(lhs.clone().int_le(rhs.clone()))
    } else {
        None
    }
}

/// Build a `<` comparison for BV or Int sorts.
fn build_lt(lhs: &Expr, rhs: &Expr, is_signed: bool) -> Option<Expr> {
    if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
        Some(if is_signed {
            lhs.clone().bvslt(rhs.clone())
        } else {
            lhs.clone().bvult(rhs.clone())
        })
    } else if lhs.sort().is_int() && rhs.sort().is_int() {
        Some(lhs.clone().int_lt(rhs.clone()))
    } else {
        None
    }
}

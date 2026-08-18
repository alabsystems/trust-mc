// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Raw-pointer ordering and provenance recovery helpers.
//!
//! Extracted from `cmp_handlers.rs` — Part of #4142.
//! These helpers implement raw-pointer PartialEq/PartialOrd/Ord
//! comparison semantics, including wide-pointer (BV128) decomposition
//! and MIR provenance tracing for address key recovery.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::super::ChcCtx;
use super::super::codegen_call_misc::CallMisc;

/// Returns `true` if the operand resolves to a raw pointer (or a reference
/// wrapping a raw pointer), making it eligible for raw-pointer comparison
/// semantics instead of the general primitive dispatcher.
pub(super) fn operand_is_raw_pointer_like(
    operand: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    fn ty_is_raw_pointer_like(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_raw_pointer_like(inner),
            _ => false,
        }
    }

    // Guard: operand.ty() panics on out-of-bounds locals (e.g., bogus test args).
    let local_idx = match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        Operand::Constant(_) => return false,
    };
    if local_idx >= locals.len() {
        return false;
    }
    operand.ty(locals).ok().is_some_and(ty_is_raw_pointer_like)
}

/// Resolve a raw-pointer comparison operand to its SMT expression, peeling
/// reference layers as needed (`&*const T`, `&&*const T`).
pub(super) fn resolve_raw_pointer_cmp_operand(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let ty = operand.ty(ctx.body.locals()).ok()?;
    match ty.kind() {
        // Part of #4030 D3: `<&A as PartialOrd<&B>>::lt` blanket impl passes
        // `&&*const T`; peel both ref levels to recover the raw pointer value.
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner2, _))
                if matches!(inner2.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))) =>
        {
            // resolve_ref_or_const_referent peels one ref, then try_resolve_local
            // recovers the raw pointer value from the second ref's target.
            ctx.resolve_ref_or_const_referent(operand, modified_locals)
        }
        // `cmp(&ptr, &other)` passes `&*const T`; peel that outer reference to
        // recover the raw pointer value, but do not chase a by-value raw pointer
        // through `ref_targets` to its pointee.
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::RawPtr(..))) =>
        {
            ctx.resolve_ref_operand(operand, modified_locals)
                .or_else(|| ctx.translate_operand_with_modified(operand, modified_locals))
        }
        TyKind::RigidTy(RigidTy::RawPtr(..)) => {
            ctx.translate_operand_with_modified(operand, modified_locals)
        }
        _ => ctx.resolve_ref_or_const_referent(operand, modified_locals),
    }
}

/// Build a three-way comparison expression (`-1` / `0` / `+1` as BV32) for
/// two raw-pointer operands, decomposing wide pointers into (addr, metadata).
pub(super) fn raw_pointer_cmp_expr_with_operands(
    ctx: &mut ChcCtx<'_, '_>,
    lhs_expr: &Expr,
    rhs_expr: &Expr,
    lhs_operand: &Operand,
    rhs_operand: &Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let (lhs_ptr, lhs_meta) =
        raw_pointer_order_components_from_operand(ctx, lhs_operand, lhs_expr, modified_locals)?;
    let (rhs_ptr, rhs_meta) =
        raw_pointer_order_components_from_operand(ctx, rhs_operand, rhs_expr, modified_locals)?;
    raw_pointer_cmp_expr_from_components(lhs_ptr, lhs_meta, rhs_ptr, rhs_meta)
}

/// Build a boolean ordering predicate (`lt`, `le`, `gt`, `ge`) from a
/// three-way raw-pointer comparison result.
pub(super) fn raw_pointer_ord_expr_with_operands(
    ctx: &mut ChcCtx<'_, '_>,
    lhs_expr: &Expr,
    rhs_expr: &Expr,
    lhs_operand: &Operand,
    rhs_operand: &Operand,
    method: &str,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let cmp = raw_pointer_cmp_expr_with_operands(
        ctx,
        lhs_expr,
        rhs_expr,
        lhs_operand,
        rhs_operand,
        modified_locals,
    )?;
    let less = Expr::bitvec_const(-1i128, 32);
    let greater = Expr::bitvec_const(1, 32);
    Some(match method {
        "lt" => cmp.eq(less),
        "le" => cmp.ne(greater),
        "gt" => cmp.eq(greater),
        "ge" => cmp.ne(less),
        _ => return None,
    })
}

fn raw_pointer_order_components_from_operand(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    expr: &Expr,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<(Loc, Option<Val>)> {
    if let Some((addr, metadata)) =
        resolve_raw_pointer_order_key_from_operand(ctx, operand, modified_locals)
    {
        return Some((addr, metadata));
    }
    raw_pointer_order_components(expr)
}

fn resolve_raw_pointer_order_key_from_operand(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<(Loc, Option<Val>)> {
    let (source_place, raw_ptr_operand) = resolve_raw_pointer_source_place(ctx, operand, 8)?;
    // `translate_ref_to_address` is address-of on a place — one of the two
    // functions that MINT addresses in this encoder — and as of wave 11 it
    // says so in its return type, so this site no longer re-tags.
    // `translate_ptr_metadata` already hands back a `Val`.
    let addr = ctx.translate_ref_to_address(&source_place, modified_locals)?;
    let metadata = if raw_pointer_operand_has_metadata(&raw_ptr_operand, ctx.body.locals()) {
        ctx.translate_ptr_metadata(&raw_ptr_operand, modified_locals)
    } else {
        None
    };
    Some((addr, metadata))
}

fn resolve_raw_pointer_source_place(
    ctx: &ChcCtx<'_, '_>,
    operand: &Operand,
    depth_remaining: usize,
) -> Option<(Place, Operand)> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    if !place.projection.is_empty() || depth_remaining == 0 {
        return None;
    }

    let ty = place.ty(ctx.body.locals()).ok()?;
    let direct_raw_ptr_operand = matches!(ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
        .then(|| Operand::Copy(Place { local: place.local, projection: Vec::new() }));

    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if lhs.local != place.local || !lhs.projection.is_empty() {
                continue;
            }

            match rhs {
                Rvalue::Ref(_, _, source) | Rvalue::AddressOf(_, source) => {
                    if let Some(raw_ptr_operand) = direct_raw_ptr_operand.clone() {
                        return Some((source.clone(), raw_ptr_operand));
                    }
                    if source.projection.is_empty() {
                        return resolve_raw_pointer_source_place(
                            ctx,
                            &Operand::Copy(source.clone()),
                            depth_remaining - 1,
                        );
                    }
                }
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                | Rvalue::CopyForDeref(src)
                    if src.projection.is_empty() =>
                {
                    let (source_place, traced_raw_ptr_operand) = resolve_raw_pointer_source_place(
                        ctx,
                        &Operand::Copy(src.clone()),
                        depth_remaining - 1,
                    )?;
                    return Some((
                        source_place,
                        direct_raw_ptr_operand.unwrap_or(traced_raw_ptr_operand),
                    ));
                }
                _ => {}
            }
        }
    }

    if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&place.local) {
        let target_place =
            Place { local: ref_target.local, projection: ref_target.projections.clone() };
        if target_place.projection.is_empty() {
            let traced = resolve_raw_pointer_source_place(
                ctx,
                &Operand::Copy(target_place.clone()),
                depth_remaining - 1,
            );
            return match (traced, direct_raw_ptr_operand) {
                (Some((source_place, _traced_raw_ptr_operand)), Some(raw_ptr_operand)) => {
                    Some((source_place, raw_ptr_operand))
                }
                (Some((source_place, traced_raw_ptr_operand)), None) => {
                    Some((source_place, traced_raw_ptr_operand))
                }
                (None, Some(raw_ptr_operand)) => Some((target_place, raw_ptr_operand)),
                (None, None) => None,
            };
        }
        // Part of #4030: call-forwarded raw pointers often preserve their
        // precise provenance as projected ref_targets. Keep that place intact
        // so translate_ref_to_address() can recover the canonical address key.
        if let Some(raw_ptr_operand) = direct_raw_ptr_operand {
            return Some((target_place, raw_ptr_operand));
        }
        let bare_target =
            Operand::Copy(Place { local: target_place.local, projection: Vec::new() });
        let (_, traced_raw_ptr_operand) =
            resolve_raw_pointer_source_place(ctx, &bare_target, depth_remaining - 1)?;
        return Some((target_place, traced_raw_ptr_operand));
    }

    for bb in &ctx.body.blocks {
        if let TerminatorKind::Call { destination, .. } = &bb.terminator.kind
            && destination.local == place.local
            && destination.projection.is_empty()
        {
            // Part of #4030: call-produced raw-pointer locals are not reliably
            // traceable to a single source place. `max` and `clamp` can return
            // a non-first operand, so aliasing the result to `args.first()`
            // fabricates the wrong address key and turns real helper semantics
            // into genuine CTREX. Fall back to the call result expression for
            // these locals instead of inventing provenance here.
            return None;
        }
    }

    None
}

fn raw_pointer_operand_has_metadata(
    operand: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    let Ok(mut ty) = operand.ty(locals) else {
        return false;
    };
    loop {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty = inner,
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                return matches!(
                    inner.kind(),
                    TyKind::RigidTy(RigidTy::Slice(_))
                        | TyKind::RigidTy(RigidTy::Str)
                        | TyKind::RigidTy(RigidTy::Dynamic(..))
                ) || inner.layout().ok().is_some_and(|layout| layout.shape().is_unsized());
            }
            _ => return false,
        }
    }
}

fn raw_pointer_cmp_expr_from_components(
    lhs_ptr: Loc,
    lhs_meta: Option<Val>,
    rhs_ptr: Loc,
    rhs_meta: Option<Val>,
) -> Option<Expr> {
    let (lhs_ptr, rhs_ptr) = (lhs_ptr.into_expr(), rhs_ptr.into_expr());
    let ptr_width = ChcCtx::max_bitvec_width(&lhs_ptr, &rhs_ptr)?;
    let lhs_ptr = coerce_bitvec_width_safe(lhs_ptr, ptr_width, SignExtension::ZeroExtend);
    let rhs_ptr = coerce_bitvec_width_safe(rhs_ptr, ptr_width, SignExtension::ZeroExtend);
    let ptr_lt = lhs_ptr.clone().bvult(rhs_ptr.clone());
    let ptr_eq = lhs_ptr.eq(rhs_ptr);
    let tie_cmp = match (lhs_meta, rhs_meta) {
        (None, None) => Expr::bitvec_const(0, 32),
        (Some(lhs_meta), Some(rhs_meta)) => {
            let (lhs_meta, rhs_meta) = (lhs_meta.into_expr(), rhs_meta.into_expr());
            let meta_width = ChcCtx::max_bitvec_width(&lhs_meta, &rhs_meta)?;
            let lhs_meta =
                coerce_bitvec_width_safe(lhs_meta, meta_width, SignExtension::ZeroExtend);
            let rhs_meta =
                coerce_bitvec_width_safe(rhs_meta, meta_width, SignExtension::ZeroExtend);
            let meta_lt = lhs_meta.clone().bvult(rhs_meta.clone());
            let meta_eq = lhs_meta.eq(rhs_meta);
            Expr::ite(
                meta_lt,
                Expr::bitvec_const(-1i128, 32),
                Expr::ite(meta_eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
            )
        }
        _ => return None,
    };

    Some(Expr::ite(
        ptr_lt,
        Expr::bitvec_const(-1i128, 32),
        Expr::ite(ptr_eq, tie_cmp, Expr::bitvec_const(1, 32)),
    ))
}

/// Splits a raw-pointer expression into its address and (optional) metadata.
///
/// Wave 4 of the address-vs-value conversion. Part of #4030: call-produced raw
/// wide-pointer locals (`Ord::min`/`max`/`clamp`) can no longer be traced to a
/// single provenance source place, so their data/metadata structure has to be
/// recovered from the expression itself rather than collapsed to a thin key.
///
/// The two width tests that used to do that recovery are deleted. Reading bits
/// 127..64 as metadata "because the expression is double-width" cannot tell a
/// real fat pointer from a thin one widened into a BV128 slot, and ordering two
/// pointers on padding produces an arbitrary but *stable-looking* answer — the
/// worst kind. `PtrRepr` decodes the shape structurally and reports no metadata
/// for `WidenedThin`, which routes the comparison to its address-only lane.
///
/// The datatype arm reports DECLARED roles (`fld_ptr` / `fld_len` / ...).
fn raw_pointer_order_components(expr: &Expr) -> Option<(Loc, Option<Val>)> {
    if let Some(repr) = PtrRepr::classify(expr) {
        return Some(repr.into_parts());
    }

    let dt = expr.sort().datatype_sort()?;
    let cons = dt.constructors.first()?;
    let ptr_field = cons.fields.iter().find(|field| {
        (field.name == "fld_ptr" || field.name == "ptr" || field.name == "fld_data")
            && field.sort.is_bitvec()
    })?;
    if !ptr_field.sort.is_bitvec() {
        return None;
    }
    let ptr = Loc::of_address(expr.clone().field_select(
        &dt.name,
        &ptr_field.name,
        ptr_field.sort.clone(),
    ));
    let metadata = cons
        .fields
        .iter()
        .find(|field| {
            (field.name == "fld_len" || field.name == "fld_vtable" || field.name == "fld_meta")
                && field.sort.is_bitvec()
        })
        .map(|field| {
            Val::of_value(expr.clone().field_select(&dt.name, &field.name, field.sort.clone()))
        });
    Some((ptr, metadata))
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dyn drop dispatch and MIR analysis helpers for drop placeholders.
//!
//! Extracted from drop_placeholders.rs for 500-line file-size compliance.
//! Part of #4206.

use super::super::ChcCtx;
use super::super::inline_shared::PlaceResolver;
use super::InlineReturn;
use super::pointer_wrapper::resolve_nested_ref_arg_referent;
use super::walker::translate_virtual_body_inline;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeMap, HashMap};

pub(super) fn resolve_nested_drop_arg_value<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    arg: &Operand,
    pointee_ty: rustc_public::ty::Ty,
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<Expr> {
    let referent = resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver)?;
    if ctx.extract_embedded_vtable_expr(&referent).is_some() {
        return Some(referent);
    }
    if referent.sort().bitvec_width().is_some()
        && let Some(loaded) = ctx.load_from_memory(referent.clone(), pointee_ty)
    {
        return Some(loaded);
    }
    Some(referent)
}

pub(super) fn forwarded_heap_vtable_for_expr(ctx: &ChcCtx<'_, '_>, expr: &Expr) -> Option<Expr> {
    if let Some((obj_id, offset)) = ChcCtx::try_extract_constant_addr(expr) {
        let fwd_key = ((obj_id as u64) << 32) | (offset as u64);
        if let Some(vtable) = ctx.heap_state.region_vtable_forwards.get(&fwd_key) {
            return Some(vtable.clone());
        }
    }
    ctx.heap_state.region_vtable_forward_exprs.get(&format!("{expr}")).cloned()
}

pub(super) fn dyn_projection_locals(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> Vec<usize> {
    use rustc_public::mir::{Operand, Rvalue, StatementKind};

    let mut locals = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            let Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) = rhs else {
                continue;
            };
            if !lhs.projection.is_empty() || src.projection.is_empty() {
                continue;
            }
            if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(
                ctx,
                ctx.resolve_body_ty(*target_ty),
            )
            .is_some()
            {
                locals.push(lhs.local);
            }
        }
    }
    locals.sort_unstable();
    locals.dedup();
    locals
}

pub(super) fn is_box_new_call(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    func: &rustc_public::mir::Operand,
) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::mir::mono::Instance;
    use rustc_public::rustc_internal;

    let Ok(func_ty) = func.ty(body.locals()) else {
        return false;
    };
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return false,
    };
    let def_id =
        Instance::resolve(fn_def, &fn_args).ok().map_or(fn_def.def_id(), |inst| inst.def.def_id());
    let path = ctx.tcx.def_path_str(rustc_internal::internal(ctx.tcx, def_id));
    path.contains("boxed::Box") && path.ends_with("::new")
}

pub(super) fn find_box_new_payload_local(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<usize> {
    use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

    if depth_remaining == 0 {
        return None;
    }

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if lhs.local != local_idx || !lhs.projection.is_empty() {
                continue;
            }
            let next_local = match rhs {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    if src.projection.is_empty() && src.local != local_idx =>
                {
                    src.local
                }
                _ => continue,
            };
            return find_box_new_payload_local(ctx, body, next_local, depth_remaining - 1)
                .or(Some(next_local));
        }

        let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
            continue;
        };
        if destination.local != local_idx
            || !destination.projection.is_empty()
            || !is_box_new_call(ctx, body, func)
        {
            continue;
        }
        let Some(Operand::Copy(src) | Operand::Move(src)) = args.first() else {
            continue;
        };
        if src.projection.is_empty() {
            return Some(src.local);
        }
    }

    None
}

pub(super) fn seed_box_new_payload_vtable_inline(
    ctx: &ChcCtx<'_, '_>,
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    dropped_local: usize,
    callee_body: &rustc_public::mir::Body,
    caller_vtable_ids: &mut HashMap<usize, Expr>,
) {
    let Some(payload_local) = find_box_new_payload_local(ctx, outer_body, dropped_local, 8) else {
        return;
    };
    let Some(payload_vtable) = inline_vtable_ids
        .get(&payload_local)
        .cloned()
        .or_else(|| ctx.known_vtable_expr_for_local(payload_local))
        .or_else(|| {
            local_exprs.get(&payload_local).and_then(|expr| ctx.extract_embedded_vtable_expr(expr))
        })
    else {
        return;
    };
    for local_idx in dyn_projection_locals(ctx, callee_body) {
        caller_vtable_ids.entry(local_idx).or_insert_with(|| payload_vtable.clone());
    }
}

fn extract_wrapper_payload_vtable_from_expr(
    ctx: &ChcCtx<'_, '_>,
    expr: &Expr,
    depth_remaining: usize,
) -> Option<Expr> {
    if depth_remaining == 0 {
        return None;
    }

    ctx.extract_embedded_vtable_expr(expr)
        .or_else(|| forwarded_heap_vtable_for_expr(ctx, expr))
        .or_else(|| {
            let dt = expr.sort().datatype_sort()?;
            let cons = dt.constructors.first()?;
            let field = cons.fields.first()?;
            let field_expr = expr.clone().field_select(&dt.name, &field.name, field.sort.clone());
            extract_wrapper_payload_vtable_from_expr(ctx, &field_expr, depth_remaining - 1)
        })
}

fn extract_wrapper_payload_vtable_from_addr(
    ctx: &mut ChcCtx<'_, '_>,
    addr: &Expr,
    ty: rustc_public::ty::Ty,
    depth_remaining: usize,
) -> Option<Expr> {
    if depth_remaining == 0 {
        return None;
    }
    let loaded = ctx.load_from_memory(addr.clone(), ty)?;
    extract_wrapper_payload_vtable_from_expr(ctx, &loaded, depth_remaining).or_else(|| {
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) =
            ty.kind()
        else {
            return None;
        };
        let variants = def.variants();
        let variant = variants.first()?;
        if variant.fields().len() != 1 {
            return None;
        }
        let field_ty = ctx.resolve_body_ty(variant.fields()[0].ty_with_args(&args));
        extract_wrapper_payload_vtable_from_addr(ctx, addr, field_ty, depth_remaining - 1)
    })
}

fn extract_nested_wrapper_payload_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    self_expr: &Expr,
) -> Option<Expr> {
    let self_ty = ctx.resolve_body_ty(body.locals().get(1)?.ty);
    let wrapper_ty = match self_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => ctx.resolve_body_ty(pointee),
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => ctx.resolve_body_ty(pointee),
        _ => return None,
    };
    extract_wrapper_payload_vtable_from_addr(ctx, self_expr, wrapper_ty, 8)
}

fn seed_nested_wrapper_payload_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    self_expr: &Expr,
    caller_vtable_ids: &mut HashMap<usize, Expr>,
) {
    let dyn_locals = dyn_projection_locals(ctx, body);
    let payload_vtable = extract_nested_wrapper_payload_vtable(ctx, body, self_expr);
    let Some(payload_vtable) = payload_vtable else {
        return;
    };
    for local_idx in dyn_locals {
        caller_vtable_ids.entry(local_idx).or_insert_with(|| payload_vtable.clone());
    }
}

pub(super) fn try_inline_dyn_drop_dispatch_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    drop_ty: rustc_public::ty::Ty,
    self_expr: Expr,
    vtable_disc: Option<Expr>,
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    dropped_local: Option<usize>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let trait_def_id =
        crate::codegen_ay::chc::dyn_coercion::extract_dyn_trait_def_id(ctx, drop_ty)?;
    let candidates =
        crate::codegen_ay::chc::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    if candidates.is_empty() {
        return Some(InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)));
    }

    let params = [self_expr];
    let mut drop_bodies: Vec<(u64, rustc_public::mir::Body, rustc_public::mir::mono::Instance)> =
        Vec::new();
    for candidate in &candidates {
        let drop_instance =
            rustc_public::mir::mono::Instance::resolve_drop_in_place(candidate.concrete_ty);
        if drop_instance.is_empty_shim() {
            continue;
        }
        if let Some(body) = drop_instance.body() {
            drop_bodies.push((candidate.vtable_id, body, drop_instance));
        }
    }
    if drop_bodies.is_empty() {
        return Some(InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)));
    }

    if drop_bodies.len() == 1 {
        let (_, ref body, ref drop_instance) = drop_bodies[0];
        let mut caller_vtable_ids = HashMap::new();
        if let Some(vtable_expr) = vtable_disc.clone() {
            caller_vtable_ids.insert(1, vtable_expr);
        }
        if let Some(dropped_local) = dropped_local {
            seed_box_new_payload_vtable_inline(
                ctx,
                outer_body,
                local_exprs,
                inline_vtable_ids,
                dropped_local,
                body,
                &mut caller_vtable_ids,
            );
        }
        seed_nested_wrapper_payload_vtable(ctx, body, &params[0], &mut caller_vtable_ids);
        return translate_virtual_body_inline(
            ctx,
            body,
            &params,
            0,
            &caller_vtable_ids,
            Some(*drop_instance),
            inline_depth + 1,
        );
    }

    if let Some(disc_u64) = vtable_disc.as_ref().and_then(|disc| {
        let ay_bindings::ExprValue::BitVecConst { value, .. } = disc.value() else {
            return None;
        };
        Some(value.to_u64_digits().1.first().copied().unwrap_or(0))
    }) && let Some((_, body, drop_instance)) =
        drop_bodies.iter().find(|(vtable_id, _, _)| *vtable_id == disc_u64)
    {
        let mut caller_vtable_ids = HashMap::new();
        if let Some(vtable_expr) = vtable_disc.clone() {
            caller_vtable_ids.insert(1, vtable_expr);
        }
        if let Some(dropped_local) = dropped_local {
            seed_box_new_payload_vtable_inline(
                ctx,
                outer_body,
                local_exprs,
                inline_vtable_ids,
                dropped_local,
                body,
                &mut caller_vtable_ids,
            );
        }
        seed_nested_wrapper_payload_vtable(ctx, body, &params[0], &mut caller_vtable_ids);
        return translate_virtual_body_inline(
            ctx,
            body,
            &params,
            0,
            &caller_vtable_ids,
            Some(*drop_instance),
            inline_depth + 1,
        );
    }

    let total_impls = drop_bodies.len();
    let dispatch_vtable = vtable_disc.clone().unwrap_or_else(|| {
        super::super::declare_pending_var(
            super::super::chc_fresh_name("__dyn_drop_call_vtable"),
            ay_bindings::Sort::bitvec(POINTER_WIDTH),
        )
    });
    let mut inlined: Vec<(u64, InlineReturn)> = Vec::new();
    for (vtable_id, body, drop_instance) in &drop_bodies {
        let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
        let modified_snapshot = ctx.encode.modified_state_indices.clone();
        let mut caller_vtable_ids = HashMap::new();
        if let Some(vtable_expr) = vtable_disc.clone() {
            caller_vtable_ids.insert(1, vtable_expr);
        }
        if let Some(dropped_local) = dropped_local {
            seed_box_new_payload_vtable_inline(
                ctx,
                outer_body,
                local_exprs,
                inline_vtable_ids,
                dropped_local,
                body,
                &mut caller_vtable_ids,
            );
        }
        seed_nested_wrapper_payload_vtable(ctx, body, &params[0], &mut caller_vtable_ids);
        match translate_virtual_body_inline(
            ctx,
            body,
            &params,
            0,
            &caller_vtable_ids,
            Some(*drop_instance),
            inline_depth + 1,
        ) {
            Some(result) => inlined.push((*vtable_id, result)),
            None => {
                ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
                ctx.encode.modified_state_indices = modified_snapshot;
            }
        }
    }
    if inlined.is_empty() {
        return None;
    }

    let skipped = total_impls - inlined.len();
    if skipped > 0 {
        ctx.record_aggregate_gap("inline_dispatch_skipped_impls");
    }

    let result_sort = inlined[0].1.value.sort().clone();
    let mut result_value = super::super::declare_pending_var(
        super::super::chc_fresh_name("__partial_vdisp"),
        result_sort.clone(),
    );
    let mut result_vtable = inlined
        .iter()
        .find_map(|(_, result)| result.vtable.as_ref().map(|vtable| vtable.sort().clone()))
        .map(|vtable_sort| {
            super::super::declare_pending_var(
                super::super::chc_fresh_name("__partial_vdisp_vtable"),
                vtable_sort,
            )
        });
    let mut alias_key_sorts: BTreeMap<usize, ay_bindings::Sort> = BTreeMap::new();
    for (_, result) in &inlined {
        for (&key, expr) in &result.alias_updates {
            alias_key_sorts.entry(key).or_insert_with(|| expr.sort().clone());
        }
    }
    let mut result_alias_updates: BTreeMap<usize, Expr> = alias_key_sorts
        .iter()
        .map(|(&key, sort)| {
            let var = super::super::declare_pending_var(
                super::super::chc_fresh_name(&format!("__partial_vdisp_alias_{key}")),
                sort.clone(),
            );
            (key, var)
        })
        .collect();

    // Assert-guard side-channel: same exact-guard merge as
    // `dispatch.rs::build_dispatch_ite_chain_impl` (distinct vtable ids ⇒
    // mutually exclusive dispatch conditions).
    let mut merged_checks: Vec<super::super::inline_body::DeferredInlineCheck> = Vec::new();
    for (vtable_id, mut impl_result) in inlined.into_iter().rev() {
        let cond = dispatch_vtable.clone().eq(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH));
        merged_checks.extend(
            std::mem::take(&mut impl_result.deferred_checks)
                .into_iter()
                .map(|check| check.weaken_by_guard(&cond)),
        );
        if *impl_result.value.sort() != result_sort {
            continue;
        }
        result_value = Expr::ite(cond.clone(), impl_result.value, result_value);
        if let Some(current_vtable) = result_vtable.take() {
            result_vtable = match impl_result.vtable {
                Some(impl_vtable) if impl_vtable.sort() == current_vtable.sort() => {
                    Some(Expr::ite(cond.clone(), impl_vtable, current_vtable))
                }
                Some(_) => None,
                None => Some(current_vtable),
            };
        }
        let mut new_alias = BTreeMap::new();
        for (&key, current_val) in &result_alias_updates {
            let merged = match impl_result.alias_updates.get(&key) {
                Some(impl_val) if impl_val.sort() == current_val.sort() => {
                    Expr::ite(cond.clone(), impl_val.clone(), current_val.clone())
                }
                Some(_) => continue,
                None => current_val.clone(),
            };
            new_alias.insert(key, merged);
        }
        result_alias_updates = new_alias;
    }

    Some(InlineReturn {
        value: result_value,
        vtable: result_vtable,
        alloc_id: None,
        alias_updates: result_alias_updates,
        deferred_checks: merged_checks,
    })
}

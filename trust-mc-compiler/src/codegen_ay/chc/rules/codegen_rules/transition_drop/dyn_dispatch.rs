// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_bindings::Expr;
use tracing::{debug, warn};

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::inline_body::extract_inline_assert_guard;

use super::super::{CodegenRules, TransitionContext};
use super::dyn_dispatch_multi::{dispatch_d2_multi_impl, resolve_d2_vtable_discriminant};
use super::emit_helpers::emit_inline_guard_error;

fn is_box_new_call(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    func: &rustc_public::mir::Operand,
) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::mir::mono::Instance;
    use rustc_public::rustc_internal;
    use rustc_public::ty::{RigidTy, TyKind};

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

fn find_box_new_payload_local(
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

pub(super) fn dyn_projection_locals(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> Vec<usize> {
    use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};

    let mut locals = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            let Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) = rhs else {
                continue;
            };
            if !lhs.projection.is_empty()
                || src.projection.is_empty()
                || !matches!(src.projection.first(), Some(ProjectionElem::Deref))
            {
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

pub(super) fn seed_box_new_payload_vtable(
    ctx: &ChcCtx<'_, '_>,
    dropped_local: usize,
    callee_body: &rustc_public::mir::Body,
    caller_vtable_ids: &mut std::collections::HashMap<usize, Expr>,
) {
    let Some(payload_local) = find_box_new_payload_local(ctx, ctx.body, dropped_local, 8) else {
        return;
    };
    let Some(payload_vtable) = ctx.known_vtable_expr_for_local(payload_local) else {
        return;
    };
    for local_idx in dyn_projection_locals(ctx, callee_body) {
        caller_vtable_ids.entry(local_idx).or_insert_with(|| payload_vtable.clone());
    }
}

/// Try to dispatch a `Drop` terminator for a `dyn Trait` type through
/// vtable-aware concrete candidate resolution. Part of #3793.
///
/// Returns `true` if dispatch succeeded (transition rule(s) emitted), `false`
/// to fall through to the `DynDropUnsupported` sound-fallback path.
///
/// Two lanes:
/// 1. **Unique candidate:** exactly one concrete drop body → inline directly.
/// 2. **Multi-impl:** multiple concrete drop bodies → emit one guarded
///    transition rule per candidate, keyed by vtable discriminant.
///
/// `self_expr_override`: if `Some`, use this as the `&mut self` address instead
/// of resolving from `place`. Used by the Box<dyn T> path where the inner
/// value's heap address is already extracted from the fat pointer.
///
/// `dealloc_extras`: additional constraints (e.g., Box deallocation) to append
/// to every emitted rule. Empty for non-Box dyn drops.
pub(super) fn try_dyn_drop_dispatch(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    drop_ty: rustc_public::ty::Ty,
    target: usize,
    tctx: &TransitionContext<'_>,
    self_expr_override: Option<Expr>,
    dealloc_extras: &[Expr],
) -> bool {
    use rustc_public::mir::mono::Instance;

    // Step 1: Extract the principal trait DefId from the dyn type.
    // For Box<dyn T>, extract_dyn_trait_def_id resolves through the unsized tail.
    let Some(trait_def_id) =
        super::super::super::dyn_coercion::extract_dyn_trait_def_id(ctx, drop_ty)
    else {
        return false;
    };

    // Part of #4231: When the dyn trait is non-assertion-relevant (e.g.,
    // `core::error::Error`), skip vtable dispatch entirely. Return false to
    // let the caller fall through to its dealloc-only or skip path. Without
    // this, `try_extract_vtable_discriminant_for_trait` creates an
    // unconstrained BV64 (`virtual_missing_vtable`) that causes solver
    // timeouts (PROOF → UNKNOWN regression for pathbuf.rs).
    let trait_path = ctx.tcx.def_path_str(trait_def_id);
    if ChcCtx::is_formatting_path(&trait_path) {
        debug!(
            bb_idx = tctx.bb_idx,
            %trait_path,
            "dyn drop dispatch: non-assertion-relevant trait, skip (#4231)"
        );
        return false;
    }

    // Step 2: Collect concrete candidates for this trait.
    let candidates =
        super::super::super::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    if candidates.is_empty() {
        return false;
    }

    // Step 3: Resolve drop bodies for each candidate.
    let mut drop_bodies: Vec<(u64, rustc_public::mir::Body, Instance)> = Vec::new();
    for candidate in &candidates {
        let drop_instance = Instance::resolve_drop_in_place(candidate.concrete_ty);
        if drop_instance.is_empty_shim() {
            continue;
        }
        if let Some(body) = drop_instance.body() {
            drop_bodies.push((candidate.vtable_id, body, drop_instance));
        }
    }

    if drop_bodies.is_empty() {
        return false;
    }

    // Step 4: Resolve the address of the dropped place.
    let self_expr = if let Some(expr) = self_expr_override {
        expr
    } else {
        // `self_expr_override` is an inline-body parameter term of unreported
        // provenance, so the merged slot stays a bare `Expr`; the address lane
        // drops its wave-11 tag here instead of tagging the override lane.
        match ctx.translate_ref_to_address(place, tctx.modified_locals) {
            Some(addr) => addr.into_expr(),
            None => return false,
        }
    };

    warn!(
        bb_idx = tctx.bb_idx,
        num_bodies = drop_bodies.len(),
        num_candidates = candidates.len(),
        "dyn drop dispatch: resolved candidates"
    );
    if drop_bodies.len() == 1 {
        // D1: Unique candidate — inline directly without vtable guard.
        let (_, ref body, ref drop_instance) = drop_bodies[0];
        let params = [self_expr];
        // Part of #4097: Register callee statics before inlining.
        ctx.register_callee_body_statics(body);
        ctx.mark_inline_field_reads(body, &params, tctx.bb_idx);
        let vtable_disc = ctx.try_extract_vtable_discriminant_for_trait(
            &params,
            Some(place.local),
            Some(trait_def_id),
        );
        let mut caller_vtable_ids = std::collections::HashMap::new();
        caller_vtable_ids.insert(1, vtable_disc);
        seed_box_new_payload_vtable(ctx, place.local, body, &mut caller_vtable_ids);
        if let Some(inline_result) =
            crate::codegen_ay::chc::call::inline_body::translate_inline_body(
                ctx,
                body,
                &params,
                tctx.bb_idx,
                &caller_vtable_ids,
                Some(*drop_instance),
                0,
            )
        {
            let inline_guard = extract_inline_assert_guard(&inline_result.value);
            emit_inline_guard_error(
                ctx,
                tctx.from_app,
                tctx.shared_constraints,
                tctx.bb_idx,
                inline_guard.as_ref(),
            );
            for check in ctx.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
                ctx.emit_error_rule_for_condition_shared(
                    tctx.from_app,
                    check,
                    tctx.shared_constraints,
                    tctx.bb_idx,
                );
            }
            let mut extra_constraints = Vec::new();
            extra_constraints.append(&mut ctx.heap_state.pending_updates);
            extra_constraints.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
            extra_constraints.extend(inline_guard);
            extra_constraints.extend_from_slice(dealloc_extras);
            let new_output_args = ctx.build_block_output_args(tctx.modified_locals, None);
            ctx.emit_goto_rule_shared_extra(
                tctx.from_app,
                target,
                &new_output_args,
                tctx.shared_constraints,
                extra_constraints,
            );
            debug!(
                bb_idx = tctx.bb_idx,
                has_dealloc = !dealloc_extras.is_empty(),
                "CHC: Drop(dyn) → unique candidate inlined ({})",
                drop_instance.name()
            );
            return true;
        }
        return false;
    }

    // D2: Multi-impl dispatch — delegated to dyn_dispatch_multi module.
    let vtable_disc = resolve_d2_vtable_discriminant(ctx, place, tctx);
    dispatch_d2_multi_impl(
        ctx,
        place,
        &self_expr,
        &vtable_disc,
        &drop_bodies,
        target,
        tctx,
        dealloc_extras,
    )
}

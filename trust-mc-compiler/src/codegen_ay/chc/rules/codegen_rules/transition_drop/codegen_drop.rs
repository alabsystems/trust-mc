// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use tracing::debug;

use super::super::{CodegenRules, TransitionContext};
use super::DropFallbackReason;
use super::arc_drop::try_codegen_arc_drop;
use super::box_drop::try_codegen_box_drop;
use super::dyn_dispatch::try_dyn_drop_dispatch;
use super::no_drop::ty_trivially_no_drop_with_dyn_candidates;
use super::shared_ptr::is_mutex_rwlock_drop;
use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::codegen_call_coroutine::elision::pin_box_coroutine_local_has_elidable_uses;
use crate::codegen_ay::chc::call::inline_body::extract_inline_assert_guard;
use crate::codegen_ay::chc::rules::codegen_rules_helpers::CodegenRulesHelpers;
use crate::codegen_ay::shared::IntoOption;

fn drop_inline_walk_site_reason(place: &rustc_public::mir::Place, bb_idx: usize) -> String {
    format!("drop_inline_walk_failed@bb{bb_idx}:local{}", place.local)
}

/// Handle Drop terminator with optional Box dealloc logic.
pub(in crate::codegen_ay::chc::rules::codegen_rules) fn codegen_drop(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
    let drop_ty = place.ty(ctx.body.locals()).into_option();
    if try_codegen_box_drop(ctx, place, drop_ty, target, tctx) {
        return;
    }
    // Part of #4067: Handle Arc<T>/Rc<T> drop as simple deallocation.
    // In single-threaded verification, Arc/Rc always have strong count=1,
    // so drop always deallocates. The full drop shim contains recursive
    // drop_in_place calls through vtable dispatch that cause recursion
    // unwinding assertions. Emit dealloc + skip inner drop (sound for
    // assertion checking, same as Box dealloc-only fallback).
    if try_codegen_arc_drop(ctx, place, drop_ty, target, tctx) {
        return;
    }

    // Part of #4067: Mutex/RwLock drop is a no-op in single-threaded CHC verification.
    // The Mutex type is transparent (Mutex<T> → T), so its Drop impl just destroys
    // the platform mutex (pthread) which has no semantic effect. The drop shim body
    // contains calls to <Mutex as Drop>::drop (prefix-abstracted, no body) and
    // pthread_* foreign functions — inlining fails or creates spurious error() rules.
    // Skip the entire drop as a plain goto to the successor block.
    if let Some(ty) = drop_ty {
        if is_mutex_rwlock_drop(ty) {
            ctx.emit_goto_rule_shared(
                tctx.from_app,
                target,
                tctx.output_args,
                tctx.shared_constraints,
            );
            tracing::debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Mutex/RwLock) → noop skip (#4067)");
            return;
        }
    }

    if try_codegen_pin_box_coroutine_drop(ctx, place, drop_ty, target, tctx) {
        return;
    }
    if try_codegen_direct_coroutine_drop(ctx, drop_ty, target, tctx) {
        return;
    }

    // Part of #3791: Inline Drop::drop() for concrete types with custom Drop impls.
    // Phase 1: covers non-dyn types with available MIR bodies. Dyn drops remain
    // on the sound_fallback path (Phase 3 — vtable dispatch).
    // Track fallback reason for provenance-coded diagnostics (#3791 D1).
    let mut drop_fallback_reason: Option<DropFallbackReason> = None;
    let mut translation_drop_site_reason: Option<String> = None;
    if let Some(drop_ty) = drop_ty
        && !ty_trivially_no_drop_with_dyn_candidates(ctx, drop_ty)
    {
        use rustc_public::mir::mono::Instance;
        use rustc_public::ty::{RigidTy, TyKind};
        if matches!(drop_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
            // Part of #3793: Try dyn drop dispatch before falling back.
            if try_dyn_drop_dispatch(ctx, place, drop_ty, target, tctx, None, &[]) {
                return;
            }
            drop_fallback_reason = Some(DropFallbackReason::DynDropUnsupported);
        } else {
            let drop_instance = Instance::resolve_drop_in_place(drop_ty);
            if !drop_instance.is_empty_shim() {
                let body_and_addr = drop_instance.body().map(|body| {
                    let self_expr = ctx
                        .translate_ref_to_address(place, tctx.modified_locals)
                        .unwrap_or_else(|| {
                            crate::codegen_ay::chc::declare_pending_var(
                                crate::codegen_ay::chc::chc_fresh_name("__drop_self"),
                                ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
                            )
                        });
                    (body, self_expr)
                });
                if let Some((body, self_expr)) = body_and_addr {
                    let params = [self_expr];
                    // Part of #4097: Register callee statics before inlining.
                    ctx.register_callee_body_statics(&body);
                    ctx.mark_inline_field_reads(&body, &params, tctx.bb_idx);
                    let mut caller_vtable_ids = std::collections::HashMap::new();
                    if let Some(vtable_id) = ctx.resolve_unique_wrapped_dyn_vtable_id(drop_ty) {
                        caller_vtable_ids.insert(
                            1,
                            ay_bindings::Expr::bitvec_const(
                                vtable_id as u128,
                                crate::codegen_ay::types::POINTER_WIDTH,
                            ),
                        );
                    }
                    if let Some(inline_result) =
                        crate::codegen_ay::chc::call::inline_body::translate_inline_body(
                            ctx,
                            &body,
                            &params,
                            tctx.bb_idx,
                            &caller_vtable_ids,
                            Some(drop_instance),
                            0,
                        )
                    {
                        let inline_guard = extract_inline_assert_guard(&inline_result.value);
                        if let Some(guard) = &inline_guard {
                            ctx.emit_error_rule_for_condition_shared(
                                tctx.from_app,
                                guard.clone(),
                                tctx.shared_constraints,
                                tctx.bb_idx,
                            );
                        }
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
                        extra_constraints
                            .append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
                        extra_constraints.extend(inline_guard);
                        let new_output_args =
                            ctx.build_block_output_args(tctx.modified_locals, None);
                        ctx.emit_goto_rule_extra(
                            tctx.from_app,
                            target,
                            &new_output_args,
                            tctx.shared_constraints,
                            extra_constraints,
                        );
                        debug!(
                            bb_idx = tctx.bb_idx,
                            "CHC: Drop({}) → inlined drop body",
                            drop_instance.name()
                        );
                        return;
                    }
                    drop_fallback_reason = Some(DropFallbackReason::DropInlineWalkFailed);
                    translation_drop_site_reason =
                        Some(drop_inline_walk_site_reason(place, tctx.bb_idx));
                } else {
                    drop_fallback_reason = Some(DropFallbackReason::DropShimNoBody);
                }
            } else {
                // Empty shim: type has no Drop impl, safe to skip without fallback.
                ctx.emit_goto_rule_shared(
                    tctx.from_app,
                    target,
                    tctx.output_args,
                    tctx.shared_constraints,
                );
                debug!(bb_idx = tctx.bb_idx, "CHC: Drop → empty shim, skip");
                return;
            }
        }
    }

    // Fallback: Record sound fallback for non-Box drops where the type
    // may implement Drop (#3499). Drop terminators on such types are
    // over-approximated as skip (plain goto) when inline fails.
    //
    // Part of #3872: For dyn types where try_dyn_drop_dispatch failed,
    // check the concrete candidate set before recording fallback. If all
    // candidates are trivially no-drop, the skip semantics are exact.
    if drop_ty.is_some_and(|ty| !ty_trivially_no_drop_with_dyn_candidates(ctx, ty)) {
        // Part of #3814: upgrade to reason-coded recording.
        ctx.record_sound_fallback_reason("drop_fallback");
        if let Some(site_reason) = translation_drop_site_reason.as_deref() {
            crate::codegen_ay::chc::codegen_ctx::record_translation_drop_site_reason_for_fn(
                &ctx.fn_name,
                site_reason,
            );
        }
        if let Some(reason) = drop_fallback_reason {
            crate::codegen_ay::chc::codegen_ctx::record_drop_fallback_reason_for_fn(
                &ctx.fn_name,
                reason.as_str(),
            );
            debug!(
                bb_idx = tctx.bb_idx,
                reason = reason.as_str(),
                "CHC: Drop fallback with reason"
            );
        }
    }
    ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
}

fn try_codegen_pin_box_coroutine_drop(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    drop_ty: Option<rustc_public::ty::Ty>,
    target: usize,
    tctx: &TransitionContext<'_>,
) -> bool {
    let Some(drop_ty) = drop_ty else {
        return false;
    };
    let Some(coroutine_ty) = pin_box_coroutine_inner_ty(drop_ty) else {
        return false;
    };

    if !coroutine_drop_fields_trivially_no_drop(ctx, coroutine_ty) {
        debug!(
            bb_idx = tctx.bb_idx,
            ?drop_ty,
            "CHC: Drop(Pin<Box<Coroutine>>) kept on generic path; captured Drop may be relevant"
        );
        return false;
    }
    if !pin_box_coroutine_local_has_elidable_uses(ctx, place.local) {
        debug!(
            bb_idx = tctx.bb_idx,
            local_idx = place.local,
            "CHC: Drop(Pin<Box<Coroutine>>) kept on generic path; pinbox result is used"
        );
        return false;
    }

    ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
    debug!(
        bb_idx = tctx.bb_idx,
        local_idx = place.local,
        "CHC: Drop(Pin<Box<Coroutine>>) → guarded no-op"
    );
    true
}

fn try_codegen_direct_coroutine_drop(
    ctx: &mut ChcCtx<'_, '_>,
    drop_ty: Option<rustc_public::ty::Ty>,
    target: usize,
    tctx: &TransitionContext<'_>,
) -> bool {
    let Some(drop_ty) = drop_ty else {
        return false;
    };
    if !is_coroutine_ty(drop_ty) {
        return false;
    }
    if !coroutine_drop_fields_trivially_no_drop(ctx, drop_ty) {
        return false;
    }

    ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
    debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Coroutine) → guarded no-op");
    true
}

pub(in crate::codegen_ay::chc) fn pin_box_coroutine_inner_ty(
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    let TyKind::RigidTy(RigidTy::Adt(pin_def, pin_args)) = ty.kind() else {
        return None;
    };
    if pin_def.trimmed_name() != "Pin" {
        return None;
    }

    let box_ty = match pin_args.0.first()? {
        GenericArgKind::Type(ty) => *ty,
        _ => return None,
    };
    if !ChcCtx::is_box_ty(box_ty) {
        return None;
    }

    let TyKind::RigidTy(RigidTy::Adt(_, box_args)) = box_ty.kind() else {
        return None;
    };
    let inner_ty = match box_args.0.first()? {
        GenericArgKind::Type(ty) => *ty,
        _ => return None,
    };

    is_coroutine_ty(inner_ty).then_some(inner_ty)
}

fn is_coroutine_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(ty.kind(), rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Coroutine(..)))
}

pub(in crate::codegen_ay::chc) fn coroutine_drop_fields_trivially_no_drop(
    ctx: &ChcCtx<'_, '_>,
    coroutine_ty: rustc_public::ty::Ty,
) -> bool {
    drop_ty_trivially_no_assertion_effects(ctx, coroutine_ty, 0)
}

fn drop_ty_trivially_no_assertion_effects(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
    depth: usize,
) -> bool {
    use rustc_public::ty::{RigidTy, TyKind};

    if depth > 8 {
        return false;
    }

    let ty = ctx.resolve_body_ty(ty);
    if ty_trivially_no_drop_with_dyn_candidates(ctx, ty) {
        return true;
    }

    if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
        return coroutine_drop_glue_trivially_no_drop(ctx, ty, depth + 1);
    }

    false
}

fn coroutine_drop_glue_trivially_no_drop(
    ctx: &ChcCtx<'_, '_>,
    coroutine_ty: rustc_public::ty::Ty,
    depth: usize,
) -> bool {
    use rustc_public::mir::TerminatorKind;
    use rustc_public::mir::mono::Instance;

    let drop_instance = Instance::resolve_drop_in_place(coroutine_ty);
    if drop_instance.is_empty_shim() {
        return true;
    }
    let Some(drop_body) = drop_instance.body() else {
        return false;
    };

    for block in &drop_body.blocks {
        if let TerminatorKind::Drop { place, .. } = &block.terminator.kind {
            let Ok(drop_ty) = place.ty(drop_body.locals()) else {
                return false;
            };
            if !drop_ty_trivially_no_assertion_effects(ctx, drop_ty, depth + 1) {
                return false;
            }
        }
    }

    true
}

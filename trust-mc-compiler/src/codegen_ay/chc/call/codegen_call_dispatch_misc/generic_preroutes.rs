// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Generic pre-route dispatch: trivial drop, Box drop, copy/copy_nonoverlapping,
//! raw_eq, slice::as_ptr, str::len, UnsafeCell::get, Cell::new, ManuallyDrop::new,
//! downcast_unchecked_ref, vtable intrinsics, IndexRange len.
//! Extracted from codegen_call_dispatch_misc (Part of #4010).

use crate::codegen_ay::stubs::StubKind;
use ay_bindings::Expr;
use rustc_public::mir::Operand;

use super::super::ChcCtx;
use super::super::chc_call_context::{CallEmitContext, ChcCallContext, DispatchCallContext};
use super::super::codegen_call_cell::CallCell;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_coerce::{emit_sound_fallback_goto, emit_sound_fallback_goto_extra};
use super::super::codegen_call_index_range_len::CallIndexRangeLen;
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_call_ptr::CallPtr;
use super::super::codegen_call_unsafe_cell::CallUnsafeCell;
use super::super::codegen_call_vtable_intrinsic::CallVtableIntrinsic;
use super::super::codegen_rules::CodegenRules;
use super::super::codegen_rules_helpers::{
    CodegenRulesHelpers, rust_dealloc_base_ptr_for_known_alloc_id,
    traced_alloc_id_for_unprojected_drop_place,
};
use super::super::dispatch_helpers::DispatchHelpers;
use super::super::dyn_coercion::extract_pointer_expr;
use super::super::inline_body::extract_inline_assert_guard;
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::{
    SharedPointerDeallocEffects, collect_shared_pointer_dealloc_effects,
    shared_pointer_drop_local_from_drop_arg, shared_pointer_inner_ty,
    shared_pointer_value_ptr_for_drop, try_translate_shared_pointer_inner_drop,
};
use crate::codegen_ay::types::POINTER_WIDTH;
use tracing::{debug, warn};

/// Whether `path` is a canonical standard-library `Cell`/`RefCell` operation
/// that must FAIL CLOSED when the dedicated semantic lane
/// (`codegen_call_cell.rs`) does not handle it precisely.
///
/// - All canonical `Cell` operations except `::new`: kept boundary-visible by
///   the inline pass; the semantic lane models `get`/`set`/`replace`/`take`/
///   `as_ptr` at the recovered referent address, everything else (or any
///   declined interception) lands here.
/// - The canonical `RefCell` boundary trio (`replace`/`replace_with`/
///   `as_ptr`): kept boundary-visible for the semantic lane; a decline (e.g.
///   the borrow-guard gate or unrecoverable address) must quarantine, not
///   codegen-time deep-inline. Other `RefCell` methods are never boundary-kept
///   and keep their existing deep-inline behavior.
fn is_quarantined_cell_operation_path(path: &str) -> bool {
    if let Some(suffix) =
        path.strip_prefix("core::cell::Cell").or_else(|| path.strip_prefix("std::cell::Cell"))
        && (suffix.starts_with("::") || suffix.starts_with('<'))
        && !path.ends_with("::new")
    {
        return true;
    }
    if let Some(suffix) =
        path.strip_prefix("core::cell::RefCell").or_else(|| path.strip_prefix("std::cell::RefCell"))
        && (suffix.starts_with("::") || suffix.starts_with('<'))
        && (path.ends_with("::replace")
            || path.ends_with("::replace_with")
            || path.ends_with("::as_ptr"))
    {
        return true;
    }
    false
}

fn trivial_drop_call_pointee_ty(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
) -> Option<rustc_public::ty::Ty> {
    let arg_ty = ctx.resolve_body_ty(args.first()?.ty(ctx.body.locals()).ok()?);
    match arg_ty.kind() {
        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, pointee, _))
        | rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(pointee, _)) => {
            Some(ctx.resolve_body_ty(pointee))
        }
        _ => None,
    }
}

fn is_trivial_drop_call(ctx: &ChcCtx<'_, '_>, func: &Operand, args: &[Operand]) -> bool {
    let Some(path) = ctx.resolve_callee_path(func) else {
        return false;
    };
    if !path.contains("Drop>::drop") && !path.contains("drop_in_place") {
        return false;
    }

    let vec_into_iter_drop = path.contains("vec::IntoIter");
    let Some(pointee_ty) = trivial_drop_call_pointee_ty(ctx, args) else {
        return false;
    };
    // Part of #4193: Rc/Arc must NOT be classified as trivial drops here.
    // They need inner-drop + dealloc handling via is_arc_rc_drop_call below.
    // ty_trivially_no_drop returns true for Rc/Arc (dealloc-only allowlist),
    // but that classification is for *nested field* recursion — at the call
    // dispatch level, Rc/Arc drops must go through the shared pointer path
    // that inlines the inner T's Drop::drop body before deallocating.
    if shared_pointer_inner_ty(pointee_ty).is_some() {
        return false;
    }
    vec_into_iter_drop
        || crate::codegen_ay::chc::rules::codegen_rules::transition_drop::ty_trivially_no_drop(
            pointee_ty,
        )
}

/// Part of #4067: Detect call terminators for `drop_in_place::<Arc<T>>` or
/// `drop_in_place::<Rc<T>>`. In single-threaded verification, Arc/Rc always
/// have strong_count=1, so drop always deallocates. The full drop shim contains
/// atomic ops and recursive `drop_in_place::<dyn T>` through vtable dispatch
/// that cause recursion unwinding assertions. Treat as skip (sound: skipping
/// drop only adds behaviors).
fn is_arc_rc_drop_call(ctx: &ChcCtx<'_, '_>, func: &Operand, args: &[Operand]) -> bool {
    let Some(path) = ctx.resolve_callee_path(func) else {
        return false;
    };
    if !path.contains("drop_in_place") && !path.contains("Drop>::drop") {
        return false;
    }

    trivial_drop_call_pointee_ty(ctx, args).and_then(shared_pointer_inner_ty).is_some()
}

fn try_emit_shared_pointer_drop_call(
    ctx: &mut ChcCtx<'_, '_>,
    bb_idx: usize,
    func: &Operand,
    args: &[Operand],
    destination: &rustc_public::mir::Place,
    target: &Option<rustc_public::mir::BasicBlockIdx>,
    from_app: &trust_mc_core::chc::RelationApp,
    stmt_constraints: &[Expr],
    modified_locals: &std::collections::HashSet<usize>,
) -> bool {
    let Some(pointee_ty) = trivial_drop_call_pointee_ty(ctx, args) else {
        return false;
    };
    let Some(inner_ty) = shared_pointer_inner_ty(pointee_ty) else {
        return false;
    };

    let Some(target) = target else {
        ctx.record_diverging_call_drop(func, Some(bb_idx), "misc::arc_rc_drop_call", None);
        return true;
    };

    let dest_local = destination.local;
    let wrapper_local_idx =
        args.first().and_then(|arg| shared_pointer_drop_local_from_drop_arg(ctx, arg));
    let wrapper_expr = args.first().and_then(|arg| {
        let ref_result = ctx.resolve_ref_or_const_referent(arg, modified_locals);
        let result =
            ref_result.or_else(|| ctx.translate_operand_with_modified(arg, modified_locals));
        result
    });
    let known_alloc_id = wrapper_local_idx.and_then(|idx| {
        traced_alloc_id_for_unprojected_drop_place(
            ctx,
            &rustc_public::mir::Place { local: idx, projection: Vec::new() },
        )
    });
    let wrapper_expr =
        wrapper_expr.or_else(|| known_alloc_id.map(rust_dealloc_base_ptr_for_known_alloc_id));

    if let Some(wrapper_expr) = wrapper_expr
        && let Some(dealloc_effects) =
            collect_shared_pointer_dealloc_effects(ctx, &wrapper_expr, known_alloc_id)
    {
        if let Some(inline_result) = try_translate_shared_pointer_inner_drop(
            ctx,
            inner_ty,
            wrapper_local_idx,
            known_alloc_id,
            &wrapper_expr,
            bb_idx,
            0,
        ) {
            emit_shared_ptr_inner_drop_success(
                ctx,
                inline_result,
                &dealloc_effects,
                from_app,
                stmt_constraints,
                modified_locals,
                dest_local,
                *target,
                bb_idx,
            );
            debug!(bb_idx, "Call dispatch: Arc/Rc drop_in_place → inner drop + dealloc");
        } else if let Some(concrete_inner_ty) =
            find_concrete_rc_inner_ty_for_call(ctx, inner_ty, wrapper_local_idx)
        {
            // Part of #4226: Retry with concrete inner type resolved from
            // other Rc/Arc<ConcreteType> locals sharing the same ADT.
            if let Some(inline_result) = try_translate_shared_pointer_inner_drop(
                ctx,
                concrete_inner_ty,
                wrapper_local_idx,
                known_alloc_id,
                &wrapper_expr,
                bb_idx,
                0,
            ) {
                emit_shared_ptr_inner_drop_success(
                    ctx,
                    inline_result,
                    &dealloc_effects,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                    dest_local,
                    *target,
                    bb_idx,
                );
                debug!(
                    bb_idx,
                    "Call dispatch: Arc/Rc drop_in_place → concrete inner drop + dealloc"
                );
            } else {
                emit_shared_ptr_dealloc_only(
                    ctx,
                    &dealloc_effects,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                    dest_local,
                    *target,
                    bb_idx,
                );
            }
        } else if try_emit_shared_pointer_dyn_drop_dispatch(
            ctx,
            inner_ty,
            wrapper_local_idx,
            &wrapper_expr,
            &dealloc_effects,
            from_app,
            stmt_constraints,
            modified_locals,
            dest_local,
            *target,
            bb_idx,
        ) {
            // Part of #4226: dyn dispatch fallback for Rc/Arc<dyn Trait>.
            debug!(
                bb_idx,
                "Call dispatch: Arc/Rc drop_in_place → dyn inner drop dispatch + dealloc"
            );
        } else {
            emit_shared_ptr_dealloc_only(
                ctx,
                &dealloc_effects,
                from_app,
                stmt_constraints,
                modified_locals,
                dest_local,
                *target,
                bb_idx,
            );
        }
        return true;
    }

    let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
    ctx.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
    debug!(bb_idx, "Call dispatch: Arc/Rc drop_in_place → skip");
    true
}

/// Shared success path for call-terminator Rc/Arc inner drop: emit inline guard
/// + dealloc constraints. Mirrors `emit_arc_inner_drop_success` in arc_drop.rs
/// but uses call-terminator emit methods.
fn emit_shared_ptr_inner_drop_success(
    ctx: &mut ChcCtx<'_, '_>,
    inline_result: super::super::inline_body::InlineReturn,
    dealloc_effects: &SharedPointerDeallocEffects,
    from_app: &trust_mc_core::chc::RelationApp,
    stmt_constraints: &[Expr],
    modified_locals: &std::collections::HashSet<usize>,
    dest_local: usize,
    target: rustc_public::mir::BasicBlockIdx,
    bb_idx: usize,
) {
    let inline_guard = extract_inline_assert_guard(&inline_result.value);
    if let Some(guard) = &inline_guard {
        ctx.emit_error_rule_for_condition(from_app, guard.clone(), stmt_constraints, bb_idx);
    }
    for check in ctx.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
        ctx.emit_error_rule_for_condition(from_app, check, stmt_constraints, bb_idx);
    }
    for check in &dealloc_effects.pending_checks {
        ctx.emit_error_rule_for_condition(from_app, check.clone(), stmt_constraints, bb_idx);
    }
    let mut extra_constraints = Vec::new();
    extra_constraints.append(&mut ctx.heap_state.pending_updates);
    extra_constraints.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
    extra_constraints.extend(inline_guard);
    extra_constraints.extend(dealloc_effects.pending_updates.iter().cloned());
    let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(
        from_app,
        target,
        &new_output_args,
        stmt_constraints,
        extra_constraints,
    );
}

/// Dealloc-only fallback for call-terminator Rc/Arc drop: emit dealloc checks
/// and constraints without inner drop inlining.
fn emit_shared_ptr_dealloc_only(
    ctx: &mut ChcCtx<'_, '_>,
    dealloc_effects: &SharedPointerDeallocEffects,
    from_app: &trust_mc_core::chc::RelationApp,
    stmt_constraints: &[Expr],
    modified_locals: &std::collections::HashSet<usize>,
    dest_local: usize,
    target: rustc_public::mir::BasicBlockIdx,
    bb_idx: usize,
) {
    for check in &dealloc_effects.pending_checks {
        ctx.emit_error_rule_for_condition(from_app, check.clone(), stmt_constraints, bb_idx);
    }
    let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(
        from_app,
        target,
        &new_output_args,
        stmt_constraints,
        dealloc_effects.pending_updates.clone(),
    );
    debug!(bb_idx, "Call dispatch: Arc/Rc drop_in_place → dealloc only");
}

/// Find the concrete inner type for an Rc/Arc whose inner type has a dyn tail.
/// Mirrors `find_concrete_rc_inner_ty` in arc_drop.rs for the call-terminator path.
///
/// When dropping `Rc<Wrapper<dyn Trait>>`, the unsized drop shim may fail to inline.
/// This function scans the harness body for other Rc/Arc locals with the same outer
/// ADT but concrete type parameters.
fn find_concrete_rc_inner_ty_for_call(
    ctx: &ChcCtx<'_, '_>,
    dyn_inner_ty: rustc_public::ty::Ty,
    dropped_local: Option<usize>,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    // Only applicable when the inner type has a dyn tail.
    if super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, dyn_inner_ty).is_none() {
        return None;
    }

    // Extract the outer ADT name for matching (e.g., "Wrapper").
    let dyn_adt_name = match dyn_inner_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => Some(def.name()),
        _ => None,
    };

    // Strategy 1: Trace Move/Copy chains from the dropped local back to a
    // concrete Rc source.
    if let Some(local_idx) = dropped_local {
        if let Some(ty) = trace_rc_local_to_concrete_call(ctx, local_idx, 8) {
            return Some(ty);
        }
    }

    // Strategy 2: Scan all Rc/Arc locals in the body for a concrete version
    // of the same ADT.
    for local in ctx.body.locals() {
        let ty = ctx.resolve_body_ty(local.ty);
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            continue;
        };
        let trimmed = def.trimmed_name();
        if !matches!(trimmed.as_str(), "Rc" | "Arc") {
            continue;
        }
        let Some(GenericArgKind::Type(inner_ty)) = args.0.first() else {
            continue;
        };
        let inner_ty = ctx.resolve_body_ty(*inner_ty);
        // Skip dyn types — we want concrete.
        if super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty).is_some() {
            continue;
        }
        // Check if this inner type matches the same ADT as the dyn one.
        if let Some(ref dyn_name) = dyn_adt_name
            && let TyKind::RigidTy(RigidTy::Adt(concrete_def, _)) = inner_ty.kind()
            && concrete_def.name() == *dyn_name
        {
            return Some(inner_ty);
        }
    }

    None
}

/// Trace Move/Copy assignment chains from a local back to find a concrete Rc source.
fn trace_rc_local_to_concrete_call(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::mir::{Operand, Rvalue, StatementKind};
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    if depth_remaining == 0 {
        return None;
    }

    // Check the local's type directly.
    let local_ty = ctx.body.locals().get(local_idx).map(|l| ctx.resolve_body_ty(l.ty));
    if let Some(ty) = local_ty {
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let trimmed = def.trimmed_name();
            if matches!(trimmed.as_str(), "Rc" | "Arc") {
                if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
                    let inner_ty = ctx.resolve_body_ty(*inner_ty);
                    if super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty).is_none() {
                        return Some(inner_ty);
                    }
                }
            }
        }
    }

    // Trace assignment chains.
    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(place, rhs) = &stmt.kind else {
                continue;
            };
            if place.local != local_idx || !place.projection.is_empty() {
                continue;
            }
            if let Rvalue::Use(Operand::Move(src) | Operand::Copy(src)) = rhs
                && src.projection.is_empty()
                && src.local != local_idx
            {
                return trace_rc_local_to_concrete_call(ctx, src.local, depth_remaining - 1);
            }
        }
    }

    None
}

/// Part of #4226: Try dyn drop dispatch for Rc/Arc<dyn Trait> via the call-terminator path.
///
/// When the inner type has a dyn trait tail, extract the trait DefId, collect
/// concrete candidates, resolve their drop bodies, and inline the unique
/// candidate's drop. Mirrors the dyn dispatch fallback in arc_drop.rs lines 122-153
/// but uses call-terminator emit methods.
#[allow(clippy::too_many_arguments)]
fn try_emit_shared_pointer_dyn_drop_dispatch(
    ctx: &mut ChcCtx<'_, '_>,
    inner_ty: rustc_public::ty::Ty,
    wrapper_local_idx: Option<usize>,
    wrapper_expr: &Expr,
    dealloc_effects: &SharedPointerDeallocEffects,
    from_app: &trust_mc_core::chc::RelationApp,
    stmt_constraints: &[Expr],
    modified_locals: &std::collections::HashSet<usize>,
    dest_local: usize,
    target: rustc_public::mir::BasicBlockIdx,
    bb_idx: usize,
) -> bool {
    use rustc_public::mir::mono::Instance;

    // Only applicable when inner type has a dyn trait tail.
    if super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty).is_none() {
        return false;
    }

    let Some(value_ptr) =
        shared_pointer_value_ptr_for_drop(ctx, wrapper_local_idx, inner_ty, wrapper_expr)
    else {
        return false;
    };

    // Extract the principal trait DefId from the dyn type.
    let Some(trait_def_id) = super::super::dyn_coercion::extract_dyn_trait_def_id(ctx, inner_ty)
    else {
        return false;
    };

    // Collect concrete candidates for this trait.
    let candidates = super::super::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    if candidates.is_empty() {
        return false;
    }

    // Resolve drop bodies for each candidate.
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

    warn!(
        bb_idx,
        num_bodies = drop_bodies.len(),
        num_candidates = candidates.len(),
        "Call dispatch: dyn drop dispatch resolved candidates (#4226)"
    );

    // Emit dealloc checks up front (shared across all dispatch paths).
    for check in &dealloc_effects.pending_checks {
        ctx.emit_error_rule_for_condition(from_app, check.clone(), stmt_constraints, bb_idx);
    }

    if drop_bodies.len() == 1 {
        // Unique candidate — inline directly without vtable guard.
        let (_, ref body, ref drop_instance) = drop_bodies[0];
        let params = [value_ptr];
        ctx.register_callee_body_statics(body);
        ctx.mark_inline_field_reads(body, &params, bb_idx);
        let local_for_vtable = wrapper_local_idx.unwrap_or(dest_local);
        let vtable_disc = ctx.try_extract_vtable_discriminant_for_trait(
            &params,
            Some(local_for_vtable),
            Some(trait_def_id),
        );
        let mut caller_vtable_ids = std::collections::HashMap::new();
        caller_vtable_ids.insert(1, vtable_disc);
        if let Some(inline_result) =
            crate::codegen_ay::chc::call::inline_body::translate_inline_body(
                ctx,
                body,
                &params,
                bb_idx,
                &caller_vtable_ids,
                Some(*drop_instance),
                0,
            )
        {
            let inline_guard = extract_inline_assert_guard(&inline_result.value);
            if let Some(guard) = &inline_guard {
                ctx.emit_error_rule_for_condition(
                    from_app,
                    guard.clone(),
                    stmt_constraints,
                    bb_idx,
                );
            }
            for check in ctx.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
                ctx.emit_error_rule_for_condition(from_app, check, stmt_constraints, bb_idx);
            }
            let mut extra_constraints = Vec::new();
            extra_constraints.append(&mut ctx.heap_state.pending_updates);
            extra_constraints.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
            extra_constraints.extend(inline_guard);
            extra_constraints.extend(dealloc_effects.pending_updates.iter().cloned());
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                from_app,
                target,
                &new_output_args,
                stmt_constraints,
                extra_constraints,
            );
            return true;
        }
        return false;
    }

    // Multi-candidate: emit dealloc-only for now (sound over-approximation).
    // Full D2 multi-impl dispatch with vtable guards is handled by the
    // Drop-terminator path; call-terminator multi-candidate is rare.
    let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(
        from_app,
        target,
        &new_output_args,
        stmt_constraints,
        dealloc_effects.pending_updates.clone(),
    );
    debug!(
        bb_idx,
        num_candidates = drop_bodies.len(),
        "Call dispatch: Arc/Rc dyn drop → multi-candidate dealloc-only fallback"
    );
    true
}

pub(super) fn callee_leaf(path: &str) -> Option<&str> {
    path.rsplit("::")
        .find(|segment| !segment.is_empty() && !segment.starts_with('<'))?
        .split('<')
        .next()
}

/// Extension trait for generic (non-pointer) pre-route dispatch.
pub(super) trait CallDispatchMiscGenericPreroutes {
    fn try_dispatch_misc_generic_preroutes_early(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
    fn try_dispatch_misc_generic_preroutes_late(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchMiscGenericPreroutes for ChcCtx<'tcx, 'body> {
    /// Early generic pre-routes: trivial drop, Box drop, copy, raw_eq, slice::as_ptr.
    fn try_dispatch_misc_generic_preroutes_early(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let (bb_idx, func, args, destination, target, from_app, stmt_constraints, modified_locals) = (
            dcx.bb_idx,
            dcx.func,
            dcx.args,
            dcx.destination,
            dcx.target,
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.modified_locals,
        );

        // Part of #3945: explicit drop calls on trivially-no-drop carriers should
        // behave like implicit Drop terminators and nested-inline trivial-drop
        // placeholders.
        if is_trivial_drop_call(self, func, args) {
            if let Some(target) = target {
                let dest_local = destination.local;
                if let Some((_, dest_var)) = self.resolve_destination(dest_local)
                    && let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        Expr::bitvec_const(0u64, POINTER_WIDTH),
                        dest_var.sort(),
                        dest_local,
                        "misc::trivial_drop_call",
                    )
                {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        [eq],
                    );
                } else {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
                }
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::trivial_drop_call",
                    None,
                );
            }
            return true;
        }

        // Part of #4067, updated #4193: Arc/Rc drop calls via `drop_in_place`.
        // Attempts inner-drop inlining + deallocation effects. Falls back to
        // dealloc-only or plain skip when wrapper expression is unresolvable
        // (sound over-approximation: skipping drop only adds behaviors).
        if is_arc_rc_drop_call(self, func, args) {
            return try_emit_shared_pointer_drop_call(
                self,
                bb_idx,
                func,
                args,
                destination,
                target,
                from_app,
                stmt_constraints,
                modified_locals,
            );
        }

        // Fix #2736: `drop(box_value)` often lowers to a call terminator instead
        // of `TerminatorKind::Drop`.
        if self.detect_box_drop_call(func, args) {
            if let Some(target) = target {
                let box_drop_local =
                    args.first().and_then(|arg| shared_pointer_drop_local_from_drop_arg(self, arg));
                let box_known_alloc_id = box_drop_local.and_then(|local| {
                    traced_alloc_id_for_unprojected_drop_place(
                        self,
                        &rustc_public::mir::Place { local, projection: Vec::new() },
                    )
                });
                let ptr_expr = args
                    .first()
                    .and_then(|arg| {
                        if let rustc_public::mir::Operand::Copy(p)
                        | rustc_public::mir::Operand::Move(p) = arg
                        {
                            if p.projection.is_empty()
                                && self.flatten.flattened_tuple_locals.contains(&p.local)
                            {
                                return self.flattened_local_field_expr(
                                    p.local,
                                    0,
                                    modified_locals,
                                );
                            }
                        }
                        self.resolve_ref_or_const_referent(arg, modified_locals)
                            .or_else(|| self.resolve_ref_operand(arg, modified_locals))
                            .or_else(|| self.translate_operand_with_modified(arg, modified_locals))
                    })
                    .or_else(|| box_known_alloc_id.map(rust_dealloc_base_ptr_for_known_alloc_id));
                if let Some(ptr_expr) = ptr_expr
                    && self.emit_box_dealloc_transition(
                        bb_idx,
                        from_app,
                        *target,
                        ptr_expr,
                        box_known_alloc_id,
                        stmt_constraints,
                        modified_locals,
                    )
                {
                    debug!("modeled mem::drop(Box<T>) as dealloc transition (bb{})", bb_idx);
                } else {
                    tracing::warn!(
                        bb_idx,
                        "CHC: Box dealloc encoding failed — recording fallback (Part of #3123)"
                    );
                    self.record_fallback();
                    let new_output_args =
                        self.build_output_args(modified_locals, &[destination.local]);
                    self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
                }
            } else {
                self.record_diverging_call_drop(func, Some(bb_idx), "misc::box_drop_call", None);
            }
            return true;
        }

        // std::ptr::copy_nonoverlapping lowered as call terminator (Part of #2110)
        if self.detect_copy_nonoverlapping_call(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub: StubKind::PtrWrite,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_copy_nonoverlapping(bb_idx, &cx, false);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::copy_nonoverlapping_call",
                    Some(StubKind::PtrWrite),
                );
            }
            return true;
        }

        // std::intrinsics::copy (overlapping-safe variant) — same value
        // encoding as copy_nonoverlapping (the element model reads pre-copy
        // source values = memmove semantics), but the range-disjointness UB
        // obligation is suppressed: overlap is LEGAL for this variant.
        // Part of #3766, P4-1.
        if self.resolve_callee_path(func).is_some_and(|p| {
            let leaf = callee_leaf(&p);
            (p.starts_with("core::") || p.starts_with("std::"))
                && !p.contains("copy_nonoverlapping")
                && matches!(leaf, Some("copy"))
                && (p.contains("intrinsics::") || p.contains("ptr::"))
        }) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub: StubKind::PtrWrite,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_copy_nonoverlapping(bb_idx, &cx, true);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::copy_call",
                    Some(StubKind::PtrWrite),
                );
            }
            return true;
        }

        // std::intrinsics::raw_eq (array/scalar equality)
        if self.detect_raw_eq_call(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub: StubKind::PrimitiveClone,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_raw_eq(func, &cx);
            } else {
                self.record_diverging_call_drop(func, Some(bb_idx), "misc::raw_eq_call", None);
            }
            return true;
        }

        // slice::as_ptr / as_mut_ptr — identity pointer operation (Part of #2979).
        if self.detect_slice_as_ptr_call(func) {
            return self.emit_identity_call_with_success(
                dcx,
                "misc::slice_as_ptr",
                |ctx, d| {
                    d.args.first().and_then(|arg| {
                        ctx.slice_as_ptr_data_expr(arg, d.modified_locals)
                            .or_else(|| ctx.translate_operand_with_modified(arg, d.modified_locals))
                    })
                },
                |ctx, d| {
                    if let Some(arg) = d.args.first() {
                        ctx.propagate_slice_as_ptr_metadata(d.destination.local, arg);
                        if let Some(addr) = ctx.slice_as_ptr_data_expr(arg, d.modified_locals) {
                            ctx.record_known_stack_addr_expr(
                                d.destination.local,
                                addr,
                                "slice-as-ptr",
                            );
                        }
                    }
                },
            );
        }

        // str::as_bytes — fat-pointer identity with byte-slice metadata.
        if self.detect_str_as_bytes_call(func) {
            return self.emit_identity_call_with_success(
                dcx,
                "misc::str_as_bytes",
                |ctx, d| {
                    d.args
                        .first()
                        .and_then(|arg| ctx.translate_operand_with_modified(arg, d.modified_locals))
                },
                |ctx, d| {
                    if let Some(arg) = d.args.first() {
                        ctx.propagate_str_as_bytes_metadata(
                            d.destination.local,
                            arg,
                            d.modified_locals,
                        );
                    }
                },
            );
        }

        false
    }

    /// Late generic pre-routes: str::len, UnsafeCell::get, Cell accessors/new,
    /// ManuallyDrop::new, downcast_unchecked_ref, vtable intrinsics, IndexRange len.
    fn try_dispatch_misc_generic_preroutes_late(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let (bb_idx, func, args, destination, target, from_app, stmt_constraints, modified_locals) = (
            dcx.bb_idx,
            dcx.func,
            dcx.args,
            dcx.destination,
            dcx.target,
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.modified_locals,
        );

        // str::len — returns the metadata component of the &str fat pointer.
        if self.detect_str_len_call(func) {
            if let Some(target) = target {
                let dest_local = destination.local;
                let eq_constraint = args.first().and_then(|arg| {
                    let metadata_expr = self.translate_ptr_metadata(arg, modified_locals)?;
                    let vec_idx = self.try_state_idx_for_local(dest_local)?;
                    let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
                    let out_sort = out_sort.clone();
                    let dest_var = Expr::var(&**out_name, out_sort.clone());
                    self.make_coerced_eq_constraint(
                        &dest_var,
                        metadata_expr,
                        &out_sort,
                        dest_local,
                        "misc::str_len_metadata",
                    )
                });
                let constrained = eq_constraint.is_some();
                if constrained {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq_constraint,
                    );
                } else {
                    emit_sound_fallback_goto_extra(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                        eq_constraint,
                    );
                }
                debug!(constrained, "modeled str::len (bb{})", bb_idx);
            } else {
                self.record_diverging_call_drop(func, Some(bb_idx), "misc::str_len_call", None);
            }
            return true;
        }

        // UnsafeCell::get — see codegen_call_unsafe_cell.rs (#3452, #3516).
        if self.detect_unsafe_cell_get_call(func) {
            debug!(bb_idx, dest = destination.local, "UnsafeCell::get detected");
            if let Some(target) = target {
                let ecx = CallEmitContext {
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_unsafe_cell_get(bb_idx, &ecx);
            } else {
                self.record_diverging_call_drop(func, Some(bb_idx), "misc::unsafe_cell_get", None);
            }
            return true;
        }

        // Cell/RefCell accessor methods (get/set/replace/take/replace_with/
        // as_ptr) — the certified semantic lane: a direct load/store at the
        // recovered referent address, with as_ptr bound as a plain
        // split-pointer value so contract reads observe the same memory-mirror
        // lane the stores write (see codegen_call_cell.rs, representation
        // coherence). RefCell mutators are additionally gated on the absence
        // of borrow guards in the body (the skipped borrow-flag panic check).
        // A declined interception NEVER falls to deep-inline — it drops into
        // the fail-closed quarantine below.
        if let Some(method) = self.detect_cell_method(func)
            && !self.refcell_mutator_must_fail_close(func, method)
            && let Some(target) = target
        {
            let ecx = CallEmitContext {
                args,
                destination,
                target: *target,
                from_app,
                stmt_constraints,
                modified_locals,
            };
            if self.codegen_call_cell_method(bb_idx, &ecx, method) {
                debug!(bb_idx, ?method, "modeled Cell/RefCell accessor via direct load/store");
                return true;
            }
            // Declined (address unrecoverable / operand unresolved): fall
            // through to the fail-closed quarantine.
        }

        // Quarantine floor for every canonical Cell operation (and the
        // boundary-kept RefCell trio) the semantic lane did not model
        // precisely: deep-inlining can read pointer/address bits as the
        // flattened value, while a partial memory-only model can diverge from
        // the register mirror. Preserve the canonical call boundary and fail
        // closed. The destination is havoced and the unlisted fallback reason
        // forces any solver Success to Unknown at the publication boundary.
        if self
            .resolve_callee_path(func)
            .is_some_and(|path| is_quarantined_cell_operation_path(&path))
        {
            self.record_sound_fallback_reason("cell_accessor_semantics_quarantined");
            if let Some(target) = target {
                let output_args = self.build_output_args(modified_locals, &[destination.local]);
                self.emit_goto_rule(from_app, *target, &output_args, stmt_constraints);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::cell_accessor_quarantined",
                    None,
                );
            }
            return true;
        }

        // Cell::new — value identity (Part of #3681).
        if self.detect_cell_new_call(func) {
            return self.emit_identity_call(dcx, "misc::cell_new", |ctx, d| {
                d.args
                    .first()
                    .and_then(|arg| ctx.translate_operand_with_modified(arg, d.modified_locals))
            });
        }

        // ManuallyDrop::new — transparent-wrapper identity (Part of #2183).
        if self.detect_manually_drop_new_call(func) {
            return self.emit_identity_call(dcx, "misc::manually_drop_new", |ctx, d| {
                d.args
                    .first()
                    .and_then(|arg| ctx.translate_operand_with_modified(arg, d.modified_locals))
            });
        }

        // Mutex::new / into_inner / get_mut — transparent identity (Part of #4067).
        // Mutex<T> is T in single-threaded verification; these are passthrough ops.
        //
        // Exception: `Mutex::into_inner(self) -> LockResult<T>` and
        // `Mutex::get_mut(&mut self) -> LockResult<&mut T>` return a Result
        // datatype, not raw T. When the destination sort is a Result DT we
        // must wrap the inner value in `Result::Ok(T)` (mirroring the
        // `lock`/`read`/`write` handler below). Otherwise the inliner returns
        // raw T which collides with the Result sort at the destination and
        // triggers a type_sort_fallback EncodingGap (see probe_mutex_new.rs).
        if self.detect_mutex_new_call(func) {
            let is_result_returning = self
                .resolve_callee_path(func)
                .is_some_and(|p| p.ends_with("::into_inner") || p.ends_with("::get_mut"));
            if is_result_returning {
                if let Some(target) = target {
                    let dest_local = destination.local;
                    let inner_val = args
                        .first()
                        .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));
                    let eq_constraint = inner_val.and_then(|val| {
                        let vec_idx = self.try_state_idx_for_local(dest_local)?;
                        let (out_name, out_sort) =
                            self.state_var_mgr.output_state_vars.get(vec_idx)?;
                        let out_sort = out_sort.clone();
                        let dest_var = Expr::var(&**out_name, out_sort.clone());
                        // Destination is Result<T, PoisonError<T>>; wrap with Ok(T).
                        let ok_expr = self.build_result_ok_expr(val.clone(), &out_sort);
                        if let Some(ok_expr) = ok_expr {
                            self.declare_datatype_sort_if_needed(&out_sort);
                            self.make_coerced_eq_constraint(
                                &dest_var,
                                ok_expr,
                                &out_sort,
                                dest_local,
                                "misc::mutex_into_inner_ok",
                            )
                        } else {
                            // Destination sort is not a Result DT (already flattened
                            // or BV-encoded). Fall back to identity assignment.
                            self.make_coerced_eq_constraint(
                                &dest_var,
                                val,
                                &out_sort,
                                dest_local,
                                "misc::mutex_into_inner_identity",
                            )
                        }
                    });
                    let constrained = eq_constraint.is_some();
                    if constrained {
                        let new_output_args =
                            self.build_output_args(modified_locals, &[dest_local]);
                        self.emit_goto_rule_extra(
                            from_app,
                            *target,
                            &new_output_args,
                            stmt_constraints,
                            eq_constraint,
                        );
                    } else {
                        emit_sound_fallback_goto_extra(
                            self,
                            from_app,
                            *target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                            eq_constraint,
                        );
                    }
                    debug!(
                        constrained,
                        "modeled Mutex::into_inner/get_mut wrapped Ok (bb{})", bb_idx
                    );
                } else {
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        "misc::mutex_into_inner",
                        None,
                    );
                }
                return true;
            }
            return self.emit_identity_call(dcx, "misc::mutex_new", |ctx, d| {
                d.args
                    .first()
                    .and_then(|arg| ctx.translate_operand_with_modified(arg, d.modified_locals))
            });
        }

        // drop_in_place::<Mutex<T>> / <Mutex as Drop>::drop — no-op (Part of #4067).
        // Mutex is transparent in CHC; its drop just destroys the platform mutex
        // (pthread) which has no semantic effect. Without this, fn-inline walks the
        // body and hits pthread foreign calls creating unconstrained memory.
        if self.detect_mutex_drop_call(func) {
            if let Some(target) = target {
                let new_output_args = self.build_output_args(modified_locals, &[]);
                self.emit_goto_rule_extra(
                    from_app,
                    *target,
                    &new_output_args,
                    stmt_constraints,
                    None,
                );
                debug!("modeled Mutex/RwLock drop as noop (bb{})", bb_idx);
            }
            return true;
        }

        // Mutex::lock / RwLock::read / RwLock::write — always-Ok in single-threaded
        // verification. Returns Result::Ok(inner_value) where the guard is transparent
        // to the inner T. Without this, the call falls through to pthread_mutex_lock
        // (foreign function) producing unconstrained results. Part of #4067 D2.
        if self.detect_mutex_lock_call(func) {
            if let Some(target) = target {
                let dest_local = destination.local;
                let inner_val = args
                    .first()
                    .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));
                let eq_constraint = inner_val.and_then(|val| {
                    let vec_idx = self.try_state_idx_for_local(dest_local)?;
                    let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
                    let out_sort = out_sort.clone();
                    let dest_var = Expr::var(&**out_name, out_sort.clone());
                    // Destination is Result<MutexGuard<T>, PoisonError<MutexGuard<T>>>.
                    // After transparent wrapper unwrapping, try to construct Ok(val).
                    let ok_expr = self.build_result_ok_expr(val.clone(), &out_sort);
                    if let Some(ok_expr) = ok_expr {
                        self.declare_datatype_sort_if_needed(&out_sort);
                        self.make_coerced_eq_constraint(
                            &dest_var,
                            ok_expr,
                            &out_sort,
                            dest_local,
                            "misc::mutex_lock_ok",
                        )
                    } else {
                        // Destination sort is not a Result DT (e.g. already flattened
                        // or BV-encoded). Fall back to identity assignment.
                        self.make_coerced_eq_constraint(
                            &dest_var,
                            val,
                            &out_sort,
                            dest_local,
                            "misc::mutex_lock_identity",
                        )
                    }
                });
                let constrained = eq_constraint.is_some();
                if constrained {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq_constraint,
                    );
                } else {
                    emit_sound_fallback_goto_extra(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                        eq_constraint,
                    );
                }
                debug!(constrained, "modeled Mutex::lock/RwLock::read|write (bb{})", bb_idx);
            } else {
                self.record_diverging_call_drop(func, Some(bb_idx), "misc::mutex_lock", None);
            }
            return true;
        }

        // <dyn Any>::downcast_unchecked_ref — pointer-identity cast (#3635).
        if self.detect_downcast_unchecked_ref(func) {
            debug!(bb_idx, dest = destination.local, "downcast_unchecked_ref detected");
            return self.emit_identity_call(dcx, "misc::downcast_unchecked_ref", |ctx, d| {
                let ptr_expr = d
                    .args
                    .first()
                    .and_then(|arg| ctx.translate_operand_with_modified(arg, d.modified_locals))?;
                Some(extract_pointer_expr(&ptr_expr).unwrap_or(ptr_expr))
            });
        }

        // vtable_size / vtable_align intrinsics (Part of #3159).
        if let Some(intrinsic_kind) = self.detect_vtable_intrinsic_kind(func) {
            if let Some(target) = target {
                let ecx = CallEmitContext {
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                let constrained = !self.vtable_type_metadata.is_empty()
                    && self.try_constrain_vtable_intrinsic(intrinsic_kind, bb_idx, &ecx);
                if !constrained {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[destination.local],
                        stmt_constraints,
                    );
                    debug!("modeled vtable_size/vtable_align as unconstrained stub (bb{})", bb_idx);
                }
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::vtable_intrinsic_call",
                    None,
                );
            }
            return true;
        }

        // `<IndexRange as ExactSizeIterator>::len` — must not fall through as unhandled.
        if let Some(target) = target
            && self.try_codegen_index_range_exact_size_len(dcx, *target)
        {
            return true;
        }

        // Filesystem operations (std::fs::remove_file, std::fs::write, etc.) — pure OS
        // side effects with no verification semantics. Modeled as always-Ok():
        // constrain the Result destination to zero (Ok variant with ZST payload).
        // The unconstrained model was CTREX because the solver explored invalid
        // io::Error drop paths from the unconstrained Err variant. Part of #4134.
        if self.detect_fs_operation_call(func) {
            if let Some(target) = target {
                let dest_local = destination.local;
                let eq_constraint =
                    self.try_state_idx_for_local(dest_local).and_then(|dest_vec_idx| {
                        let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                        let dest_var = Expr::var(
                            &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                            out_sort.clone(),
                        );
                        self.make_coerced_eq_constraint(
                            &dest_var,
                            Expr::bitvec_const(
                                0u64,
                                out_sort.bitvec_width().unwrap_or(POINTER_WIDTH),
                            ),
                            &out_sort,
                            dest_local,
                            "misc::fs_operation_ok",
                        )
                    });
                let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    from_app,
                    *target,
                    &new_output_args,
                    stmt_constraints,
                    eq_constraint,
                );
                debug!("modeled fs operation as Ok(()) (bb{})", bb_idx);
            } else {
                self.record_diverging_call_drop(func, Some(bb_idx), "misc::fs_operation", None);
            }
            return true;
        }

        false
    }
}

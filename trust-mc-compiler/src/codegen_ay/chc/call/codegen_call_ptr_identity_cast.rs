// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer-cast identity handling split from `codegen_call_ptr_identity`.

use tracing::{debug, warn};

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_ptr_identity::{propagate_alloc_id_with_obj, try_extract_data_obj_id};
use super::codegen_call_ptr_identity_ref_target::propagate_ref_target;
use super::codegen_rules::CodegenRules;
use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, TyKind};

pub(super) fn codegen_call_ptr_cast_impl(ctx: &mut ChcCtx<'_, '_>, cx: &ChcCallContext<'_>) {
    let dest_local: usize = cx.destination.local;
    debug!("ptr_cast_stub dest={}", dest_local);

    if let Some(wrapper_local) = nonnull_ref_receiver_local(ctx, cx)
        && try_emit_nonnull_ref_cast(ctx, cx, dest_local, wrapper_local)
    {
        return;
    }
    // `NonNull::as_ref(&self)` / `as_mut(&mut self)` return the pointer the
    // receiver POINTS AT. Their argument is a reference to the `NonNull`, so
    // the identity below would hand back the address of the `NonNull`'s slot
    // (for `Rc::inner`, `&(*self).ptr`, the address of the `Rc` local) and a
    // read through the result reads that slot plus the field offset. When the
    // receiver is no whole local, read the `NonNull` through it; when that
    // read yields no pointer, fail closed.
    if nonnull_ref_receiver_arg_local(ctx, cx).is_some() {
        if try_emit_nonnull_ref_deref(ctx, cx, dest_local) {
            return;
        }
        debug!(dest_local, "NonNull::as_ref/as_mut: receiver pointee unresolved — fail closed");
        ctx.known_alloc_ids.remove(&dest_local);
        ctx.known_stack_addr_exprs.remove(&dest_local);
        ctx.ref_resolution.ref_targets.remove(&dest_local);
        ctx.record_sound_fallback_reason(NONNULL_AS_REF_RECEIVER_UNRESOLVED);
        emit_sound_fallback_goto(
            ctx,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            &[dest_local],
            cx.stmt_constraints,
        );
        return;
    }

    let ptr_expr = cx.args.first().and_then(|arg| {
        ctx.translate_operand_with_modified(arg, cx.modified_locals)
            .or_else(|| ctx.resolve_ref_operand(arg, cx.modified_locals))
    });
    let src_local = cx.args.first().and_then(|arg| match arg {
        rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p)
            if p.projection.is_empty() =>
        {
            Some(p.local)
        }
        _ => None,
    });

    if let Some(ptr) = ptr_expr
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        let ptr_obj_id = try_extract_data_obj_id(&ptr);
        if let Some(eq) = ctx.make_coerced_eq_constraint(
            &dest_var,
            ptr.clone(),
            dest_var.sort(),
            dest_local,
            "codegen_call_ptr_cast",
        ) {
            propagate_alloc_id_with_obj(ctx, dest_local, src_local, ptr_obj_id);
            propagate_ref_target(ctx, dest_local, src_local, ptr_obj_id);
            if let Some(addr) = src_local
                .filter(|sl| ctx.path_insensitive_metadata_copy_is_unique(*sl, dest_local))
                .and_then(|sl| ctx.known_stack_addr_expr(sl))
            {
                ctx.known_stack_addr_exprs.insert(dest_local, addr);
            } else {
                ctx.record_known_stack_addr_expr(dest_local, ptr, "ptr-cast");
            }
            let new_output_args = ctx.build_output_args(cx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                [eq],
            );
            return;
        }
    }

    ctx.known_alloc_ids.remove(&dest_local);
    ctx.known_stack_addr_exprs.remove(&dest_local);
    warn!(
        fn_name = %ctx.fn_name,
        "CHC: ptr.cast unresolved/coercion failed; emitting unconstrained transition with fallback metadata"
    );
    emit_sound_fallback_goto(
        ctx,
        cx.from_app,
        cx.target,
        cx.modified_locals,
        &[dest_local],
        cx.stmt_constraints,
    );
}

fn try_emit_nonnull_ref_cast(
    ctx: &mut ChcCtx<'_, '_>,
    cx: &ChcCallContext<'_>,
    dest_local: usize,
    wrapper_local: usize,
) -> bool {
    let wrapper_place = rustc_public::mir::Place { local: wrapper_local, projection: Vec::new() };
    let ptr_expr = ctx
        .translate_place_with_modified(&wrapper_place, cx.modified_locals)
        .and_then(|expr| ctx.extract_pointer_storage_expr(&expr));
    let Some(ptr) = ptr_expr else { return false };
    let Some((_, dest_var)) = ctx.resolve_destination(dest_local) else {
        return false;
    };
    let ptr_obj_id = try_extract_data_obj_id(ptr.as_expr());
    let Some(eq) = ctx.make_coerced_eq_constraint(
        &dest_var,
        ptr.as_expr().clone(),
        dest_var.sort(),
        dest_local,
        "codegen_call_nonnull_ref_cast",
    ) else {
        return false;
    };

    propagate_alloc_id_with_obj(ctx, dest_local, Some(wrapper_local), ptr_obj_id);
    propagate_ref_target(ctx, dest_local, Some(wrapper_local), ptr_obj_id);
    let mut extra = vec![eq];
    if let Some(vc) = ctx.propagate_vtable_discriminant(wrapper_local, dest_local).or_else(|| {
        ctx.known_vtable_expr_for_local(wrapper_local)
            .and_then(|vtable| ctx.capture_known_vtable_constraint(dest_local, vtable))
    }) {
        extra.push(vc);
    }
    let new_output_args = ctx.build_output_args(cx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints, extra);
    true
}

/// Reason recorded when `NonNull::as_ref`/`as_mut` is handed a receiver whose
/// `NonNull` the encoder cannot read (see `codegen_call_ptr_cast_impl`).
pub(in crate::codegen_ay::chc) const NONNULL_AS_REF_RECEIVER_UNRESOLVED: &str =
    "nonnull_as_ref_receiver_unresolved";

/// The argument local of a `&NonNull<T> -> &T` call (`NonNull::as_ref`,
/// `NonNull::as_mut`): the destination is a reference and the only argument a
/// reference to a `NonNull`, held in a whole local. `from_ref`/`from_mut`,
/// which share the stub, return a `NonNull` and never match.
fn nonnull_ref_receiver_arg_local(ctx: &ChcCtx<'_, '_>, cx: &ChcCallContext<'_>) -> Option<usize> {
    if !matches!(
        ctx.body.locals()[cx.destination.local].ty.kind(),
        TyKind::RigidTy(RigidTy::Ref(_, _, _))
    ) {
        return None;
    }

    let arg = cx.args.first()?;
    let arg_ty = arg.ty(ctx.body.locals()).ok()?;
    let TyKind::RigidTy(RigidTy::Ref(_, receiver_ty, _)) = arg_ty.kind() else {
        return None;
    };
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = receiver_ty.kind() else {
        return None;
    };
    if def.trimmed_name() != "NonNull" {
        return None;
    }

    match arg {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            Some(place.local)
        }
        _ => None,
    }
}

/// `NonNull::as_ref`/`as_mut` through a receiver that is no whole `NonNull`
/// local (`&(*self).ptr`): the result is the `NonNull` read through the
/// receiver, `*arg`. The receiver's own ref target names the `NonNull`'s slot,
/// not the pointee, so it is not carried over.
fn try_emit_nonnull_ref_deref(
    ctx: &mut ChcCtx<'_, '_>,
    cx: &ChcCallContext<'_>,
    dest_local: usize,
) -> bool {
    let Some(arg_local) = nonnull_ref_receiver_arg_local(ctx, cx) else {
        return false;
    };
    let deref_place = rustc_public::mir::Place {
        local: arg_local,
        projection: vec![rustc_public::mir::ProjectionElem::Deref],
    };
    let ptr_expr = ctx
        .translate_place_with_modified(&deref_place, cx.modified_locals)
        .and_then(|expr| ctx.extract_pointer_storage_expr(&expr));
    let Some(ptr) = ptr_expr else { return false };
    let Some((_, dest_var)) = ctx.resolve_destination(dest_local) else {
        return false;
    };
    let ptr_obj_id = try_extract_data_obj_id(ptr.as_expr());
    let Some(eq) = ctx.make_coerced_eq_constraint(
        &dest_var,
        ptr.as_expr().clone(),
        dest_var.sort(),
        dest_local,
        "codegen_call_nonnull_ref_deref",
    ) else {
        return false;
    };
    debug!(
        dest_local,
        arg_local,
        ?ptr_obj_id,
        "NonNull::as_ref/as_mut: read the receiver's NonNull"
    );
    ctx.known_stack_addr_exprs.remove(&dest_local);
    ctx.ref_resolution.ref_targets.remove(&dest_local);
    propagate_alloc_id_with_obj(ctx, dest_local, None, ptr_obj_id);
    propagate_ref_target(ctx, dest_local, None, ptr_obj_id);
    let new_output_args = ctx.build_output_args(cx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints, [eq]);
    true
}

fn nonnull_ref_receiver_local(ctx: &ChcCtx<'_, '_>, cx: &ChcCallContext<'_>) -> Option<usize> {
    let arg_local = nonnull_ref_receiver_arg_local(ctx, cx)?;

    ctx.ref_resolution
        .ref_targets
        .get(&arg_local)
        .filter(|target| target.projections.is_empty())
        .map(|target| target.local)
        .or_else(|| {
            ctx.body.blocks.iter().find_map(|bb_data| {
                bb_data.statements.iter().find_map(|stmt| {
                    let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        return None;
                    };
                    if lhs.local != arg_local || !lhs.projection.is_empty() {
                        return None;
                    }
                    let rustc_public::mir::Rvalue::Ref(_, _, place) = rhs else {
                        return None;
                    };
                    place.projection.is_empty().then_some(place.local)
                })
            })
        })
}

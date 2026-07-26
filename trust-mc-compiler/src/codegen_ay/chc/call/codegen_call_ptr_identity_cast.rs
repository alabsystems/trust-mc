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
            if let Some(addr) = src_local.and_then(|sl| ctx.known_stack_addr_expr(sl)) {
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
    let ptr_obj_id = try_extract_data_obj_id(&ptr);
    let Some(eq) = ctx.make_coerced_eq_constraint(
        &dest_var,
        ptr.clone(),
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

fn nonnull_ref_receiver_local(ctx: &ChcCtx<'_, '_>, cx: &ChcCallContext<'_>) -> Option<usize> {
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

    let arg_local = match arg {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            place.local
        }
        _ => return None,
    };

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

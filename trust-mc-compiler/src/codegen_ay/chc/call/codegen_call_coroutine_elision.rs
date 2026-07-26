// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Guarded no-op models for unused `Pin<Box<Coroutine>>` allocation/drop glue.

use rustc_public::mir::Operand;
use tracing::debug;

use super::{ChcCtx, DispatchCallContext};
use crate::codegen_ay::chc::call::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::chc::rules::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::{
    coroutine_drop_fields_trivially_no_drop, pin_box_coroutine_inner_ty,
};
use crate::codegen_ay::stubs::StubKind;

#[path = "codegen_call_coroutine_elision_box.rs"]
mod box_flow;
#[path = "codegen_call_coroutine_elision_drop.rs"]
mod drop_flow;
#[path = "codegen_call_coroutine_elision_mentions.rs"]
mod mentions;
#[path = "codegen_call_coroutine_elision_pin.rs"]
mod pin_flow;
#[path = "codegen_call_coroutine_elision_ty.rs"]
mod ty;

use box_flow::box_coroutine_local_flows_only_to_elided_pin_drop;
use pin_flow::{
    has_box_into_pin_coroutine_definition, has_box_pin_coroutine_definition,
    has_pin_new_unchecked_box_coroutine_definition, local_is_in_elidable_pin_box_drop_chain,
    pin_box_local_used_only_by_drop,
};
use ty::{box_coroutine_inner_ty, is_box_pin_path, is_coroutine_ty, is_dealloc_like_path};

/// Intercept `Box::pin(coroutine)` when the boxed pin is only created to be
/// dropped. In that shape the allocation and the later `Pin<Box<_>>` drop have
/// no assertion-visible effect as long as captured coroutine drops are trivial.
pub(super) fn try_dispatch_unused_box_pin_coroutine(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let Some(coroutine_ty) = box_pin_coroutine_call_ty(ctx, dcx) else {
        return false;
    };

    if !coroutine_drop_fields_trivially_no_drop(ctx, coroutine_ty) {
        debug!(
            bb_idx = dcx.bb_idx,
            "CHC: Box::pin(Coroutine) kept on generic path; captured Drop may be relevant"
        );
        return false;
    }

    let dest_local = dcx.destination.local;
    if !pin_box_local_used_only_by_drop(ctx, dest_local, Some(dcx.bb_idx)) {
        debug!(
            bb_idx = dcx.bb_idx,
            dest_local, "CHC: Box::pin(Coroutine) kept on generic path; result is used"
        );
        return false;
    }

    let Some(target) = dcx.target else {
        ctx.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), "coroutine::box_pin", None);
        return true;
    };

    let output_args = ctx.build_output_args(dcx.modified_locals, &[]);
    ctx.emit_goto_rule_extra(dcx.from_app, *target, &output_args, dcx.stmt_constraints, None);
    debug!(bb_idx = dcx.bb_idx, dest_local, "CHC: Box::pin(Coroutine) → guarded elision");
    true
}

/// Intercept `Box::new(coroutine)` when the Box only flows into an unused
/// `Pin<Box<_>>`. This is the MIR shape produced when `Box::pin` has already
/// been inlined before CHC call dispatch.
pub(super) fn try_dispatch_unused_box_new_coroutine(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let Some(coroutine_ty) = box_new_coroutine_call_ty(ctx, dcx) else {
        return false;
    };

    if !coroutine_drop_fields_trivially_no_drop(ctx, coroutine_ty) {
        debug!(
            bb_idx = dcx.bb_idx,
            "CHC: Box::new(Coroutine) kept on generic path; captured Drop may be relevant"
        );
        return false;
    }

    let dest_local = dcx.destination.local;
    if !box_coroutine_local_flows_only_to_elided_pin_drop(ctx, dest_local, Some(dcx.bb_idx)) {
        debug!(
            bb_idx = dcx.bb_idx,
            dest_local, "CHC: Box::new(Coroutine) kept on generic path; Box result is used"
        );
        return false;
    }

    let Some(target) = dcx.target else {
        ctx.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), "coroutine::box_new", None);
        return true;
    };

    let output_args = ctx.build_output_args(dcx.modified_locals, &[]);
    ctx.emit_goto_rule_extra(dcx.from_app, *target, &output_args, dcx.stmt_constraints, None);
    debug!(bb_idx = dcx.bb_idx, dest_local, "CHC: Box::new(Coroutine) → guarded elision");
    true
}

/// Drop glue for an elided `Pin<Box<Coroutine>>` may already be expanded into
/// allocator deallocation calls. Once the corresponding allocation is proven
/// assertion-irrelevant, the deallocation is likewise a no-op for CHC.
pub(super) fn try_dispatch_elided_pin_box_coroutine_drop_glue_call(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let callee_path = dcx
        .callee_path
        .clone()
        .or_else(|| ctx.resolve_callee_path(dcx.func))
        .or_else(|| ctx.resolve_fn_def_name(dcx.func));
    let Some(callee_path) = callee_path else {
        return false;
    };
    if !is_dealloc_like_path(&callee_path) {
        return false;
    }
    if !dcx.args.iter().any(|arg| {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return false;
        };
        place.projection.is_empty() && local_is_in_elidable_pin_box_drop_chain(ctx, place.local)
    }) {
        return false;
    }

    let Some(target) = dcx.target else {
        ctx.record_diverging_call_drop(
            dcx.func,
            Some(dcx.bb_idx),
            "coroutine::pinbox_dealloc",
            None,
        );
        return true;
    };

    let output_args = ctx.build_output_args(dcx.modified_locals, &[]);
    ctx.emit_goto_rule_extra(dcx.from_app, *target, &output_args, dcx.stmt_constraints, None);
    debug!(
        bb_idx = dcx.bb_idx,
        %callee_path,
        "CHC: elided Pin<Box<Coroutine>> dealloc glue → no-op"
    );
    true
}

pub(in crate::codegen_ay::chc) fn pin_box_coroutine_local_has_elidable_uses(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
) -> bool {
    (has_box_pin_coroutine_definition(ctx, local_idx)
        || has_pin_new_unchecked_box_coroutine_definition(ctx, local_idx)
        || has_box_into_pin_coroutine_definition(ctx, local_idx))
        && pin_box_local_used_only_by_drop(ctx, local_idx, None)
}

fn box_pin_coroutine_call_ty(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<rustc_public::ty::Ty> {
    let callee_path = dcx
        .callee_path
        .clone()
        .or_else(|| ctx.resolve_callee_path(dcx.func))
        .or_else(|| ctx.resolve_fn_def_name(dcx.func))?;
    if !is_box_pin_path(&callee_path) {
        return None;
    }

    let dest_ty = ctx.resolve_body_ty(dcx.destination.ty(ctx.body.locals()).ok()?);
    let coroutine_ty = pin_box_coroutine_inner_ty(dest_ty)?;
    let arg_ty = dcx.args.first()?.ty(ctx.body.locals()).ok()?;
    is_coroutine_ty(ctx.resolve_body_ty(arg_ty)).then_some(coroutine_ty)
}

fn box_new_coroutine_call_ty(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<rustc_public::ty::Ty> {
    if ctx.detect_alloc_stub(dcx.func) != Some(StubKind::BoxNew) {
        return None;
    }

    let dest_ty = ctx.resolve_body_ty(dcx.destination.ty(ctx.body.locals()).ok()?);
    let coroutine_ty = box_coroutine_inner_ty(ctx, dest_ty)?;
    let arg_ty = dcx.args.first()?.ty(ctx.body.locals()).ok()?;
    is_coroutine_ty(ctx.resolve_body_ty(arg_ty)).then_some(coroutine_ty)
}

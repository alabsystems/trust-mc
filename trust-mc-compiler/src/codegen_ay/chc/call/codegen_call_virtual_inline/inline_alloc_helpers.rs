// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline allocation helpers for the nested-call walker.
//!
//! Part of #3768: when inline walking hits alloc-like calls that cannot be
//! recursively inlined, synthesize the same heap metadata facts that the
//! dedicated allocation stubs would have produced.

use crate::args::ChcTrackLevel;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;

use super::super::ChcCtx;

pub(super) fn inline_alloc_size_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    translated_args: &[Expr],
) -> Expr {
    if callee_path.contains("Box") && callee_path.ends_with("::new") {
        if let Some(arg_ty) = args
            .first()
            .and_then(|arg| arg.ty(outer_body.locals()).ok())
            .map(|ty| ctx.resolve_body_ty(ty))
            && let Some(size) = ctx.get_type_size(arg_ty)
        {
            return Expr::bitvec_const(size as i128, 32);
        }
        ctx.record_sound_fallback_reason("inline_box_new_size_unknown");
    } else if let Some(size_expr) =
        translated_args.first().cloned().and_then(|expr| ctx.coerce_to_heap_bv32(expr))
    {
        return size_expr;
    } else if !translated_args.is_empty() {
        ctx.record_sound_fallback_reason("inline_alloc_size_bv32_coercion_failed");
    } else {
        ctx.record_sound_fallback_reason("inline_alloc_size_missing");
    }

    ctx.record_aggregate_gap("inline_alloc_size_symbolic");
    super::super::declare_pending_var(
        super::super::chc_fresh_name("__inline_alloc_size"),
        Sort::bitvec(32),
    )
}

pub(super) fn emit_inline_alloc_metadata<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    obj_id: u32,
    size_expr: Expr,
    is_zeroed: bool,
) {
    let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
    let obj_valid_in = super::super::codegen_expr_heap::obj_valid_in();
    let obj_valid_out = super::super::codegen_expr_heap::obj_valid_out();
    let obj_size_in = super::super::codegen_expr_heap::obj_size_in();
    let obj_size_out = super::super::codegen_expr_heap::obj_size_out();

    ctx.heap_state
        .pending_updates
        .push(obj_valid_out.eq(obj_valid_in.store(obj_id_expr.clone(), Expr::bool_const(true))));
    ctx.record_known_heap_alloc_size_expr(obj_id, &size_expr);
    ctx.heap_state.pending_updates.push(obj_size_out.eq(obj_size_in.store(obj_id_expr, size_expr)));
    ctx.mark_heap_metadata_modified();

    if ctx.track_level >= ChcTrackLevel::Ptr {
        let _ = ctx.assign_region_array_to_relation(obj_id, Sort::bitvec(8));
    }
    if is_zeroed {
        ctx.heap_state.mark_heap_obj_zeroed(obj_id);
    }
}

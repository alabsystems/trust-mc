// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Metadata propagation helpers for inline `SliceIndex` special-cases.

use std::collections::HashMap;

use ay_bindings::Expr;

use crate::codegen_ay::chc::codegen_ctx::ChcCtx;

pub(super) fn propagate_inline_range_full_metadata(
    ctx: &mut ChcCtx<'_, '_>,
    src_local: usize,
    dest_local: usize,
) {
    if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&src_local).cloned() {
        ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
        ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
    } else {
        ctx.ref_resolution.ref_targets.remove(&dest_local);
        ctx.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
    }

    copy_or_clear_expr(
        &ctx.ref_resolution.const_ref_values.get(&src_local).cloned(),
        &mut ctx.ref_resolution.const_ref_values,
        dest_local,
    );
    copy_or_clear_expr(
        &ctx.ref_resolution.const_ref_slice_views.get(&src_local).cloned(),
        &mut ctx.ref_resolution.const_ref_slice_views,
        dest_local,
    );
    copy_or_clear_expr(
        &ctx.ref_resolution.subslice_len.get(&src_local).cloned(),
        &mut ctx.ref_resolution.subslice_len,
        dest_local,
    );
    copy_or_clear_expr(
        &ctx.ref_resolution.subslice_offset.get(&src_local).cloned(),
        &mut ctx.ref_resolution.subslice_offset,
        dest_local,
    );
}

fn copy_or_clear_expr(value: &Option<Expr>, map: &mut HashMap<usize, Expr>, dest_local: usize) {
    if let Some(expr) = value {
        map.insert(dest_local, expr.clone());
    } else {
        map.remove(&dest_local);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Walk only the actual runtime drop selected by bound vtable metadata.

use super::{
    ChcCtx,
    inline_body::{InlineReturn, translate_inline_body, walk_drop_body},
};
use crate::{callee_body::CalleeBody, codegen_ay::shared::mono_ty};
use ay_bindings::{Expr, ExprValue};
use rustc_public::ty::Ty;
use std::collections::HashMap;

pub(in crate::codegen_ay::chc) fn translate_bound_dyn_drop(
    ctx: &mut ChcCtx<'_, '_>,
    dynamic: Ty,
    pointer: Expr,
    vtable: Option<Expr>,
    bb: usize,
    depth: usize,
) -> Option<InlineReturn> {
    let heap = ctx.heap_state.snapshot_transient_rule_state();
    let modified = ctx.encode.modified_state_indices.clone();
    let result = (|| {
        let vtable = vtable?;
        let ExprValue::BitVecConst { value, width: 64 } = vtable.value() else { return None };
        let id = u64::try_from(value).ok()?;
        let principal = super::dyn_coercion::extract_dyn_trait_def_id(ctx, dynamic)?;
        let candidates = super::dyn_coercion::collect_dyn_trait_candidates(ctx, principal);
        let candidate = candidates.iter().find(|candidate| candidate.vtable_id == id)?;
        let instance = mono_ty::drop_in_place(candidate.concrete_ty)?;
        if instance.is_empty_shim() {
            return Some(InlineReturn::value_only(Expr::bool_const(true)));
        }
        let body = instance.callee_body()?;
        ctx.register_callee_body_consts(&body);
        ctx.mark_inline_field_reads(&body, std::slice::from_ref(&pointer), bb);
        walk_drop_body(ctx, |ctx| {
            translate_inline_body(
                ctx,
                &body,
                std::slice::from_ref(&pointer),
                bb,
                &HashMap::new(),
                Some(instance),
                depth + 1,
            )
        })
    })();
    if result.is_none() {
        ctx.heap_state.restore_transient_rule_state(&heap);
        ctx.encode.modified_state_indices = modified;
        ctx.record_sound_fallback_reason("walked_dyn_drop_bound_metadata_or_effects_unavailable");
    }
    result
}

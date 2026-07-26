// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared helper for writing back alias updates from inlined call results.
//!
//! After inline body translation returns an `InlineReturn` with `alias_updates`,
//! each top-level consumer (fn_inline, virtual, fn_ptr) must map callee
//! arg-local indices back to caller locals and emit constraints. This module
//! provides `apply_inline_alias_updates` to do that uniformly.
//!
//! Part of #3936 D4: replaces per-consumer single-receiver propagation with
//! a shared loop over all modified aliasable args.

use std::collections::BTreeMap;

use ay_bindings::Expr;
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_result_mem::build_call_result_memory_bridge_constraints;
use super::codegen_call_virtual_inline::receiver_base_local;
use super::ptr_receiver_mem::resolve_ptr_target_local;

/// Resolve the caller-side target local for a callee arg-local index.
///
/// `callee_arg_local` is 1-based (MIR convention: local 1 = first arg).
/// Maps to `dcx.args[callee_arg_local - 1]` and resolves through
/// `ref_targets` (ptr) or plain place extraction (receiver).
pub(in crate::codegen_ay::chc) fn resolve_call_arg_target_local_fallback(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    callee_arg_local: usize,
) -> Option<usize> {
    let arg_idx = callee_arg_local.checked_sub(1)?;
    let arg = dcx.args.get(arg_idx)?;
    resolve_ptr_target_local(ctx, arg).or_else(|| receiver_base_local(arg))
}

pub(in crate::codegen_ay::chc) fn resolve_call_arg_target_local(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    callee_arg_local: usize,
) -> Option<usize> {
    if let Some(owner_local) = ctx.resolve_coroutine_call_arg_owner_local(dcx, callee_arg_local) {
        return Some(owner_local);
    }
    resolve_call_arg_target_local_fallback(ctx, dcx, callee_arg_local)
}

/// Pre-resolve all arg target locals before inline translation.
///
/// Must be called before `translate_inline_body` because the walker may
/// modify `ref_resolution` during body traversal, losing caller-side
/// temp-ref mappings.
pub(in crate::codegen_ay::chc) fn pre_resolve_arg_target_locals(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> BTreeMap<usize, usize> {
    let mut resolved = BTreeMap::new();
    for (i, _) in dcx.args.iter().enumerate() {
        let callee_arg_local = i + 1; // 1-based
        if let Some(caller_local) = resolve_call_arg_target_local(ctx, dcx, callee_arg_local) {
            resolved.insert(callee_arg_local, caller_local);
        }
    }
    resolved
}

/// Apply all alias updates from an `InlineReturn` to the caller's state.
///
/// For each entry in `alias_updates`:
/// 1. Resolve the callee arg-local index to a caller local
/// 2. Push the caller local into `extra_dests`
/// 3. Emit `build_local_update_constraints` and memory bridge constraints
/// 4. Invalidate `const_folded_call_results` for the caller local
///
/// `pre_resolved` is a pre-computed map from `pre_resolve_arg_target_locals`.
/// When `pre_resolved` is empty, live resolution via `dcx` is used as fallback.
pub(in crate::codegen_ay::chc) fn apply_inline_alias_updates(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    alias_updates: &BTreeMap<usize, Expr>,
    pre_resolved: &BTreeMap<usize, usize>,
    dest_local: usize,
    extra_dests: &mut Vec<usize>,
    value_constraints: &mut Vec<Expr>,
    mem_constraints: &mut Vec<Expr>,
    reason_prefix: &'static str,
) {
    for (&callee_arg_local, update_expr) in alias_updates {
        let caller_local = pre_resolved
            .get(&callee_arg_local)
            .copied()
            .or_else(|| resolve_call_arg_target_local(ctx, dcx, callee_arg_local));

        let Some(caller_local) = caller_local else {
            debug!(
                bb_idx = dcx.bb_idx,
                callee_arg_local,
                fn_name = %ctx.fn_name,
                "{reason_prefix}: alias update arg target unresolved, sound over-approx"
            );
            ctx.record_sound_fallback_reason(reason_prefix);
            continue;
        };

        if caller_local != dest_local && !extra_dests.contains(&caller_local) {
            extra_dests.push(caller_local);
        }

        if let Some(mut constraints) =
            ctx.build_local_update_constraints(caller_local, update_expr.clone(), reason_prefix)
        {
            value_constraints.append(&mut constraints);
        } else {
            debug!(
                bb_idx = dcx.bb_idx,
                caller_local,
                callee_arg_local,
                fn_name = %ctx.fn_name,
                "{reason_prefix}: alias update unresolved, sound over-approx"
            );
            ctx.record_sound_fallback_reason(reason_prefix);
        }

        // Mirror alias update into typed memory.
        mem_constraints.extend(build_call_result_memory_bridge_constraints(
            ctx,
            caller_local,
            update_expr,
            dcx.modified_locals,
        ));

        // Invalidate stale cross-block constant propagation for this local.
        ctx.encode.invalidate_local_cache(caller_local);
    }
}

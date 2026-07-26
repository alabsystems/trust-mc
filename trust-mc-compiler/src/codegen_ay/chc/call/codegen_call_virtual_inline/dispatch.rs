// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Multi-impl dispatch ITE chain construction.
//!
//! Part of #3226: Shared between main dispatch and nested inline handler.
//! Part of #3639: Extracted from codegen_call_virtual_inline.rs.

use ay_bindings::Expr;
use std::collections::{BTreeMap, HashMap};
use tracing::debug;

use super::super::ChcCtx;
use super::super::dyn_coercion::ResolvedDispatchBody;
use super::InlineReturn;
use super::walker::translate_virtual_body_inline;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Build a multi-impl dispatch ITE chain from inlined virtual method bodies.
///
/// Part of #3226: Shared between main dispatch and nested inline handler.
pub(in crate::codegen_ay::chc) fn build_dispatch_ite_chain(
    ctx: &mut ChcCtx<'_, '_>,
    concrete_bodies: &[ResolvedDispatchBody],
    param_exprs: &[Expr],
    vtable_disc: Expr,
    bb_idx: usize,
    caller_vtable_ids: &HashMap<usize, Expr>,
) -> Option<InlineReturn> {
    build_dispatch_ite_chain_impl(
        ctx,
        concrete_bodies,
        param_exprs,
        vtable_disc,
        bb_idx,
        caller_vtable_ids,
        0,
    )
}

/// Inner implementation with inline recursion depth tracking.
/// Part of #3614.
pub(in crate::codegen_ay::chc) fn build_dispatch_ite_chain_impl(
    ctx: &mut ChcCtx<'_, '_>,
    concrete_bodies: &[ResolvedDispatchBody],
    param_exprs: &[Expr],
    vtable_disc: Expr,
    bb_idx: usize,
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let initial_self_field_hints = ctx.inline_self_field_hints.clone();

    // Part of #4075 D2: When the vtable discriminant is a known constant
    // (e.g., from the spawn scheduler vtable model), short-circuit to the
    // matching concrete body instead of building a full N-way ITE chain.
    // This prevents expression tree explosion for dyn Future::poll inside
    // Scheduler::run, where N = number of concrete Future types.
    if let ay_bindings::ExprValue::BitVecConst { value: disc_val, .. } = vtable_disc.value() {
        let disc_u64 = disc_val.to_u64_digits().1.first().copied().unwrap_or(0);
        if let Some(matching_body) = concrete_bodies.iter().find(|b| b.vtable_id == disc_u64) {
            debug!(
                vtable_id = disc_u64,
                total_candidates = concrete_bodies.len(),
                bb_idx,
                "dispatch ITE: constant vtable shortcircuit (#4075 D2)"
            );
            ctx.mark_inline_field_reads(&matching_body.body, param_exprs, bb_idx);
            // Roll back partial heap/index mutations if the speculative walk bails.
            let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
            let modified_snapshot = ctx.encode.modified_state_indices.clone();
            ctx.inline_self_field_hints = initial_self_field_hints.clone();
            let result = translate_virtual_body_inline(
                ctx,
                &matching_body.body,
                param_exprs,
                bb_idx,
                caller_vtable_ids,
                None,
                inline_depth,
            );
            if result.is_none() {
                ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
                ctx.encode.modified_state_indices = modified_snapshot;
                debug!(
                    vtable_id = disc_u64,
                    bb_idx,
                    "dispatch ITE: constant-vtable inline walk failed, restored transient state"
                );
            }
            return result;
        }
    }

    let total_impls = concrete_bodies.len();
    let mut inlined: Vec<(u64, InlineReturn)> = Vec::new();
    for dispatch_body in concrete_bodies {
        let vtable_id = dispatch_body.vtable_id;
        let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
        let modified_snapshot = ctx.encode.modified_state_indices.clone();
        ctx.inline_self_field_hints = initial_self_field_hints.clone();
        match translate_virtual_body_inline(
            ctx,
            &dispatch_body.body,
            param_exprs,
            bb_idx,
            caller_vtable_ids,
            None,
            inline_depth,
        ) {
            Some(result) => inlined.push((vtable_id, result)),
            None => {
                ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
                ctx.encode.modified_state_indices = modified_snapshot;
                debug!(
                    vtable_id,
                    bb_idx,
                    "build_dispatch_ite_chain: impl failed to inline, restored transient state and skipped"
                );
            }
        }
    }

    if inlined.is_empty() {
        debug!(bb_idx, "build_dispatch_ite_chain: no impls inlined successfully");
        return None;
    }

    let skipped = total_impls - inlined.len();
    if skipped > 0 {
        debug!(
            bb_idx,
            inlined = inlined.len(),
            skipped,
            "build_dispatch_ite_chain: partial dispatch — {}/{} impls inlined",
            inlined.len(),
            total_impls,
        );
    }

    let result_sort = inlined[0].1.value.sort().clone();

    let mut result_value = super::super::declare_pending_var(
        super::super::chc_fresh_name("__partial_vdisp"),
        result_sort.clone(),
    );
    let mut result_vtable = inlined
        .iter()
        .find_map(|(_, result)| result.vtable.as_ref().map(|vtable| vtable.sort().clone()))
        .map(|vtable_sort| {
            super::super::declare_pending_var(
                super::super::chc_fresh_name("__partial_vdisp_vtable"),
                vtable_sort,
            )
        });
    // Part of #3936 D3: Build per-key pending vars for alias_updates.
    // Collect all keys and their sorts from across all impls.
    let mut alias_key_sorts: BTreeMap<usize, ay_bindings::Sort> = BTreeMap::new();
    for (_, result) in &inlined {
        for (&key, expr) in &result.alias_updates {
            alias_key_sorts.entry(key).or_insert_with(|| expr.sort().clone());
        }
    }
    let mut result_alias_updates: BTreeMap<usize, Expr> = alias_key_sorts
        .iter()
        .map(|(&key, sort)| {
            let var = super::super::declare_pending_var(
                super::super::chc_fresh_name(&format!("__partial_vdisp_alias_{key}")),
                sort.clone(),
            );
            (key, var)
        })
        .collect();

    if skipped > 0 {
        ctx.record_aggregate_gap("inline_dispatch_skipped_impls");
    }

    // Assert-guard side-channel: vtable ids are distinct, so the dispatch
    // conditions are mutually exclusive — weakening each impl's entries by its
    // own `disc == id` guard is exact. Checks survive even for impls whose
    // VALUE is dropped from the merge (sort mismatch): the impl was walked, so
    // its checks are real under its dispatch condition.
    let mut merged_checks: Vec<super::super::inline_body::DeferredInlineCheck> = Vec::new();
    for (vtable_id, mut impl_result) in inlined.into_iter().rev() {
        let cond = vtable_disc.clone().eq(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH));
        merged_checks.extend(
            std::mem::take(&mut impl_result.deferred_checks)
                .into_iter()
                .map(|check| check.weaken_by_guard(&cond)),
        );
        if *impl_result.value.sort() != result_sort {
            debug!(
                "build_dispatch_ite_chain: sort mismatch for impl {} ({:?} vs {:?}), skipping",
                vtable_id,
                impl_result.value.sort(),
                result_sort,
            );
            continue;
        }
        result_value = Expr::ite(cond.clone(), impl_result.value, result_value);
        if let Some(current_vtable) = result_vtable.take() {
            result_vtable = match impl_result.vtable {
                Some(impl_vtable) => {
                    if impl_vtable.sort() != current_vtable.sort() {
                        debug!(
                            "build_dispatch_ite_chain: vtable sort mismatch for impl {} ({:?} vs {:?}), dropping vtable precision",
                            vtable_id,
                            impl_vtable.sort(),
                            current_vtable.sort(),
                        );
                        None
                    } else {
                        Some(Expr::ite(cond.clone(), impl_vtable, current_vtable))
                    }
                }
                None => Some(current_vtable),
            };
        }
        // Part of #3936 D3: Merge alias_updates per-key across dispatch impls.
        let mut new_alias = BTreeMap::new();
        for (&key, current_val) in &result_alias_updates {
            let merged = match impl_result.alias_updates.get(&key) {
                Some(impl_val) => {
                    if impl_val.sort() != current_val.sort() {
                        debug!(
                            "build_dispatch_ite_chain: alias-update sort mismatch for impl {} key {} ({:?} vs {:?}), dropping",
                            vtable_id,
                            key,
                            impl_val.sort(),
                            current_val.sort(),
                        );
                        continue;
                    }
                    Expr::ite(cond.clone(), impl_val.clone(), current_val.clone())
                }
                None => current_val.clone(),
            };
            new_alias.insert(key, merged);
        }
        result_alias_updates = new_alias;
    }

    Some(InlineReturn {
        value: result_value,
        vtable: result_vtable,
        alloc_id: None,
        alias_updates: result_alias_updates,
        deferred_checks: merged_checks,
    })
}

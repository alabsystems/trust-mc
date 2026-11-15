// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Multi-impl dispatch ITE chain construction.
//!
//! Part of #3226: Shared between main dispatch and nested inline handler.
//! Part of #3639: Extracted from codegen_call_virtual_inline.rs.

use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc};
use ay_bindings::Expr;
use std::collections::{BTreeMap, HashMap};
use tracing::debug;

use super::super::ChcCtx;
use super::super::dyn_coercion::ResolvedDispatchBody;
use super::super::dyn_dispatch_scope::{DYN_CANDIDATE_UNWALKABLE, DynDispatchScope};
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
    scope: &DynDispatchScope,
) -> Option<InlineReturn> {
    build_dispatch_ite_chain_impl(
        ctx,
        concrete_bodies,
        param_exprs,
        vtable_disc,
        bb_idx,
        caller_vtable_ids,
        0,
        Some(scope),
    )
}

/// Inner implementation with inline recursion depth tracking.
/// Part of #3614.
///
/// `scope` decides the merge's default arm and whether a candidate that
/// fails to walk matters (design 3: `dyn_dispatch_scope.rs`). `None` keeps the
/// policy from before design 3 (a skipped candidate is an aggregate gap and
/// the default arm is silent). Only the dyn DROP dispatch passes `None`: a
/// runtime type whose drop glue is empty needs no arm there, which the scope's
/// coverage test does not model yet, so that door is not covered by design 3.
#[allow(clippy::too_many_arguments)]
pub(in crate::codegen_ay::chc) fn build_dispatch_ite_chain_impl(
    ctx: &mut ChcCtx<'_, '_>,
    concrete_bodies: &[ResolvedDispatchBody],
    param_exprs: &[Expr],
    vtable_disc: Expr,
    bb_idx: usize,
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_depth: usize,
    scope: Option<&DynDispatchScope>,
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
            ctx.inline_walk_param_address_seeds =
                Some(super::super::inline_walk_guard::dyn_door_address_seeds(
                    ctx,
                    &matching_body.body,
                    param_exprs,
                ));
            let result = translate_virtual_body_inline(
                ctx,
                &matching_body.body,
                param_exprs,
                bb_idx,
                caller_vtable_ids,
                None,
                inline_depth,
            );
            ctx.inline_walk_param_address_seeds = None;
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
    // Phase 0 (inline_walk_guard.rs): ONE write mark over the whole candidate
    // loop, not one per walk. A successful candidate's heap stores are kept
    // and the next candidate is walked against them, so its reads after them
    // must fail closed; and with several candidates, a candidate's memory
    // effect reaches the host unguarded (the branch-arm rule).
    ctx.with_inline_walk_write_mark(|ctx| {
        for dispatch_body in concrete_bodies {
            let vtable_id = dispatch_body.vtable_id;
            let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
            let modified_snapshot = ctx.encode.modified_state_indices.clone();
            let effects_before = ctx.heap_state.effect_mark();
            let checks_before = ctx.heap_state.pending_checks.len();
            ctx.inline_self_field_hints = initial_self_field_hints.clone();
            ctx.inline_walk_param_address_seeds = Some(
                super::super::inline_walk_guard::dyn_door_address_seeds(
                    ctx,
                    &dispatch_body.body,
                    param_exprs,
                ),
            );
            let walked = translate_virtual_body_inline(
                ctx,
                &dispatch_body.body,
                param_exprs,
                bb_idx,
                caller_vtable_ids,
                None,
                inline_depth,
            );
            ctx.inline_walk_param_address_seeds = None;
            match walked {
                Some(result) => {
                    if total_impls > 1 {
                        ctx.note_inline_branch_arm_effects(effects_before);
                    }
                    guard_dispatch_arm_pending_checks(ctx, checks_before, &vtable_disc, vtable_id);
                    inlined.push((vtable_id, result));
                }
                None => {
                    ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
                    ctx.encode.modified_state_indices = modified_snapshot;
                    debug!(
                        vtable_id,
                        bb_idx,
                        "build_dispatch_ite_chain: impl failed to inline, restored transient state and skipped"
                    );
                    // Design 3: a candidate that can be the runtime type and
                    // is not walked leaves its obligations and effects to the
                    // default arm (`bug_multi_impl_big_body`).
                    if scope.is_some_and(|scope| scope.may_be_runtime(vtable_id)) {
                        ctx.record_sound_fallback_reason(DYN_CANDIDATE_UNWALKABLE);
                    }
                }
            }
        }
    });

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

    if skipped > 0 {
        ctx.record_aggregate_gap("inline_dispatch_skipped_impls");
    }
    let walked: Vec<u64> = inlined.iter().map(|(id, _)| *id).collect();
    // A constant discriminant (or an if-then-else of constants) with a leaf
    // none of the walked arms covers selects the default arm outright.
    let default = match scope {
        None => DispatchDefault::Covered,
        Some(scope) => scope.default_arm(&walked, &vtable_disc),
    };
    Some(merge_guarded_dispatch_results(ctx, inlined, &vtable_disc, default))
}

/// Weaken the heap checks a dispatch arm's walk left on the host's pending
/// list by the arm's dispatch condition `disc == id`.
///
/// A walked arm's memory accesses push their checks onto
/// `heap_state.pending_checks`, which the host drains as error rules with no
/// guard, so an arm that is not the runtime target had its accesses checked
/// on every path, at the runtime object's address: with `DV` and `DA` both
/// `Tv` impls, `let o: Box<dyn Tv> = Box::new(DV { .. }); o.get()` checked the
/// `DA` arm's read past the two bytes of the `DV` and lost the proof once
/// accesses through a symbolic object lane took a bound (review of lostwrite
/// round 1). The merge weakens the arm's deferred checks by the same
/// condition, which is exact: the ids are distinct, and a discriminant that
/// is none of them takes the default arm, whose policy is the merge's
/// (`DispatchDefault`).
///
/// Every entry at `since` or later was pushed by this arm's walk: an entry
/// pushed before it is only ever drained or truncated away, never moved to a
/// later index. An entry the walk pushed after draining the list below `since`
/// stays unguarded, which only keeps it stronger.
pub(in crate::codegen_ay::chc) fn guard_dispatch_arm_pending_checks(
    ctx: &mut ChcCtx<'_, '_>,
    since: usize,
    disc: &Expr,
    id: u64,
) {
    if ctx.heap_state.pending_checks.len() <= since {
        return;
    }
    let cond = disc.clone().eq(Expr::bitvec_const(id as u128, POINTER_WIDTH));
    for check in &mut ctx.heap_state.pending_checks[since..] {
        *check = cond.clone().not().or(check.clone());
    }
}

/// What the fresh default arm of a guarded dispatch stands for (design 3 of
/// `docs/chc-hole-fix-designs-2026-09-24.md`: complete or fail closed, never a
/// silent default arm for a target no arm covers).
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) enum DispatchDefault {
    /// Every runtime target has an arm. The default is reached only on a model
    /// path whose discriminant is none of the ids, which a havocked
    /// discriminant admits (and its producer records); every real target's
    /// obligations are on its own arm. Carries no obligation.
    Covered,
    /// Every value the discriminant can hold is one of the arms' ids. The
    /// default arm is the checked obligation `disc ∈ ids` with this message,
    /// so a wrong completeness argument is a failure, not a dropped behaviour.
    ///
    /// `taint`, when set, is a fresh boolean recorded as the freed variable of
    /// a sound havoc (`fn_ptr_targets.rs`, [`FN_PTR_OBLIGATION_UNCERTIFIED`]):
    /// the obligation becomes `disc ∈ ids ∨ taint`. A free variable in the
    /// error rule can always be false, so the obligation fails exactly when
    /// it did, and a proof is unchanged; what changes is that a counterexample
    /// violating it reads a freed variable and is never certified Genuine.
    /// Set when the discriminant's value came from memory or a call (the
    /// universe completed the set), where the memory model can hand back a
    /// value the program never stored.
    ///
    /// [`FN_PTR_OBLIGATION_UNCERTIFIED`]: super::super::fn_ptr_targets::FN_PTR_OBLIGATION_UNCERTIFIED
    Obligation { message: &'static str, taint: Option<Expr> },
    /// The arms may miss the runtime target: record this reason, which is not
    /// on the blessed list.
    FailClosed(&'static str),
}

/// Merge per-candidate walk results under their dispatch conditions
/// (`vtable_disc == id`): the value, vtable and alias updates as ITE chains
/// over a fresh default (see [`DispatchDefault`]), and each candidate's
/// side-channel checks weakened by its own condition (exact, since the ids
/// are distinct). `inlined` must be non-empty.
///
/// Shared by [`build_dispatch_ite_chain_impl`], the Fn-trait direct dispatch
/// (`fn_trait_dispatch.rs`), which walks closure / fn-item bodies instead of
/// the trait method's, and the fn-pointer dispatches (`nested_call.rs`,
/// `codegen_call_fn_ptr.rs`).
pub(in crate::codegen_ay::chc) fn merge_guarded_dispatch_results(
    ctx: &ChcCtx<'_, '_>,
    inlined: Vec<(u64, InlineReturn)>,
    vtable_disc: &Expr,
    default: DispatchDefault,
) -> InlineReturn {
    let result_sort = inlined[0].1.value.sort().clone();
    let arm_ids: Vec<u64> = inlined.iter().map(|(id, _)| *id).collect();

    // Rule E: what the fresh default stands for is the `DispatchDefault`. A
    // `FailClosed` default is booked here, once, and the default's values stand
    // on that booking. Otherwise no execution reads them as data: a `Covered`
    // default is reached only on a model path whose discriminant some producer
    // havocked (and booked), or for an arm whose value was dropped (booked
    // below, `DISPATCH_ARM_VALUE_DROPPED`); an `Obligation` default is the
    // failing side of the emitted `disc ∈ ids` check.
    let default_booking = match &default {
        DispatchDefault::FailClosed(reason) => Some(ctx.record_sound_fallback_reason(reason)),
        DispatchDefault::Covered | DispatchDefault::Obligation { .. } => None,
    };
    let mint_default = |name: String, sort: ay_bindings::Sort| match default_booking {
        Some(booked) => Havoc::booked(booked, name, sort),
        None => ExactVar::unobserved(name, sort),
    };
    let mut result_value =
        mint_default(super::super::chc_fresh_name("__partial_vdisp"), result_sort.clone());
    let mut result_vtable = inlined
        .iter()
        .find_map(|(_, result)| result.vtable.as_ref().map(|vtable| vtable.sort().clone()))
        .map(|vtable_sort| {
            mint_default(super::super::chc_fresh_name("__partial_vdisp_vtable"), vtable_sort)
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
            let var = mint_default(
                super::super::chc_fresh_name(&format!("__partial_vdisp_alias_{key}")),
                sort.clone(),
            );
            (key, var)
        })
        .collect();

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
            // The arm's value and alias updates fall to the fresh default:
            // its writes are lost for the host (design 3).
            ctx.record_sound_fallback_reason(
                super::super::fn_ptr_targets::DISPATCH_ARM_VALUE_DROPPED,
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
                        // F5 (docs/chc-hole-fix-designs-2026-09-24.md section
                        // 2): this used to `continue`, which dropped the KEY for
                        // every impl, so no alias update reached the host and
                        // the written cell was framed as unchanged
                        // (walker_dyn_heap_write_dual.rs multi_bump). This
                        // impl's update is havocked under its own condition
                        // instead, and the harness fails closed.
                        debug!(
                            "build_dispatch_ite_chain: alias-update sort mismatch for impl {} key {} ({:?} vs {:?}), havocking",
                            vtable_id,
                            key,
                            impl_val.sort(),
                            current_val.sort(),
                        );
                        let booked = ctx.record_sound_fallback_reason(
                            super::super::inline_walk_guard::DYN_DISPATCH_ALIAS_UPDATE_SORT_MISMATCH,
                        );
                        let havoc = Havoc::booked(
                            booked,
                            super::super::chc_fresh_name(&format!("__vdisp_alias_mismatch_{key}")),
                            current_val.sort().clone(),
                        );
                        new_alias.insert(key, Expr::ite(cond.clone(), havoc, current_val.clone()));
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

    match default {
        DispatchDefault::Covered => {}
        DispatchDefault::Obligation { message, taint } => {
            let mut obligation =
                super::super::fn_ptr_targets::invalid_fn_ptr_obligation(ctx, vtable_disc, &arm_ids);
            obligation.message = Some(message.to_string());
            if let Some(taint) = taint {
                obligation.check = obligation.check.or(taint);
            }
            merged_checks.push(obligation);
        }
        // Booked when the default was minted (above).
        DispatchDefault::FailClosed(_) => {}
    }

    InlineReturn {
        value: result_value,
        vtable: result_vtable,
        alloc_id: None,
        alias_updates: result_alias_updates,
        deferred_checks: merged_checks,
    }
}

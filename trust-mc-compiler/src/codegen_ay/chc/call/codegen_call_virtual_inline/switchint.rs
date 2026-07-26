// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SwitchInt translation into nested ITE expressions.
//!
//! Part of #3188: SwitchInt support for inline translators.
//! Part of #3639: Extracted from codegen_call_virtual_inline.rs.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, TerminatorKind};
use std::collections::{BTreeMap, HashMap, HashSet};
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::super::codegen_types::CodegenTypes;
use super::super::inline_body::DeferredInlineCheck;
use super::super::inline_shared::inline_operand_to_expr;
use super::execution_state::InlineExecutionState;
use super::walker::{InlineWalkCtx, walk_blocks_to_return};
use super::{InlineReturn, MAX_SWITCHINT_DEPTH, switchint_walk_node_budget};

/// Produce a fresh symbolic InlineReturn when a SwitchInt branch walk bails.
///
/// Sound over-approximation: the branch result is unconstrained. This
/// prevents a single failing branch from killing the entire SwitchInt ITE
/// chain. The return sort is derived from the body's return local (local 0).
///
/// Part of #4031: SwitchInt resilience for methods with nested call failures.
/// Part of #4050: edge-keyed caching — reuse the same symbolic variable for
/// repeated walks of the same (switchint_bb, target_bb) edge across loop replay
/// iterations. Reduces O(iterations × edges) to O(unique_edges).
/// The cache key uses the callee-local `switchint_bb` (the basic block
/// containing this SwitchInt terminator) as the site identifier. This is
/// precise per-site, unlike the earlier `walk_ctx.bb_idx` which was the outer
/// call-site block and could not distinguish two different SwitchInt sites
/// in the same callee body.
fn switchint_branch_fallback<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    switchint_bb: usize,
    target_bb: usize,
) -> Option<InlineReturn> {
    let key = (switchint_bb, target_bb);
    if let Some(cached) = walk_ctx.switchint_overapprox_cache.borrow().get(&key) {
        return Some(InlineReturn::value_only(cached.clone()));
    }
    let ret_ty = ctx.resolve_inline_local_ty(walk_ctx.body, 0).unwrap_or(walk_ctx.locals[0].ty);
    let ret_sort = ChcCtx::translate_ty(ret_ty)?;
    // Do NOT unwrap with option_value_sort here — the sibling branch results
    // use the raw return sort, and ITE merge requires matching sorts.
    let name = chc_fresh_name("__switchint_branch_overapprox");
    let var = declare_pending_var(name, ret_sort);
    walk_ctx.switchint_overapprox_cache.borrow_mut().insert(key, var.clone());
    Some(InlineReturn::value_only(var))
}

/// Check if a basic block is a dead branch (empty statements + Unreachable terminator).
/// Part of #3889: Conservative dead-branch detection for SwitchInt.
fn is_unreachable_block(walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> bool {
    bb < walk_ctx.body.blocks.len()
        && walk_ctx.body.blocks[bb].statements.is_empty()
        && matches!(walk_ctx.body.blocks[bb].terminator.kind, TerminatorKind::Unreachable)
}

/// Check if a basic block is a diverging branch (ends with a Call that has no
/// return target — i.e., it always panics/aborts). This covers the None arm of
/// Option/Result panic-or-extract patterns.
///
/// Part of #4050: Detecting these as dead branches prevents Option extract
/// SwitchInts from consuming SwitchInt depth. Each becomes single-target,
/// which avoids depth accumulation in loop bodies that repeatedly extract
/// (e.g., `pop()` followed by discriminant check inside a while loop).
fn is_diverging_block(walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> bool {
    if bb >= walk_ctx.body.blocks.len() {
        return false;
    }
    let block = &walk_ctx.body.blocks[bb];
    // Direct diverging call: the block ends with Call { target: None }.
    if matches!(block.terminator.kind, TerminatorKind::Call { target: None, .. }) {
        return true;
    }
    // One-hop Goto chain: the block Gotos another block that diverges.
    // Covers patterns where rustc inserts a setup block before the panic call.
    if let TerminatorKind::Goto { target } = block.terminator.kind {
        if target < walk_ctx.body.blocks.len() {
            let next = &walk_ctx.body.blocks[target];
            if matches!(next.terminator.kind, TerminatorKind::Call { target: None, .. })
                || matches!(next.terminator.kind, TerminatorKind::Unreachable)
            {
                return true;
            }
        }
    }
    false
}

/// Check if a basic block is effectively dead for SwitchInt branch purposes.
/// Combines Unreachable detection (#3889) with diverging-call detection (#4050).
fn is_dead_branch_target(walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> bool {
    is_unreachable_block(walk_ctx, bb) || is_diverging_block(walk_ctx, bb)
}

/// Translate a SwitchInt terminator into nested ITE expressions.
///
/// Part of #3188: SwitchInt support for inline translators.
pub(in crate::codegen_ay::chc) fn translate_switchint_ite<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    discr: &Operand,
    targets: &rustc_public::mir::SwitchTargets,
    local_exprs: HashMap<usize, Expr>,
    inline_vtable_ids: HashMap<usize, Expr>,
    inline_alloc_ids: HashMap<usize, u32>,
    modified_locals: HashSet<usize>,
    assume_guards: Vec<Expr>,
    assert_guards: Vec<Expr>,
    deferred_checks: Vec<DeferredInlineCheck>,
    switchint_bb: usize,
    switchint_depth: usize,
    inline_depth: usize,
) -> Option<InlineReturn> {
    if switchint_depth >= MAX_SWITCHINT_DEPTH {
        debug!(switchint_bb, switchint_depth, "virtual body: SwitchInt depth limit reached");
        return None;
    }
    // P5.3 (fail-closed): per-harness walk-node budget. Depth bounds one
    // chain, but forked sub-walks multiply across nesting, loop replay, and
    // call sites — unbounded, they burn the driver watchdog to a hard kill.
    // Take the SAME sound-overapprox bail path as depth exhaustion (callers
    // substitute an unconstrained branch result or havoc the inline), and
    // book a FailClose fallback so any resulting verdict is an honest
    // Demoted UNDETERMINED — a fast demotion instead of an ~80s hard kill.
    if ctx.switchint_walk_nodes_spent >= switchint_walk_node_budget() {
        ctx.record_sound_fallback_reason("walker_node_budget_exhausted");
        debug!(
            switchint_bb,
            nodes_spent = ctx.switchint_walk_nodes_spent,
            "virtual body: SwitchInt walk-node budget exhausted (P5.3), bailing fail-closed"
        );
        return None;
    }
    // Assert-guard side-channel: entries recorded BEFORE this SwitchInt are
    // path-independent of the branch guards. They are held aside here (branch
    // walk states start with an EMPTY side-channel) and re-attached to the
    // merged result unweakened; per-branch entries get their branch guard
    // composed in the merge fold below.
    let pre_switch_checks = deferred_checks;

    let resolver = walk_ctx.resolver;
    let discr_expr = inline_operand_to_expr(ctx, discr, &local_exprs, &resolver, walk_ctx.locals)?;

    // Part of #3936 D3: Capture all aliasable arg-local values at entry.
    // When some branches modify an arg and others don't, the unmodified
    // side of the ITE merge must use the original value (not dropped).
    let alias_at_entry: HashMap<usize, Expr> = local_exprs.clone();

    let branches: Vec<(u128, usize)> = targets.branches().collect();
    let otherwise_bb = targets.otherwise();

    // Part of #3889/#4050: Dead-branch detection — skip branches whose target
    // is Unreachable (e.g., otherwise arm of a 2-variant enum) OR diverging
    // (panic/abort path, e.g., None arm of Option::unwrap). This prevents
    // Option unwrap SwitchInts from consuming depth unnecessarily.
    let otherwise_is_dead = is_dead_branch_target(walk_ctx, otherwise_bb);
    let entry_loop_fuel = walk_ctx.snapshot_loop_header_fuel();

    let mut local_exprs = Some(local_exprs);
    let mut inline_vtable_ids = Some(inline_vtable_ids);
    let mut inline_alloc_ids = Some(inline_alloc_ids);
    let mut modified_locals = Some(modified_locals);
    let mut assume_guards = Some(assume_guards);
    let mut assert_guards = Some(assert_guards);

    // Part of #4050 D1: Collect live explicit branches, then deduplicate by
    // unique target block. Walk each unique target once; reuse the result for
    // every case value that points at the same block. This reduces duplicate
    // walks and overapprox variables from O(case_values) to O(unique_targets).
    let live_explicit: Vec<(u128, usize)> = branches
        .iter()
        .rev()
        .filter(|(_, bb)| !is_dead_branch_target(walk_ctx, *bb))
        .copied()
        .collect();

    // Part of #55 piece 2: EXACT constant discriminant — walk ONLY the taken
    // arm. Match semantics mirror the guard construction in the merge fold
    // below byte-for-byte: bool via `value != 0`; bitvec via raw-bits equality
    // at the discriminant's width, normalized through the SAME
    // `Expr::bitvec_const(value, width)` constructor the guard uses (no
    // hand-rolled masking — a width/signedness mismatch here would prune the
    // WRONG arm and false-prove). An undecidable fold leaves the full ITE
    // walk untouched. This is what lets concrete recursion (fib(6), fac(5),
    // hanoi) unroll one arm per level instead of exploding both arms.
    let folded_target: Option<usize> =
        const_fold_switch_target(&discr_expr, &branches, otherwise_bb);
    let (live_explicit, otherwise_is_dead) = match folded_target {
        Some(taken) if taken == otherwise_bb => (Vec::new(), otherwise_is_dead),
        Some(taken) => (live_explicit.into_iter().filter(|(_, bb)| *bb == taken).collect(), true),
        None => (live_explicit, otherwise_is_dead),
    };
    if folded_target.is_some() {
        debug!(
            switchint_bb,
            ?folded_target,
            "virtual body: SwitchInt discriminant folded to a constant — single-arm walk"
        );
    }

    // Build unique target list preserving first-seen order.
    let mut unique_targets: Vec<usize> = Vec::new();
    {
        let mut seen = HashSet::new();
        if !otherwise_is_dead {
            seen.insert(otherwise_bb);
            unique_targets.push(otherwise_bb);
        }
        for &(_, tbb) in &live_explicit {
            if seen.insert(tbb) {
                unique_targets.push(tbb);
            }
        }
    }
    let total_walks = unique_targets.len();
    let mut walk_num = 0usize;

    // Part of #4050 D3: Don't consume SwitchInt depth budget for
    // single-target SwitchInts (dead-branch filtering leaves one live arm):
    // no ITE branching, structurally sequential (e.g., unwrap() patterns).
    //
    // Part of #4145: Loop-fuel-bearing bodies must STILL increment depth.
    // The previous exemption (`has_loop_fuel → no depth increment`) caused
    // infinite recursion when nested inlined calls (e.g., scale → mul →
    // reduce → gcd) each had their own while-loop SwitchInts — depth
    // never increased, bypassing MAX_SWITCHINT_DEPTH entirely.
    let walk_depth = if total_walks <= 1 { switchint_depth } else { switchint_depth + 1 };

    // Walk each unique target block once and cache the result.
    let mut target_results: HashMap<usize, InlineReturn> =
        HashMap::with_capacity(unique_targets.len());
    for &tbb in &unique_targets {
        // P5.3: one walk node per sub-walk fork (survives speculative
        // rollback, like const_recursion_nodes_spent — the WORK was done
        // even when a branch walk bails).
        ctx.switchint_walk_nodes_spent += 1;
        walk_ctx.restore_loop_header_fuel(&entry_loop_fuel);
        walk_num += 1;
        let mut state = if walk_num == total_walks {
            InlineExecutionState::new(
                local_exprs.take().expect("invariant: consumed only once"),
                inline_vtable_ids.take().expect("invariant: consumed only once"),
                modified_locals.take().expect("invariant: consumed only once"),
            )
        } else {
            InlineExecutionState::new(
                local_exprs.as_ref().expect("invariant: not yet consumed").clone(),
                inline_vtable_ids.as_ref().expect("invariant: not yet consumed").clone(),
                modified_locals.as_ref().expect("invariant: not yet consumed").clone(),
            )
        };
        state.inline_alloc_ids = if walk_num == total_walks {
            inline_alloc_ids.take().expect("invariant: consumed only once")
        } else {
            inline_alloc_ids.as_ref().expect("invariant: not yet consumed").clone()
        };
        state.assume_guards = if walk_num == total_walks {
            assume_guards.take().expect("invariant: consumed only once")
        } else {
            assume_guards.as_ref().expect("invariant: not yet consumed").clone()
        };
        state.assert_guards = if walk_num == total_walks {
            assert_guards.take().expect("invariant: consumed only once")
        } else {
            assert_guards.as_ref().expect("invariant: not yet consumed").clone()
        };
        // Part of #4185: Snapshot heap state before each branch walk.
        // If the walk bails, partial heap mutations (stores, pending_updates)
        // from branch N must not contaminate branch N+1.
        let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
        // Part of #4185 Fix 4: Snapshot modified_state_indices alongside heap.
        let modified_snapshot = ctx.encode.modified_state_indices.clone();
        let walk_result =
            walk_blocks_to_return(ctx, walk_ctx, tbb, state, walk_depth, inline_depth);
        let result = match walk_result {
            Some(r) => r,
            None => {
                // Part of #4185: Restore heap state after failed branch walk.
                ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
                // Part of #4185 Fix 4: Restore modified_state_indices on bail-out.
                ctx.encode.modified_state_indices = modified_snapshot;
                debug!(
                    switchint_bb,
                    target_bb = tbb,
                    "virtual body: SwitchInt branch walk failed, using overapprox (#4031/#4050)"
                );
                switchint_branch_fallback(ctx, walk_ctx, switchint_bb, tbb)?
            }
        };
        target_results.insert(tbb, result);
    }

    // Part of #4050: If only one unique live target exists (all live arms go
    // to the same block, or single-arm after dead-branch filtering), skip ITE
    // construction entirely — just return the single walk result.
    if unique_targets.len() == 1 {
        let mut sole_result = target_results.into_values().next().expect("invariant: 1 target");
        // Re-attach the pre-switch side-channel entries (no branch condition
        // applies: the single live arm is taken unconditionally).
        sole_result.deferred_checks.extend(pre_switch_checks);
        walk_ctx.restore_loop_header_fuel(&entry_loop_fuel);
        debug!(
            switchint_bb,
            sole_target = unique_targets[0],
            "virtual body: SwitchInt single live target, skipping ITE (#4050)"
        );
        return Some(sole_result);
    }

    // Map otherwise and explicit branches to their pre-walked results.
    let otherwise_result = if otherwise_is_dead {
        debug!(
            switchint_bb,
            otherwise_bb, "virtual body: SwitchInt otherwise is dead, skipping (#3889/#4050)"
        );
        None
    } else {
        Some(target_results.get(&otherwise_bb).expect("invariant: walked").clone())
    };

    let mut branch_results: Vec<(u128, InlineReturn)> = Vec::with_capacity(live_explicit.len());
    for &(value, tbb) in &live_explicit {
        let result = target_results.get(&tbb).expect("invariant: walked").clone();
        branch_results.push((value, result));
    }
    walk_ctx.restore_loop_header_fuel(&entry_loop_fuel);

    // Merge: start with otherwise_result as accumulator, or first explicit branch if dead.
    if otherwise_result.is_none() && branch_results.is_empty() {
        debug!(switchint_bb, "virtual body: SwitchInt all branches dead, bailing");
        return None;
    }
    let mut result = if let Some(r) = otherwise_result { r } else { branch_results.remove(0).1 };

    for (value, mut branch_result) in branch_results {
        let guard = if discr_expr.sort().is_bool() {
            if value != 0 { discr_expr.clone() } else { discr_expr.clone().not() }
        } else if let Some(width) = discr_expr.sort().bitvec_width() {
            discr_expr.clone().eq(Expr::bitvec_const(value, width))
        } else if discr_expr.sort().is_int() {
            discr_expr.clone().eq(Expr::int_const(value))
        } else {
            return None;
        };

        if branch_result.value.sort() != result.value.sort() {
            debug!(
                switchint_bb,
                branch_result = ?branch_result.value,
                result = ?result.value,
                "virtual body: SwitchInt branch sort mismatch, coercing (#4031)"
            );
            // Part of #4031: Instead of bailing on sort mismatch, replace the
            // mismatched side with a fresh symbolic of the other side's sort.
            // Sound over-approximation: the coerced branch is unconstrained.
            // The side-channel entries survive the coercion — the branch WAS
            // walked, so its checks are real; only the VALUE is havocked.
            // (Pre-side-channel, the coercion silently dropped any assert ITE
            // riding the replaced value — one of the documented check-loss
            // shapes this side-channel exists to close.)
            let target_sort = result.value.sort().clone();
            let coerced =
                declare_pending_var(chc_fresh_name("__switchint_sort_coerce"), target_sort);
            let branch_checks = std::mem::take(&mut branch_result.deferred_checks);
            branch_result = InlineReturn::value_only(coerced);
            branch_result.deferred_checks = branch_checks;
        }
        let vtable = match (branch_result.vtable, result.vtable) {
            (Some(branch_vtable), Some(result_vtable)) => {
                if branch_vtable.sort() != result_vtable.sort() {
                    debug!(
                        switchint_bb,
                        branch_vtable = ?branch_vtable,
                        result_vtable = ?result_vtable,
                        "virtual body: SwitchInt vtable sort mismatch, bailing"
                    );
                    return None;
                }
                Some(Expr::ite(guard.clone(), branch_vtable, result_vtable))
            }
            _ => None,
        };
        // Part of #3936 D3: Merge alias_updates per-key across SwitchInt branches.
        let alias_updates = merge_alias_updates_ite(
            &guard,
            branch_result.alias_updates,
            result.alias_updates,
            &alias_at_entry,
            switchint_bb,
        );
        // Assert-guard side-channel: `ite(guard, branch, result)` means the
        // branch's checks apply when `guard` holds and the accumulator's when
        // it doesn't. Explicit case guards test the SAME discriminant against
        // DISTINCT values, so weakening each branch entry by only its own
        // guard is exact; accumulator entries pick up `guard ∨ check` per fold
        // step, matching the nested-ITE path condition exactly.
        let mut deferred_checks: Vec<DeferredInlineCheck> = branch_result
            .deferred_checks
            .into_iter()
            .map(|check| check.weaken_by_guard(&guard))
            .collect();
        deferred_checks.extend(
            result.deferred_checks.into_iter().map(|check| check.weaken_by_negated_guard(&guard)),
        );
        result = InlineReturn {
            value: Expr::ite(guard, branch_result.value, result.value),
            vtable,
            alloc_id: None,
            alias_updates,
            deferred_checks,
        };
    }
    // Re-attach pre-switch side-channel entries unweakened (recorded before
    // any branch guard applied).
    result.deferred_checks.extend(pre_switch_checks);

    debug!(
        switchint_bb,
        num_branches = branches.len(),
        switchint_depth,
        "virtual body: translated SwitchInt to ITE chain (#3188)"
    );

    Some(result)
}

/// Merge two `alias_updates` maps across an ITE branch.
///
/// For each key present in either side:
/// - Both present with same sort: `ite(guard, branch, result)`
/// - Only one present: use entry-state original for the missing side if sorts match
/// - Sort mismatch: drop that key (sound — over-approximation)
///
/// Part of #3936 D3: generalizes the former single-key receiver_update merge.
fn merge_alias_updates_ite(
    guard: &Expr,
    branch: BTreeMap<usize, Expr>,
    result: BTreeMap<usize, Expr>,
    at_entry: &HashMap<usize, Expr>,
    switchint_bb: usize,
) -> BTreeMap<usize, Expr> {
    let all_keys: HashSet<usize> = branch.keys().chain(result.keys()).copied().collect();
    let mut merged = BTreeMap::new();
    for key in all_keys {
        let merged_expr = match (branch.get(&key), result.get(&key)) {
            (Some(b), Some(r)) => {
                if b.sort() != r.sort() {
                    debug!(
                        switchint_bb,
                        key, "SwitchInt alias-update sort mismatch for key {key}, dropping"
                    );
                    continue;
                }
                Expr::ite(guard.clone(), b.clone(), r.clone())
            }
            (Some(b), None) => {
                if let Some(original) = at_entry.get(&key) {
                    if b.sort() == original.sort() {
                        Expr::ite(guard.clone(), b.clone(), original.clone())
                    } else {
                        b.clone()
                    }
                } else {
                    b.clone()
                }
            }
            (None, Some(r)) => {
                if let Some(original) = at_entry.get(&key) {
                    if r.sort() == original.sort() {
                        Expr::ite(guard.clone(), original.clone(), r.clone())
                    } else {
                        r.clone()
                    }
                } else {
                    r.clone()
                }
            }
            (None, None) => unreachable!("key came from one of the maps"),
        };
        merged.insert(key, merged_expr);
    }
    merged
}

/// Part of #55 piece 2: decide the taken SwitchInt target when the
/// discriminant evaluates to an exact constant.
///
/// MUST mirror the runtime guard semantics built in the merge fold of
/// `translate_switchint_ite`: bool discriminants match a branch when
/// `(value != 0) == discr`; bitvec discriminants match on raw-bits equality
/// after normalizing the branch's `u128` through `Expr::bitvec_const(value,
/// width)` — exactly the numeral the guard compares against. Returns `None`
/// (full ITE walk) for any sort or expression the evaluator cannot decide.
fn const_fold_switch_target(
    discr_expr: &Expr,
    branches: &[(u128, usize)],
    otherwise_bb: usize,
) -> Option<usize> {
    use trust_mc_core::chc_const_prop::eval::{try_eval_to_bool, try_eval_to_const};
    if discr_expr.sort().is_bool() {
        let b = try_eval_to_bool(discr_expr)?;
        return Some(
            branches.iter().find(|(v, _)| (*v != 0) == b).map(|(_, t)| *t).unwrap_or(otherwise_bb),
        );
    }
    let width = discr_expr.sort().bitvec_width()?;
    let folded = try_eval_to_const(discr_expr)?;
    let ay_bindings::ExprValue::BitVecConst { value: dv, .. } = folded.value() else {
        return None;
    };
    Some(
        branches
            .iter()
            .find(|(v, _)| {
                let guard_numeral = Expr::bitvec_const(*v, width);
                matches!(
                    guard_numeral.value(),
                    ay_bindings::ExprValue::BitVecConst { value: gv, .. } if gv == dv
                )
            })
            .map(|(_, t)| *t)
            .unwrap_or(otherwise_bb),
    )
}

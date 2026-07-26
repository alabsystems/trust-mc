// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Core inline body walker — entrypoint + linear CFG traversal.
//! Part of #3159, #3639: Extracted from codegen_call_virtual_inline.rs.
//! Part of #3913: Reduced to front-door setup + loop control.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::Instance;
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_ctx::diagnostics::CellCounter;
use super::super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::super::codegen_types::CodegenTypes;
use super::super::inline_body::speculative_inline;
use super::super::inline_budget::chc_inline_effective_block_limit;
use super::super::inline_shared::PlaceResolver;
use super::execution_state::InlineExecutionState;
use super::field_map::build_self_field_map;
use super::loop_replay::loop_exhaustion_fallback;
use super::statement_exec::execute_inline_statement;
use super::terminator_exec::{TerminatorStep, execute_inline_terminator};
use super::{InlineReturn, MAX_INLINE_DEPTH};
use crate::codegen_ay::shared::{count_effective_blocks, inline_effective_block_limit};

/// Translate a virtual method body inline. Part of #3159.
pub(in crate::codegen_ay::chc) fn translate_virtual_body_inline<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
    bb_idx: usize,
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_instance: Option<Instance>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    // Part of #4014: Pre-register statics in the callee body so their
    // addresses and initial values are available during the inline walk
    // and in the entry rule. Without this, statics only referenced in
    // callees (not the harness) have unconstrained memory.
    ctx.register_callee_body_statics(body);

    // Part of #3929: detect self-recursive calls and use harness unwind bound.
    let is_self_recursive = match (ctx.current_instance, inline_instance) {
        (Some(caller), Some(callee)) => caller.def.def_id() == callee.def.def_id(),
        _ => false,
    };
    // Part of #55 piece 3: const-argument recursion depth relief. When every
    // parameter of a self-recursive callee evaluates to an exact constant, the
    // single-arm switchInt fold (piece 2) unrolls one concrete level per
    // inline — grant a deep bound so fib(6)/fac(5)/hanoi walk to completion.
    // An explicit #[kani::unwind] still wins (exact Kani semantics), and a
    // per-harness node budget caps exponential call trees; once spent, relief
    // stops and exhaustion fail-closes on the existing typed recursion-unwind
    // lane below (never a silent PROOF).
    const CONST_RECURSION_MAX_DEPTH: usize = 64;
    const CONST_RECURSION_NODE_BUDGET: usize = 4096;
    let all_params_const = || {
        !params.is_empty()
            && params
                .iter()
                .all(|p| trust_mc_core::chc_const_prop::eval::try_eval_to_const(p).is_some())
    };
    let max_depth = if is_self_recursive && ctx.recursive_unwind_depth > 0 {
        ctx.recursive_unwind_depth as usize
    } else if is_self_recursive
        && ctx.const_recursion_nodes_spent < CONST_RECURSION_NODE_BUDGET
        && all_params_const()
    {
        ctx.const_recursion_nodes_spent += 1;
        CONST_RECURSION_MAX_DEPTH
    } else {
        MAX_INLINE_DEPTH
    };

    let saved_instance = ctx.current_instance;
    ctx.current_instance = inline_instance;
    let result = speculative_inline(ctx, |ctx| {
        translate_virtual_body_inline_impl(
            ctx,
            body,
            params,
            bb_idx,
            caller_vtable_ids,
            inline_depth,
            max_depth,
        )
    });
    ctx.current_instance = saved_instance;

    // Part of #3929 D4: when a recursive call exhausts its unwind budget,
    // the impl returns None. Instead of propagating None (which degrades to
    // the generic inferable-predicate fallback), return a typed
    // over-approximation so the exhaustion reason is explicit.
    // Part of #4058 D1: split on unwinding_assertions — when enabled, emit
    // an inline-assert fallback (`__assert_fail_inline*`) so the driver can
    // relabel the failure as a recursion unwinding assertion.
    if result.is_none() && is_self_recursive && inline_depth > max_depth {
        if let Some((_, ret_decl)) = body.local_decls().next() {
            if let Some(ret_sort) = ChcCtx::translate_ty(ret_decl.ty) {
                // Part of #4067: drop_in_place::<dyn T> self-recurses through vtable
                // dispatch. Skipping the drop is sound (only adds behaviors), so don't
                // emit a recursion unwinding assertion — return an unconstrained value.
                let fn_name: String = inline_instance.map(|i| i.name()).unwrap_or_default();
                let is_dyn_drop = fn_name.contains("drop_in_place") && fn_name.contains("dyn ");
                if !is_dyn_drop {
                    ctx.diagnostics.recursive_unwind_exhausted.inc();
                }
                debug!(
                    inline_depth,
                    max_depth,
                    unwinding_assertions = ctx.unwinding_assertions,
                    is_dyn_drop,
                    "recursive inline: unwind budget exhausted (#3929, #4058)"
                );
                if ctx.unwinding_assertions && !is_dyn_drop {
                    // Emit an inline-assert fallback that
                    // `extract_inline_assert_guard` will recognise as a
                    // fail-closed guard. The driver relabels this as a
                    // recursion unwinding assertion via the SMT marker.
                    let name = chc_fresh_name("__assert_fail_inline_recursive_unwind");
                    return Some(InlineReturn::value_only(declare_pending_var(name, ret_sort)));
                }
                if is_dyn_drop {
                    // Part of #4067: drop_in_place returns () which is Bool.
                    // Return a concrete unit value instead of unconstrained —
                    // skipping the drop body is sound and the return is always ().
                    // This avoids recording a sound_fallback that would prevent PROOF.
                    // Unit () translates to bool_sort() (codegen_types.rs:111),
                    // so we must return Bool, not BV64.
                    return Some(InlineReturn::value_only(Expr::bool_const(true)));
                }
                let name = chc_fresh_name("__recursive_unwind_exhausted");
                return Some(InlineReturn::value_only(declare_pending_var(name, ret_sort)));
            }
        }
    }

    result
}

/// Inner implementation with inline recursion depth tracking.
/// Part of #3614: Prevents stack overflow on recursive Rust functions.
fn translate_virtual_body_inline_impl<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
    bb_idx: usize,
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_depth: usize,
    max_depth: usize,
) -> Option<InlineReturn> {
    let ((), effective_blocks) = prepare_inline_walk(ctx, body, bb_idx, inline_depth, max_depth)?;

    let mut local_exprs: HashMap<usize, Expr> = HashMap::new();
    for (i, param) in params.iter().enumerate() {
        local_exprs.insert(i + 1, param.clone());
    }

    let inline_vtable_ids = caller_vtable_ids.clone();
    let self_field_map = build_self_field_map(ctx, body, params);
    debug!(
        bb_idx,
        field_map_entries = self_field_map.len(),
        param_count = params.len(),
        param0_sort = ?params.first().map(|p| p.sort()),
        "virtual inline: starting body translation (#3159 debug)"
    );

    let resolver = PlaceResolver::FieldMap(&self_field_map);
    let walk_ctx = InlineWalkCtx::new_with_loop_fuel_override(
        body,
        resolver,
        effective_blocks,
        bb_idx,
        current_spawn_scheduler_run_loop_fuel(ctx),
    );
    let state = InlineExecutionState::new(local_exprs, inline_vtable_ids, HashSet::new());
    let result = walk_blocks_to_return(ctx, &walk_ctx, 0, state, 0, inline_depth);
    if result.is_none() {
        debug!(bb_idx, "virtual inline: walk_blocks_to_return returned None");
    }
    result
}

/// Translate a MIR body inline with a pre-built PlaceResolver and local_exprs.
/// Part of #3241: neutral walker API for closure-walker unification.
pub(in crate::codegen_ay::chc) fn translate_body_with_resolver<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    local_exprs: HashMap<usize, Expr>,
    resolver: PlaceResolver<'_>,
    bb_idx: usize,
    caller_vtable_ids: HashMap<usize, Expr>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    // Part of #4014: Pre-register callee statics (same as translate_virtual_body_inline).
    ctx.register_callee_body_statics(body);
    speculative_inline(ctx, |ctx| {
        let ((), effective_blocks) =
            prepare_inline_walk(ctx, body, bb_idx, inline_depth, MAX_INLINE_DEPTH)?;

        let walk_ctx = InlineWalkCtx::new_with_loop_fuel_override(
            body,
            resolver,
            effective_blocks,
            bb_idx,
            current_spawn_scheduler_run_loop_fuel(ctx),
        );
        let state = InlineExecutionState::new(local_exprs, caller_vtable_ids, HashSet::new());
        walk_blocks_to_return(ctx, &walk_ctx, 0, state, 0, inline_depth)
    })
}

fn current_spawn_scheduler_run_loop_fuel(ctx: &ChcCtx<'_, '_>) -> Option<usize> {
    let callee = super::current_inline_callee_name(ctx)?;
    let is_scheduler_run = callee.contains("Scheduler") && callee.contains("run");
    is_scheduler_run
        .then(|| ctx.spawn_scheduler_vtable_model.as_ref()?.scheduler_loop_replay_fuel())
        .flatten()
}

/// Shared preflight for both front doors: depth guard + budget check.
/// Returns `((), effective_blocks)` on success, `None` if the body is too
/// large or the recursion limit is exceeded.
/// Part of #3929: `max_depth` allows callers to override `MAX_INLINE_DEPTH`
/// for self-recursive calls using the harness unwind bound.
fn prepare_inline_walk(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    bb_idx: usize,
    inline_depth: usize,
    max_depth: usize,
) -> Option<((), usize)> {
    if inline_depth > max_depth {
        debug!(bb_idx, inline_depth, max_depth, "inline body: depth limit reached (#3614, #3929)");
        return None;
    }
    let effective_blocks = count_effective_blocks(body);
    let shared_limit = inline_effective_block_limit(body, effective_blocks);
    let limit = chc_inline_effective_block_limit(body, effective_blocks);
    let callee = super::current_inline_callee_name(ctx).unwrap_or_else(|| "<unknown>".to_string());
    // Part of #4075: When the spawn scheduler vtable model is active, the
    // block_on handler is inlining Scheduler::block_on, which calls
    // Scheduler::run as a nested call. Scheduler::run has a while loop that
    // exceeds the normal block limit but is handled by bounded loop replay
    // (fuel=5). Apply a relaxed limit so the walker can enter the body.
    // The limit is generous (80 blocks) to accommodate MIR expansion of the
    // scheduler loop + poll dispatch + Vec/Option operations.
    // Only relax for Scheduler::run itself — not all nested calls.
    const MAX_INLINE_SPAWN_SCHEDULER_BLOCKS: usize = 80;
    let is_scheduler_run = callee.contains("Scheduler") && callee.contains("run");
    let spawn_relaxed = ctx.spawn_scheduler_vtable_model.is_some()
        && is_scheduler_run
        && effective_blocks <= MAX_INLINE_SPAWN_SCHEDULER_BLOCKS;
    if effective_blocks > limit && !spawn_relaxed {
        debug!(
            bb_idx,
            inline_depth,
            effective_blocks,
            shared_limit,
            chc_limit = limit,
            %callee,
            "inline body: body too large"
        );
        return None;
    }
    if spawn_relaxed && effective_blocks > limit {
        debug!(
            bb_idx,
            inline_depth,
            effective_blocks,
            shared_limit,
            chc_limit = limit,
            spawn_limit = MAX_INLINE_SPAWN_SCHEDULER_BLOCKS,
            %callee,
            "inline body: admitted via spawn scheduler relaxed budget (#4075)"
        );
    }
    if effective_blocks > shared_limit {
        debug!(
            bb_idx,
            inline_depth,
            effective_blocks,
            shared_limit,
            chc_limit = limit,
            %callee,
            "inline body: admitted via CHC relaxed budget"
        );
    }
    Some(((), effective_blocks))
}

// Re-export: struct moved to loop_replay.rs (#3853).
pub(in crate::codegen_ay::chc) use super::loop_replay::InlineWalkCtx;

/// Walk basic blocks from `start_bb` until Return. Part of #3188.
/// Part of #3913: reduced to thin loop — statement and terminator logic
/// delegated to `statement_exec` and `terminator_exec`.
pub(in crate::codegen_ay::chc) fn walk_blocks_to_return<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    start_bb: usize,
    mut state: InlineExecutionState,
    switchint_depth: usize,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let mut current_bb = start_bb;
    let mut visited = 0usize;
    let total_loop_fuel: usize = walk_ctx.loop_header_fuel.borrow().values().copied().sum();
    let visit_limit = if total_loop_fuel > 0 {
        walk_ctx.effective_blocks * (total_loop_fuel + 1)
    } else {
        walk_ctx.effective_blocks
    };
    loop {
        if current_bb >= walk_ctx.body.blocks.len() || visited > visit_limit {
            debug!(current_bb, visited, visit_limit, "walker bail: block bounds exceeded");
            return None;
        }
        // Part of #3853: check loop header fuel before processing block.
        // Part of #4050: on exhaustion, take the loop EXIT path instead of
        // returning an unconstrained fallback. This matches kani::unwind(N)
        // semantics: after N iterations, assume the loop terminates.
        //
        // MIR while-loop patterns:
        //   Pattern A: header has SwitchInt directly → otherwise is the exit.
        //   Pattern B: header is Goto → condition_check has SwitchInt →
        //     otherwise is the exit.
        //   Pattern C: header calls Vec::len() → target has SwitchInt.
        // In all cases, we process statements and follow Goto/Call chains
        // until we reach the SwitchInt, then take its otherwise (exit) target.
        {
            let mut fuel = walk_ctx.loop_header_fuel.borrow_mut();
            if let Some(f) = fuel.get_mut(&current_bb) {
                if *f == 0 {
                    // Remove this header from fuel map so re-entry
                    // (e.g., from the exit path looping back) won't
                    // trigger the exhaustion handler again.
                    let exhausted_bb = current_bb;
                    fuel.remove(&exhausted_bb);
                    drop(fuel);
                    let mut exit_bb = exhausted_bb;
                    let mut hops = 0usize;
                    const MAX_EXIT_HOPS: usize = 3;
                    let exit_target = loop {
                        if exit_bb >= walk_ctx.body.blocks.len() || hops >= MAX_EXIT_HOPS {
                            break None;
                        }
                        let block = &walk_ctx.body.blocks[exit_bb];
                        for stmt in &block.statements {
                            execute_inline_statement(ctx, walk_ctx, &mut state, stmt, exit_bb)?;
                        }
                        match &block.terminator.kind {
                            TerminatorKind::SwitchInt { targets, .. } => {
                                break Some(targets.otherwise());
                            }
                            TerminatorKind::Goto { target } => {
                                exit_bb = *target;
                                hops += 1;
                            }
                            // Pattern C: header calls Vec::len() (or similar)
                            // then the call target has the SwitchInt condition.
                            TerminatorKind::Call { target: Some(t), .. } => {
                                exit_bb = *t;
                                hops += 1;
                            }
                            _ => break None,
                        }
                    };
                    if let Some(exit) = exit_target {
                        debug!(
                            current_bb,
                            exit, hops, "walker: loop fuel exhausted, taking exit branch (#4050)"
                        );
                        current_bb = exit;
                        visited += 1;
                        continue;
                    }
                    return loop_exhaustion_fallback(ctx, walk_ctx);
                }
                *f -= 1;
            }
        }
        visited += 1;
        let block = &walk_ctx.body.blocks[current_bb];

        // Execute all statements in this block.
        for stmt in &block.statements {
            execute_inline_statement(ctx, walk_ctx, &mut state, stmt, current_bb)?;
        }

        // Execute the terminator.
        match execute_inline_terminator(
            ctx,
            walk_ctx,
            &mut state,
            current_bb,
            switchint_depth,
            inline_depth,
        ) {
            TerminatorStep::ContinueAt(next) => current_bb = next,
            TerminatorStep::Return(result) => return result,
        }
    }
}

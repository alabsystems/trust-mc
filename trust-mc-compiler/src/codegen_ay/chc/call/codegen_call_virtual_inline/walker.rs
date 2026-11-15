// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Core inline body walker — entrypoint + linear CFG traversal.
//! Part of #3159, #3639: Extracted from codegen_call_virtual_inline.rs.
//! Part of #3913: Reduced to front-door setup + loop control.

use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc};
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::Instance;
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::chc_fresh_name;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_body::speculative_inline;
use super::super::inline_budget::chc_inline_effective_block_limit;
use super::super::inline_shared::PlaceResolver;
use super::execution_state::InlineExecutionState;
use super::field_map::build_self_field_map;
use super::loop_replay::LoopHeaderVisit;
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
    ctx.spend_inline_work()?;
    #[cfg(all(trust_toolchain, version("1.101")))]
    if inline_instance.as_ref().is_some_and(|instance| {
        crate::codegen_ay::native_init_boundary(ctx.tcx, instance).is_some()
            || crate::codegen_ay::native_maybe_unsafe_accessor(ctx.tcx, instance)
    }) {
        ctx.record_sound_fallback_reason("native_initialized_handoff_walk_without_custody");
        return None;
    }
    #[cfg(all(trust_toolchain, version("1.101")))]
    if crate::codegen_ay::shared::native_maybe_memory::body_has_native_maybe_memory(ctx.tcx, body) {
        ctx.record_sound_fallback_reason("native_maybe_frame_without_initializedness_provenance");
        return None;
    }
    // Part of #4014: Pre-register statics in the callee body so their
    // addresses and initial values are available during the inline walk
    // and in the entry rule. Without this, statics only referenced in
    // callees (not the harness) have unconstrained memory.
    ctx.register_callee_body_consts(body);
    // Memory the callee rewrites or reads under a type it was not written as
    // (`stmt/codegen_stmt_store/untyped_view_scan.rs`).
    ctx.record_untyped_view_reasons_for_inline_body(body, inline_instance);

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
    // The subslice side tables are keyed by LOCAL, and this body's locals are
    // its own index space: an entry the walk records (a slice view's length)
    // must not outlive it and be read by a host or caller local of the same
    // index, nor overwrite theirs; and an entry the host or a caller walk
    // holds must not be read by this body's local of the same index
    // ([`enter_body_subslice_scope`]). Restored after the walk.
    let saved_subslice = enter_body_subslice_scope(ctx, body);
    // Phase 0 (call/inline_walk_guard.rs): the outermost walk takes the write
    // mark F1 reads against, and every walk gets its own frame of
    // address-bound reference locals (F2).
    let result = ctx.with_inline_walk_write_mark(|ctx| {
        speculative_inline(ctx, |ctx| {
            ctx.with_inline_walk_frame(body, |ctx| {
                translate_virtual_body_inline_impl(
                    ctx,
                    body,
                    params,
                    bb_idx,
                    caller_vtable_ids,
                    inline_depth,
                    max_depth,
                )
            })
        })
    });
    ctx.current_instance = saved_instance;
    exit_body_subslice_scope(ctx, saved_subslice);

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
                // Booked through the counter the driver turns into a recursion
                // unwinding failure (`RECURSIVE_UNWIND_ASSERTION`).
                let booked =
                    (!is_dyn_drop).then(|| ctx.diagnostics.book_recursive_unwind_exhausted());
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
                    return Some(InlineReturn::value_only(ExactVar::unobserved(name, ret_sort)));
                }
                if is_dyn_drop {
                    // Part of #4067: drop_in_place returns () which is Bool.
                    // Return a concrete unit value instead of unconstrained —
                    // the return is always (). Unit () translates to
                    // bool_sort() (codegen_types.rs:111), so we must return
                    // Bool, not BV64.
                    //
                    // Skipping the drop body is sound for the VALUE and the
                    // state it frees, not for its checks: a `Drop::drop`
                    // `assert!`, a dealloc's validity. It used to record
                    // nothing ("only adds behaviors"), so a nested `dyn` drop
                    // past the depth bound lost them. It fails closed now when
                    // the skipped drop can carry an obligation
                    // (fix/chc-walker-fail-closed, item c).
                    let skipped_may_fail = inline_instance.is_none_or(|instance| {
                        crate::codegen_ay::obligation_free_walk::instance_obligation_verdict(
                            ctx.tcx,
                            instance,
                            &crate::kani_middle::transform::walker_stub_map(),
                        ) != crate::codegen_ay::obligation_free_walk::Verdict::Free
                    });
                    if skipped_may_fail {
                        ctx.record_sound_fallback_reason("walker_dyn_drop_depth_skipped");
                    }
                    return Some(InlineReturn::value_only(Expr::bool_const(true)));
                }
                let name = chc_fresh_name("__recursive_unwind_exhausted");
                let booked = booked.expect("the dyn-drop path returned above");
                return Some(InlineReturn::value_only(Havoc::booked(booked, name, ret_sort)));
            }
        }
    }

    result
}

/// The subslice side-table entries (`ref_resolution.subslice_len` /
/// `subslice_offset`) of every local index `body` has, which a walk of it
/// restores when it ends ([`restore_body_subslice_entries`]).
type BodySubsliceEntries = Vec<(usize, Option<Expr>, Option<Expr>)>;

fn save_body_subslice_entries(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> BodySubsliceEntries {
    (0..body.locals().len())
        .map(|local| {
            (
                local,
                ctx.ref_resolution.subslice_len.get(&local).cloned(),
                ctx.ref_resolution.subslice_offset.get(&local).cloned(),
            )
        })
        .collect()
}

/// Enter a walked body's subslice scope: save the entries of every local
/// index `body` has, then CLEAR them and apply only the argument entries the
/// front door handed over (`ref_resolution.inline_arg_subslice_seeds`, taken
/// here so a later walk cannot inherit them).
///
/// Saving and restoring alone scoped what the walk WRITES; its argument
/// locals, which the walk never writes, still read whatever the host or a
/// caller walk left at the same index. A nested callee's argument `_5` read
/// the caller walk's `_5`, an array view of length 4, and a walked method's
/// argument `_3` read the harness's `_3`, a subslice of length 6: a length
/// assertion on the argument verified clean where Kani fails it, and its
/// safe twin was certified Genuine (walker fail-closed review 6 round 2,
/// finding 3, `rp3b_slice_len_index.rs`). An argument with no seed has no
/// entry: its length is read from its own value.
fn enter_body_subslice_scope(
    ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> BodySubsliceEntries {
    let saved = save_body_subslice_entries(ctx, body);
    let seeds = ctx.ref_resolution.inline_arg_subslice_seeds.take();
    let local_count = body.locals().len();
    for local in 0..local_count {
        ctx.ref_resolution.subslice_len.remove(&local);
        ctx.ref_resolution.subslice_offset.remove(&local);
    }
    if let Some((lens, offsets)) = seeds {
        let arg_range = 1..=body.arg_locals().len();
        for (local, len) in lens {
            if arg_range.contains(&local) {
                ctx.ref_resolution.subslice_len.insert(local, len);
            }
        }
        for (local, offset) in offsets {
            if arg_range.contains(&local) {
                ctx.ref_resolution.subslice_offset.insert(local, offset);
            }
        }
    }
    saved
}

/// Leave a walked body's subslice scope: capture its return local's entries
/// (`ref_resolution.inline_return_subslice`) and restore the saved ones.
fn exit_body_subslice_scope(ctx: &mut ChcCtx<'_, '_>, saved: BodySubsliceEntries) {
    ctx.ref_resolution.inline_return_subslice = (
        ctx.ref_resolution.subslice_len.get(&0).cloned(),
        ctx.ref_resolution.subslice_offset.get(&0).cloned(),
    );
    restore_body_subslice_entries(ctx, saved);
}

fn restore_body_subslice_entries(ctx: &mut ChcCtx<'_, '_>, saved: BodySubsliceEntries) {
    for (local, len, offset) in saved {
        match len {
            Some(len) => {
                ctx.ref_resolution.subslice_len.insert(local, len);
            }
            None => {
                ctx.ref_resolution.subslice_len.remove(&local);
            }
        }
        match offset {
            Some(offset) => {
                ctx.ref_resolution.subslice_offset.insert(local, offset);
            }
            None => {
                ctx.ref_resolution.subslice_offset.remove(&local);
            }
        }
    }
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

    // Seed the ARGUMENT locals only. A caller can pass more operands than the
    // body has arguments: `Fn::call(&closure, ())` hands a zero-argument
    // closure body (arg_count 1: its environment) the untupled `()` as a second
    // operand. Seeding it bound `()` to local 2, the body's first TEMP, so when
    // the rvalue that defines that temp was declined, later reads saw the stale
    // `()` instead of an unpopulated local: `bytes.len() == 1` read `1 == 1`.
    let arg_count = body.arg_locals().len();
    let mut local_exprs: HashMap<usize, Expr> = HashMap::new();
    for (i, param) in params.iter().take(arg_count).enumerate() {
        local_exprs.insert(i + 1, param.clone());
    }
    if params.len() > arg_count {
        debug!(
            params = params.len(),
            arg_count, "virtual inline: more operands than argument locals; seeding arguments only"
        );
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
    let spawn_loop_fuel = current_spawn_scheduler_run_loop_fuel(ctx);
    let declared_unwind = ctx.recursive_unwind_depth as usize;
    let new_walk_ctx = || {
        InlineWalkCtx::new_with_loop_policy(
            body,
            resolver,
            effective_blocks,
            bb_idx,
            spawn_loop_fuel,
            declared_unwind,
        )
    };
    let walk_ctx = new_walk_ctx();
    // The caller's assumed bound on an argument, visible at the host call
    // (`host_call_assumed_bound`), raises the replay of the body the host
    // walks: paths within the bound are then replayed, and the abandoned
    // arm past them is one the host's assumption makes infeasible, so a
    // counterexample within the bound is not shadowed by the arm's reach
    // check. Only more replay, never less; ignored under a declared unwind,
    // which the replay follows exactly.
    //
    // Only where that reach check exists: a loop whose abandoned region can
    // carry an obligation (`uncertified_check::region_may_carry_obligation`
    // from its header, the loop and everything after it). Elsewhere the arm
    // past the replay is the sound value havoc, a proof over it is a proof,
    // and the raise bought nothing but time: 17 passes of a loop whose state
    // feeds an index or itself several times (`acc += table[acc % 4]`) made
    // a term the walk finished and compilation then stalled on (a
    // CompileTimeout that took every harness of the file with it), or the
    // solver gave up, on programs main proves in about 10 s (walker
    // fail-closed review 6, finding 5, `rj_dep_safe20`, `rj_dep_scalar20`).
    //
    // And only where the raised walk stays small: the walk is speculative,
    // and a result whose terms, written out as trees, exceed
    // `MAX_RAISED_REPLAY_TREE_NODES` is discarded for the walk at the
    // built-in replay count. A loop whose state feeds its own update several
    // times (an index derived from the accumulator, `table[(acc as i8 % 4)
    // as usize]`) doubles the written-out term every pass; the walk shares
    // it, but what compiles it afterwards does not, and 17 passes did not
    // compile in 155 s (`g2_signed_rem_index_bug`, `g3_trunc_cast_index_bug`).
    //
    // And only where the raised replay can reach the loop's exit: a bound
    // past the replay ceiling leaves the loop abandoned, its arm's reach
    // check in place, and the raise bought 16 passes of every loop of every
    // candidate instead of 5. `rg_region.rs` (`n < 20`, eight harnesses each
    // walking nine `Run` impls) took 128 s as a whole file where main takes
    // 92 s, and under load one harness's solve overran into the driver's
    // 365 s watchdog, leaving four harnesses undecided (walker fail-closed
    // review 6 round 2, finding 7).
    let raise = if inline_depth == 0
        && ctx.recursive_unwind_depth == 0
        && let Some(bound) = host_call_assumed_bound(ctx, bb_idx)
        && InlineWalkCtx::raise_covers(bound)
        && walk_ctx
            .fuelled_headers()
            .any(|header| super::uncertified_check::region_may_carry_obligation(ctx, body, header))
    {
        Some(bound)
    } else {
        None
    };
    if let Some(bound) = raise {
        let mut raised_ctx = new_walk_ctx();
        raised_ctx.raise_loop_fuel(bound.saturating_add(1));
        debug!(bb_idx, bound, "walker: the caller's assumed bound raises the replay");
        let state = InlineExecutionState::new(
            local_exprs.clone(),
            inline_vtable_ids.clone(),
            HashSet::new(),
        );
        let raised = speculative_inline(ctx, |ctx| {
            let result = walk_blocks_to_return(ctx, &raised_ctx, 0, None, state, 0, inline_depth)?;
            let size = inline_return_tree_size(&result, MAX_RAISED_REPLAY_TREE_NODES);
            debug!(bb_idx, bound, size, "walker: raised replay written-out size");
            if size > MAX_RAISED_REPLAY_TREE_NODES {
                debug!(
                    bb_idx,
                    bound,
                    size,
                    "walker: the raised replay's terms are too large — built-in replay instead"
                );
                ctx.note_gap_reason("walker_raised_replay_too_large");
                return None;
            }
            Some(result)
        });
        if raised.is_some() {
            return raised;
        }
    }
    // Under a declared unwind bound the replay follows Kani's passes exactly
    // (package round 2 item b), and a std loop walked that way can build
    // terms AY refuses ("datatype signature surface exceeds copy/comparison
    // work bound": `slice::contains` over six elements under `unwind(8)`,
    // 545,843 nodes written out) or cannot decide in the harness's budget,
    // where the built-in replay failed closed at once (walker fail-closed
    // review 6 round 2, finding 6, `ct_contains_u8_safe`, `mx_max_u8_safe`).
    // The top-level walk is therefore speculative: a result whose terms,
    // written out as trees, pass `MAX_DECLARED_REPLAY_TREE_NODES` is
    // discarded and the walk fails closed (a `FailClose` record, so neither a
    // proof nor a certified counterexample rests on the call). Re-walking
    // with capped loop fuel was measured and rejected: it compiled, but left
    // 181 properties (163 memory-safety checks of the walked passes) that AY
    // could not decide in the harness's budget, 67 s for a false failure the
    // base decides in under a second.
    if inline_depth == 0 && declared_unwind > 0 {
        let state = InlineExecutionState::new(
            local_exprs.clone(),
            inline_vtable_ids.clone(),
            HashSet::new(),
        );
        let mut too_large = false;
        let exact = speculative_inline(ctx, |ctx| {
            let result = walk_blocks_to_return(ctx, &walk_ctx, 0, None, state, 0, inline_depth)?;
            let size = inline_return_tree_size(&result, MAX_DECLARED_REPLAY_TREE_NODES);
            debug!(
                bb_idx,
                declared_unwind, size, "walker: declared-unwind replay written-out size"
            );
            if size > MAX_DECLARED_REPLAY_TREE_NODES {
                too_large = true;
                return None;
            }
            Some(result)
        });
        if !too_large {
            if exact.is_none() {
                debug!(bb_idx, "virtual inline: walk_blocks_to_return returned None");
            }
            return exact;
        }
        debug!(
            bb_idx,
            declared_unwind,
            "walker: the declared-unwind replay's terms are too large — failing closed"
        );
        ctx.note_gap_reason(WALKER_DECLARED_REPLAY_TOO_LARGE);
        ctx.record_sound_fallback_reason(WALKER_DECLARED_REPLAY_TOO_LARGE);
        return None;
    }
    let state = InlineExecutionState::new(local_exprs, inline_vtable_ids, HashSet::new());
    if inline_depth > 0 {
        let result = walk_blocks_to_return(ctx, &walk_ctx, 0, None, state, 0, inline_depth);
        if result.is_none() {
            debug!(bb_idx, "virtual inline: walk_blocks_to_return returned None");
        }
        return result;
    }
    // The ordinary replay has the same ceiling the raised and declared ones
    // have, set where compilation stops keeping up: a replay that grew past
    // `MAX_ORDINARY_REPLAY_TREE_NODES` written out fails closed, as the
    // declared-unwind one does. The walker shares its terms; what compiles
    // them afterwards does not (walker fail-closed review 6 round 3: a replay
    // run to the SwitchInt depth limit did not compile in 600 s).
    let mut too_large = false;
    let result = speculative_inline(ctx, |ctx| {
        let result = walk_blocks_to_return(ctx, &walk_ctx, 0, None, state, 0, inline_depth)?;
        let size = inline_return_tree_size(&result, MAX_ORDINARY_REPLAY_TREE_NODES);
        if size > MAX_ORDINARY_REPLAY_TREE_NODES {
            debug!(bb_idx, size, "walker: the replay's terms are too large — failing closed");
            too_large = true;
            return None;
        }
        Some(result)
    });
    if too_large {
        ctx.note_gap_reason(WALKER_REPLAY_TOO_LARGE);
        ctx.record_sound_fallback_reason(WALKER_REPLAY_TOO_LARGE);
    } else if result.is_none() {
        debug!(bb_idx, "virtual inline: walk_blocks_to_return returned None");
    }
    result
}

/// The ceiling on the written-out size of an ordinary top-level walk's
/// result, past which the walk fails closed. Above the raised replay's
/// ceiling: measured on those walks, 598,628 nodes compiled in 9.7 s and
/// 2,079,723 did not compile in 155 s (`MAX_RAISED_REPLAY_TREE_NODES`).
const MAX_ORDINARY_REPLAY_TREE_NODES: u64 = 1_000_000;

/// The fail-closed record of a top-level walk abandoned because it grew past
/// [`MAX_ORDINARY_REPLAY_TREE_NODES`] (a `FailClose` reason).
const WALKER_REPLAY_TOO_LARGE: &str = "walker_replay_too_large";

/// The ceiling on the written-out size of a top-level walk's result under a
/// declared unwind bound, past which the body is walked again with capped
/// loop fuel (see `translate_virtual_body_inline_impl`). Calibrated in
/// docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed: repair
/// round 2".
const MAX_DECLARED_REPLAY_TREE_NODES: u64 = 200_000;

/// The fail-closed record of a top-level walk abandoned because its
/// declared-unwind replay grew past [`MAX_DECLARED_REPLAY_TREE_NODES`] (a
/// `FailClose` reason: `codegen_ctx::fallback_soundness` does not bless it).
const WALKER_DECLARED_REPLAY_TOO_LARGE: &str = "walker_declared_replay_too_large";

/// The ceiling on the written-out size of a raised replay's result
/// ([`inline_return_tree_size`]), past which the walk falls back to the
/// built-in replay count (see `translate_virtual_body_inline_impl`).
/// Measured 2026-09-28 on the raised walks of walker fail-closed review 6,
/// finding 5 (ay 22db3bcc1): `b_assume_bound_safe` 774, the region probes
/// `g6` 8,273 and `g1` 22,783, each compiling in about a second; `g4`
/// 598,628, 9.7 s of compilation; `g2` 2,079,723, not compiled in 155 s.
const MAX_RAISED_REPLAY_TREE_NODES: u64 = 200_000;

/// The size of an inline walk's result written out as trees (its value, its
/// vtable and alias updates, and its side-channel checks), counting a shared
/// subterm once per occurrence, saturating a little past `cap`. Computed over
/// the shared DAG with one visit per node.
fn inline_return_tree_size(result: &InlineReturn, cap: u64) -> u64 {
    let tree_size = expr_written_out_size;
    let mut memo = HashMap::new();
    let mut total = tree_size(&result.value, &mut memo, cap);
    for expr in result.vtable.iter().chain(result.alias_updates.values()) {
        total = total.saturating_add(tree_size(expr, &mut memo, cap));
    }
    for check in &result.deferred_checks {
        total = total.saturating_add(tree_size(&check.check, &mut memo, cap));
    }
    total
}

/// The size of `expr` written out as a tree (a shared subterm counted once
/// per occurrence), saturating a little past `cap`, computed over the shared
/// DAG with one visit per node (`memo` is keyed by node identity and may be
/// shared across terms).
pub(in crate::codegen_ay::chc) fn expr_written_out_size(
    expr: &Expr,
    memo: &mut HashMap<*const ay_bindings::ExprValue, u64>,
    cap: u64,
) -> u64 {
    let key = std::ptr::from_ref(expr.value());
    if let Some(&size) = memo.get(&key) {
        return size;
    }
    let mut size: u64 = 1;
    for child in expr.children() {
        size =
            size.saturating_add(expr_written_out_size(child, memo, cap)).min(cap.saturating_mul(2));
    }
    memo.insert(key, size);
    size
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
    ctx.spend_inline_work()?;
    // Part of #4014: Pre-register callee statics (same as translate_virtual_body_inline).
    ctx.register_callee_body_consts(body);
    // A closure body: the same untyped-view nets.
    ctx.record_untyped_view_reasons_for_inline_body(body, None);
    // The walk's subslice entries are scoped to this body, as in
    // `translate_virtual_body_inline`.
    let saved_subslice = enter_body_subslice_scope(ctx, body);
    // Phase 0 (call/inline_walk_guard.rs): write mark and frame, as in
    // `translate_virtual_body_inline`.
    let result = ctx.with_inline_walk_write_mark(|ctx| {
        speculative_inline(ctx, |ctx| {
            ctx.with_inline_walk_frame(body, |ctx| {
                let ((), effective_blocks) =
                    prepare_inline_walk(ctx, body, bb_idx, inline_depth, MAX_INLINE_DEPTH)?;

                let walk_ctx = InlineWalkCtx::new_with_loop_policy(
                    body,
                    resolver,
                    effective_blocks,
                    bb_idx,
                    current_spawn_scheduler_run_loop_fuel(ctx),
                    ctx.recursive_unwind_depth as usize,
                );
                let state =
                    InlineExecutionState::new(local_exprs, caller_vtable_ids, HashSet::new());
                walk_blocks_to_return(ctx, &walk_ctx, 0, None, state, 0, inline_depth)
            })
        })
    });
    exit_body_subslice_scope(ctx, saved_subslice);
    result
}

/// The largest of the bounds the HOST assumes on the arguments of the call in
/// its block `bb_idx` (per argument the tightest): `kani::assume(x <= K)` (or
/// `x < K`, `K >= x`, `K > x`, `x == K`) over a local `x` the call passes
/// whole. Read syntactically, with no dominance or reassignment reasoning,
/// because it only sizes the replay: a wrong bound costs precision or time,
/// never soundness. `None` when the block is no call or nothing bounds its
/// arguments.
fn host_call_assumed_bound(ctx: &ChcCtx<'_, '_>, bb_idx: usize) -> Option<usize> {
    use rustc_public::mir::{BinOp, Operand, Rvalue, StatementKind};
    let host = ctx.body;
    let TerminatorKind::Call { args, .. } = &host.blocks.get(bb_idx)?.terminator.kind else {
        debug!(bb_idx, "walker: host block is no call; no assumed bound");
        return None;
    };
    let arg_locals: HashSet<usize> = args
        .iter()
        .filter_map(|arg| match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        })
        .collect();
    if arg_locals.is_empty() {
        return None;
    }
    // Each bool local defined by a comparison of an argument with a constant:
    // the argument and its bound.
    let mut bounds_by_cond: HashMap<usize, (usize, u128)> = HashMap::new();
    for block in &host.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, Rvalue::BinaryOp(op, lhs, rhs)) = &stmt.kind else {
                continue;
            };
            if !place.projection.is_empty() {
                continue;
            }
            let local_of = |op: &Operand| match op {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            };
            let constant = |op: &Operand| {
                super::super::codegen_call_vec_builder_pattern::extract_operand_const_uint(op)
            };
            let bound = match (op, local_of(lhs), constant(rhs), local_of(rhs), constant(lhs)) {
                (BinOp::Le | BinOp::Eq, Some(l), Some(k), _, _) => Some((l, k)),
                (BinOp::Lt, Some(l), Some(k), _, _) => k.checked_sub(1).map(|k| (l, k)),
                (BinOp::Ge | BinOp::Eq, _, _, Some(l), Some(k)) => Some((l, k)),
                (BinOp::Gt, _, _, Some(l), Some(k)) => k.checked_sub(1).map(|k| (l, k)),
                _ => None,
            };
            if let Some((local, bound)) = bound
                && arg_locals.contains(&local)
            {
                bounds_by_cond.insert(place.local, (local, bound));
            }
        }
    }
    let mut per_arg: HashMap<usize, u128> = HashMap::new();
    for block in &host.blocks {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
            continue;
        };
        if !matches!(
            ctx.detect_kani_hook(func),
            Some(crate::kani_middle::kani_functions::KaniHook::Assume)
        ) {
            continue;
        }
        if let Some(Operand::Copy(cond) | Operand::Move(cond)) = args.first()
            && cond.projection.is_empty()
            && let Some(&(local, bound)) = bounds_by_cond.get(&cond.local)
        {
            let tightest = per_arg.entry(local).or_insert(bound);
            *tightest = (*tightest).min(bound);
        }
    }
    per_arg.values().max().and_then(|&b| usize::try_from(b).ok())
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

/// Kani's description of an unwinding-assertion failure (`unwinding assertion
/// loop N`; the walker does not number loops).
use super::host_bound_discharge::LOOP_UNWINDING_ASSERTION_MESSAGE;

// Re-export: struct moved to loop_replay.rs (#3853).
pub(in crate::codegen_ay::chc) use super::loop_replay::InlineWalkCtx;

/// Walk basic blocks from `start_bb` until Return. Part of #3188.
/// Part of #3913: reduced to thin loop — statement and terminator logic
/// delegated to `statement_exec` and `terminator_exec`.
/// `entry_pred` is the block the walk comes from (the SwitchInt of an arm
/// walk; `None` at the body's entry), which the declared-unwind replay reads
/// to tell a loop's entry from its back edge.
pub(in crate::codegen_ay::chc) fn walk_blocks_to_return<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    start_bb: usize,
    entry_pred: Option<usize>,
    mut state: InlineExecutionState,
    switchint_depth: usize,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let mut current_bb = start_bb;
    let mut pred_bb = entry_pred;
    let mut visited = 0usize;
    let total_loop_fuel: usize = walk_ctx.loop_header_fuel.borrow().values().copied().sum();
    let visit_limit = if total_loop_fuel > 0 {
        walk_ctx.effective_blocks * (total_loop_fuel + 1)
    } else {
        walk_ctx.effective_blocks
    };
    loop {
        crate::codegen_ay::translation_deadline::check("chc_inline_walker");
        ctx.spend_inline_work()?;
        if current_bb >= walk_ctx.body.blocks.len() || visited > visit_limit {
            debug!(current_bb, visited, visit_limit, "walker bail: block bounds exceeded");
            return None;
        }
        // Part of #3853: account the visit against the loop header's fuel
        // (`InlineWalkCtx::visit_loop_header`). The visit that finds the fuel
        // spent is the loop's last pass and walks on: the exit test decides,
        // exactly. A path back at that header needs more iterations than the
        // walker replays, so its walk fails here and the SwitchInt arm it is
        // on takes the bailed-arm fallback (switchint.rs), which accounts for
        // everything past this point. This replaced the #4050 exit-branch
        // jump, which skipped the exit test (see `visit_loop_header`).
        match walk_ctx.visit_loop_header(current_bb, pred_bb) {
            LoopHeaderVisit::Continue => {}
            LoopHeaderVisit::LastPass => {
                debug!(current_bb, "walker: loop fuel spent, last pass through the header");
            }
            LoopHeaderVisit::Outrun => {
                debug!(
                    current_bb,
                    "walker bail: back at a spent loop header — the loop outruns the replay bound"
                );
                return None;
            }
            LoopHeaderVisit::UnwindExceeded => {
                // Kani's unwinding assertion fails here, exactly: the path
                // needs one more pass than the declared bound allows
                // (`InlineWalkCtx::visit_loop_header`). The failure is
                // recorded (with unwinding assertions on) and the path ends,
                // as Kani's `assert(false); assume(false)` does.
                debug!(
                    current_bb,
                    "walker: loop passes the declared unwind bound — unwinding assertion"
                );
                if ctx.unwinding_assertions {
                    state.record_deferred_check(
                        trust_mc_core::violation::PropertyKind::Other,
                        Some(LOOP_UNWINDING_ASSERTION_MESSAGE.to_string()),
                        ay_bindings::Expr::bool_const(false),
                        ctx.heap_state.write_mark(),
                    );
                }
                return super::switchint::pruned_path_return(ctx, walk_ctx, state);
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
            TerminatorStep::ContinueAt(next) => {
                pred_bb = Some(current_bb);
                current_bb = next;
            }
            TerminatorStep::Return(result) => return result,
        }
    }
}

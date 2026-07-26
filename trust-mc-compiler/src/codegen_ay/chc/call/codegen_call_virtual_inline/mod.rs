// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline body translation for devirtualized method calls.
//!
//! Translates a concrete method body into AY expressions, walking the MIR CFG
//! linearly and converting rvalues/operands to AY Expr nodes. Used by the
//! virtual call dispatch handler when a single concrete implementation is found.
//!
//! Part of #3159: DynTrait category recovery Phase 1.
//! Part of #3639: Decomposed from monolithic file into 8 submodules.

mod atomic_inline;
mod dispatch;
mod drop_placeholder_dispatch;
mod drop_placeholders;
mod execution_state;
mod field_map;
mod fn_trait_dispatch;
mod gap_classify;
mod inline_alloc_helpers;
mod inline_call_classify;
mod inline_drop;
mod inline_drop_helpers;
mod inline_shared_drop;
mod kani_inline;
pub(in crate::codegen_ay::chc) mod loop_replay;
mod nested_call;
mod nested_call_fallback;
mod nested_iter_next;
pub(in crate::codegen_ay::chc) mod nested_option_state;
#[allow(dead_code)] // Call site wired in dirty-tree nested_call.rs (#4067)
mod nested_option_unwrap;
mod nested_spawn_schedule;
#[allow(dead_code)] // Call site wired in dirty-tree nested_call.rs (#4161)
mod nested_string_leaf;
mod nested_vec_pop;
mod nested_vec_push;
mod pointer_wrapper;
mod projected_assign;
mod projected_assign_helpers;
mod register_contract;
#[allow(dead_code)] // Call site wired in dirty-tree nested_call.rs (#3979)
mod result_copied;
mod slice_index_inline;
mod slice_index_metadata;
mod slice_index_trace;
mod statement_exec;
mod statement_exec_helpers;
mod statement_metadata;
mod switchint;
mod terminator_exec;
mod vtable_prop;
mod walker;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, ProjectionElem};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

// Re-export generic inline types from their neutral homes.
// Part of #3241: generic callers now import from inline_field_map / inline_body.
pub(in crate::codegen_ay::chc) use super::inline_body::InlineReturn;
pub(in crate::codegen_ay::chc) use nested_option_state::is_option_like_sort;
pub(in crate::codegen_ay::chc) use vtable_prop::attach_spawn_task_slot_vtable;

// Part of #3995: Re-export fn_trait_dispatch helpers for top-level virtual dispatch.
pub(in crate::codegen_ay::chc) use fn_trait_dispatch::{
    is_fn_trait_call, try_fn_trait_direct_dispatch,
};
// Part of #4000: Re-export mut-ref resolution for closure dispatch path.
pub(super) use fn_trait_dispatch::{bridge_mut_ref_alias_updates, resolve_mut_ref_value_args};

pub(in crate::codegen_ay::chc) fn receiver_base_local(receiver: &Operand) -> Option<usize> {
    match receiver {
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.is_empty()
                || place.projection.iter().all(|proj| matches!(proj, ProjectionElem::Deref)) =>
        {
            Some(place.local)
        }
        _ => None,
    }
}

/// Maximum SwitchInt nesting depth to prevent exponential path explosion.
/// Each loop iteration with an inner branch consumes 2 depth levels
/// (loop-condition SwitchInt + inner SwitchInt). At depth 8, the walker can
/// unroll ~3 iterations of while loops with inner branches.
/// Part of #3814: increased from 4 to 8 for struct methods with while loops.
/// Part of #4050: tested at 12 but reverted — deeper unrolling eliminated
/// SwitchInt overapprox vars but introduced 25 sound_fallback vars from
/// loop-exhaustion, making the encoding strictly worse for PDR.
/// Part of #4145: raised from 8→16 because loop-fuel bodies now correctly
/// increment depth (fixing infinite recursion from nested inlined loops).
/// A while loop with 2 SwitchInts/iter × 5 fuel iterations = 10 depth;
/// 16 gives headroom for nested calls that add their own SwitchInts.
const MAX_SWITCHINT_DEPTH: usize = 16;

/// Residual-775 Wall-1 P5.3: per-harness budget for SwitchInt branch
/// sub-walks across the WHOLE harness codegen (a ChcCtx counter, unlike the
/// per-chain `MAX_SWITCHINT_DEPTH`). Nested SwitchInts fork sub-walks
/// multiplicatively, and depth alone does not bound the total: wide bodies
/// re-walked across loop-replay iterations and call sites can reach
/// millions of sub-walks and burn the driver's wall-clock watchdog to a
/// hard kill. On exhaustion the SwitchInt bails exactly like depth
/// exhaustion (sound overapprox / demoted, fail-closed) — an ~80s hard-kill
/// DriverTimeout becomes a fast honest Demoted verdict.
///
/// Default 50_000: legitimate deep walks measured on the corpus (fib(6)
/// concrete recursion, Tower_of_Hanoi, Vector/DynTrait suites) stay well
/// under the budget — see the Wall-1 probe notes. Env-tunable for corpus
/// headroom probing; tuning it DOWN only demotes (fail-closed), never
/// flips a verdict unsoundly.
const MAX_SWITCHINT_WALK_NODES: usize = 50_000;

/// Resolve the P5.3 walk-node budget (env override or default). Read once.
pub(in crate::codegen_ay::chc) fn switchint_walk_node_budget() -> usize {
    static BUDGET: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *BUDGET.get_or_init(|| {
        std::env::var("TRUST_MC_SWITCHINT_WALK_NODE_BUDGET")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(MAX_SWITCHINT_WALK_NODES)
    })
}

/// Maximum inline recursion depth to prevent stack overflow on recursive Rust functions.
/// At depth 4, we've inlined 4 nested bodies which is sufficient for most non-recursive
/// call chains. Recursive functions bail to None (sound: falls through to over-approximation).
/// Part of #3614: Prevents compiler crash on valid recursive Rust code.
const MAX_INLINE_DEPTH: usize = 4;

pub(super) fn current_inline_callee_name(ctx: &ChcCtx<'_, '_>) -> Option<String> {
    let instance = ctx.current_instance?;
    let def_id = rustc_internal::internal(ctx.tcx, instance.def.def_id());
    Some(ctx.tcx.def_path_str(def_id))
}

fn virtual_panic_fallback<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    walk_ctx: &walker::InlineWalkCtx<'_>,
) -> Option<InlineReturn> {
    // Part of #3955: resolve return local through body-local normalization
    // so async fn return sorts match state-var sorts.
    let ret_ty = ctx.resolve_inline_local_ty(walk_ctx.body, 0).unwrap_or(walk_ctx.locals[0].ty);
    let ret_sort = match ret_ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => {
            ay_bindings::Expr::bool_const(true).sort().clone()
        }
        _ => ChcCtx::translate_ty(ret_ty)?,
    };
    let callee =
        current_inline_callee_name(ctx).unwrap_or_else(|| format!("<unknown:{}>", ctx.fn_name));
    let reason = format!("inline_panic_fallback_symbolic@{callee}");
    debug!(
        bb_idx = walk_ctx.bb_idx,
        fn_name = %ctx.fn_name,
        %callee,
        "virtual body: panic/assert fallback -> __assert_fail_inline"
    );
    ctx.record_aggregate_gap(&reason);
    Some(InlineReturn::value_only(super::declare_pending_var(
        super::chc_fresh_name("__assert_fail_inline"),
        ret_sort,
    )))
}

// Public API re-exports for external consumers.
pub(in crate::codegen_ay::chc) use dispatch::build_dispatch_ite_chain;
pub(in crate::codegen_ay::chc) use walker::translate_body_with_resolver;
pub(in crate::codegen_ay::chc) use walker::translate_virtual_body_inline;

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(super) fn try_inline_nested_call_step(
    ctx: &mut ChcCtx<'_, '_>,
    func: &Operand,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &std::collections::HashMap<usize, ay_bindings::Expr>,
    resolver: &super::inline_shared::PlaceResolver<'_>,
    inline_vtable_ids: &std::collections::HashMap<usize, ay_bindings::Expr>,
    inline_alloc_ids: &std::collections::HashMap<usize, u32>,
    destination: &rustc_public::mir::Place,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let mut result = nested_call::try_inline_nested_call(
        ctx,
        func,
        args,
        outer_body,
        local_exprs,
        resolver,
        inline_vtable_ids,
        inline_alloc_ids,
        destination,
        inline_depth,
    )?;
    let callee_path = terminator_exec::resolve_inline_callee_path(ctx, func, outer_body.locals());
    vtable_prop::attach_spawn_task_slot_vtable(
        ctx,
        callee_path.as_deref(),
        destination,
        outer_body,
        &mut result,
    );
    Some(result)
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(super) fn build_nested_call_fallback_expr_for_test(
    effective_sort: ay_bindings::Sort,
    is_pointer_like: bool,
) -> ay_bindings::Expr {
    nested_call_fallback::build_nested_call_fallback_expr_for_test(effective_sort, is_pointer_like)
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(super) fn unprojected_inline_drop_arg_base_local_for_test(
    outer_body: &rustc_public::mir::Body,
    arg: &Operand,
) -> Option<usize> {
    drop_placeholders::unprojected_inline_drop_arg_base_local(outer_body, arg)
}

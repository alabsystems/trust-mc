// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Neutral inline body translation API for generic callers.
//!
//! Provides `InlineReturn` and `translate_inline_body` as the generic
//! entry point for inline body translation, used by fn-inline, fn-ptr,
//! closure, and virtual dispatch callers. Delegates to the virtual-inline
//! walker implementation.
//!
//! Part of #3241: neutral home for generic inline API extracted from
//! `codegen_call_virtual_inline`.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Operand, mono::Instance};
use std::collections::{BTreeMap, HashMap, HashSet};
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use super::ChcCtx;
use super::codegen_ctx::types::RefTarget;
use super::inline_shared::PlaceResolver;

/// A check accumulated by the inline walker's assert SIDE-CHANNEL.
///
/// Historically an inline `kani::assert` / MIR `Assert` guard only reached the
/// host call site by riding the return-value ITE built in
/// `execution_state.rs::finish_return` (`ite(guard, val, __assert_fail_inline)`),
/// recovered via `extract_inline_assert_guard`. That recovery only recurses
/// through `Ite` nodes, so any consumer that discards or re-wraps the value
/// (unit destinations, SwitchInt sort coercions, constructor wrapping) silently
/// dropped the check. The side-channel carries each check independently of the
/// value so the host can emit a REAL per-property error rule
/// (`host_reach ∧ path_cond ∧ ¬check → error_pN`) through the standard BSEM-18
/// machinery regardless of destination shape.
///
/// `check` is the MUST-HOLD condition and must already include the walker's
/// path condition at the record point: assume-guard weakening is applied at
/// record time (`path_guard → check`), and SwitchInt / dispatch branch guards
/// are composed at the ITE merge points (`weaken_by_guard`). Emitting an entry
/// without its path condition would fabricate counterexamples.
#[derive(Clone)]
pub(in crate::codegen_ay::chc) struct DeferredInlineCheck {
    /// MUST-HOLD condition (violation = ¬check), path condition included.
    pub(in crate::codegen_ay::chc) check: Expr,
    /// Property kind for the per-property error head (BSEM-18).
    pub(in crate::codegen_ay::chc) kind: PropertyKind,
    /// Kani-parity property description (e.g. the `kani::assert` message).
    pub(in crate::codegen_ay::chc) message: Option<String>,
}

impl DeferredInlineCheck {
    /// Weaken the check so it only applies when `guard` holds:
    /// `guard → check`, i.e. `¬guard ∨ check`.
    pub(in crate::codegen_ay::chc) fn weaken_by_guard(mut self, guard: &Expr) -> Self {
        self.check = guard.clone().not().or(self.check);
        self
    }

    /// Weaken the check so it only applies when `guard` does NOT hold:
    /// `¬guard → check`, i.e. `guard ∨ check`.
    pub(in crate::codegen_ay::chc) fn weaken_by_negated_guard(mut self, guard: &Expr) -> Self {
        self.check = guard.clone().or(self.check);
        self
    }
}

/// Return value from inline body translation.
///
/// `alias_updates` carries per-arg-local updated expressions for every
/// modified aliasable (`&mut` / `*mut`) argument. Keyed by callee arg-local
/// index (1-based: local 1 = arg 0, local 2 = arg 1, ...).
///
/// Part of #3936 D1: replaces the former single `receiver_update: Option<Expr>`
/// so the inline contract can represent writes to multiple caller-visible args.
///
/// `deferred_checks` is the assert-guard side-channel: every check recorded
/// during the walk of this body (and absorbed from nested walks), each with
/// its path condition baked in. Because the entries ride the `InlineReturn`
/// (not `ChcCtx`), a failed/rolled-back speculative walk discards them
/// automatically — no snapshot machinery is needed and no phantom error rules
/// can leak from abandoned branches.
#[derive(Clone)]
pub(in crate::codegen_ay::chc) struct InlineReturn {
    pub(in crate::codegen_ay::chc) value: Expr,
    pub(in crate::codegen_ay::chc) vtable: Option<Expr>,
    pub(in crate::codegen_ay::chc) alloc_id: Option<u32>,
    pub(in crate::codegen_ay::chc) alias_updates: BTreeMap<usize, Expr>,
    pub(in crate::codegen_ay::chc) deferred_checks: Vec<DeferredInlineCheck>,
}

impl InlineReturn {
    pub(in crate::codegen_ay::chc) fn value_only(value: Expr) -> Self {
        Self {
            value,
            vtable: None,
            alloc_id: None,
            alias_updates: BTreeMap::new(),
            deferred_checks: Vec::new(),
        }
    }
}

#[derive(Clone)]
struct InlineRefResolutionSnapshot {
    ref_targets: HashMap<usize, RefTarget>,
    call_forwarded_raw_ptrs: HashSet<usize>,
    const_ref_values: HashMap<usize, Expr>,
    const_ref_slice_views: HashMap<usize, Expr>,
    subslice_len: HashMap<usize, Expr>,
    subslice_offset: HashMap<usize, Expr>,
}

fn snapshot_inline_ref_resolution(ctx: &ChcCtx<'_, '_>) -> InlineRefResolutionSnapshot {
    InlineRefResolutionSnapshot {
        ref_targets: ctx.ref_resolution.ref_targets.clone(),
        call_forwarded_raw_ptrs: ctx.ref_resolution.call_forwarded_raw_ptrs.clone(),
        const_ref_values: ctx.ref_resolution.const_ref_values.clone(),
        const_ref_slice_views: ctx.ref_resolution.const_ref_slice_views.clone(),
        subslice_len: ctx.ref_resolution.subslice_len.clone(),
        subslice_offset: ctx.ref_resolution.subslice_offset.clone(),
    }
}

fn restore_inline_ref_resolution(ctx: &mut ChcCtx<'_, '_>, snapshot: InlineRefResolutionSnapshot) {
    ctx.ref_resolution.ref_targets = snapshot.ref_targets;
    ctx.ref_resolution.call_forwarded_raw_ptrs = snapshot.call_forwarded_raw_ptrs;
    ctx.ref_resolution.const_ref_values = snapshot.const_ref_values;
    ctx.ref_resolution.const_ref_slice_views = snapshot.const_ref_slice_views;
    ctx.ref_resolution.subslice_len = snapshot.subslice_len;
    ctx.ref_resolution.subslice_offset = snapshot.subslice_offset;
}

pub(in crate::codegen_ay::chc) fn speculative_inline<T>(
    ctx: &mut ChcCtx<'_, '_>,
    inline_attempt: impl FnOnce(&mut ChcCtx<'_, '_>) -> Option<T>,
) -> Option<T> {
    let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
    let modified_snapshot = ctx.encode.modified_state_indices.clone();
    let ref_resolution_snapshot = snapshot_inline_ref_resolution(ctx);
    let result = inline_attempt(ctx);
    if result.is_none() {
        ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
        ctx.encode.modified_state_indices = modified_snapshot;
        restore_inline_ref_resolution(ctx, ref_resolution_snapshot);
    }
    result
}

fn is_inline_assert_fallback(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::Var { name } if name.starts_with("__assert_fail_inline")
    )
}

fn is_inline_assume_pruned(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::Var { name } if name.starts_with("__assume_pruned_inline")
    )
}

pub(in crate::codegen_ay::chc) fn extract_inline_assert_guard(expr: &Expr) -> Option<Expr> {
    if is_inline_assert_fallback(expr) {
        return Some(Expr::bool_const(false));
    }
    match expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_guard = extract_inline_assert_guard(&then_expr);
            let else_guard = extract_inline_assert_guard(&else_expr);
            match (then_guard, else_guard) {
                (None, None) => None,
                (Some(then_guard), None) => {
                    Some(Expr::ite(cond.clone(), then_guard, Expr::bool_const(true)))
                }
                (None, Some(else_guard)) => {
                    Some(Expr::ite(cond.clone(), Expr::bool_const(true), else_guard))
                }
                (Some(then_guard), Some(else_guard)) => {
                    Some(Expr::ite(cond.clone(), then_guard, else_guard))
                }
            }
        }
        _ => None,
    }
}

pub(in crate::codegen_ay::chc) fn extract_inline_assume_guard(expr: &Expr) -> Option<Expr> {
    if is_inline_assume_pruned(expr) {
        return Some(Expr::bool_const(false));
    }
    match expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_guard = extract_inline_assume_guard(&then_expr);
            let else_guard = extract_inline_assume_guard(&else_expr);
            match (then_guard, else_guard) {
                (None, None) => None,
                (Some(then_guard), None) => {
                    Some(Expr::ite(cond.clone(), then_guard, Expr::bool_const(true)))
                }
                (None, Some(else_guard)) => {
                    Some(Expr::ite(cond.clone(), Expr::bool_const(true), else_guard))
                }
                (Some(then_guard), Some(else_guard)) => {
                    Some(Expr::ite(cond.clone(), then_guard, else_guard))
                }
            }
        }
        _ => None,
    }
}

/// Remove inline-assert fallback leaves once the caller has recorded their guard.
///
/// Nested inline callers continue execution on the success path and separately
/// accumulate the extracted guard as an error condition. Keeping the fallback
/// wrapper in the value expression leaks `__assert_fail_inline*` markers into
/// later arithmetic/assertions even though the path is already constrained by
/// the same guard.
pub(in crate::codegen_ay::chc) fn strip_inline_assert_fallback(expr: &Expr) -> Option<Expr> {
    if is_inline_assert_fallback(expr) {
        return None;
    }
    match expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let stripped_then = strip_inline_assert_fallback(&then_expr);
            let stripped_else = strip_inline_assert_fallback(&else_expr);
            match (stripped_then, stripped_else) {
                (Some(then_expr), Some(else_expr)) => {
                    Some(Expr::ite(cond.clone(), then_expr, else_expr))
                }
                (Some(then_expr), None) => Some(then_expr),
                (None, Some(else_expr)) => Some(else_expr),
                (None, None) => None,
            }
        }
        _ => Some(expr.clone()),
    }
}

/// Remove inline-assume pruned leaves once the caller has recorded the assume
/// guard as a transition constraint.
pub(in crate::codegen_ay::chc) fn strip_inline_assume_pruned(expr: &Expr) -> Option<Expr> {
    if is_inline_assume_pruned(expr) {
        return None;
    }
    match expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let stripped_then = strip_inline_assume_pruned(&then_expr);
            let stripped_else = strip_inline_assume_pruned(&else_expr);
            match (stripped_then, stripped_else) {
                (Some(then_expr), Some(else_expr)) => {
                    Some(Expr::ite(cond.clone(), then_expr, else_expr))
                }
                (Some(then_expr), None) => Some(then_expr),
                (None, Some(else_expr)) => Some(else_expr),
                (None, None) => None,
            }
        }
        _ => Some(expr.clone()),
    }
}

pub(in crate::codegen_ay::chc) fn build_inline_subslice_maps_from_args(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
) -> (HashMap<usize, Expr>, HashMap<usize, Expr>) {
    let mut caller_subslice_lens = HashMap::new();
    let mut caller_subslice_offsets = HashMap::new();
    for (i, arg) in args.iter().enumerate() {
        let Some(local_idx) = super::codegen_call_virtual_inline::receiver_base_local(arg) else {
            continue;
        };
        if let Some(len_expr) = ctx.ref_resolution.subslice_len.get(&local_idx) {
            caller_subslice_lens.insert(i + 1, len_expr.clone());
        }
        if let Some(offset_expr) = ctx.ref_resolution.subslice_offset.get(&local_idx) {
            caller_subslice_offsets.insert(i + 1, offset_expr.clone());
        }
    }
    (caller_subslice_lens, caller_subslice_offsets)
}

fn restore_inline_subslice_map(map: &mut HashMap<usize, Expr>, saved: Vec<(usize, Option<Expr>)>) {
    for (local, value) in saved {
        match value {
            Some(expr) => {
                map.insert(local, expr);
            }
            None => {
                map.remove(&local);
            }
        }
    }
}

pub(in crate::codegen_ay::chc) fn translate_inline_body_with_metadata<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
    bb_idx: usize,
    caller_vtable_ids: &HashMap<usize, Expr>,
    caller_subslice_lens: &HashMap<usize, Expr>,
    caller_subslice_offsets: &HashMap<usize, Expr>,
    inline_instance: Option<Instance>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let local_count = body.locals().len();
    let saved_lens: Vec<(usize, Option<Expr>)> = (0..local_count)
        .map(|local| (local, ctx.ref_resolution.subslice_len.get(&local).cloned()))
        .collect();
    let saved_offsets: Vec<(usize, Option<Expr>)> = (0..local_count)
        .map(|local| (local, ctx.ref_resolution.subslice_offset.get(&local).cloned()))
        .collect();

    for (local, len_expr) in caller_subslice_lens {
        ctx.ref_resolution.subslice_len.insert(*local, len_expr.clone());
    }
    for (local, offset_expr) in caller_subslice_offsets {
        ctx.ref_resolution.subslice_offset.insert(*local, offset_expr.clone());
    }

    let result = super::codegen_call_virtual_inline::translate_virtual_body_inline(
        ctx,
        body,
        params,
        bb_idx,
        caller_vtable_ids,
        inline_instance,
        inline_depth,
    );

    restore_inline_subslice_map(&mut ctx.ref_resolution.subslice_len, saved_lens);
    restore_inline_subslice_map(&mut ctx.ref_resolution.subslice_offset, saved_offsets);
    result
}

/// Translate a method/function body inline into AY expressions.
///
/// This is the generic entry point for all inline body translation.
/// Delegates to the virtual-inline walker which handles the full CFG
/// traversal, SwitchInt merging, and nested call resolution.
pub(in crate::codegen_ay::chc) fn translate_inline_body<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
    bb_idx: usize,
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_instance: Option<Instance>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    super::codegen_call_virtual_inline::translate_virtual_body_inline(
        ctx,
        body,
        params,
        bb_idx,
        caller_vtable_ids,
        inline_instance,
        inline_depth,
    )
}

/// Translate a closure body inline, returning the full `InlineReturn`.
///
/// Maps closure parameter conventions (local 2..2+N for args, local 1 for
/// closure struct ref) onto the generic walker by building adapted local_exprs
/// and a Captures resolver.
///
/// This replaces the standalone `translate_closure_body_multi_arg` walker,
/// giving closures access to the full virtual walker capabilities: SwitchInt
/// merging, multi-block nested call inlining, Assert guard accumulation, and
/// Kani intrinsic handling.
///
/// Part of #3241: closure walker unification Phase 2.
/// Part of #3805: returns full InlineReturn so callers can consume side effects.
///
/// `inline_depth` is the caller's current inline recursion depth. Top-level
/// dispatch callers pass `0`; nested callers (e.g. a `kani_register_contract`
/// closure re-entered while already inlining) MUST pass `caller_depth + 1` so
/// the shared `MAX_INLINE_DEPTH` guard in `prepare_inline_walk` can terminate
/// otherwise-unbounded recursive-contract inlining (previously this path reset
/// the counter to 0 on every self-call → infinite inlining → stack overflow).
pub(in crate::codegen_ay::chc) fn translate_closure_inline_result<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
    captures: &[Expr],
    bb_idx: usize,
    inline_depth: usize,
) -> Option<InlineReturn> {
    // Build local_exprs with closure parameter conventions:
    //   local 0 = return value (not mapped)
    //   local 1 = closure struct ref (dummy — captures resolve field access)
    //   local 2..2+N = function parameters from `params`
    let mut local_exprs: HashMap<usize, Expr> = HashMap::new();
    for (i, param) in params.iter().enumerate() {
        local_exprs.insert(2 + i, param.clone());
    }

    let resolver = PlaceResolver::Captures(captures);
    let empty_vtable_ids = HashMap::new();

    debug!(
        bb_idx,
        param_count = params.len(),
        capture_count = captures.len(),
        "closure inline: starting unified body translation (#3241)"
    );

    super::codegen_call_virtual_inline::translate_body_with_resolver(
        ctx,
        body,
        local_exprs,
        resolver,
        bb_idx,
        empty_vtable_ids,
        // Thread the caller's real inline depth (previously hardcoded 0, which
        // defeated MAX_INLINE_DEPTH for recursive contract-register closures).
        inline_depth,
    )
}

/// Value-only wrapper for closure inline translation.
///
/// Intentionally discards `vtable` and `alias_updates` from InlineReturn.
/// Use `translate_closure_inline_result` when side effects must be preserved.
pub(in crate::codegen_ay::chc) fn translate_closure_inline_body<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
    captures: &[Expr],
    bb_idx: usize,
    inline_depth: usize,
) -> Option<Expr> {
    translate_closure_inline_result(ctx, body, params, captures, bb_idx, inline_depth)
        .map(|r| r.value)
}

#[cfg(test)]
mod deferred_check_tests {
    use super::DeferredInlineCheck;
    use ay_bindings::{Expr, Sort};
    use trust_mc_core::violation::PropertyKind;

    fn check_of(cond: Expr) -> DeferredInlineCheck {
        DeferredInlineCheck { check: cond, kind: PropertyKind::Assertion, message: None }
    }

    /// `weaken_by_guard` must produce the implication `guard → check`
    /// (`¬guard ∨ check`): the entry only fires on paths where the branch
    /// guard holds. Getting this polarity wrong would either mask the check
    /// (too weak everywhere) or fabricate counterexamples (fires off-branch).
    #[test]
    fn weaken_by_guard_is_guard_implies_check() {
        let guard = Expr::var("g", Sort::bool());
        let check = Expr::var("c", Sort::bool());
        let weakened = check_of(check.clone()).weaken_by_guard(&guard);
        assert_eq!(weakened.check, guard.not().or(check));
    }

    /// `weaken_by_negated_guard` must produce `¬guard → check`
    /// (`guard ∨ check`): the accumulator side of an ITE merge fires only
    /// when the branch guard does NOT hold.
    #[test]
    fn weaken_by_negated_guard_is_not_guard_implies_check() {
        let guard = Expr::var("g", Sort::bool());
        let check = Expr::var("c", Sort::bool());
        let weakened = check_of(check.clone()).weaken_by_negated_guard(&guard);
        assert_eq!(weakened.check, guard.or(check));
    }

    /// Kind and message must survive weakening — they feed the per-property
    /// error head (BSEM-18) at the host.
    #[test]
    fn weakening_preserves_kind_and_message() {
        let guard = Expr::var("g", Sort::bool());
        let entry = DeferredInlineCheck {
            check: Expr::var("c", Sort::bool()),
            kind: PropertyKind::Assertion,
            message: Some("|result| old(*ptr + 2) == *ptr".to_string()),
        };
        let weakened = entry.weaken_by_guard(&guard);
        assert_eq!(weakened.kind, PropertyKind::Assertion);
        assert_eq!(weakened.message.as_deref(), Some("|result| old(*ptr + 2) == *ptr"));
    }
}

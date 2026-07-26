// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Explicit mutable state for the inline body walker.
//! Part of #3913: extracted from walker.rs parallel locals.

use ay_bindings::{Expr, ExprValue};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeMap, HashMap, HashSet};
use trust_mc_core::violation::PropertyKind;

use super::super::ChcCtx;
use super::super::inline_body::DeferredInlineCheck;
use super::InlineReturn;
use super::kani_inline::refine_inline_value_from_assume;
use super::loop_replay::InlineWalkCtx;
pub(in crate::codegen_ay::chc) struct InlineExecutionState {
    pub(super) local_exprs: HashMap<usize, Expr>,
    pub(super) inline_vtable_ids: HashMap<usize, Expr>,
    pub(super) inline_alloc_ids: HashMap<usize, u32>,
    pub(super) modified_locals: HashSet<usize>,
    pub(super) assume_guards: Vec<Expr>,
    pub(super) assert_guards: Vec<Expr>,
    /// Assert-guard SIDE-CHANNEL: checks recorded during this walk segment,
    /// emitted as real per-property error rules at the host call site. Rides
    /// the walk state / `InlineReturn` (never `ChcCtx`), so failed speculative
    /// walks discard entries with the rest of the state — no phantom rules.
    pub(super) deferred_checks: Vec<DeferredInlineCheck>,
}

impl InlineExecutionState {
    fn current_assume_guard(&self) -> Option<Expr> {
        self.assume_guards.iter().cloned().reduce(|a, b| a.and(b))
    }

    pub(super) fn new(
        local_exprs: HashMap<usize, Expr>,
        inline_vtable_ids: HashMap<usize, Expr>,
        modified_locals: HashSet<usize>,
    ) -> Self {
        Self {
            local_exprs,
            inline_vtable_ids,
            inline_alloc_ids: HashMap::new(),
            modified_locals,
            assume_guards: Vec::new(),
            assert_guards: Vec::new(),
            deferred_checks: Vec::new(),
        }
    }

    /// Record a local assignment (plain, non-projected).
    pub(super) fn write_local(&mut self, local: usize, expr: Expr) {
        self.local_exprs.insert(local, expr);
        self.inline_alloc_ids.remove(&local);
        self.modified_locals.insert(local);
    }

    /// Record a local assignment with inline-body allocation provenance.
    pub(super) fn write_local_with_alloc_id(
        &mut self,
        local: usize,
        expr: Expr,
        alloc_id: Option<u32>,
    ) {
        self.local_exprs.insert(local, expr);
        match alloc_id {
            Some(alloc_id) => {
                self.inline_alloc_ids.insert(local, alloc_id);
            }
            None => {
                self.inline_alloc_ids.remove(&local);
            }
        }
        self.modified_locals.insert(local);
    }

    /// Record an assert guard condition.
    pub(super) fn record_assert_guard(&mut self, guard: Expr) {
        let guard = if let Some(path_guard) = self.current_assume_guard() {
            path_guard.not().or(guard)
        } else {
            guard
        };
        self.assert_guards.push(guard);
    }

    /// Record a side-channel check entry (assert-guard side-channel).
    ///
    /// Applies the same assume-guard path weakening as `record_assert_guard`
    /// (`path_guard → check`), so the host-emitted error rule only fires on
    /// paths the walker's assume conjunction admits. Callers that also thread
    /// the guard through the return-value ITE must call `record_assert_guard`
    /// separately — the two channels are independent.
    pub(super) fn record_deferred_check(
        &mut self,
        kind: PropertyKind,
        message: Option<String>,
        check: Expr,
    ) {
        let check = if let Some(path_guard) = self.current_assume_guard() {
            path_guard.not().or(check)
        } else {
            check
        };
        self.deferred_checks.push(DeferredInlineCheck { check, kind, message });
    }

    /// Absorb side-channel entries from a successfully-inlined NESTED call.
    ///
    /// The entries' intra-callee path conditions are already baked in; here
    /// they are additionally weakened by the CURRENT outer assume-guard
    /// conjunction (assumes recorded so far on this walk segment). Outer
    /// SwitchInt / dispatch branch guards are composed later at the ITE merge
    /// points, exactly mirroring how the return-value ITE composes.
    pub(super) fn absorb_nested_deferred_checks(&mut self, checks: Vec<DeferredInlineCheck>) {
        if checks.is_empty() {
            return;
        }
        let path_guard = self.current_assume_guard();
        for mut check in checks {
            if let Some(path_guard) = &path_guard {
                check.check = path_guard.clone().not().or(check.check);
            }
            self.deferred_checks.push(check);
        }
    }

    /// Synthesize the final `InlineReturn` from accumulated state.
    ///
    /// Handles:
    /// - unit-return fallback
    /// - assert-guard ITE wrapping
    /// - alias_updates collection for all modified aliasable arg locals
    ///
    /// Part of #3936 D1+D2: collects all modified aliasable arg locals
    /// (Ref/RawPtr) into `alias_updates` on the returned `InlineReturn`.
    pub(super) fn finish_return(
        &mut self,
        ctx: &ChcCtx<'_, '_>,
        walk_ctx: &InlineWalkCtx<'_>,
    ) -> Option<InlineReturn> {
        let return_val = match self.local_exprs.get(&0).cloned() {
            Some(val) => val,
            None => {
                let ret_ty = walk_ctx.locals[0].ty;
                match ret_ty.kind() {
                    TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => {
                        Expr::bool_const(true)
                    }
                    _ => return None,
                }
            }
        };
        let return_vtable = self.inline_vtable_ids.get(&0).cloned();
        let return_alloc_id = self.inline_alloc_ids.get(&0).copied();

        let alias_updates = self.collect_alias_updates(ctx, walk_ctx);

        let path_guard =
            std::mem::take(&mut self.assume_guards).into_iter().reduce(|a, b| a.and(b));
        let return_val = if let Some(path_guard) = path_guard {
            let return_val = refine_inline_value_from_assume(return_val, &path_guard);
            let pruned = super::super::declare_pending_var(
                super::super::chc_fresh_name("__assume_pruned_inline"),
                return_val.sort().clone(),
            );
            Expr::ite(path_guard, return_val, pruned)
        } else {
            return_val
        };
        // Side-channel entries leave the walk with the return, independent of
        // whatever happens to the value expression downstream.
        let deferred_checks = std::mem::take(&mut self.deferred_checks);
        let assert_guards = std::mem::take(&mut self.assert_guards);
        if assert_guards.is_empty() {
            return Some(InlineReturn {
                value: return_val,
                vtable: return_vtable,
                alloc_id: return_alloc_id,
                alias_updates,
                deferred_checks,
            });
        }
        let combined_guard = assert_guards
            .into_iter()
            .reduce(|a, b| a.and(b))
            .expect("invariant: assert_guards is non-empty (checked above)");
        ctx.record_aggregate_gap("inline_assert_fail_fallback");
        let fallback = super::super::declare_pending_var(
            super::super::chc_fresh_name("__assert_fail_inline"),
            return_val.sort().clone(),
        );
        // Part of #4014: preserve the vtable even when assert guards are
        // present.  The vtable identifies the *concrete type* behind a dyn
        // trait pointer — a compile-time property independent of runtime
        // assertion values.  Dropping it to None caused
        // widen_inline_result_for_fat_pointer to skip the BV64→BV128
        // widening, leaving the vtable portion unconstrained and allowing the
        // solver to violate alignment/value checks.
        Some(InlineReturn {
            value: Expr::ite(combined_guard, return_val, fallback),
            vtable: return_vtable,
            alloc_id: return_alloc_id,
            alias_updates,
            deferred_checks,
        })
    }

    /// Collect all modified aliasable arg locals into a BTreeMap.
    ///
    /// Part of #3936 D2: iterates arg_locals, filters to Ref/RawPtr types,
    /// keeps only modified locals, looks up final expressions, and drops
    /// entries contaminated by nested-call fallback markers.
    fn collect_alias_updates(
        &self,
        ctx: &ChcCtx<'_, '_>,
        walk_ctx: &InlineWalkCtx<'_>,
    ) -> BTreeMap<usize, Expr> {
        let mut updates = BTreeMap::new();
        let arg_count = walk_ctx.body.arg_locals().len();
        if arg_count == 0 {
            return updates;
        }
        // MIR arg locals are numbered 1..=arg_count.
        for local_idx in 1..=arg_count {
            let Some(decl) = walk_ctx.locals.get(local_idx) else {
                continue;
            };
            let expr = if matches!(
                decl.ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
            ) {
                if !self.modified_locals.contains(&local_idx) {
                    continue;
                }
                self.local_exprs.get(&local_idx).cloned()
            } else if let Some((root_state_idx, _, _)) =
                ctx.resolve_coroutine_root_state_expr(local_idx)
            {
                let Some(owner_local) = ctx.coroutine_owner_local_for_state_idx(root_state_idx)
                else {
                    continue;
                };
                if !self.modified_locals.contains(&owner_local) {
                    continue;
                }
                self.local_exprs.get(&owner_local).cloned()
            } else {
                continue;
            };
            let Some(expr) = expr else {
                continue;
            };
            if expr_contains_var_fragment(&expr, "__nested_call_overapprox") {
                continue;
            }
            updates.insert(local_idx, expr);
        }
        updates
    }
}

/// Push the direct children of `expr` onto `stack`.
/// Pattern mirrors tests/common.rs:expr_children (Part of #3911).
/// Split into unary/binary helpers to stay under 80-line function limit.
fn push_expr_children<'a>(expr: &'a Expr, stack: &mut Vec<&'a Expr>) {
    match expr.value() {
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_)
        | ExprValue::Var { .. } => {}
        ExprValue::Ite { cond, then_expr, else_expr } => {
            stack.extend([cond, then_expr, else_expr]);
        }
        ExprValue::Store { array, index, value } => {
            stack.extend([array, index, value]);
        }
        ExprValue::And(es) | ExprValue::Or(es) | ExprValue::Distinct(es) => {
            stack.extend(es.iter());
        }
        ExprValue::DatatypeConstructor { args, .. } | ExprValue::FuncApp { args, .. } => {
            stack.extend(args.iter());
        }
        other => push_unary_or_binary_children(other, stack),
    }
}

/// Handle unary (1-child) and binary (2-child) ExprValue variants.
fn push_unary_or_binary_children<'a>(val: &'a ExprValue, stack: &mut Vec<&'a Expr>) {
    match val {
        ExprValue::Not(c)
        | ExprValue::BvNeg(c)
        | ExprValue::BvNot(c)
        | ExprValue::IntNeg(c)
        | ExprValue::RealNeg(c)
        | ExprValue::Bv2Int(c)
        | ExprValue::IntToReal(c)
        | ExprValue::BvZeroExtend { expr: c, .. }
        | ExprValue::BvSignExtend { expr: c, .. }
        | ExprValue::BvExtract { expr: c, .. }
        | ExprValue::DatatypeSelector { expr: c, .. }
        | ExprValue::DatatypeTester { expr: c, .. }
        | ExprValue::BvNegNoOverflow(c)
        | ExprValue::Int2Bv(c, _)
        | ExprValue::ConstArray { value: c, .. }
        | ExprValue::Forall { body: c, .. }
        | ExprValue::Exists { body: c, .. } => {
            stack.push(c);
        }
        ExprValue::Eq(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvMul(a, b)
        | ExprValue::BvUDiv(a, b)
        | ExprValue::BvSDiv(a, b)
        | ExprValue::BvURem(a, b)
        | ExprValue::BvSRem(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvXor(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvConcat(a, b)
        | ExprValue::BvULt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::IntAdd(a, b)
        | ExprValue::IntSub(a, b)
        | ExprValue::IntMul(a, b)
        | ExprValue::IntDiv(a, b)
        | ExprValue::IntMod(a, b)
        | ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b)
        | ExprValue::RealAdd(a, b)
        | ExprValue::RealSub(a, b)
        | ExprValue::RealMul(a, b)
        | ExprValue::RealDiv(a, b)
        | ExprValue::RealLt(a, b)
        | ExprValue::RealLe(a, b)
        | ExprValue::RealGt(a, b)
        | ExprValue::RealGe(a, b)
        | ExprValue::Implies(a, b)
        | ExprValue::Xor(a, b)
        | ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvAddNoOverflowSigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b)
        | ExprValue::BvSubNoOverflowSigned(a, b)
        | ExprValue::BvMulNoOverflowUnsigned(a, b)
        | ExprValue::BvMulNoOverflowSigned(a, b)
        | ExprValue::BvSdivNoOverflow(a, b)
        | ExprValue::Select { array: a, index: b } => stack.extend([a, b]),
        _ => {}
    }
}

/// Part of #3911: check whether an `Expr` tree contains a `Var` whose name
/// includes `needle`. Used to detect nested-call fallback contamination in
/// a candidate receiver expression without a global boolean.
pub(in crate::codegen_ay::chc) fn expr_contains_var_fragment(expr: &Expr, needle: &str) -> bool {
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        if let ExprValue::Var { name } = e.value() {
            if name.contains(needle) {
                return true;
            }
        }
        push_expr_children(e, &mut stack);
    }
    false
}

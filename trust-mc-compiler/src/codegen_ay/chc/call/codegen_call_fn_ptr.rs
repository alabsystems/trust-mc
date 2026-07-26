// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Function pointer call resolution for CHC codegen.
//!
//! Handles `TerminatorKind::Call` where the callee operand has type
//! `RigidTy::FnPtr(..)` — indirect calls through function pointers.
//!
//! The entire dispatch chain only handles `RigidTy::FnDef`; FnPtr calls
//! fall through all dispatchers to the unconstrained fallback, producing
//! false CTREX due to unhandled_calls.
//!
//! Resolution strategy: scan the caller MIR for `PointerCoercion::ReifyFnPointer`
//! and `PointerCoercion::ClosureFnPointer` casts that produce the function
//! pointer local. These casts reveal the concrete function or closure that
//! was coerced to a fn pointer, allowing resolution and inline translation.
//!
//! Part of #1739: UNKNOWN→PROOF smoke suite recovery.

use ay_bindings::Expr;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{CastKind, Operand, PointerCoercion, Rvalue, StatementKind};
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::shared::{MAX_INLINE_EFFECTIVE_BLOCKS, count_effective_blocks};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::inline_body::{
    InlineReturn, extract_inline_assert_guard, strip_inline_assert_fallback, translate_inline_body,
};
use super::inline_result_shared::{
    InlineResultEpilogueSpec, emit_prepared_inline_result, prepare_inline_result_epilogue,
};

/// Extension trait for function pointer call resolution on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchFnPtr {
    /// Attempt to resolve and inline an indirect function pointer call.
    /// Returns `true` if handled.
    fn try_dispatch_call_fn_ptr(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchFnPtr for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_fn_ptr(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };

        // Only handle FnPtr calls.
        let func_ty = match dcx.func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        if !matches!(func_ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(..))) {
            return false;
        }

        let (body, is_closure) = match self.resolve_fn_ptr_callee_body(dcx) {
            Some(resolved) => resolved,
            None => return false,
        };

        // Complexity gate: only inline small bodies.
        let effective = count_effective_blocks(&body);
        if effective > MAX_INLINE_EFFECTIVE_BLOCKS {
            return false;
        }

        // Translate arguments using the same operand resolution as fn_inline.
        let params: Vec<Expr> = dcx
            .args
            .iter()
            .filter_map(|arg| {
                if let Some(expr) = self.resolve_ref_operand(arg, dcx.modified_locals) {
                    return Some(expr);
                }
                self.translate_operand_with_modified(arg, dcx.modified_locals)
            })
            .collect();
        if params.len() != dcx.args.len() {
            return false;
        }

        // Part of #3608: Mark type arrays read by the inline field map.
        self.mark_inline_field_reads(&body, &params, dcx.bb_idx);
        // Part of #4185: Snapshot heap state before speculative inline walk.
        let heap_snapshot = self.heap_state.snapshot_transient_rule_state();
        // Part of #4185 Fix 4: Snapshot modified_state_indices alongside heap.
        let modified_snapshot = self.encode.modified_state_indices.clone();
        let (result, inline_address_constraints) =
            self.inline_fn_ptr_body(&body, &params, is_closure, dcx.bb_idx);
        let Some(inline_result) = result else {
            // Part of #4185: Restore heap state after failed inline walk.
            self.heap_state.restore_transient_rule_state(&heap_snapshot);
            // Part of #4185 Fix 4: Restore modified_state_indices on bail-out.
            self.encode.modified_state_indices = modified_snapshot;
            return false;
        };

        debug!(
            bb_idx = dcx.bb_idx,
            effective_blocks = effective,
            "fn_ptr: successfully resolved and inlined function pointer call (#1739)"
        );

        self.emit_fn_ptr_result(dcx, *target, inline_result, &inline_address_constraints);
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Inline a resolved fn-ptr body (closure or plain function).
    fn inline_fn_ptr_body(
        &mut self,
        body: &rustc_public::mir::Body,
        params: &[Expr],
        is_closure: bool,
        bb_idx: usize,
    ) -> (Option<InlineReturn>, Vec<Expr>) {
        if is_closure {
            let no_captures: Vec<Expr> = Vec::new();
            let (address_hints, address_constraints) =
                self.build_inline_zst_param_address_hints(body, bb_idx);
            let saved_inline_hints = self.inline_local_address_hints.take();
            if !address_hints.is_empty() {
                let body_key = &raw const *body as usize;
                self.inline_local_address_hints = Some((body_key, address_hints));
            }
            // Value-only semantics for vtable/alias_updates (unchanged), but
            // PRESERVE the assert-guard side-channel from the closure walk.
            let result = super::inline_body::translate_closure_inline_result(
                self,
                body,
                params,
                &no_captures,
                bb_idx,
                0,
            )
            .map(|full| {
                let mut value_only = InlineReturn::value_only(full.value);
                value_only.deferred_checks = full.deferred_checks;
                value_only
            });
            self.inline_local_address_hints = saved_inline_hints;
            (result, address_constraints)
        } else {
            let caller_vtable_ids = std::collections::HashMap::new();
            (
                translate_inline_body(self, body, params, bb_idx, &caller_vtable_ids, None, 0),
                Vec::new(),
            )
        }
    }

    /// Emit a transition rule for a resolved function pointer call result.
    fn emit_fn_ptr_result(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        inline_result: InlineReturn,
        inline_address_constraints: &[Expr],
    ) {
        let dest_local: usize = dcx.destination.local;
        let InlineReturn { value: result_expr, vtable, alias_updates, deferred_checks, .. } =
            inline_result;
        // Assert-guard SIDE-CHANNEL host emission (see emit_deferred_inline_check_errors).
        self.emit_deferred_inline_check_errors(dcx, deferred_checks);
        let empty_pre_resolved = std::collections::BTreeMap::new();
        let inline_assert_guard = extract_inline_assert_guard(&result_expr);
        let result_expr = strip_inline_assert_fallback(&result_expr).unwrap_or(result_expr);
        let mut extra_constraints = self.emit_inline_assert_guard_error(dcx, inline_assert_guard);
        extra_constraints.extend_from_slice(inline_address_constraints);
        let prepared = prepare_inline_result_epilogue(
            self,
            InlineResultEpilogueSpec {
                dcx,
                target,
                dest_local,
                result_expr,
                inline_vtable: vtable,
                fallback_vtable: None,
                alias_updates: &alias_updates,
                pre_resolved_args: &empty_pre_resolved,
                eq_reason: "codegen_call_fn_ptr",
                alias_reason: "fn_ptr_alias_update",
                extra_constraints,
                extra_dests: Vec::new(),
                drain_pending_updates: false,
                drain_pending_checks: false,
            },
        );
        if self.operands_have_single_assign_sources(dcx.args) {
            self.cache_single_assign_scalar_expr(dest_local, &prepared.result_expr, true);
        }

        if let Err(prepared) = emit_prepared_inline_result(self, prepared) {
            // Sound over-approximation: destination unresolved, leave unconstrained.
            // Previous `bool_const(false)` killed the transition (dead rule in CHC).
            let effective_stmts = prepared.effective_stmts().to_vec();
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &prepared.extra_dests);
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &new_output_args,
                &effective_stmts,
                prepared.extra_constraints,
            );
            self.record_sound_fallback_reason("fn_ptr_dest_unresolved");
        }
    }

    pub(in crate::codegen_ay::chc) fn build_inline_zst_param_address_hints(
        &self,
        body: &rustc_public::mir::Body,
        bb_idx: usize,
    ) -> (std::collections::HashMap<usize, Expr>, Vec<Expr>) {
        let mut address_taken_zst_params = std::collections::BTreeSet::new();
        for block in &body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(
                        _,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                    ) if place.projection.is_empty() && place.local >= 2 => {
                        let Some(local_decl) = body.locals().get(place.local) else { continue };
                        let local_ty = self.resolve_body_ty(local_decl.ty);
                        if self.get_type_size(local_ty) == Some(0) {
                            address_taken_zst_params.insert(place.local);
                        }
                    }
                    _ => {}
                }
            }
        }

        let mut hints = std::collections::HashMap::new();
        let pointer_width = crate::codegen_ay::types::POINTER_WIDTH;

        for (ordinal, local) in address_taken_zst_params.into_iter().enumerate() {
            // The address is synthetic and scoped to this inline walk. Use a
            // concrete non-zero/distinct value instead of fresh BV arithmetic:
            // AY's CHC engine currently cannot prove `(fresh & mask) | tag != 0`
            // in HORN mode, which turns provable ZST address checks into CTREX.
            let addr = Expr::bitvec_const(
                (((bb_idx as u128) + 1) << 16) | ((local as u128) << 4) | ((ordinal as u128) + 1),
                pointer_width,
            );
            hints.insert(local, addr);
        }

        (hints, Vec::new())
    }

    /// Resolve the concrete callee body for a function pointer call.
    ///
    /// First tries copy/move chain following from the fn_ptr local, then falls
    /// back to scanning the entire body for ReifyFnPointer/ClosureFnPointer casts.
    /// Handles operands with projections (e.g., field access on a struct) by
    /// skipping chain resolution and using the body-scan fallback directly.
    fn resolve_fn_ptr_callee_body(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<(rustc_public::mir::Body, bool)> {
        // When the operand has a projection (e.g., `(_5).formatter`),
        // skip local-chain resolution and go directly to body-scan fallback.
        let fn_ptr_local = match dcx.func {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        };

        if let Some(resolved) = fn_ptr_local.and_then(|local| self.resolve_fn_ptr_body(local)) {
            return Some(resolved);
        }

        // Fallback: scan the entire body for any ReifyFnPointer/ClosureFnPointer cast.
        // Handles fn ptrs flowing through struct fields, iterators, or other data-flow
        // patterns that simple copy/move chain tracing cannot follow.
        // Part of #3335: resolve_any_fn_ptr_body now returns (body, is_closure).
        self.resolve_any_fn_ptr_body()
    }

    /// Resolve a function pointer local to its concrete MIR body.
    ///
    /// Scans the caller MIR for `ReifyFnPointer` or `ClosureFnPointer` casts
    /// that assign to `fn_ptr_local`, following copy/move chains up to 5 hops.
    /// Returns (body, is_closure) — is_closure=true for ClosureFnPointer coercions.
    fn resolve_fn_ptr_body(&self, fn_ptr_local: usize) -> Option<(rustc_public::mir::Body, bool)> {
        // Collect locals in the copy/move chain leading to fn_ptr_local.
        let mut target_locals = std::collections::HashSet::new();
        target_locals.insert(fn_ptr_local);

        // Follow copy/move chains backwards up to 5 hops.
        for _ in 0..5 {
            let mut new_locals = Vec::new();
            for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                        let dest = place.local;
                        if !target_locals.contains(&dest) {
                            continue;
                        }
                        match rvalue {
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                                if src.projection.is_empty() =>
                            {
                                new_locals.push(src.local);
                            }
                            _ => {}
                        }
                    }
                }
            }
            if new_locals.is_empty() {
                break;
            }
            target_locals.extend(new_locals);
        }

        // Scan for ReifyFnPointer/ClosureFnPointer casts to any tracked local.
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    if !target_locals.contains(&place.local) {
                        continue;
                    }
                    match rvalue {
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                            operand,
                            _,
                        ) => {
                            if let Some(body) = self.resolve_fn_ptr_operand_body(operand) {
                                debug!("fn_ptr: resolved via ReifyFnPointer coercion (#1739)");
                                return Some((body, false));
                            }
                        }
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)),
                            operand,
                            _,
                        ) => {
                            if let Some(body) = self.resolve_closure_fn_ptr_body(operand) {
                                debug!("fn_ptr: resolved via ClosureFnPointer coercion (#1739)");
                                return Some((body, true));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        None
    }

    /// Scan all MIR statements for any `ReifyFnPointer` or `ClosureFnPointer`
    /// cast, regardless of target local. Used by the nested inline handler where
    /// the fn ptr is a parameter (not a local of the harness body).
    ///
    /// Returns `(body, is_closure)` — `is_closure=true` for ClosureFnPointer
    /// coercions, which use RustCall ABI (local 1 = closure env, local 2+ = params).
    /// Part of #3335: previously returned bare Body, losing the closure distinction.
    pub(in crate::codegen_ay::chc) fn resolve_any_fn_ptr_body(
        &self,
    ) -> Option<(rustc_public::mir::Body, bool)> {
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_place, rvalue) = &stmt.kind {
                    match rvalue {
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                            operand,
                            _,
                        ) => {
                            if let Some(body) = self.resolve_fn_ptr_operand_body(operand) {
                                return Some((body, false));
                            }
                        }
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)),
                            operand,
                            _,
                        ) => {
                            if let Some(body) = self.resolve_closure_fn_ptr_body(operand) {
                                return Some((body, true));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        None
    }

    /// Resolve a `ReifyFnPointer` operand to its MIR body.
    fn resolve_fn_ptr_operand_body(&self, operand: &Operand) -> Option<rustc_public::mir::Body> {
        let ty = operand.ty(self.body.locals()).ok()?;
        let (fn_def, fn_substs) = match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };
        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        instance.body()
    }

    /// Resolve a `ClosureFnPointer` operand to its MIR body.
    ///
    /// Tries all three closure kinds (Fn, FnMut, FnOnce) since the closure's
    /// native kind determines which `Instance::resolve_closure` call succeeds
    /// and produces a body (vs. a shim without an accessible body).
    fn resolve_closure_fn_ptr_body(&self, operand: &Operand) -> Option<rustc_public::mir::Body> {
        let ty = operand.ty(self.body.locals()).ok()?;
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                    if let Ok(inst) = Instance::resolve_closure(def, &args, kind) {
                        if let Some(body) = inst.body() {
                            return Some(body);
                        }
                    }
                }
                None
            }
            TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_substs)) => {
                let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
                instance.body()
            }
            _ => None,
        }
    }
}

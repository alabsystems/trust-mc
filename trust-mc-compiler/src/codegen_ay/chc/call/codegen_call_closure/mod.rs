// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Closure call dispatch for CHC codegen.
//!
//! Handles `<Closure as Fn>::call`, `FnMut::call_mut`, `FnOnce::call_once`
//! by resolving the closure body and translating it inline.
//!
//! Part of #1739: recover PROOF verdicts on closure harnesses.

mod alias_writeback;
mod call_args;
mod dyn_callable_resolver;
mod register_contract;

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Operand, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;
use tracing::debug;

use self::alias_writeback::pre_resolve_closure_alias_target_locals;
use self::register_contract::resolve_closure_body_for_ty;
use super::inline_body::{
    InlineReturn, extract_inline_assert_guard, strip_inline_assert_fallback,
    translate_closure_inline_result, translate_inline_body,
};
pub(in crate::codegen_ay::chc) use dyn_callable_resolver::resolve_unique_dyn_callable_body;
pub(in crate::codegen_ay::chc) use register_contract::operand_is_closure_shaped;
pub(in crate::codegen_ay::chc) use register_contract::resolve_closure_body_for_operand;
pub(in crate::codegen_ay::chc) use register_contract::resolve_closure_body_via_unique_aggregate_def;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_fn_inline::widen_inline_result_for_fat_pointer;
use super::codegen_call_misc::CallMisc;
use super::codegen_call_virtual_inline::{
    bridge_mut_ref_alias_updates, resolve_mut_ref_value_args,
};
use super::codegen_rules::CodegenRules;
use super::inline_result_shared::{
    InlineResultEpilogueSpec, emit_prepared_inline_result, prepare_inline_result_epilogue,
};

/// Extension trait for closure call dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchClosure {
    /// Attempt to dispatch a closure call (`Fn::call`, `FnMut::call_mut`,
    /// `FnOnce::call_once`). Returns `true` if handled.
    fn try_dispatch_call_closure(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchClosure for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_closure(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let (bb_idx, func, args, destination, modified_locals) =
            (dcx.bb_idx, dcx.func, dcx.args, dcx.destination, dcx.modified_locals);

        // Detect closure call: func must be FnDef with a Closure type in its generic args,
        // OR (Wall-2) a local typed as the closure ITSELF.
        let func_ty = match func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        let callee_path;
        let mut closure_body: Option<rustc_public::mir::Body>;
        if matches!(func_ty.kind(), TyKind::RigidTy(RigidTy::Closure(..))) {
            // Wall-2 (loop-contract closure-inline fallback): the loop-contract
            // proof rule (`rule.rs::apply_loop_rule`'s `fn_op`) emits invariant
            // evaluations `_v = <shim>(&closure, ())` whose callee operand is a
            // fresh un-assigned LOCAL whose declared type is the invariant
            // CLOSURE itself (`Instance::ty()` of a closure Fn shim is the
            // closure type, not a FnDef). No dispatcher recognized that shape:
            // every rule-lane invariant evaluation that survived MIR inlining
            // fell through ALL dispatch stages to the unhandled-call havoc, so
            // the base/step invariant obligations became fully symbolic and the
            // harness demoted (OverApproximation) — the multiple_loops class.
            // Recover the closure body from the operand's declared TYPE and
            // route it through the SAME closure-inline lane as `Fn::call`
            // (captures from args[0] = &closure, params from args[1] tuple).
            // Anything unresolvable falls through to the existing fallback
            // lattice unchanged (fail-closed demotion preserved).
            callee_path = "<closure-typed callee>".to_string();
            closure_body = resolve_closure_body_for_ty(self.tcx, func_ty);
        } else {
            let (fn_def, fn_args) = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
                _ => return false, // external enum: TyKind
            };
            if self.is_register_contract_fn(fn_def) {
                return self.try_dispatch_call_register_contract(dcx, *target);
            }

            // Check if this is a Fn/FnMut/FnOnce::call variant.
            let Some(path) = self.resolve_callee_path(func) else {
                return false;
            };

            let is_closure_call = path.ends_with("::call")
                || path.ends_with("::call_mut")
                || path.ends_with("::call_once");
            if !is_closure_call {
                return false;
            }
            callee_path = path;

            closure_body = None;
            for arg in &fn_args.0 {
                let Some(arg_ty) = arg.ty() else { continue };
                if matches!(arg_ty.kind(), TyKind::RigidTy(RigidTy::Closure(..))) {
                    closure_body = resolve_closure_body_for_ty(self.tcx, *arg_ty);
                    if closure_body.is_some() {
                        break;
                    }
                }
            }

            if closure_body.is_none() {
                closure_body = resolve_unique_dyn_callable_body(self, fn_def, &fn_args);
            }
        }

        let Some(closure_body) = closure_body else {
            debug!(
                ?bb_idx,
                %callee_path,
                "closure call detected but could not resolve closure body"
            );
            return false;
        };

        debug!(
            "closure call dispatch bb{} path={} blocks={} locals={}",
            bb_idx,
            callee_path,
            closure_body.blocks.len(),
            closure_body.locals().len(),
        );

        // Extract captures from the closure environment (args[0] = &self/&mut self).
        // The closure aggregate was built by translate_closure_aggregate with cap_N fields.
        let captures = if !args.is_empty() {
            self.extract_closure_env_captures(&args[0], modified_locals)
        } else {
            Vec::new()
        };

        // Extract call arguments. For Fn::call, args[1] is the argument tuple.
        // For a 1-arg closure |n: i32|, args[1] is (n,) — a 1-element tuple.
        // For a 2-arg closure |a, b|, args[1] is (a, b) — a 2-element tuple.
        let call_params = if args.len() >= 2 {
            self.extract_closure_call_args(&args[1], modified_locals)
        } else {
            Vec::new()
        };

        // Translate the closure body inline, preserving full InlineReturn.
        // Part of #3805: use translate_closure_inline_result to preserve
        // vtable, alias_updates, and heap side effects.
        // Part of #4185: Snapshot heap state before speculative inline walk.
        let heap_snapshot = self.heap_state.snapshot_transient_rule_state();
        // Part of #4185 Fix 4: Snapshot modified_state_indices alongside heap.
        let modified_snapshot = self.encode.modified_state_indices.clone();
        let result = if closure_body.arg_locals().len() == call_params.len() {
            // dyn-callable resolution can recover a plain function-item body
            // (for example a boxed `&fn item`) rather than a closure ABI body.
            // Those bodies do not reserve local 1 for a capture environment, so
            // the closure-specific local mapping would drop the real arguments.
            //
            // Part of #4000: For `&mut T` parameters, resolve addresses to VALUES
            // before the inline walk. The inline walker uses Deref-as-identity
            // (`*_1` = `local_exprs[1]`), so if the arg holds an ADDRESS (bv64),
            // the body would compute on the address instead of the pointee value.
            let mut resolved_params = call_params;
            let mut_targets = resolve_mut_ref_value_args(self, &mut resolved_params, &closure_body);
            let empty_vtable_ids = std::collections::HashMap::new();
            let result = translate_inline_body(
                self,
                &closure_body,
                &resolved_params,
                bb_idx,
                &empty_vtable_ids,
                None,
                0,
            );
            // Part of #4000: Bridge alias_updates from modified `&mut T` args back
            // to outer target locals (state vars + heap memory at Mem level).
            if let Some(mut r) = result {
                bridge_mut_ref_alias_updates(self, &r, &mut_targets);
                for &(body_arg_idx, _) in &mut_targets {
                    r.alias_updates.remove(&body_arg_idx);
                }
                Some(r)
            } else {
                None
            }
        } else {
            translate_closure_inline_result(self, &closure_body, &call_params, &captures, bb_idx, 0)
        };

        let Some(inline_result) = result else {
            debug!(
                ?bb_idx,
                %callee_path,
                "closure body translation failed — declining so virtual dispatch can try"
            );
            // Return unclaimed: the single-block closure inliner cannot handle
            // this body (e.g., capturing closure calling stdlib methods), but
            // the virtual dispatch handler has a richer multi-block inliner
            // (MAX_INLINE_EFFECTIVE_BLOCKS = 16) that may succeed.
            // (Part of #3680: was fail-closed from #2323, now deferred to
            // virtual dispatch for better coverage)
            // Part of #4185: Restore heap state after failed inline walk.
            self.heap_state.restore_transient_rule_state(&heap_snapshot);
            // Part of #4185 Fix 4: Restore modified_state_indices on bail-out.
            self.encode.modified_state_indices = modified_snapshot;
            return false;
        };

        // Part of #3805: emit through the full side-effect bridge instead of
        // the old destination-only fast path. This drains pending_updates,
        // pending_checks, store chains, and propagates alias_updates.
        let closure_ref = args.first();
        self.emit_closure_inline_result(dcx, *target, closure_ref, inline_result);

        debug!(
            "closure call dispatch bb{} → constrained destination _{}",
            bb_idx, destination.local,
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Extract captured variable expressions from the closure environment operand.
    ///
    /// For `Fn::call(&self, args)`, the first argument is a reference to the
    /// closure environment. We resolve the ref to find the closure local, then
    /// search all blocks for the `Aggregate(Closure, fields)` that constructed it.
    pub(in crate::codegen_ay::chc) fn extract_closure_env_captures(
        &mut self,
        closure_ref: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Vec<Expr> {
        // Resolve the closure ref to the underlying closure local.
        let ref_local = match closure_ref {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return Vec::new(), // external enum: Operand
        };
        // Follow ref_targets: args[0] is &closure, so ref_targets maps it to the closure local.
        let closure_local =
            self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);

        // Search all blocks for the Aggregate(Closure, ...) that built this local.
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind
                    && place.local == closure_local
                    && let Rvalue::Aggregate(AggregateKind::Closure(_, _), fields) = rvalue
                {
                    return fields
                        .iter()
                        .filter_map(|op| self.resolve_closure_capture_expr(op, modified_locals))
                        .collect();
                }
            }
        }

        debug!(?closure_local, "could not find closure aggregate for captures");
        Vec::new()
    }

    fn resolve_closure_capture_expr(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let mut current = operand.clone();
        let mut visited = HashSet::new();

        for _ in 0..6 {
            let maybe_local = match &current {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    Some(place.local)
                }
                _ => None,
            };

            if let Some(expr) = self.resolve_ref_or_const_referent(&current, modified_locals) {
                let keep_peeling = maybe_local.is_some_and(|local| {
                    matches!(self.body.locals()[local].ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)))
                        && expr.sort().bitvec_width()
                            == Some(crate::codegen_ay::types::POINTER_WIDTH)
                });
                if !keep_peeling {
                    return Some(expr);
                }
            }

            let Some(local) = maybe_local else {
                return self.translate_operand_with_modified(&current, modified_locals);
            };
            if !visited.insert(local) {
                break;
            }
            let Some(next_local) = self.find_closure_capture_source_local(local) else {
                break;
            };
            current = Operand::Copy(rustc_public::mir::Place {
                local: next_local,
                projection: Vec::new(),
            });
        }

        self.translate_operand_with_modified(&current, modified_locals)
    }

    fn find_closure_capture_source_local(&self, local: usize) -> Option<usize> {
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                        if src.projection.is_empty() =>
                    {
                        return Some(src.local);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                        if src.projection.is_empty() =>
                    {
                        return Some(src.local);
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Resolve the closure environment local from a closure reference operand.
    ///
    /// For `Fn::call(&self, args)`, `args[0]` is `&closure_env`. This follows
    /// `ref_targets` to find the underlying closure local, reusing the same
    /// resolution logic used by `extract_closure_env_captures`.
    ///
    /// Part of #3805 D2: shared resolver for capture extraction and receiver_update.
    pub(super) fn resolve_closure_env_local(&self, closure_ref: &Operand) -> Option<usize> {
        let ref_local = match closure_ref {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None, // external enum: Operand
        };
        Some(self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local))
    }

    /// Emit a closure inline result through the full side-effect bridge.
    ///
    /// Reuses the shared inline-result epilogue while preserving the closure
    /// ABI-specific alias target resolution and unit-destination fallback.
    ///
    /// Part of #3805 D3 and #3964 D3.
    pub(in crate::codegen_ay::chc) fn emit_closure_inline_result(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        closure_ref: Option<&Operand>,
        inline_result: InlineReturn,
    ) {
        let dest_local: usize = dcx.destination.local;
        let InlineReturn { value: result_expr, vtable, alias_updates, deferred_checks, .. } =
            inline_result;
        // Assert-guard SIDE-CHANNEL host emission (see emit_deferred_inline_check_errors).
        self.emit_deferred_inline_check_errors(dcx, deferred_checks);
        let inline_assert_guard = extract_inline_assert_guard(&result_expr);
        let result_expr = strip_inline_assert_fallback(&result_expr).unwrap_or(result_expr);
        let result_expr =
            widen_inline_result_for_fat_pointer(self, dest_local, result_expr, &vtable);
        let extra_constraints = self.emit_inline_assert_guard_error(dcx, inline_assert_guard);
        let pre_resolved_args = pre_resolve_closure_alias_target_locals(self, dcx, closure_ref);
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
                pre_resolved_args: &pre_resolved_args,
                eq_reason: "codegen_call_closure",
                alias_reason: "closure_inline_alias_update",
                extra_constraints,
                extra_dests: Vec::new(),
                drain_pending_updates: false,
                drain_pending_checks: true,
            },
        );

        if let Err(prepared) = emit_prepared_inline_result(self, prepared) {
            let effective_stmts = prepared.effective_stmts().to_vec();
            let dest_is_unit = self.body.locals().get(dest_local).is_some_and(|decl| {
                matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty())
            });
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &prepared.extra_dests);
            let extra: Vec<Expr> =
                prepared.mem_constraints.into_iter().chain(prepared.extra_constraints).collect();
            if dest_is_unit {
                // Unit destination — no constraint needed, but still emit side effects.
                if extra.is_empty() {
                    self.emit_goto_rule(dcx.from_app, target, &new_output_args, &effective_stmts);
                } else {
                    self.emit_goto_rule_extra(
                        dcx.from_app,
                        target,
                        &new_output_args,
                        &effective_stmts,
                        extra,
                    );
                }
            } else {
                // Part of #3897: sound over-approximation for untracked destinations.
                // Previously used `false` which killed the transition.
                debug!(
                    bb_idx = dcx.bb_idx,
                    dest_local,
                    fn_name = %self.fn_name,
                    "closure: untracked destination, sound over-approx"
                );
                self.record_sound_fallback_reason("closure_dest_untracked");
                self.emit_goto_rule_extra(
                    dcx.from_app,
                    target,
                    &new_output_args,
                    &effective_stmts,
                    extra,
                );
            }
        }
    }

    // Closure call argument extraction and translation moved to call_args.rs per #4206.
}

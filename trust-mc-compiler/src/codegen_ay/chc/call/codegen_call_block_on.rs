// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Specialized `block_on` call dispatch for CHC codegen.
//!
//! `kani::block_on` is a simple busy-poll loop:
//! 1. build a noop waker/context
//! 2. pin the future
//! 3. `loop { match poll(...) { Ready(v) => return v, Pending => continue } }`
//!
//! Running that body through generic fn-inline leaves an unbounded self-loop
//! around the `poll` call. For simple async futures that complete in one poll,
//! we can soundly specialize the body by cutting the Pending backedge and
//! inlining the single-poll Ready path directly.
//!
//! Part of #3955.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeMap, HashMap};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;
use super::inline_alias_writeback::pre_resolve_arg_target_locals;
use super::inline_body::{
    InlineReturn, extract_inline_assert_guard, strip_inline_assert_fallback, translate_inline_body,
};
use super::inline_result_shared::{
    InlineResultEpilogueSpec, emit_prepared_inline_result, prepare_inline_result_epilogue,
};

pub(in crate::codegen_ay::chc) trait CallDispatchBlockOn {
    fn try_dispatch_call_block_on(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchBlockOn for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_block_on(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            return false;
        };
        let Some((instance, callee_name, specialized_body, spawn_model)) =
            self.resolve_block_on_inline_target(dcx)
        else {
            return false;
        };
        // Part of #4075: install spawn vtable model early so downstream
        // dyn Future dispatch can use cycling vtable IDs.
        if spawn_model.is_some() {
            self.spawn_scheduler_vtable_model = spawn_model;
        }

        let Some((params, caller_vtable_ids)) = self.resolve_block_on_params(dcx) else {
            return false;
        };
        let pre_resolved_args = pre_resolve_arg_target_locals(self, dcx);
        let is_spawn = self.spawn_scheduler_vtable_model.is_some();
        let vtable_miss_before = self.spawn_vtable_miss_count_if_active(is_spawn);
        let rule_count_before = self.vc.rules.len();

        self.mark_inline_field_reads(&specialized_body, &params, dcx.bb_idx);
        let inline_result = translate_inline_body(
            self,
            &specialized_body,
            &params,
            dcx.bb_idx,
            &caller_vtable_ids,
            Some(instance),
            0,
        );

        // Part of #4075 D3: vtable miss check before emit.
        if self.try_claim_spawn_vtable_fallback(
            dcx,
            *target,
            is_spawn,
            vtable_miss_before,
            &inline_result,
            &callee_name,
        ) {
            return true;
        }

        let Some(inline_result) = inline_result else {
            debug!(bb_idx = dcx.bb_idx, callee = %callee_name, "block_on: inline bailed");
            return false;
        };
        self.spawn_scheduler_vtable_model = None;
        debug!(bb_idx = dcx.bb_idx, callee = %callee_name, "block_on: single-poll dispatch");
        let result = self.emit_block_on_inline_result(
            dcx,
            *target,
            inline_result,
            &pre_resolved_args,
            &caller_vtable_ids,
            &callee_name,
        );

        // Part of #4075: truncate excessive spawn scheduler rule expansion.
        if is_spawn && result {
            self.try_truncate_spawn_rule_budget(dcx, *target, rule_count_before, &callee_name);
        }
        result
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn resolve_block_on_inline_target(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<(
        Instance,
        String,
        rustc_public::mir::Body,
        Option<super::codegen_ctx::SpawnSchedulerVtableModel>,
    )> {
        let func = dcx.func;
        let func_ty = func.ty(self.body.locals()).ok()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };
        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        let callee_name =
            self.tcx.def_path_str(rustc_internal::internal(self.tcx, instance.def.def_id()));
        // Part of #4075: block_on_with_spawn is inlined by rustc, so the MIR
        // call is to Scheduler::block_on (which ends_with("::block_on")).
        // Check for spawn path first by trying to build the vtable model.
        if callee_name == "block_on_with_spawn"
            || callee_name.ends_with("::block_on_with_spawn")
            || callee_name == "block_on"
            || callee_name.ends_with("::block_on")
        {
            debug!(callee = %callee_name, fn_name = %self.fn_name, "block_on: name matched");
            let body = instance.body()?;

            // Try spawn path first: Scheduler::block_on with a scheduling plan
            // argument indicates the spawn runtime (inlined block_on_with_spawn).
            if let Some(spawn_model) =
                self.build_spawn_scheduler_vtable_model(dcx, &body, &callee_name)
            {
                return Some((instance, callee_name, body, Some(spawn_model)));
            }

            // Fall back to single-poll block_on (no spawn).
            let specialized_body = self.specialize_block_on_body_for_single_poll(&body);
            if specialized_body.is_none() {
                debug!(
                    callee = %callee_name,
                    blocks = body.blocks.len(),
                    "block_on: single-poll specialization failed"
                );
            }
            let specialized_body = specialized_body?;
            return Some((instance, callee_name, specialized_body, None));
        }

        None
    }

    fn emit_block_on_inline_result(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        inline_result: InlineReturn,
        pre_resolved_args: &BTreeMap<usize, usize>,
        caller_vtable_ids: &HashMap<usize, Expr>,
        callee_path: &str,
    ) -> bool {
        let InlineReturn {
            value: result_expr,
            vtable: inline_vtable,
            alias_updates,
            deferred_checks,
            ..
        } = inline_result;
        // Assert-guard SIDE-CHANNEL host emission (see emit_deferred_inline_check_errors).
        self.emit_deferred_inline_check_errors(dcx, deferred_checks);
        let inline_assert_guard = extract_inline_assert_guard(&result_expr);
        let result_expr = strip_inline_assert_fallback(&result_expr).unwrap_or(result_expr);
        let dest_local = dcx.destination.local;
        let mut extra_dests = Vec::new();
        let mut extra_constraints = self.emit_inline_assert_guard_error(dcx, inline_assert_guard);
        extra_constraints.append(&mut self.invalidate_moved_block_on_args(
            dcx,
            dest_local,
            &mut extra_dests,
        ));
        let prepared = prepare_inline_result_epilogue(
            self,
            InlineResultEpilogueSpec {
                dcx,
                target,
                dest_local,
                result_expr,
                inline_vtable,
                fallback_vtable: caller_vtable_ids.get(&1).cloned(),
                alias_updates: &alias_updates,
                pre_resolved_args,
                eq_reason: "codegen_call_block_on",
                alias_reason: "block_on_inline_alias_update",
                extra_constraints,
                extra_dests,
                drain_pending_updates: true,
                drain_pending_checks: true,
            },
        );

        if let Err(prepared) = emit_prepared_inline_result(self, prepared) {
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                fn_name = %self.fn_name,
                callee = %callee_path,
                "block_on: untracked destination, sound over-approx"
            );
            self.record_sound_fallback_reason("block_on_dest_untracked");
            let effective_stmts = prepared.effective_stmts().to_vec();
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &new_output_args,
                &effective_stmts,
                prepared.extra_constraints,
            );
        }

        true
    }

    fn resolve_block_on_params(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<(Vec<Expr>, HashMap<usize, Expr>)> {
        let mut params = Vec::with_capacity(dcx.args.len());
        for arg in dcx.args {
            params.push(self.resolve_ref_or_const_referent(arg, dcx.modified_locals)?);
        }

        let mut caller_vtable_ids = HashMap::new();
        for (i, arg) in dcx.args.iter().enumerate() {
            let arg_local = match arg {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    Some(place.local)
                }
                _ => None,
            };
            if let Some(local_idx) = arg_local
                && let Some(vtable) = self.known_vtable_expr_for_local(local_idx)
            {
                caller_vtable_ids.insert(i + 1, vtable);
            }
        }

        Some((params, caller_vtable_ids))
    }

    pub(in crate::codegen_ay::chc) fn build_spawn_scheduler_vtable_model(
        &self,
        dcx: &DispatchCallContext<'_>,
        callee_body: &rustc_public::mir::Body,
        callee_name: &str,
    ) -> Option<super::codegen_ctx::SpawnSchedulerVtableModel> {
        // Part of #4075: block_on_with_spawn is inlined by rustc, so the MIR
        // call we see is Scheduler::block_on (which has &mut self, fut,
        // scheduling_plan). Detect whether the callee is already
        // Scheduler::block_on vs block_on_with_spawn to determine arg layout
        // and body traversal depth.
        let is_scheduler_block_on = callee_name.contains("Scheduler::block_on");

        // For Scheduler::block_on: args are (&mut self=0, fut=1, plan=2)
        // For block_on_with_spawn: args are (fut=0, plan=1)
        let plan_arg_idx = if is_scheduler_block_on { 2 } else { 1 };
        let fut_arg_idx = if is_scheduler_block_on { 1 } else { 0 };

        let scheduling_plan_ty = dcx.args.get(plan_arg_idx)?.ty(self.body.locals()).ok()?;
        let scheduling_plan_ty = self.resolve_body_ty(scheduling_plan_ty);
        if !matches!(
            scheduling_plan_ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RoundRobin"
        ) {
            return None;
        }

        let root_future_ty =
            self.resolve_body_ty(dcx.args.get(fut_arg_idx)?.ty(self.body.locals()).ok()?);
        let root_future_body = self.coroutine_body_for_future_ty(root_future_ty)?;

        // When callee is Scheduler::block_on, search for Scheduler::run
        // directly in callee_body. Otherwise descend through Scheduler::block_on.
        let scheduler_run_search_body = if is_scheduler_block_on {
            std::borrow::Cow::Borrowed(callee_body)
        } else {
            let sbo =
                self.resolve_body_call_instance_by_suffix(callee_body, "Scheduler::block_on")?;
            std::borrow::Cow::Owned(sbo.body()?)
        };
        let scheduler_run = self
            .resolve_body_call_instance_by_suffix(&scheduler_run_search_body, "Scheduler::run")?;
        let scheduler_run_body = scheduler_run.body()?;
        let future_trait_def_id =
            self.resolve_future_trait_def_id_from_body(&scheduler_run_body)?;
        let candidates =
            super::dyn_coercion::collect_dyn_trait_candidates(self, future_trait_def_id);

        // Part of #4075: resolve vtable IDs from the coercion scan. When the
        // scan finds no candidates (compiletest: coercions happen in library
        // code, invisible to the harness compilation unit), fall back to
        // synthesized sequential IDs. The IDs only need internal consistency
        // (same type → same ID) for dispatch ITE chain construction.
        let spawn_future_tys = self.collect_spawn_future_tys(&root_future_body);
        let spawn_future_count = spawn_future_tys.len();
        let has_yield_now = self.body_has_call_suffix(&root_future_body, "yield_now");
        let has_join_handle_poll = self.body_has_call_suffix(&root_future_body, "JoinHandle::poll");

        let mut poll_vtable_ids = Vec::new();
        let mut synthetic_next_id = 1u64;
        let mut synthetic_map: std::collections::HashMap<rustc_public::ty::Ty, u64> =
            std::collections::HashMap::new();

        let resolve_or_synthesize =
            |ty: rustc_public::ty::Ty,
             candidates: &[super::dyn_coercion::DynCandidate],
             synthetic_map: &mut std::collections::HashMap<rustc_public::ty::Ty, u64>,
             next_id: &mut u64| {
                if let Some(id) = super::dyn_coercion::resolve_vtable_id(candidates, ty) {
                    return id;
                }
                *synthetic_map.entry(ty).or_insert_with(|| {
                    let id = *next_id;
                    *next_id += 1;
                    id
                })
            };

        poll_vtable_ids.push(resolve_or_synthesize(
            root_future_ty,
            &candidates,
            &mut synthetic_map,
            &mut synthetic_next_id,
        ));
        for spawn_future_ty in &spawn_future_tys {
            poll_vtable_ids.push(resolve_or_synthesize(
                *spawn_future_ty,
                &candidates,
                &mut synthetic_map,
                &mut synthetic_next_id,
            ));
        }
        if has_yield_now {
            poll_vtable_ids.push(resolve_or_synthesize(
                root_future_ty,
                &candidates,
                &mut synthetic_map,
                &mut synthetic_next_id,
            ));
        }
        let poll_task_indices = if spawn_future_count <= 1 && !has_join_handle_poll {
            let mut indices =
                Vec::with_capacity(1 + spawn_future_count + usize::from(has_yield_now));
            indices.push(0);
            indices.extend((1..=spawn_future_count).map(|idx| idx as u64));
            if has_yield_now {
                indices.push(0);
            }
            indices
        } else {
            Vec::new()
        };
        let vtable_count = poll_vtable_ids.len();
        let scheduler_loop_replay_fuel = (spawn_future_count <= 1 && !has_join_handle_poll)
            .then_some(1 + spawn_future_count + usize::from(has_yield_now));
        let model = (vtable_count >= 2).then_some(super::codegen_ctx::SpawnSchedulerVtableModel {
            poll_vtable_ids,
            next_poll_idx: 0,
            poll_task_indices,
            next_task_idx: 0,
            current_task_vtable_id: None,
            scheduler_loop_replay_fuel,
        });
        debug!(
            fn_name = %self.fn_name,
            vtable_count,
            candidates = candidates.len(),
            synthetic_count = synthetic_map.len(),
            poll_task_indices = ?model.as_ref().map(|m| &m.poll_task_indices),
            scheduler_loop_replay_fuel,
            model_built = model.is_some(),
            "spawn_model: build result"
        );
        model
    }

    fn invalidate_moved_block_on_args(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        extra_dests: &mut Vec<usize>,
    ) -> Vec<Expr> {
        let mut constraints = Vec::new();
        for arg in dcx.args {
            let Operand::Move(place) = arg else {
                continue;
            };
            if !place.projection.is_empty() || place.local == dest_local {
                continue;
            }

            let local_idx = place.local;
            if !extra_dests.contains(&local_idx) {
                extra_dests.push(local_idx);
            }
            self.known_alloc_ids.remove(&local_idx);
            self.clear_known_vtable_discriminant(local_idx);

            let Some((_, dest_var)) = self.resolve_destination(local_idx) else {
                continue;
            };
            let Some(default_expr) = ChcCtx::sort_default_expr(dest_var.sort()) else {
                continue;
            };
            if let Some(mut local_constraints) = self.build_local_update_constraints(
                local_idx,
                default_expr,
                "block_on_move_arg_invalidated",
            ) {
                constraints.append(&mut local_constraints);
            }
        }
        constraints
    }
}

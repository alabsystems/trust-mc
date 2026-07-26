// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Spawn scheduler type-array prediction for CHC stub-internal declarations.
//!
//! Extracted from `codegen_decl_stub_internal.rs` for 500-LOC compliance.
//! Part of #4119.
//!
//! Part of #4075: when the harness reaches the async spawn scheduler,
//! predeclare the runtime support arrays up front so translation does not
//! widen relation signatures mid-block for noop waker/context carriers
//! and boxed-future task slots.

use std::collections::{BTreeMap, BTreeSet};

use ay_bindings::Sort;
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{bv8_sort, ptr_sort};

use super::ChcCtx;
use super::codegen_rules_entry::CodegenRulesEntry;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn predeclare_spawn_scheduler_type_arrays(&mut self) {
        if !self.is_spawn_scheduler_reachable() {
            return;
        }

        let mut type_arrays: BTreeMap<String, Sort> = BTreeMap::new();

        self.collect_spawn_scheduler_type_arrays_from_body(self.body, &mut type_arrays);
        self.predeclare_spawn_scheduler_core_type_arrays(&mut type_arrays);
        let harness_body = (*self.body).clone();
        self.predeclare_spawn_scheduler_heap_regions_from_body(&harness_body);

        let root_future_body = self.spawn_root_future_body();
        if let Some(body) = root_future_body.as_ref() {
            self.collect_spawn_scheduler_type_arrays_from_body(body, &mut type_arrays);
            self.predeclare_spawn_scheduler_heap_regions_from_body(body);
            for fut_ty in self.collect_spawn_future_tys(body) {
                if let Some(spawned_body) = self.coroutine_body_for_future_ty(fut_ty) {
                    self.collect_spawn_scheduler_type_arrays_from_body(
                        &spawned_body,
                        &mut type_arrays,
                    );
                    self.predeclare_spawn_scheduler_heap_regions_from_body(&spawned_body);
                }
            }
            if let Some(spawn_fn) = self.resolve_body_call_instance_by_suffix(body, "spawn")
                && let Some(spawn_body) = spawn_fn.body()
            {
                self.collect_spawn_scheduler_type_arrays_from_body(&spawn_body, &mut type_arrays);
                self.predeclare_spawn_scheduler_heap_regions_from_body(&spawn_body);
                if let Some(scheduler_spawn) =
                    self.resolve_body_call_instance_by_suffix(&spawn_body, "Scheduler::spawn")
                    && let Some(scheduler_spawn_body) = scheduler_spawn.body()
                {
                    self.collect_spawn_scheduler_type_arrays_from_body(
                        &scheduler_spawn_body,
                        &mut type_arrays,
                    );
                    self.predeclare_spawn_scheduler_heap_regions_from_body(&scheduler_spawn_body);
                }
            }
            if let Some(join_handle_poll) =
                self.resolve_body_call_instance_by_suffix(body, "JoinHandle::poll")
                && let Some(join_handle_poll_body) = join_handle_poll.body()
            {
                self.collect_spawn_scheduler_type_arrays_from_body(
                    &join_handle_poll_body,
                    &mut type_arrays,
                );
                self.predeclare_spawn_scheduler_heap_regions_from_body(&join_handle_poll_body);
            }
        }

        if let Some(block_on_with_spawn_body) = self.spawn_block_on_with_spawn_body() {
            self.collect_spawn_scheduler_type_arrays_from_body(
                &block_on_with_spawn_body,
                &mut type_arrays,
            );
            self.predeclare_spawn_scheduler_heap_regions_from_body(&block_on_with_spawn_body);
        }

        if let Some(scheduler_block_on_body) = self.spawn_scheduler_block_on_body() {
            self.collect_spawn_scheduler_type_arrays_from_body(
                &scheduler_block_on_body,
                &mut type_arrays,
            );
            self.predeclare_spawn_scheduler_heap_regions_from_body(&scheduler_block_on_body);
            if let Some(scheduler_run) = self
                .resolve_body_call_instance_by_suffix(&scheduler_block_on_body, "Scheduler::run")
                && let Some(scheduler_run_body) = scheduler_run.body()
            {
                self.collect_spawn_scheduler_type_arrays_from_body(
                    &scheduler_run_body,
                    &mut type_arrays,
                );
                self.predeclare_spawn_scheduler_heap_regions_from_body(&scheduler_run_body);
            }
        }

        for (type_key, elem_sort) in type_arrays {
            self.predeclare_type_array_with_sort_if_missing(&type_key, elem_sort);
        }
    }

    fn is_spawn_scheduler_reachable(&self) -> bool {
        self.body_has_call_suffix(self.body, "block_on_with_spawn")
            || self.body_has_call_suffix(self.body, "Scheduler::block_on")
    }

    fn spawn_root_future_body(&self) -> Option<rustc_public::mir::Body> {
        self.body.blocks.iter().find_map(|block| {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                return None;
            };
            let callee_path = self.resolve_body_callee_path(self.body, func)?;
            let fut_arg_idx = if callee_path == "block_on_with_spawn"
                || callee_path.ends_with("::block_on_with_spawn")
            {
                0
            } else if callee_path.contains("Scheduler::block_on") {
                1
            } else {
                return None;
            };
            let fut_ty = self.resolve_body_ty(args.get(fut_arg_idx)?.ty(self.body.locals()).ok()?);
            self.coroutine_body_for_future_ty(fut_ty)
        })
    }

    fn spawn_scheduler_block_on_body(&self) -> Option<rustc_public::mir::Body> {
        if let Some(scheduler_block_on) =
            self.resolve_body_call_instance_by_suffix(self.body, "Scheduler::block_on")
        {
            return scheduler_block_on.body();
        }

        let block_on_with_spawn =
            self.resolve_body_call_instance_by_suffix(self.body, "block_on_with_spawn")?;
        let block_on_with_spawn_body = block_on_with_spawn.body()?;
        self.resolve_body_call_instance_by_suffix(&block_on_with_spawn_body, "Scheduler::block_on")?
            .body()
    }

    fn spawn_block_on_with_spawn_body(&self) -> Option<rustc_public::mir::Body> {
        self.resolve_body_call_instance_by_suffix(self.body, "block_on_with_spawn")?.body()
    }

    fn predeclare_spawn_scheduler_core_type_arrays(
        &self,
        type_arrays: &mut BTreeMap<String, Sort>,
    ) {
        for (key, sort) in [("ptr", ptr_sort()), ("std_boxed_Box_u8_std_alloc_Global", ptr_sort())]
        {
            type_arrays.entry(key.to_owned()).or_insert(sort);
        }
    }

    fn collect_spawn_scheduler_type_arrays_from_body(
        &self,
        body: &rustc_public::mir::Body,
        type_arrays: &mut BTreeMap<String, Sort>,
    ) {
        for local in body.locals() {
            let ty = self.resolve_body_ty(local.ty);
            let key = self.type_key_for_body_ty(ty);
            if self.is_spawn_scheduler_support_type_key(key.as_ref()) {
                type_arrays
                    .entry(key.into_owned())
                    .or_insert_with(|| self.elem_sort_for_memory_array(ty));
            }
        }
    }

    fn is_spawn_scheduler_support_type_key(&self, type_key: &str) -> bool {
        type_key.contains("Scheduler")
            || type_key.contains("JoinHandle")
            || type_key.contains("YieldNow")
            || type_key.contains("RoundRobin")
            || type_key.contains("SchedulingAssumption")
            || type_key.contains("AtomicI64")
            || type_key.contains("Future_Output_unit_Sync")
            || type_key.contains("std_task_Waker")
            || type_key.contains("std_task_LocalWaker")
            || type_key.contains("std_task_Context")
            || type_key.contains("std_task_RawWaker")
            || type_key.contains("std_task_RawWakerVTable")
            || type_key.contains("core_task_wake_ExtData")
            || type_key == "ptr"
            || type_key == "std_boxed_Box_u8_std_alloc_Global"
    }

    pub(super) fn prune_spawn_scheduler_task_slot_array_liveness(&mut self) {
        if !self.is_spawn_scheduler_reachable() {
            return;
        }

        let mut pruned_indices = BTreeSet::new();
        let locals = self.body.locals();
        for (&local_idx, &base_idx) in &self.state_var_mgr.local_to_state_idx {
            if !self.flatten.flattened_tuple_locals.contains(&local_idx) {
                continue;
            }
            let Some(local_decl) = locals.get(local_idx) else {
                continue;
            };
            let ty = self.resolve_body_ty(local_decl.ty);
            let type_key = self.type_key_for_body_ty(ty);
            if !Self::is_spawn_scheduler_task_slot_carrier_key(type_key.as_ref()) {
                continue;
            }

            for field_idx in 0..self.flattened_field_count(local_idx) {
                let state_idx = base_idx + field_idx;
                if self
                    .state_var_mgr
                    .state_vars
                    .get(state_idx)
                    .is_some_and(|(_, sort)| sort.is_array())
                {
                    pruned_indices.insert(state_idx);
                }
            }
        }

        if pruned_indices.is_empty() {
            return;
        }

        for live in &mut self.state_var_mgr.live_state_indices {
            live.retain(|idx| !pruned_indices.contains(idx));
        }

        debug!(
            fn_name = %self.fn_name,
            pruned_array_fields = pruned_indices.len(),
            "CHC: pruned spawn scheduler task-slot array fields from relation liveness"
        );
    }

    fn is_spawn_scheduler_task_slot_carrier_key(type_key: &str) -> bool {
        type_key.contains("Scheduler")
            || type_key.contains("std_vec_Vec_std_option_Option_std_pin_Pin_std_boxed_Box_u8")
    }

    fn predeclare_spawn_scheduler_heap_regions_from_body(
        &mut self,
        body: &rustc_public::mir::Body,
    ) {
        if self.track_level < ChcTrackLevel::Ptr {
            return;
        }
        if self.encode.stack_alloc_constraints.is_none() {
            self.encode.stack_alloc_constraints = Some(self.allocate_stack_locals());
        }

        for bb_data in &body.blocks {
            let TerminatorKind::Call { func, args, destination, target, .. } =
                &bb_data.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) = self.resolve_body_callee_path(body, func) else {
                continue;
            };

            let elem_sort = if let Some(stub) = self.stub_registry.lookup(&callee_path) {
                match stub {
                    StubKind::BoxNew | StubKind::RustAlloc | StubKind::RustAllocZeroed => self
                        .spawn_alloc_stub_elem_sort(body, stub, args, destination.local, *target),
                    StubKind::RustRealloc => bv8_sort(),
                    StubKind::RustDealloc => continue,
                    _ => continue,
                }
            } else if Self::is_rc_arc_new_path(&callee_path) {
                bv8_sort()
            } else {
                continue;
            };

            let Some(obj_id) = self.heap_state.reserve_heap_alloc_id() else {
                warn!("CHC: allocation ID overflow during spawn scheduler pre-declaration");
                continue;
            };
            self.predeclare_region_state_var(obj_id, elem_sort);
        }
    }

    fn spawn_alloc_stub_elem_sort(
        &self,
        body: &rustc_public::mir::Body,
        stub: StubKind,
        args: &[Operand],
        destination_local: usize,
        target: Option<usize>,
    ) -> Sort {
        match stub {
            StubKind::BoxNew => args
                .first()
                .and_then(|arg| arg.ty(body.locals()).ok())
                .map(|ty| self.elem_sort_for_memory_array(ty))
                .unwrap_or_else(bv8_sort),
            StubKind::RustAlloc | StubKind::RustAllocZeroed => target
                .and_then(|target_bb| {
                    self.spawn_target_block_elem_sort_for_alloc(body, target_bb, destination_local)
                })
                .unwrap_or_else(bv8_sort),
            StubKind::RustRealloc => bv8_sort(),
            _ => bv8_sort(),
        }
    }

    fn spawn_target_block_elem_sort_for_alloc(
        &self,
        body: &rustc_public::mir::Body,
        target_bb: usize,
        alloc_local: usize,
    ) -> Option<Sort> {
        let block = body.blocks.get(target_bb)?;
        block.statements.iter().find_map(|stmt| {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                return None;
            };

            match rvalue {
                Rvalue::ShallowInitBox(operand, boxed_ty)
                    if Self::spawn_operand_is_unprojected_local(operand, alloc_local) =>
                {
                    Some(self.elem_sort_for_memory_array(*boxed_ty))
                }
                Rvalue::Cast(_, operand, target_ty)
                    if Self::spawn_operand_is_unprojected_local(operand, alloc_local) =>
                {
                    Self::spawn_pointee_ty(*target_ty).map(|ty| self.elem_sort_for_memory_array(ty))
                }
                _ => None,
            }
        })
    }

    fn spawn_pointee_ty(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some(inner),
            _ => None,
        }
    }

    fn spawn_operand_is_unprojected_local(operand: &Operand, local: usize) -> bool {
        matches!(
            operand,
            Operand::Copy(place) | Operand::Move(place)
                if place.local == local && place.projection.is_empty()
        )
    }
}

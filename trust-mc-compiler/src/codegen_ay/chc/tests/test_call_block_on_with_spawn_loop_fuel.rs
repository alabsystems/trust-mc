// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Loop-fuel regression coverage for `block_on_with_spawn`.
//!
//! Part of #4075.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::call::codegen_call_virtual_inline::loop_replay::InlineWalkCtx;
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition;
use crate::codegen_ay::shared::count_effective_blocks;
use rustc_public::mir::TerminatorKind;
use std::collections::HashSet;

const ASYNC_SPAWN_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/AsyncAwait/spawn.rs");
const LOCAL_KANI_ASYNC_RUNTIME: &str = include_str!("test_call_block_on_with_spawn_runtime.txt");

fn build_async_spawn_unit_source(source: &str) -> String {
    let mut result = String::from(LOCAL_KANI_ASYNC_RUNTIME);
    result.push('\n');
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::proof")
            || trimmed.starts_with("#[kani::unwind")
            || trimmed.starts_with("// kani-expect:")
            || trimmed.starts_with("// compile-flags:")
            || trimmed.starts_with("// kani-flags:")
            || trimmed.starts_with("//!")
        {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

fn with_block_on_with_spawn_call(
    mut body: impl FnMut(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>) + Send,
) {
    let source = build_async_spawn_unit_source(ASYNC_SPAWN_REAL_FILE);
    with_test_ay_ctx_for_source_with_edition(&source, "2018", move |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "round_robin_schedule_manual");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new_with_instance(
            ctx.tcx,
            &mir_body,
            instance,
            "round_robin_schedule_manual",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(target_bb) = *target else {
                continue;
            };
            let Some(callee_path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if !callee_path.ends_with("::block_on_with_spawn")
                && callee_path != "block_on_with_spawn"
            {
                continue;
            }

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: Some(callee_path),
            };

            body(&mut chc_ctx, &dcx);
            return;
        }

        panic!("expected a block_on_with_spawn call in round_robin_schedule_manual");
    });
}

#[test]
fn test_spawn_scheduler_model_clamps_loop_fuel_to_exact_round_robin_schedule() {
    with_block_on_with_spawn_call(|chc_ctx, dcx| {
        let (_instance, callee_name, callee_body, spawn_model) =
            chc_ctx.resolve_block_on_inline_target(dcx).expect("spawn dispatch target");
        let spawn_model = spawn_model.expect("spawn dispatch should install a scheduler model");
        assert_eq!(
            spawn_model.scheduler_loop_replay_fuel(),
            Some(3),
            "round_robin_schedule_manual has exactly three scheduler polls: root pending, child ready, root ready"
        );
        assert_eq!(
            spawn_model.poll_vtable_ids.len(),
            3,
            "modeled vtable schedule should match the three-poll round-robin packet"
        );
        assert_eq!(
            spawn_model.poll_task_indices,
            vec![0, 1, 0],
            "round_robin_schedule_manual should also carry the exact task-slot poll order"
        );

        let scheduler_run = if callee_name.contains("Scheduler::block_on") {
            chc_ctx
                .resolve_body_call_instance_by_suffix(&callee_body, "Scheduler::run")
                .expect("Scheduler::block_on should call Scheduler::run")
        } else {
            let scheduler_block_on = chc_ctx
                .resolve_body_call_instance_by_suffix(&callee_body, "Scheduler::block_on")
                .expect("block_on_with_spawn should call Scheduler::block_on");
            let scheduler_block_on_body =
                scheduler_block_on.body().expect("Scheduler::block_on body");
            chc_ctx
                .resolve_body_call_instance_by_suffix(&scheduler_block_on_body, "Scheduler::run")
                .expect("Scheduler::block_on should call Scheduler::run")
        };
        let scheduler_run_body = scheduler_run.body().expect("Scheduler::run body");
        let resolver_map = std::collections::HashMap::new();
        let walk_ctx = InlineWalkCtx::new_with_loop_fuel_override(
            &scheduler_run_body,
            PlaceResolver::FieldMap(&resolver_map),
            count_effective_blocks(&scheduler_run_body),
            0,
            spawn_model.scheduler_loop_replay_fuel(),
        );
        let loop_fuel = walk_ctx.snapshot_loop_header_fuel();

        assert!(
            !loop_fuel.is_empty(),
            "Scheduler::run should remain a loop-bearing body in the inline walker"
        );
        assert!(
            loop_fuel.values().all(|fuel| *fuel == 3),
            "spawn-specific loop override should clamp every Scheduler::run loop header to three visits, got {loop_fuel:?}"
        );
    });
}

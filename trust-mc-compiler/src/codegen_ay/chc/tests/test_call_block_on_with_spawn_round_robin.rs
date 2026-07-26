// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Round-robin scheduler regression coverage for `block_on_with_spawn`.
//!
//! Part of #4075.

#![allow(clippy::panic, clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::chc::call::inline_shared::inline_operand_to_expr;
use crate::codegen_ay::chc::call::try_inline_nested_call_step;
use ay_bindings::Expr;
use rustc_public::mir::TerminatorKind;
use std::collections::HashMap;

const ROUND_ROBIN_PICK_TASK_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::{future::Future, pin::Pin};

    type BoxFuture = Pin<Box<dyn Future<Output = ()> + Sync + 'static>>;

    pub enum SchedulingAssumption {
        CanAssumeRunning,
        CannotAssumeRunning,
    }

    pub trait SchedulingStrategy {
        fn pick_task(&mut self, num_tasks: usize) -> (usize, SchedulingAssumption);
    }

    #[derive(Default)]
    pub struct RoundRobin {
        index: usize,
    }

    impl SchedulingStrategy for RoundRobin {
        fn pick_task(&mut self, num_tasks: usize) -> (usize, SchedulingAssumption) {
            self.index = (self.index + 1) % num_tasks;
            (self.index, SchedulingAssumption::CannotAssumeRunning)
        }
    }

    pub fn probe_round_robin_pick_task(
        mut plan: RoundRobin,
        num_tasks: usize,
    ) -> (usize, SchedulingAssumption) {
        plan.pick_task(num_tasks)
    }
"#;

fn with_round_robin_pick_task_ctx<T: Send>(
    f: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &rustc_public::mir::Body,
        rustc_public::mir::Operand,
        Vec<rustc_public::mir::Operand>,
        rustc_public::mir::Place,
        String,
    ) -> T
    + Send,
) -> T {
    let mut result = None;
    with_test_ay_ctx_for_source(ROUND_ROBIN_PICK_TASK_SOURCE, |ctx| {
        let fn_name = "probe_round_robin_pick_task";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let call_sites: Vec<_> = body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => chc_ctx
                    .resolve_callee_path(func)
                    .map(|path| (func.clone(), args.clone(), destination.clone(), path)),
                _ => None,
            })
            .collect();
        let available_paths: Vec<_> =
            call_sites.iter().map(|(_, _, _, path)| path.clone()).collect();
        let (func, args, destination, callee_path) = call_sites
            .into_iter()
            .find(|(_, _, _, path)| path.ends_with("::pick_task"))
            .unwrap_or_else(|| {
                panic!("expected RoundRobin::pick_task call in probe, saw {available_paths:?}")
            });
        result = Some(f(&mut chc_ctx, &body, func, args, destination, callee_path));
    });
    result.expect("round-robin pick_task test closure should produce a result")
}

fn spawn_scheduler_model() -> crate::codegen_ay::chc::codegen_ctx::SpawnSchedulerVtableModel {
    crate::codegen_ay::chc::codegen_ctx::SpawnSchedulerVtableModel {
        poll_vtable_ids: vec![11, 22, 11],
        next_poll_idx: 0,
        poll_task_indices: vec![0, 1, 0],
        next_task_idx: 1,
        current_task_vtable_id: None,
        scheduler_loop_replay_fuel: Some(3),
    }
}

fn sort_default_or_datatype(sort: &ay_bindings::Sort) -> Option<Expr> {
    // Scalar sorts: use ChcCtx::sort_default_expr.
    if let Some(expr) = ChcCtx::sort_default_expr(sort) {
        return Some(expr);
    }
    // Datatype sorts: construct using the first constructor with zero-valued fields.
    if let ay_bindings::SortInner::Datatype(dt) = sort.inner() {
        if let Some(ctor) = dt.constructors.first() {
            let fields: Vec<Expr> =
                ctor.fields.iter().filter_map(|f| sort_default_or_datatype(&f.sort)).collect();
            if fields.len() == ctor.fields.len() {
                return Some(Expr::datatype_constructor(
                    &dt.name,
                    &ctor.name,
                    fields,
                    sort.clone(),
                ));
            }
        }
    }
    None
}

fn round_robin_local_exprs(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> HashMap<usize, Expr> {
    // Populate ALL translatable locals so MIR reborrow temporaries are covered.
    let mut map = HashMap::new();
    for (idx, local) in body.locals().iter().enumerate() {
        let resolved = chc_ctx.resolve_body_ty(local.ty);
        if let Some(sort) = ChcCtx::translate_ty(resolved) {
            if let Some(expr) = sort_default_or_datatype(&sort) {
                map.insert(idx, expr);
            }
        }
    }
    // Override num_tasks (local 2) with a non-zero value for meaningful modular arithmetic.
    map.insert(2usize, Expr::bitvec_const(2u64, crate::codegen_ay::types::POINTER_WIDTH));
    map
}

fn assert_updated_plan_uses_task_index(updated_plan: &Expr) {
    let updated_sort = updated_plan.sort();
    let updated_index = if let Some(width) = updated_sort.bitvec_width() {
        assert_eq!(
            width,
            crate::codegen_ay::types::POINTER_WIDTH,
            "flattened RoundRobin receiver should use pointer width, got {updated_sort:?}"
        );
        updated_plan.clone()
    } else {
        let ay_bindings::SortInner::Datatype(plan_dt) = updated_sort.inner() else {
            panic!(
                "RoundRobin receiver should stay a datatype or pointer-width BV, got {updated_sort:?}"
            );
        };
        let index_field = &plan_dt.constructors[0].fields[0];
        updated_plan.clone().field_select(
            &plan_dt.name,
            &index_field.name,
            index_field.sort.clone(),
        )
    };
    assert_expr_has_bv_literal(
        &updated_index,
        crate::codegen_ay::types::POINTER_WIDTH,
        1,
        "spawn scheduler packet should force the second poll onto task slot 1",
    );
}

fn assert_pick_task_result_is_exact(result_value: &Expr) {
    let tuple_sort = result_value.sort();
    let ay_bindings::SortInner::Datatype(tuple_dt) = tuple_sort.inner() else {
        panic!("pick_task result should stay a tuple datatype, got {tuple_sort:?}");
    };
    let task_idx_field = &tuple_dt.constructors[0].fields[0];
    let assumption_field = &tuple_dt.constructors[0].fields[1];
    let returned_task_idx = result_value.clone().field_select(
        &tuple_dt.name,
        &task_idx_field.name,
        task_idx_field.sort.clone(),
    );
    let returned_assumption = result_value.clone().field_select(
        &tuple_dt.name,
        &assumption_field.name,
        assumption_field.sort.clone(),
    );
    assert_expr_has_bv_literal(
        &returned_task_idx,
        crate::codegen_ay::types::POINTER_WIDTH,
        1,
        "pick_task should return the exact scheduled task index",
    );

    if let Some(width) = assumption_field.sort.bitvec_width() {
        assert_expr_has_bv_literal(
            &returned_assumption,
            width,
            1,
            "BV-backed SchedulingAssumption should encode CannotAssumeRunning as 1",
        );
    } else {
        let ay_bindings::SortInner::Datatype(assumption_dt) = assumption_field.sort.inner() else {
            panic!(
                "SchedulingAssumption should stay an enum datatype or BV sort, got {:?}",
                assumption_field.sort
            );
        };
        let cannot_ctor = assumption_dt
            .constructors
            .iter()
            .find(|ctor| ctor.name.contains("CannotAssumeRunning"))
            .expect("CannotAssumeRunning constructor");
        let is_ctor_expr =
            returned_assumption.is_constructor(&assumption_dt.name, &cannot_ctor.name);
        let is_ctor_dbg = format!("{is_ctor_expr:?}");
        assert!(
            is_ctor_dbg.contains("CannotAssumeRunning"),
            "RoundRobin::pick_task should stay on CannotAssumeRunning, got {is_ctor_dbg}"
        );
    }
}

fn assert_spawn_model_advanced(chc_ctx: &ChcCtx<'_, '_>) {
    let model = chc_ctx.spawn_scheduler_vtable_model.as_ref().expect("spawn model");
    assert_eq!(model.next_task_idx, 2, "pick_task should advance the scheduler packet once");
    assert_eq!(
        model.poll_task_indices,
        vec![0, 1, 0],
        "fast path should consume the existing exact task schedule without rewriting it"
    );
}

fn assert_expr_has_bv_literal(expr: &Expr, width: u32, value: u64, label: &str) {
    let dbg = format!("{expr:?}");
    let is_const = matches!(
        expr.value(),
        ay_bindings::ExprValue::BitVecConst { value: actual, width: actual_width }
            if *actual_width == width && *actual == num_bigint::BigInt::from(value)
    );
    // Also accept a DatatypeSelector/Constructor chain that wraps a matching literal.
    // AY does not simplify `select(mk(x)) → x`, so nested literals appear as
    // `BitVecConst { value: <v>, width: <w> }` in the debug representation.
    let hex_literal = format!("#x{:0digits$x}", value, digits = (width / 4) as usize);
    let nested_literal = format!("BitVecConst {{ value: {value}, width: {width} }}");
    assert!(
        is_const || dbg.contains(&hex_literal) || dbg.contains(&nested_literal),
        "{label}, got {dbg}",
    );
}

fn operand_debug_summaries(
    chc_ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Vec<String> {
    args.iter()
        .enumerate()
        .map(|(idx, arg)| {
            let translated =
                inline_operand_to_expr(chc_ctx, arg, local_exprs, resolver, body.locals())
                    .map(|expr| format!("{:?}", expr.sort()))
                    .unwrap_or_else(|| "<none>".to_owned());
            let arg_ty = arg
                .ty(body.locals())
                .ok()
                .map(|ty| format!("{:?}", chc_ctx.resolve_body_ty(ty)))
                .unwrap_or_else(|| "<ty-err>".to_owned());
            format!("arg{idx}: {arg:?}, ty={arg_ty}, translated={translated}")
        })
        .collect()
}

fn local_assignment_summaries(body: &rustc_public::mir::Body, local: usize) -> Vec<String> {
    body.blocks
        .iter()
        .enumerate()
        .flat_map(|(bb_idx, block)| {
            block.statements.iter().filter_map(move |stmt| match &stmt.kind {
                rustc_public::mir::StatementKind::Assign(lhs, rhs)
                    if lhs.local == local && lhs.projection.is_empty() =>
                {
                    Some(format!("bb{bb_idx}: _{local} = {rhs:?}"))
                }
                _ => None,
            })
        })
        .collect()
}

#[test]
fn test_spawn_round_robin_pick_task_uses_exact_scheduler_packet() {
    with_round_robin_pick_task_ctx(|chc_ctx, body, func, args, destination, callee_path| {
        chc_ctx.spawn_scheduler_vtable_model = Some(spawn_scheduler_model());
        let local_exprs = round_robin_local_exprs(chc_ctx, body);
        let inline_vtable_ids = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);
        let arg_debug = operand_debug_summaries(chc_ctx, &args, body, &local_exprs, &resolver);
        let receiver_local = args.first().and_then(|arg| match arg {
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
                if place.projection.is_empty() =>
            {
                Some(place.local)
            }
            _ => None,
        });
        let receiver_assignments =
            receiver_local.map(|local| local_assignment_summaries(body, local)).unwrap_or_default();
        let destination_sort = destination
            .ty(body.locals())
            .ok()
            .map(|ty| chc_ctx.resolve_body_ty(ty))
            .and_then(ChcCtx::translate_ty)
            .map(|sort| format!("{sort:?}"))
            .unwrap_or_else(|| "<none>".to_owned());

        let result = try_inline_nested_call_step(
            chc_ctx,
            &func,
            &args,
            body,
            &local_exprs,
            &resolver,
            &inline_vtable_ids,
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| {
            panic!(
                "expected nested helper call {callee_path} to inline; args={arg_debug:?}, \
                 receiver_assignments={receiver_assignments:?}, destination_sort={destination_sort}, \
                 local_expr_keys={:?}",
                local_exprs.keys().copied().collect::<Vec<_>>(),
            )
        });

        let updated_plan = result.alias_updates.get(&1).expect("pick_task should update the plan");
        assert_updated_plan_uses_task_index(updated_plan);
        assert_pick_task_result_is_exact(&result.value);
        assert_spawn_model_advanced(chc_ctx);
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exact nested-call fast paths for the spawn scheduler's `RoundRobin::pick_task`.
//!
//! Part of #4075: once the spawn packet has an exact bounded poll order, feed
//! those concrete task indices directly into `Scheduler::run` so the inline
//! walker does not carry symbolic `% num_tasks` arithmetic and symbolic
//! `Vec<Option<BoxFuture>>` indexing through the scheduler loop.

use std::collections::{BTreeMap, HashMap};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::InlineReturn;
use super::pointer_wrapper::resolve_nested_ref_arg_referent;
use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::Operand;

fn receiver_expr(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<Expr> {
    args.first().and_then(|arg| {
        resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver).or_else(|| {
            inline_operand_to_expr(ctx, arg, local_exprs, resolver, outer_body.locals())
        })
    })
}

fn build_round_robin_with_index(receiver: Expr, next_index: u64) -> Option<Expr> {
    if let Some(width) = receiver.sort().bitvec_width() {
        return Some(Expr::bitvec_const(next_index as u128, width));
    }
    let SortInner::Datatype(dt) = receiver.sort().inner() else {
        return None;
    };
    let cons = dt.constructors.first()?;
    if cons.fields.len() != 1 {
        return None;
    }
    let index_field = cons.fields.first()?;
    let width = index_field.sort.bitvec_width()?;
    let index_expr = Expr::bitvec_const(next_index as u128, width);
    Some(Expr::datatype_constructor(
        &dt.name,
        &cons.name,
        vec![index_expr],
        receiver.sort().clone(),
    ))
}

fn cannot_assume_running_expr(sort: &Sort) -> Option<Expr> {
    if let Some(width) = sort.bitvec_width() {
        return Some(Expr::bitvec_const(1u128, width));
    }
    let SortInner::Datatype(dt) = sort.inner() else {
        return None;
    };
    let ctor = dt
        .constructors
        .iter()
        .find(|ctor| ctor.fields.is_empty() && ctor.name.contains("CannotAssumeRunning"))?;
    Some(Expr::datatype_constructor(&dt.name, &ctor.name, vec![], sort.clone()))
}

fn build_pick_task_result(tuple_sort: &Sort, next_index: u64) -> Option<Expr> {
    let SortInner::Datatype(dt) = tuple_sort.inner() else {
        return None;
    };
    let cons = dt.constructors.first()?;
    if cons.fields.len() != 2 {
        return None;
    }
    let index_width = cons.fields[0].sort.bitvec_width()?;
    let index_expr = Expr::bitvec_const(next_index as u128, index_width);
    let assumption_expr = cannot_assume_running_expr(&cons.fields[1].sort)?;
    Some(Expr::datatype_constructor(
        &dt.name,
        &cons.name,
        vec![index_expr, assumption_expr],
        tuple_sort.clone(),
    ))
}

pub(super) fn try_inline_round_robin_pick_task_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<InlineReturn> {
    if !callee_path.ends_with("::pick_task") {
        return None;
    }
    if args.len() != 2 {
        return None;
    }
    let receiver = receiver_expr(ctx, args, outer_body, local_exprs, resolver)?;
    let next_index = ctx.spawn_scheduler_vtable_model.as_mut()?.next_task_index()?;
    let updated_receiver = build_round_robin_with_index(receiver, next_index)?;
    let result_sort = destination
        .ty(outer_body.locals())
        .ok()
        .map(|ty| ctx.resolve_body_ty(ty))
        .and_then(ChcCtx::translate_ty)?;
    let value = build_pick_task_result(&result_sort, next_index)?;
    let alias_updates = BTreeMap::from([(1usize, updated_receiver)]);
    Some(InlineReturn {
        value,
        vtable: None,
        alloc_id: None,
        alias_updates,
        deferred_checks: Vec::new(),
    })
}

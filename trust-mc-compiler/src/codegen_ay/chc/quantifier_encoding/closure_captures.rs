// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Closure capture resolution for quantifier encoding.
//!
//! Extracted from `mod.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, LocalDecl, Operand, Rvalue, StatementKind};
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::super::ChcCtx;
use super::super::call::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::super::decl::codegen_types::CodegenTypes;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::helpers::{
    inline_quantifier_rvalue_expr, linear_predecessor_chain, replay_quantifier_local_assignments,
};

/// Extract captured variable expressions from a closure aggregate.
///
/// Scans the current block's MIR statements to find the Aggregate(Closure, ...)
/// that constructed the closure operand, then translates each captured value.
pub(in crate::codegen_ay::chc) fn extract_closure_captures<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    closure_operand: &Operand,
    modified_locals: &HashSet<usize>,
    bb_idx: usize,
) -> Vec<Expr> {
    let closure_local = match closure_operand {
        Operand::Copy(p) | Operand::Move(p) => p.local,
        _ => return Vec::new(), // external enum: Operand
    };

    // Find the Aggregate(Closure, ...) statement that built this local
    if let Some(block) = ctx.body.blocks.get(bb_idx) {
        let locals = ctx.body.locals();
        let resolver = PlaceResolver::Captures(&[]);
        let mut local_exprs: HashMap<usize, Expr> = HashMap::new();
        let replay_blocks = linear_predecessor_chain(ctx, bb_idx);
        let mut assign_counts: HashMap<usize, usize> = HashMap::new();
        for &block_idx in &replay_blocks {
            let Some(replay_block) = ctx.body.blocks.get(block_idx) else {
                continue;
            };
            for stmt in &replay_block.statements {
                if let StatementKind::Assign(place, _) = &stmt.kind
                    && place.projection.is_empty()
                {
                    *assign_counts.entry(place.local).or_insert(0) += 1;
                }
            }
        }
        for &block_idx in replay_blocks.iter().take_while(|&&block_idx| block_idx != bb_idx) {
            let Some(replay_block) = ctx.body.blocks.get(block_idx) else {
                continue;
            };
            replay_quantifier_local_assignments(
                ctx,
                &replay_block.statements,
                &assign_counts,
                &resolver,
                &locals,
                &mut local_exprs,
            );
        }
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind
                && place.local == closure_local
                && let Rvalue::Aggregate(AggregateKind::Closure(_, _), fields) = rvalue
            {
                return fields
                    .iter()
                    .filter_map(|op| {
                        inline_operand_to_expr(ctx, op, &local_exprs, &resolver, &locals)
                            .or_else(|| {
                                resolve_closure_capture_ref_source(
                                    ctx,
                                    op,
                                    &local_exprs,
                                    &resolver,
                                    &locals,
                                    &block.statements,
                                    modified_locals,
                                )
                            })
                            .or_else(|| ctx.translate_operand_with_modified(op, modified_locals))
                    })
                    .collect();
            }
            if let StatementKind::Assign(place, rvalue) = &stmt.kind
                && place.projection.is_empty()
                && let Some(expr) = inline_quantifier_rvalue_expr(
                    ctx,
                    place.local,
                    rvalue,
                    &local_exprs,
                    &resolver,
                    &locals,
                )
            {
                local_exprs.insert(place.local, expr);
            }
        }
    }

    debug!(?bb_idx, ?closure_local, "could not find closure aggregate");
    Vec::new()
}

pub(in crate::codegen_ay::chc) fn extract_inline_closure_captures<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    closure_operand: &Operand,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Vec<Expr> {
    let Some(closure_expr) =
        inline_operand_to_expr(ctx, closure_operand, local_exprs, resolver, locals)
    else {
        return Vec::new();
    };
    declare_datatype_sorts_in_expr(ctx, &closure_expr);

    if let ay_bindings::ExprValue::DatatypeConstructor { args, .. } = closure_expr.value() {
        for arg in args {
            declare_datatype_sorts_in_expr(ctx, arg);
        }
        return args.clone();
    }

    let Some(dt) = closure_expr.sort().datatype_sort() else {
        return Vec::new();
    };
    let Some(constructor) = dt.constructors.first() else {
        return Vec::new();
    };
    let captures = constructor
        .fields
        .iter()
        .map(|field| closure_expr.clone().field_select(&dt.name, &field.name, field.sort.clone()))
        .collect::<Vec<_>>();
    for capture in &captures {
        declare_datatype_sorts_in_expr(ctx, capture);
    }
    captures
}

fn declare_datatype_sorts_in_expr<'tcx, 'body>(ctx: &mut ChcCtx<'tcx, 'body>, expr: &Expr) {
    let mut stack = vec![expr.clone()];
    while let Some(current) = stack.pop() {
        ctx.declare_datatype_sort_if_needed(current.sort());
        stack.extend(current.children().cloned());
    }
}

fn resolve_closure_capture_ref_source<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    operand: &Operand,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[rustc_public::mir::LocalDecl],
    statements: &[rustc_public::mir::Statement],
    modified_locals: &HashSet<usize>,
) -> Option<Expr> {
    let ref_local = match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place.local,
        _ => return None,
    };

    for stmt in statements {
        if let StatementKind::Assign(place, rvalue) = &stmt.kind
            && place.local == ref_local
            && let Rvalue::Ref(_, _, inner_place) = rvalue
            && inner_place.projection.is_empty()
        {
            let inner_op = Operand::Copy(inner_place.clone());
            return inline_operand_to_expr(ctx, &inner_op, local_exprs, resolver, locals)
                .or_else(|| ctx.translate_operand_with_modified(&inner_op, modified_locals));
        }
    }

    None
}

pub(super) fn inline_array_capture_aggregate_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    dest_local: usize,
    rvalue: &Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<Expr> {
    let Rvalue::Aggregate(_, operands) = rvalue else {
        return None;
    };
    let dest_sort = ChcCtx::translate_ty(locals.get(dest_local)?.ty)?;
    if !dest_sort.is_array() || operands.is_empty() {
        return None;
    }

    let mut elems = operands
        .iter()
        .map(|op| inline_operand_to_expr(ctx, op, local_exprs, resolver, locals))
        .collect::<Option<Vec<_>>>()?
        .into_iter();
    let first = elems.next()?;
    let first = ChcCtx::coerce_store_value(&dest_sort, first, false, &ctx.diagnostics);
    let index_sort = dest_sort.array_sort()?.index_sort.clone();
    let mut result = Expr::const_array(index_sort, first.clone());
    result = result.store(Expr::bitvec_const(0u64, POINTER_WIDTH), first);
    for (idx, elem) in elems.enumerate() {
        let elem = ChcCtx::coerce_store_value(&dest_sort, elem, false, &ctx.diagnostics);
        result = result.store(Expr::bitvec_const((idx + 1) as u64, POINTER_WIDTH), elem);
    }
    Some(result)
}

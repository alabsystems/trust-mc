// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Quantifier encoding helper functions: predecessor chain, local replay, rvalue inline.
//!
//! Extracted from `mod.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{Rvalue, StatementKind};
use std::collections::{HashMap, HashSet};

use super::super::ChcCtx;
use super::super::call::inline_shared::{PlaceResolver, inline_rvalue_to_expr};
use super::closure_captures::inline_array_capture_aggregate_expr;

pub(super) fn linear_predecessor_chain<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    bb_idx: usize,
) -> Vec<usize> {
    let block_count = ctx.body.blocks.len();
    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); block_count];
    for (idx, block) in ctx.body.blocks.iter().enumerate() {
        for succ in ChcCtx::block_successors(&block.terminator.kind) {
            if succ < block_count {
                predecessors[succ].push(idx);
            }
        }
    }

    let mut chain = Vec::new();
    let mut visited = HashSet::new();
    let mut current = bb_idx;
    loop {
        if !visited.insert(current) {
            break;
        }
        chain.push(current);
        let Some(preds) = predecessors.get(current) else {
            break;
        };
        if preds.len() != 1 {
            break;
        }
        current = preds[0];
    }
    chain.reverse();
    chain
}

pub(super) fn replay_quantifier_local_assignments<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    statements: &[rustc_public::mir::Statement],
    assign_counts: &HashMap<usize, usize>,
    resolver: &PlaceResolver<'_>,
    locals: &[rustc_public::mir::LocalDecl],
    local_exprs: &mut HashMap<usize, Expr>,
) {
    for stmt in statements {
        let StatementKind::Assign(place, rvalue) = &stmt.kind else {
            continue;
        };
        if !place.projection.is_empty()
            || assign_counts.get(&place.local).copied().unwrap_or(0) != 1
        {
            continue;
        }
        // Quantifiers B1: a replayed single-assignment value is the actual
        // program semantics and must take priority over any pre-populated
        // debug-const entry (a heuristic recovered from var_debug_info), so
        // successful inlining OVERWRITES existing entries. Since
        // `assign_counts == 1` guarantees one assignment per local across the
        // whole replay chain, only debug-const guesses are ever overwritten —
        // never an earlier replayed value. If inlining fails, the (name-gated)
        // debug-const entry is kept as a last resort.
        if let Some(expr) =
            inline_quantifier_rvalue_expr(ctx, place.local, rvalue, local_exprs, resolver, locals)
        {
            local_exprs.insert(place.local, expr);
        }
    }
}

pub(super) fn inline_quantifier_rvalue_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    dest_local: usize,
    rvalue: &Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<Expr> {
    inline_rvalue_to_expr(ctx, rvalue, local_exprs, resolver, locals, Some(dest_local)).or_else(
        || {
            inline_array_capture_aggregate_expr(
                ctx,
                dest_local,
                rvalue,
                local_exprs,
                resolver,
                locals,
            )
        },
    )
}

pub(in crate::codegen_ay::chc) fn resolve_debug_const_quantifier_bound<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    operand: &rustc_public::mir::Operand,
) -> Option<Expr> {
    let local = match operand {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            place.local
        }
        _ => return None,
    };
    resolve_debug_const_quantifier_local(ctx, local)
}

pub(super) fn resolve_debug_const_quantifier_local<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    local: usize,
) -> Option<Expr> {
    use super::super::expr::codegen_expr_constant::ExprConstant;

    let local_decl = ctx.body.locals().get(local)?;
    // Quantifiers B1 soundness: only a unique BY-NAME match (the local's
    // declaration-span identifier text equals a `VarDebugInfoContents::Const`
    // entry's name, with matching type) is trustworthy. The former by-type
    // fallback guessed "the only const of this type", which could bind a
    // DIFFERENT local's value into a quantifier bound (e.g. an `arr.len()`
    // upper bound picking up `lower_bound`'s constant), collapsing the range
    // to empty and turning an asserted forall into vacuous truth — a live
    // false-Safe. Fail closed (None) when no trustworthy name match exists;
    // callers fall back to assignment replay or the sound nondet path.
    let bound_name = identifier_source_snippet(&local_decl.span)?;
    let mut matching_by_name =
        ctx.body.var_debug_info.iter().filter_map(|info| match &info.value {
            rustc_public::mir::VarDebugInfoContents::Const(const_op)
                if info.name == bound_name && const_op.ty() == local_decl.ty =>
            {
                Some(const_op)
            }
            _ => None,
        });
    let const_op = matching_by_name.next()?;
    if matching_by_name.next().is_some() {
        return None;
    }
    ctx.translate_constant(const_op)
}

fn identifier_source_snippet(span: &rustc_public::ty::Span) -> Option<String> {
    let line_info = span.get_lines();
    if line_info.start_line != line_info.end_line || line_info.start_col >= line_info.end_col {
        return None;
    }

    let source = std::fs::read_to_string(span.get_filename()).ok()?;
    let line = source.lines().nth(line_info.start_line.checked_sub(1)?)?;
    let start_idx = line_info.start_col.checked_sub(1)?;
    let end_idx = line_info.end_col.checked_sub(1)?;
    let snippet = line.get(start_idx..end_idx)?.trim();
    if snippet.is_empty()
        || !snippet.chars().all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
        || !snippet.chars().next()?.is_ascii_alphabetic() && !snippet.starts_with('_')
    {
        return None;
    }
    Some(snippet.to_owned())
}

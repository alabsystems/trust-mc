// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tiny bool-return helper inlining for CHC call codegen.
//!
//! This is intentionally narrower than the general inline walker: it only
//! accepts straight-line helper bodies whose return value is built from local
//! copies/constants, boolean negation, or primitive comparisons. That catches
//! guard helpers such as `denominator_is_valid(x) -> bool { x != 0 }` without
//! adding another broad fallback path.

use ay_bindings::Expr;
use rustc_public::mir::{BinOp, Rvalue, StatementKind, TerminatorKind, UnOp};
use std::collections::HashMap;
use tracing::debug;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use super::inline_shared::{PlaceResolver, inline_rvalue_to_expr};

const MAX_SIMPLE_BOOL_HELPER_BLOCKS: usize = 4;
const MAX_SIMPLE_BOOL_HELPER_ASSIGNMENTS: usize = 8;

pub(in crate::codegen_ay::chc) fn try_inline_simple_bool_return_helper(
    ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
    callee_path: Option<&str>,
) -> Option<Expr> {
    let ret_sort = ChcCtx::translate_ty(body.locals().first()?.ty)?;
    if !ret_sort.is_bool() {
        return None;
    }
    if body.arg_locals().len() != params.len() {
        return None;
    }

    let mut local_exprs = HashMap::new();
    for (i, param) in params.iter().enumerate() {
        local_exprs.insert(i + 1, param.clone());
    }

    let field_map = HashMap::new();
    let resolver = PlaceResolver::FieldMap(&field_map);
    let mut current_bb = 0usize;
    let mut assignments = 0usize;

    for _ in 0..MAX_SIMPLE_BOOL_HELPER_BLOCKS {
        let block = body.blocks.get(current_bb)?;
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(place, rvalue)
                    if place.projection.is_empty() && is_simple_bool_helper_rvalue(rvalue) =>
                {
                    assignments += 1;
                    if assignments > MAX_SIMPLE_BOOL_HELPER_ASSIGNMENTS {
                        return None;
                    }
                    let expr = inline_rvalue_to_expr(
                        ctx,
                        rvalue,
                        &local_exprs,
                        &resolver,
                        body.locals(),
                        Some(place.local),
                    )?;
                    local_exprs.insert(place.local, expr);
                }
                kind if is_ignored_statement_kind(kind) => {}
                _ => return None,
            }
        }

        match block.terminator.kind {
            TerminatorKind::Return => {
                let result = local_exprs.get(&0)?.clone();
                if !result.sort().is_bool() {
                    return None;
                }
                debug!(
                    callee = callee_path.unwrap_or("<unknown>"),
                    "inline bool-return helper as direct expression"
                );
                return Some(result);
            }
            TerminatorKind::Goto { target } => current_bb = target,
            _ => return None,
        }
    }

    None
}

fn is_simple_bool_helper_rvalue(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(_) => true,
        Rvalue::UnaryOp(UnOp::Not, _) => true,
        Rvalue::BinaryOp(op, _, _) => {
            matches!(*op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
        }
        _ => false,
    }
}

fn is_ignored_statement_kind(kind: &StatementKind) -> bool {
    matches!(
        kind,
        StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(..)
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter
            | StatementKind::Retag(..)
    )
}

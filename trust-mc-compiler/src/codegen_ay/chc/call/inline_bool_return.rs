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

    // A walk of its own (call/inline_walk_guard.rs): its reads through a deref
    // answer to the outermost write mark and to THIS body's address-bound
    // parameters (seeded by the caller), not to the enclosing walk's locals.
    ctx.with_inline_walk_write_mark(|ctx| {
        ctx.with_inline_walk_frame(body, |ctx| {
            walk_simple_bool_return_helper(ctx, body, local_exprs, callee_path)
        })
    })
}

fn walk_simple_bool_return_helper(
    ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    mut local_exprs: HashMap<usize, Expr>,
    callee_path: Option<&str>,
) -> Option<Expr> {
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
                    // Projected reference fields require the richer walker's
                    // capture/field-map binding. This tiny resolver has neither
                    // that loaded-value authority nor a right to reinterpret
                    // an unreported address as the scalar it points at.
                    if super::inline_walk_guard::local_is_reference(ctx, body.locals(), place.local)
                        && matches!(rvalue, Rvalue::Use(rustc_public::mir::Operand::Copy(source) | rustc_public::mir::Operand::Move(source), ..)
                            if !source.projection.is_empty()
                                && !ctx.readonly_ref_value_matches(&rustc_public::mir::Operand::Copy(source.clone()), body.locals()[place.local].ty))
                    {
                        return None;
                    }
                    // This helper is a real inline frame too. A copy must
                    // preserve address/value/read facts before a later *copy
                    // can use the transparent-reference representation.
                    ctx.note_inline_mut_ref_assignment(body, place.local, Some(rvalue));
                    ctx.note_readonly_resolved_value(place.local, &expr);
                    if super::inline_walk_guard::local_is_reference(ctx, body.locals(), place.local)
                    {
                        if let Rvalue::Use(operand, ..) = rvalue {
                            let current = ctx
                                .readonly_ref_value_matches(operand, body.locals()[place.local].ty);
                            let projected = matches!(operand,
                                rustc_public::mir::Operand::Copy(source) | rustc_public::mir::Operand::Move(source)
                                if !source.projection.is_empty());
                            if ctx.inline_walk_operand_is_address(operand)
                                || (projected && !current)
                            {
                                ctx.tag_inline_walk_address_local(place.local);
                            } else if ctx.inline_walk_operand_is_referent(operand) || current {
                                ctx.tag_inline_walk_referent_local(place.local);
                            } else {
                                ctx.forget_inline_walk_referent_local(place.local);
                            }
                        }
                    }
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
        Rvalue::Use(_, ..) => true,
        Rvalue::UnaryOp(UnOp::Not, _) => true,
        Rvalue::BinaryOp(op, _, _) => {
            matches!(*op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
        }
        _ => false,
    }
}

fn is_ignored_statement_kind(kind: &StatementKind) -> bool {
    match kind {
        StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(..)
        | StatementKind::AscribeUserType { .. }
        | StatementKind::Coverage(..)
        | StatementKind::Nop
        | StatementKind::ConstEvalCounter => true,
        #[cfg(not(trust_toolchain))]
        StatementKind::Retag(..) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    #[test]
    fn bool_helper_copy_preserves_reference_address_or_current_value() {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        with_test_ay_ctx_for_source(
            "pub fn copy(value: &u64) -> bool { let copied = value; *copied == 19 }",
            |ctx| {
                let original = find_instance_by_suffix(ctx.tcx, "copy").callee_body().unwrap();
                // Keep an explicit type-correct copy even when the native MIR
                // optimizer removes the source's redundant `let copied`.
                let mut locals = original.locals().to_vec();
                let copy_local = locals.len();
                locals.push(locals[1].clone());
                let mut blocks = original.blocks.clone();
                let mut changed = false;
                for block in &mut blocks {
                    for statement in &mut block.statements {
                        if let StatementKind::Assign(_, rhs) = &mut statement.kind {
                            let operand = match rhs {
                                Rvalue::Use(operand, ..) => Some(operand),
                                Rvalue::BinaryOp(_, left, _) => Some(left),
                                _ => None,
                            };
                            if let Some(rustc_public::mir::Operand::Copy(place)) = operand
                                && place.local == 1
                                && !place.projection.is_empty()
                            {
                                place.local = copy_local;
                                changed = true;
                            }
                        }
                    }
                }
                assert!(changed, "control requires the native scalar comparison");
                let mut statement = blocks[0].statements[0].clone();
                statement.kind = StatementKind::Assign(
                    rustc_public::mir::Place { local: copy_local, projection: vec![] },
                    crate::rustc_compat::rvalue_use!(Rvalue::Use(
                        rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
                            local: 1,
                            projection: vec![]
                        })
                    )),
                );
                blocks[0].statements.insert(0, statement);
                let body = rustc_public::mir::Body::new(
                    blocks,
                    locals,
                    original.arg_locals().len(),
                    original.var_debug_info.clone(),
                    None,
                    original.span,
                );
                for address in [false, true] {
                    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
                    let mut chc = ChcCtx::new(ctx.tcx, &body, "copy", ChcConfig::default());
                    let value = Expr::bitvec_const(if address { 2u64 << 32 } else { 19 }, 64);
                    if address {
                        chc.inline_walk_param_address_seeds = Some(vec![1]);
                    } else {
                        chc.inline_walk_param_readonly_ref_seeds = Some(vec![(
                            1,
                            chc.readonly_ref_seed_for_value(body.locals()[1].ty, &value).unwrap(),
                        )]);
                    }
                    let result = try_inline_simple_bool_return_helper(
                        &mut chc,
                        &body,
                        &[value],
                        Some("copy"),
                    );
                    assert!(result.is_some());
                    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                        .remove("copy")
                        .unwrap_or_default();
                    if address {
                        assert!(
                            reasons.contains_key(
                                super::super::inline_walk_guard::WALKER_DEREF_READ_ADDRESS_AS_VALUE
                            ),
                            "{reasons:?}"
                        );
                    } else {
                        assert_eq!(
                            result
                                .as_ref()
                                .and_then(trust_mc_core::chc_const_prop::eval::try_eval_to_const),
                            Some(Expr::bool_const(true))
                        );
                        assert!(reasons.is_empty(), "{reasons:?}");
                    }
                }
            },
        );
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR/source tracing helpers for inline `SliceIndex` handling.

use rustc_public::mir::Operand;

use super::super::ChcCtx;

pub(super) const MAX_INLINE_REF_SOURCE_TRACE_DEPTH: usize = 8;

fn operand_source_place(operand: &Operand) -> Option<rustc_public::mir::Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place.clone()),
        Operand::Constant(_) => None,
    }
}

fn resolve_inline_aggregate_field_source_place(
    body: &rustc_public::mir::Body,
    aggregate_local: usize,
    field_idx: usize,
) -> Option<rustc_public::mir::Place> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if lhs.local != aggregate_local || !lhs.projection.is_empty() {
                continue;
            }
            let rustc_public::mir::Rvalue::Aggregate(_, operands) = rhs else {
                continue;
            };
            let operand = operands.get(field_idx)?;
            let source_place = operand_source_place(operand)?;
            return Some(source_place);
        }
    }
    None
}

pub(super) fn describe_inline_local_source(
    body: &rustc_public::mir::Body,
    local: usize,
) -> Option<String> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let rustc_public::mir::StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                continue;
            };
            if lhs.local == local && lhs.projection.is_empty() {
                return Some(format!("{rvalue:?}"));
            }
        }
        if let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
            &block.terminator.kind
            && destination.local == local
            && destination.projection.is_empty()
        {
            return Some(format!("Call({func:?})"));
        }
    }
    None
}

pub(super) fn rawptr_aggregate_data_operand(
    body: &rustc_public::mir::Body,
    local: usize,
) -> Option<Operand> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if lhs.local != local || !lhs.projection.is_empty() {
                continue;
            }
            let rustc_public::mir::Rvalue::Aggregate(
                rustc_public::mir::AggregateKind::RawPtr(_, _),
                operands,
            ) = rhs
            else {
                continue;
            };
            return operands.first().cloned();
        }
    }
    None
}

pub(super) fn trace_inline_source_place<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    local: usize,
    depth_remaining: usize,
) -> Option<rustc_public::mir::Place> {
    if depth_remaining == 0 {
        return None;
    }

    let recurse_or_place =
        |source_place: rustc_public::mir::Place| -> Option<rustc_public::mir::Place> {
            if source_place.projection.is_empty()
                || (source_place.projection.len() == 1
                    && matches!(
                        source_place.projection[0],
                        rustc_public::mir::ProjectionElem::Deref
                    ))
            {
                trace_inline_source_place(ctx, body, source_place.local, depth_remaining - 1)
                    .or(Some(source_place))
            } else {
                Some(source_place)
            }
        };

    body.blocks
        .iter()
        .find_map(|block| {
            block.statements.iter().find_map(|stmt| {
                let rustc_public::mir::StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    return None;
                };
                if lhs.local != local {
                    return None;
                }
                match rvalue {
                    rustc_public::mir::Rvalue::Ref(_, _, place)
                    | rustc_public::mir::Rvalue::AddressOf(_, place) => {
                        recurse_or_place(place.clone())
                    }
                    rustc_public::mir::Rvalue::Use(operand)
                    | rustc_public::mir::Rvalue::Cast(_, operand, _) => {
                        let source_place = operand_source_place(operand).and_then(|place| {
                            if place.projection.len() == 1
                                && let rustc_public::mir::ProjectionElem::Field(field_idx, _) =
                                    place.projection[0]
                            {
                                resolve_inline_aggregate_field_source_place(
                                    body,
                                    place.local,
                                    field_idx,
                                )
                                .or(Some(place))
                            } else {
                                Some(place)
                            }
                        })?;
                        recurse_or_place(source_place)
                    }
                    rustc_public::mir::Rvalue::CopyForDeref(place) => {
                        recurse_or_place(place.clone())
                    }
                    _ => None,
                }
            })
        })
        .or_else(|| {
            let ref_target = ctx.ref_resolution.ref_targets.get(&local)?;
            let target_place = rustc_public::mir::Place {
                local: ref_target.local,
                projection: ref_target.projections.clone(),
            };
            recurse_or_place(target_place)
        })
        .or_else(|| {
            body.blocks.iter().find_map(|block| {
                let rustc_public::mir::TerminatorKind::Call { args, destination, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                if destination.local != local || !destination.projection.is_empty() {
                    return None;
                }
                let source_place = args.first().and_then(operand_source_place)?;
                recurse_or_place(source_place)
            })
        })
}

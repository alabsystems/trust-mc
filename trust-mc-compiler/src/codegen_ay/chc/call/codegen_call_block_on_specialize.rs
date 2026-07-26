// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR specialization helpers for `block_on`.
//!
//! Rewrites the busy-poll loop into a single-poll `Ready` path and removes
//! cleanup-only drops that would otherwise reintroduce sound fallbacks.
//!
//! Part of #3955.

use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::BTreeSet;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn specialize_block_on_body_for_single_poll(
        &self,
        body: &rustc_public::mir::Body,
    ) -> Option<rustc_public::mir::Body> {
        let mut specialized = body.clone();
        let noop_waker_locals = self.collect_block_on_noop_waker_locals(body);
        let noop_coroutine_drop_locals = self.collect_block_on_noop_coroutine_drop_locals(body);
        let unreachable_bb = specialized
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                (block.statements.is_empty()
                    && matches!(block.terminator.kind, TerminatorKind::Unreachable))
                .then_some(bb_idx)
            })
            .unwrap_or_else(|| {
                let bb_idx = specialized.blocks.len();
                specialized.blocks.push(rustc_public::mir::BasicBlock {
                    statements: Vec::new(),
                    terminator: rustc_public::mir::Terminator {
                        kind: TerminatorKind::Unreachable,
                        span: body.blocks[0].terminator.span,
                    },
                });
                bb_idx
            });

        let mut rewrote_pending = false;
        for (call_bb, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { destination, target: Some(switch_bb), .. } =
                &block.terminator.kind
            else {
                continue;
            };

            let TerminatorKind::SwitchInt { discr, targets } =
                &body.blocks[*switch_bb].terminator.kind
            else {
                continue;
            };
            let discr_local = match discr {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    Some(place.local)
                }
                _ => None,
            };
            if !switch_uses_call_result_discriminant(
                &body.blocks[*switch_bb],
                discr_local,
                destination.local,
            ) {
                continue;
            }

            let rewritten_branches = targets
                .branches()
                .map(|(value, target_bb)| {
                    if is_loop_backedge_target(body, call_bb, target_bb) {
                        rewrote_pending = true;
                        (value, unreachable_bb)
                    } else {
                        (value, target_bb)
                    }
                })
                .collect();
            let rewritten_otherwise = if is_loop_backedge_target(body, call_bb, targets.otherwise())
            {
                rewrote_pending = true;
                unreachable_bb
            } else {
                targets.otherwise()
            };
            if !rewrote_pending {
                continue;
            }

            specialized.blocks[*switch_bb].terminator.kind = TerminatorKind::SwitchInt {
                discr: discr.clone(),
                targets: rustc_public::mir::SwitchTargets::new(
                    rewritten_branches,
                    rewritten_otherwise,
                ),
            };
        }

        if !rewrote_pending {
            return None;
        }

        for block in &mut specialized.blocks {
            let TerminatorKind::Drop { place, target, .. } = &block.terminator.kind else {
                continue;
            };
            if place.projection.is_empty()
                && (noop_waker_locals.contains(&place.local)
                    || noop_coroutine_drop_locals.contains(&place.local))
            {
                block.terminator.kind = TerminatorKind::Goto { target: *target };
            }
        }

        Some(specialized)
    }

    fn collect_block_on_noop_waker_locals(
        &self,
        body: &rustc_public::mir::Body,
    ) -> BTreeSet<usize> {
        body.blocks
            .iter()
            .filter_map(|block| {
                let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind else {
                    return None;
                };
                let callee_path = resolve_body_callee_path(self, body, func)?;
                callee_path.ends_with("::Waker::from_raw").then_some(destination.local)
            })
            .collect()
    }

    fn collect_block_on_noop_coroutine_drop_locals(
        &self,
        body: &rustc_public::mir::Body,
    ) -> BTreeSet<usize> {
        body.blocks
            .iter()
            .filter_map(|block| match &block.terminator.kind {
                TerminatorKind::Drop { place, .. } if place.projection.is_empty() => {
                    let local_ty =
                        place.ty(body.locals()).ok().map(|ty| self.resolve_body_ty(ty))?;
                    self.block_on_coroutine_drop_is_cleanup_only(local_ty).then_some(place.local)
                }
                _ => None,
            })
            .collect()
    }

    fn block_on_coroutine_drop_is_cleanup_only(&self, ty: rustc_public::ty::Ty) -> bool {
        let TyKind::RigidTy(RigidTy::Coroutine(..)) = ty.kind() else {
            return false;
        };

        let internal_ty = rustc_internal::internal(self.tcx, ty);
        let rustc_middle::ty::TyKind::Coroutine(_, args) = internal_ty.kind() else {
            return false;
        };

        args.as_coroutine().upvar_tys().iter().all(|upvar_ty| {
            crate::codegen_ay::chc::rules::codegen_rules::transition_drop::ty_trivially_no_drop(
                rustc_internal::stable(upvar_ty),
            )
        })
    }
}

fn is_loop_backedge_target(
    body: &rustc_public::mir::Body,
    call_bb: usize,
    target_bb: usize,
) -> bool {
    if target_bb <= call_bb {
        return true;
    }
    matches!(
        &body.blocks[target_bb].terminator.kind,
        TerminatorKind::Goto { target } if *target <= call_bb
    )
}

fn switch_uses_call_result_discriminant(
    block: &rustc_public::mir::BasicBlock,
    discr_local: Option<usize>,
    call_result_local: usize,
) -> bool {
    if discr_local == Some(call_result_local) {
        return true;
    }

    let Some(discr_local) = discr_local else {
        return false;
    };

    block.statements.iter().any(|stmt| {
        matches!(
            &stmt.kind,
            StatementKind::Assign(place, Rvalue::Discriminant(source))
                if place.projection.is_empty()
                    && place.local == discr_local
                    && source.projection.is_empty()
                    && source.local == call_result_local
        )
    })
}

fn resolve_body_callee_path(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    func: &Operand,
) -> Option<String> {
    let func_ty = func.ty(body.locals()).ok()?;
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };

    let instance_opt = Instance::resolve(fn_def, &fn_args).ok();
    let def_id =
        instance_opt.as_ref().map_or_else(|| fn_def.def_id(), |instance| instance.def.def_id());
    let internal_def_id = rustc_internal::internal(ctx.tcx, def_id);
    Some(ctx.tcx.def_path_str(internal_def_id))
}

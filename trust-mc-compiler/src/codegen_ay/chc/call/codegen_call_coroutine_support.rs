// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared coroutine-dispatch helpers for the CHC call dispatcher.
//!
//! Split out of `codegen_call_coroutine.rs` to keep the top-level dispatcher
//! file under the repo's 500-line limit.

use ay_bindings::Expr;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_alias_writeback::resolve_call_arg_target_local_fallback;
use super::sequence::resolve_simple_coroutine_yield_variant;
use super::{ChcCtx, DispatchCallContext};
use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::chc::rules::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::stmt::codegen_stmt_projection::{
    UnknownProjectionPolicy, collect_field_projections,
};
use crate::codegen_ay::types::{
    POINTER_WIDTH, coroutine_discriminant_select, coroutine_discriminant_update,
};
use crate::rustc_public_bridge::IndexedVal;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn coroutine_live_receiver_state_idx(
        &self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
    ) -> Option<usize> {
        dcx.args.iter().enumerate().find_map(|(arg_idx, arg): (usize, &Operand)| {
            let Ok(ty) = arg.ty(self.body.locals()) else {
                return None;
            };
            if !is_coroutine_or_ref_to_coroutine(ty) {
                return None;
            }

            let state_idx = self.resolve_coroutine_call_arg_state_idx(dcx, arg_idx + 1)?;
            self.state_var_mgr
                .live_state_indices
                .get(target)
                .is_some_and(|live| live.contains(&state_idx))
                .then_some(state_idx)
        })
    }

    pub(in crate::codegen_ay::chc) fn resolve_coroutine_call_arg_owner_local(
        &self,
        dcx: &DispatchCallContext<'_>,
        callee_arg_local: usize,
    ) -> Option<usize> {
        let state_idx = self.resolve_coroutine_call_arg_state_idx(dcx, callee_arg_local)?;
        self.coroutine_owner_local_for_state_idx(state_idx)
    }

    fn resolve_coroutine_call_arg_state_idx(
        &self,
        dcx: &DispatchCallContext<'_>,
        callee_arg_local: usize,
    ) -> Option<usize> {
        let arg_idx = callee_arg_local.checked_sub(1)?;
        let arg = dcx.args.get(arg_idx)?;
        let place = match arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };

        let mut visited = std::collections::HashSet::new();
        self.resolve_coroutine_source_state_idx(place.local, &mut visited).or_else(|| {
            let caller_local = resolve_call_arg_target_local_fallback(self, dcx, callee_arg_local)?;
            self.coroutine_receiver_state_idx(caller_local)
        })
    }

    fn resolve_coroutine_source_state_idx(
        &self,
        local_idx: usize,
        visited: &mut std::collections::HashSet<usize>,
    ) -> Option<usize> {
        if !visited.insert(local_idx) {
            return None;
        }

        if let Some(state_idx) = self.coroutine_receiver_state_idx(local_idx) {
            return Some(state_idx);
        }

        if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx)
            && (ref_target.projections.is_empty()
                || ref_target
                    .projections
                    .iter()
                    .all(|proj| matches!(proj, ProjectionElem::Deref | ProjectionElem::Field(..))))
            && let Some(resolved) =
                self.resolve_coroutine_source_state_idx(ref_target.local, visited)
        {
            return Some(resolved);
        }

        let source_local = self.find_coroutine_source_local(local_idx)?;
        self.resolve_coroutine_source_state_idx(source_local, visited)
    }

    fn find_coroutine_source_local(&self, dest_local: usize) -> Option<usize> {
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != dest_local || !place.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    | Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        return Some(src.local);
                    }
                    Rvalue::CopyForDeref(src) if src.projection.is_empty() => {
                        return Some(src.local);
                    }
                    Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src) => return Some(src.local),
                    _ => {}
                }
            }

            let TerminatorKind::Call { args, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            if destination.local != dest_local || !destination.projection.is_empty() {
                continue;
            }
            let Some(Operand::Copy(src) | Operand::Move(src)) = args.first() else {
                continue;
            };
            if src.projection.is_empty() {
                return Some(src.local);
            }
        }
        None
    }

    pub(in crate::codegen_ay::chc) fn coroutine_owner_local_for_state_idx(
        &self,
        state_idx: usize,
    ) -> Option<usize> {
        self.state_var_mgr.local_to_state_idx.iter().find_map(|(&local_idx, &local_state_idx)| {
            (local_state_idx == state_idx
                && matches!(
                    self.body.locals().get(local_idx)?.ty.kind(),
                    TyKind::RigidTy(RigidTy::Coroutine(..))
                ))
            .then_some(local_idx)
        })
    }

    fn coroutine_receiver_state_idx(&self, local_idx: usize) -> Option<usize> {
        if let Some((root_state_idx, _, _)) = self.resolve_coroutine_root_state_expr(local_idx) {
            return Some(root_state_idx);
        }

        if let Some((pointee_state_idx, _, pointee_expr)) =
            self.resolve_arg_ref_pointee_expr(local_idx)
            && coroutine_discriminant_select(pointee_expr).is_some()
        {
            return Some(pointee_state_idx);
        }

        let state_idx = self.try_state_idx_for_local(local_idx)?;
        let (_, sort) = self.state_var_mgr.state_vars.get(state_idx)?;
        crate::codegen_ay::types::is_coroutine_root_sort(sort).then_some(state_idx)
    }

    pub(in crate::codegen_ay::chc) fn try_build_simple_coroutine_receiver_writeback_eq(
        &self,
        dcx: &DispatchCallContext<'_>,
        receiver_state_idx: usize,
    ) -> Option<Expr> {
        let updated =
            self.try_build_simple_coroutine_receiver_writeback(dcx, receiver_state_idx)?;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(receiver_state_idx)?;
        let out_var = Expr::var(out_name.as_ref(), out_sort.clone());
        (out_var.sort() == updated.sort()).then(|| out_var.eq(updated))
    }

    fn try_build_simple_coroutine_receiver_writeback(
        &self,
        dcx: &DispatchCallContext<'_>,
        receiver_state_idx: usize,
    ) -> Option<Expr> {
        let receiver_root = self.resolve_coroutine_call_arg_root_expr(dcx, receiver_state_idx)?;
        let (coroutine_ty, variant_index) = resolve_simple_coroutine_yield_variant(dcx.func, self)?;
        let discr_select = coroutine_discriminant_select(receiver_root.clone())?;
        let discr_width = discr_select.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
        let internal_ty = rustc_internal::internal(self.tcx, coroutine_ty);
        let discr = internal_ty.discriminant_for_variant(
            self.tcx,
            InternalVariantIdx::from_usize(variant_index.to_index()),
        )?;
        let discr_expr = Expr::bitvec_const(
            sign_extend_discr_val(discr.val, discr.ty, self.tcx, discr_width),
            discr_width,
        );
        coroutine_discriminant_update(&receiver_root, discr_expr)
    }

    pub(super) fn resolve_coroutine_call_arg_root_expr(
        &self,
        dcx: &DispatchCallContext<'_>,
        receiver_state_idx: usize,
    ) -> Option<Expr> {
        dcx.args.iter().enumerate().find_map(|(arg_idx, arg)| {
            let Ok(ty) = arg.ty(self.body.locals()) else {
                return None;
            };
            if !is_coroutine_or_ref_to_coroutine(ty) {
                return None;
            }
            let callee_arg_local = arg_idx + 1;
            let state_idx = self.resolve_coroutine_call_arg_state_idx(dcx, callee_arg_local)?;
            if state_idx != receiver_state_idx {
                return None;
            }
            let place = match arg {
                Operand::Copy(place) | Operand::Move(place) => place,
                Operand::Constant(_) => return None,
            };
            self.resolve_coroutine_root_expr(place.local, dcx.modified_locals).or_else(|| {
                let caller_local =
                    resolve_call_arg_target_local_fallback(self, dcx, callee_arg_local)?;
                self.resolve_coroutine_root_expr(caller_local, dcx.modified_locals)
            })
        })
    }

    pub(in crate::codegen_ay::chc) fn handle_projected_destination(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        target: usize,
        yield_is_zst: bool,
        complete_is_zst: bool,
        allow_complete_branch: bool,
        live_receiver_state_idx: Option<usize>,
    ) -> bool {
        if self.try_emit_projected_yielded(
            dcx,
            dest_local,
            target,
            yield_is_zst,
            complete_is_zst,
            allow_complete_branch,
            live_receiver_state_idx,
        ) {
            return true;
        }
        if let Some(receiver_state_idx) = live_receiver_state_idx {
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                receiver_state_idx,
                projection = ?dcx.destination.projection,
                "CHC: projected coroutine body call needs receiver write-back → sound fallback"
            );
            return self.emit_coroutine_sound_fallback(
                dcx,
                dest_local,
                target,
                Some(receiver_state_idx),
            );
        }
        debug!(
            bb_idx = dcx.bb_idx,
            dest_local,
            projection = ?dcx.destination.projection,
            "CHC: projected coroutine body call → sound fallback"
        );
        self.emit_coroutine_sound_fallback(dcx, dest_local, target, None)
    }

    fn try_emit_projected_yielded(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        target: usize,
        yield_is_zst: bool,
        complete_is_zst: bool,
        allow_complete_branch: bool,
        live_receiver_state_idx: Option<usize>,
    ) -> bool {
        let projections = collect_field_projections(
            &dcx.destination.projection,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );
        if projections.is_empty() {
            return false;
        }

        let Some(root_in) = self.resolve_local_expr(dest_local, dcx.modified_locals) else {
            return false;
        };
        let Some((_, root_out)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let Some(leaf_expr) = Self::apply_field_selections(root_in.clone(), &projections) else {
            return false;
        };
        let leaf_sort = leaf_expr.sort().clone();

        let yielded_expr = super::try_construct_coroutine_state_expr(
            &leaf_sort,
            yield_is_zst,
            complete_is_zst,
            allow_complete_branch,
        )
        .or_else(|| {
            dcx.destination
                .ty(self.body.locals())
                .ok()
                .map(|ty| self.resolve_body_ty(ty))
                .and_then(Self::translate_ty)
                .and_then(|sort| {
                    super::try_construct_coroutine_state_expr(
                        &sort,
                        yield_is_zst,
                        complete_is_zst,
                        allow_complete_branch,
                    )
                })
        });
        let Some(yielded_expr) = yielded_expr else {
            return false;
        };
        let Some(projected_value) =
            super::coerce_coroutine_result_to_sort(yielded_expr, &leaf_sort)
        else {
            return false;
        };
        let Some(updated_root) =
            Self::apply_projection_update(&root_in, &projections, projected_value)
        else {
            return false;
        };
        let Some(eq) = self.make_coerced_eq_constraint(
            &root_out,
            updated_root,
            root_out.sort(),
            dest_local,
            "coroutine_body_state_projected",
        ) else {
            return false;
        };
        let receiver_eq = live_receiver_state_idx
            .and_then(|idx| self.try_build_simple_coroutine_receiver_writeback_eq(dcx, idx));
        if live_receiver_state_idx.is_some() && receiver_eq.is_none() {
            return false;
        }

        if let Some(receiver_state_idx) = live_receiver_state_idx {
            self.mark_state_var_modified(receiver_state_idx);
        }
        let output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &output_args,
            dcx.stmt_constraints,
            receiver_eq.into_iter().chain(std::iter::once(eq)),
        );
        debug!(
            bb_idx = dcx.bb_idx,
            dest_local,
            projection = ?dcx.destination.projection,
            "CHC: coroutine body call → yield-or-complete encoding (projected destination)"
        );
        true
    }
}

/// Check if any call argument has a Coroutine type (directly or behind
/// `Pin<&mut T>` / `&mut T` / `&T`).
pub(super) fn has_coroutine_arg(args: &[Operand], ctx: &ChcCtx<'_, '_>) -> bool {
    args.iter().any(|arg| {
        let Ok(ty) = arg.ty(ctx.body.locals()) else {
            return false;
        };
        is_coroutine_or_ref_to_coroutine(ty)
    })
}

/// Check if the callee's return type is `CoroutineState<Y, R>`.
pub(super) fn returns_coroutine_state(func: &Operand, ctx: &ChcCtx<'_, '_>) -> bool {
    let Ok(func_ty) = func.ty(ctx.body.locals()) else {
        return false;
    };
    let Some(sig) = func_ty.kind().fn_sig() else {
        return false;
    };
    let ret_ty = sig.skip_binder().output();
    match ret_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            let name = def.trimmed_name();
            name == "CoroutineState" || name == "GeneratorState"
        }
        _ => false,
    }
}

pub(super) fn has_simple_coroutine_yield_variant(func: &Operand, ctx: &ChcCtx<'_, '_>) -> bool {
    resolve_simple_coroutine_yield_variant(func, ctx).is_some()
}

/// Returns true if `ty` is a Coroutine or a reference/Pin wrapping a Coroutine.
pub(super) fn is_coroutine_or_ref_to_coroutine(ty: rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Coroutine(..)) => true,
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
            matches!(inner.kind(), TyKind::RigidTy(RigidTy::Coroutine(..)))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            if def.trimmed_name() == "Pin"
                && let Some(rustc_public::ty::GenericArgKind::Type(ptr_ty)) = args.0.first()
            {
                return is_coroutine_or_ref_to_coroutine(*ptr_ty);
            }
            false
        }
        _ => false,
    }
}

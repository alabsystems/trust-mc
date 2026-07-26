// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Multi-resume coroutine sequencing helpers for CHC call dispatch.

use ay_bindings::Expr;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{AggregateKind, Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind, VariantIdx};

use super::super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::{ChcCtx, DispatchCallContext};
use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::{
    POINTER_WIDTH, bool_sort, coroutine_discriminant_select, coroutine_discriminant_update,
};
use crate::rustc_public_bridge::IndexedVal;

#[derive(Clone)]
pub(super) struct SequencedCoroutineTransition {
    pub receiver_eq: Expr,
    pub yielded_now: Expr,
    pub known_state: Expr,
}

struct CoroutineResumeSequence {
    yield_variants: Vec<VariantIdx>,
    complete_variant: VariantIdx,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn try_build_sequenced_coroutine_transition(
        &self,
        dcx: &DispatchCallContext<'_>,
        receiver_state_idx: usize,
    ) -> Option<SequencedCoroutineTransition> {
        let coroutine_ty = resolve_coroutine_ty_from_call_args(dcx.args, self)?;
        let body = resolve_coroutine_body(dcx.func, self)?;
        let sequence = analyze_coroutine_resume_sequence(&body, coroutine_ty)?;

        let receiver_root = self.resolve_coroutine_call_arg_root_expr(dcx, receiver_state_idx)?;
        let current_discr = coroutine_discriminant_select(receiver_root.clone())?;
        let discr_sort = current_discr.sort().clone();
        if !discr_sort.is_bitvec() {
            return None;
        }

        let initial_variant = rustc_internal::stable(InternalVariantIdx::from_u32(0));
        let mut known_cases = vec![(
            current_discr.clone().eq(coroutine_discriminant_expr(
                coroutine_ty,
                initial_variant,
                &discr_sort,
                self,
            )?),
            coroutine_discriminant_expr(
                coroutine_ty,
                *sequence.yield_variants.first()?,
                &discr_sort,
                self,
            )?,
        )];
        for (current_variant, next_variant) in sequence.yield_variants.iter().copied().zip(
            sequence
                .yield_variants
                .iter()
                .copied()
                .skip(1)
                .chain(std::iter::once(sequence.complete_variant)),
        ) {
            known_cases.push((
                current_discr.clone().eq(coroutine_discriminant_expr(
                    coroutine_ty,
                    current_variant,
                    &discr_sort,
                    self,
                )?),
                coroutine_discriminant_expr(coroutine_ty, next_variant, &discr_sort, self)?,
            ));
        }

        let known_state = known_cases
            .iter()
            .map(|(guard, _)| guard.clone())
            .reduce(|lhs, rhs| lhs.or(rhs))
            .unwrap_or_else(|| Expr::bool_const(false));
        let last_yield_guard = current_discr.eq(coroutine_discriminant_expr(
            coroutine_ty,
            *sequence.yield_variants.last()?,
            &discr_sort,
            self,
        )?);
        let yielded_now = Expr::ite(
            known_state.clone(),
            last_yield_guard.not(),
            declare_pending_var(chc_fresh_name("__coro_yield_choice"), bool_sort()),
        );
        let next_discr = ite_cases(
            known_cases,
            declare_pending_var(chc_fresh_name("__coro_next_discr"), discr_sort),
        );
        let updated = coroutine_discriminant_update(&receiver_root, next_discr)?;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(receiver_state_idx)?;
        let out_var = Expr::var(out_name.as_ref(), out_sort.clone());
        if out_var.sort() != updated.sort() {
            return None;
        }

        Some(SequencedCoroutineTransition {
            receiver_eq: out_var.eq(updated),
            yielded_now,
            known_state,
        })
    }
}

pub(super) fn resolve_simple_coroutine_yield_variant(
    func: &Operand,
    ctx: &ChcCtx<'_, '_>,
) -> Option<(Ty, VariantIdx)> {
    let body = resolve_coroutine_body(func, ctx)?;
    // Scan per-block: find blocks that contain BOTH a CoroutineState::Yielded aggregate
    // AND a SetDiscriminant on the coroutine type. Reject coroutines that also have
    // Complete returns (non-Yielded CoroutineState aggregates), since the precise
    // Yielded encoding would be unsound for the completion path.
    let mut yield_variant: Option<(Ty, VariantIdx)> = None;
    let mut saw_non_yielded_return = false;

    for bb in &body.blocks {
        let mut bb_set_discr: Option<(Ty, VariantIdx)> = None;
        let mut bb_has_yielded = false;

        for stmt in &bb.statements {
            match &stmt.kind {
                StatementKind::SetDiscriminant { place, variant_index } => {
                    let Ok(ty) = place.ty(body.locals()) else {
                        continue;
                    };
                    if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
                        bb_set_discr = Some((ty, *variant_index));
                    }
                }
                StatementKind::Assign(
                    place,
                    Rvalue::Aggregate(AggregateKind::Adt(def, variant, _, _, _), _),
                ) if place.local == 0 && place.projection.is_empty() => {
                    let name = def.trimmed_name();
                    if name == "CoroutineState" || name == "GeneratorState" {
                        if variant.to_index() == 0 {
                            bb_has_yielded = true;
                        } else {
                            saw_non_yielded_return = true;
                        }
                    }
                }
                _ => {}
            }
        }

        if bb_has_yielded {
            if let Some(discr) = bb_set_discr {
                if let Some((_, existing)) = yield_variant {
                    if existing != discr.1 {
                        return None;
                    }
                } else {
                    yield_variant = Some(discr);
                }
            }
        }
    }

    if saw_non_yielded_return {
        return None;
    }

    yield_variant
}

fn count_yield_points(body: &Body) -> usize {
    body.blocks
        .iter()
        .filter(|bb| {
            bb.statements.iter().any(|stmt| match &stmt.kind {
                StatementKind::Assign(
                    place,
                    Rvalue::Aggregate(AggregateKind::Adt(def, variant, _, _, _), _),
                ) => {
                    let name = def.trimmed_name();
                    place.local == 0
                        && place.projection.is_empty()
                        && (name == "CoroutineState" || name == "GeneratorState")
                        && variant.to_index() == 0
                }
                _ => false,
            })
        })
        .count()
}

fn has_conditional_yields(body: &Body) -> bool {
    if count_yield_points(body) == 0 {
        return false;
    }
    // Collect all locals assigned from Discriminant(_) — these feed
    // state-machine dispatch SwitchInt, not user conditionals.
    // The coroutine body receives self as Pin<&mut Self> so the
    // discriminant source is typically `Discriminant(*_N)`, not `_0`.
    let discr_locals: std::collections::HashSet<usize> = body
        .blocks
        .iter()
        .flat_map(|bb| {
            bb.statements.iter().filter_map(|stmt| {
                if let StatementKind::Assign(place, Rvalue::Discriminant(_)) = &stmt.kind {
                    return Some(place.local);
                }
                None
            })
        })
        .collect();
    body.blocks.iter().any(|bb| {
        let TerminatorKind::SwitchInt { discr, .. } = &bb.terminator.kind else {
            return false;
        };
        let switch_local = match discr {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return true,
        };
        !discr_locals.contains(&switch_local)
    })
}

fn analyze_coroutine_resume_sequence(
    body: &Body,
    coroutine_ty: Ty,
) -> Option<CoroutineResumeSequence> {
    if has_conditional_yields(body) {
        return None;
    }

    let mut yield_variants = Vec::new();
    let mut complete_variant = None;
    for bb in &body.blocks {
        let mut bb_set_discr = None;
        let mut bb_outcome = None;
        for stmt in &bb.statements {
            match &stmt.kind {
                StatementKind::SetDiscriminant { place, variant_index } => {
                    let Ok(ty) = place.ty(body.locals()) else {
                        continue;
                    };
                    if ty == coroutine_ty {
                        bb_set_discr = Some(*variant_index);
                    }
                }
                StatementKind::Assign(
                    place,
                    Rvalue::Aggregate(AggregateKind::Adt(def, variant, _, _, _), _),
                ) if place.local == 0 && place.projection.is_empty() => {
                    let name = def.trimmed_name();
                    if name == "CoroutineState" || name == "GeneratorState" {
                        bb_outcome = Some(*variant);
                    }
                }
                _ => {}
            }
        }

        let Some(set_discr) = bb_set_discr else {
            continue;
        };
        match bb_outcome.map(|variant| variant.to_index()) {
            Some(0) => {
                if !yield_variants.contains(&set_discr) {
                    yield_variants.push(set_discr);
                }
            }
            Some(_) => {
                complete_variant = Some(set_discr);
            }
            None => {}
        }
    }

    (count_yield_points(body) == yield_variants.len() && !yield_variants.is_empty())
        .then_some(CoroutineResumeSequence { yield_variants, complete_variant: complete_variant? })
}

fn resolve_coroutine_body(func: &Operand, ctx: &ChcCtx<'_, '_>) -> Option<Body> {
    let Ok(func_ty) = func.ty(ctx.body.locals()) else {
        return None;
    };
    let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
        return None;
    };
    substs
        .0
        .first()
        .and_then(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
        .and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::Coroutine(coroutine_def, _)) => coroutine_def.body(),
            _ => None,
        })
        .or_else(|| {
            let instance = Instance::resolve(def, &substs).ok()?;
            instance.body()
        })
}

fn resolve_coroutine_ty_from_call_args(args: &[Operand], ctx: &ChcCtx<'_, '_>) -> Option<Ty> {
    args.iter().find_map(|arg| {
        let Ok(ty) = arg.ty(ctx.body.locals()) else {
            return None;
        };
        extract_coroutine_ty(ty)
    })
}

fn extract_coroutine_ty(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Coroutine(..)) => Some(ty),
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => extract_coroutine_ty(inner),
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Pin" => {
            args.0.first().and_then(|arg| match arg {
                GenericArgKind::Type(inner) => extract_coroutine_ty(*inner),
                _ => None,
            })
        }
        _ => None,
    }
}

fn coroutine_discriminant_expr(
    coroutine_ty: Ty,
    variant_index: VariantIdx,
    discr_sort: &ay_bindings::Sort,
    ctx: &ChcCtx<'_, '_>,
) -> Option<Expr> {
    let discr_width = discr_sort.bitvec_width().unwrap_or(POINTER_WIDTH);
    let internal_ty = rustc_internal::internal(ctx.tcx, coroutine_ty);
    let discr = internal_ty.discriminant_for_variant(
        ctx.tcx,
        InternalVariantIdx::from_usize(variant_index.to_index()),
    )?;
    Some(Expr::bitvec_const(
        sign_extend_discr_val(discr.val, discr.ty, ctx.tcx, discr_width),
        discr_width,
    ))
}

fn ite_cases(cases: Vec<(Expr, Expr)>, default: Expr) -> Expr {
    cases.into_iter().rev().fold(default, |acc, (guard, value)| Expr::ite(guard, value, acc))
}

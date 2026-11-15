// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::callee_body::CalleeBody;
use crate::codegen_ay::shared::mono_ty;
use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::chc::ChcCtx;

use super::super::TransitionContext;
use super::dyn_dispatch_multi::{dispatch_d2_multi_impl, resolve_d2_vtable_discriminant};

/// Try to dispatch a `Drop` terminator for a `dyn Trait` type through
/// vtable-aware concrete candidate resolution. Part of #3793.
///
/// Returns `true` if dispatch succeeded (transition rule(s) emitted), `false`
/// to fall through to the `DynDropUnsupported` sound-fallback path.
///
/// Two lanes:
/// 1. **Unique candidate:** exactly one concrete drop body → inline directly.
/// 2. **Multi-impl:** multiple concrete drop bodies → emit one guarded
///    transition rule per candidate, keyed by vtable discriminant.
///
/// `self_expr_override`: if `Some`, use this as the `&mut self` address instead
/// of resolving from `place`. Used by the Box<dyn T> path where the inner
/// value's heap address is already extracted from the fat pointer.
///
/// `dealloc_extras`: additional constraints (e.g., Box deallocation) to append
/// to every emitted rule. Empty for non-Box dyn drops.
pub(super) fn try_dyn_drop_dispatch(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    drop_ty: rustc_public::ty::Ty,
    target: usize,
    tctx: &TransitionContext<'_>,
    self_expr_override: Option<Expr>,
    dealloc_extras: &[Expr],
) -> bool {
    // Step 1: Extract the principal trait DefId from the dyn type.
    // For Box<dyn T>, extract_dyn_trait_def_id resolves through the unsized tail.
    let Some(trait_def_id) =
        super::super::super::dyn_coercion::extract_dyn_trait_def_id(ctx, drop_ty)
    else {
        return false;
    };

    // Part of #4231: When the dyn trait is non-assertion-relevant (e.g.,
    // `core::error::Error`), skip vtable dispatch entirely. Return false to
    // let the caller fall through to its dealloc-only or skip path. Without
    // this, `try_extract_vtable_discriminant_for_trait` creates an
    // unconstrained BV64 (`virtual_missing_vtable`) that causes solver
    // timeouts (PROOF → UNKNOWN regression for pathbuf.rs).
    let trait_path = ctx.tcx.def_path_str(trait_def_id);
    if ChcCtx::is_formatting_path(&trait_path) {
        debug!(
            bb_idx = tctx.bb_idx,
            %trait_path,
            "dyn drop dispatch: non-assertion-relevant trait, skip (#4231)"
        );
        return false;
    }

    // Step 2: Collect concrete candidates for this trait.
    let candidates =
        super::super::super::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    if candidates.is_empty() {
        return false;
    }

    let mut drop_bodies = Vec::new();
    for candidate in &candidates {
        let glue = mono_ty::drop_in_place(candidate.concrete_ty);
        let body = match glue {
            Some(instance) if instance.is_empty_shim() => DynDropBody::Empty,
            Some(instance) => instance
                .callee_body()
                .map(|body| DynDropBody::Body(body, instance))
                .unwrap_or(DynDropBody::Unsupported),
            None => DynDropBody::Unsupported,
        };
        drop_bodies.push(DynDropCandidate { vtable: candidate.vtable_id, body });
    }

    // Step 4: Resolve the address of the dropped place.
    let self_expr = if let Some(expr) = self_expr_override {
        expr
    } else {
        // `self_expr_override` is an inline-body parameter term of unreported
        // provenance, so the merged slot stays a bare `Expr`; the address lane
        // drops its wave-11 tag here instead of tagging the override lane.
        match ctx.translate_ref_to_address(place, tctx.modified_locals) {
            Some(addr) => addr.into_expr(),
            None => return false,
        }
    };

    // Even a single nonempty body is not a unique runtime type: empty
    // shims and unavailable bodies remain real, guarded dispatch arms.
    let vtable_disc = resolve_d2_vtable_discriminant(ctx, place, tctx);
    dispatch_d2_multi_impl(
        ctx,
        place,
        &self_expr,
        &vtable_disc,
        &drop_bodies,
        target,
        tctx,
        dealloc_extras,
    )
}

pub(super) enum DynDropBody {
    Empty,
    Body(rustc_public::mir::Body, rustc_public::mir::mono::Instance),
    Unsupported,
}
pub(super) struct DynDropCandidate {
    pub vtable: u64,
    pub body: DynDropBody,
}

pub(super) fn dyn_projection_locals(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> Vec<usize> {
    use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};

    let mut locals = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            let Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) = rhs else {
                continue;
            };
            if !lhs.projection.is_empty()
                || src.projection.is_empty()
                || !matches!(src.projection.first(), Some(ProjectionElem::Deref))
            {
                continue;
            }
            if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(
                ctx,
                ctx.resolve_body_ty(*target_ty),
            )
            .is_some()
            {
                locals.push(lhs.local);
            }
        }
    }
    locals.sort_unstable();
    locals.dedup();
    locals
}

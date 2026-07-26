// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared dyn-callable body resolution for closure dispatch.
//!
//! Part of #3638: keep boxed dyn `Fn*` calls on the closure dispatch lane.

use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};

use super::super::ChcCtx;
use super::super::dyn_coercion;

/// Resolve a single concrete body for a callable `dyn Fn*` shim in the current body.
///
/// This reuses the shared dyn-coercion candidate discovery pipeline instead of
/// the closure lane's older one-off MIR scan. Body resolution stays specialized
/// here so closure candidates resolve to the raw closure body rather than a
/// blanket-impl adapter shim. It stays conservative: any 0-body or multi-body
/// result returns `None` so the caller can keep its fallback behavior.
pub(in crate::codegen_ay::chc) fn resolve_unique_dyn_callable_body(
    ctx: &ChcCtx<'_, '_>,
    fn_def: rustc_public::ty::FnDef,
    fn_args: &rustc_public::ty::GenericArgs,
) -> Option<rustc_public::mir::Body> {
    let method_def_id = rustc_internal::internal(ctx.tcx, fn_def.def_id());
    let parent_trait_def_id = ctx.tcx.parent(method_def_id);
    if !ctx.tcx.is_trait(parent_trait_def_id) {
        return None;
    }

    let has_dyn_callable_arg = fn_args.0.iter().any(|arg| {
        let Some(arg_ty) = arg.ty() else {
            return false;
        };

        dyn_coercion::find_dyn_trait_tail_ty(ctx, *arg_ty).is_some()
    });
    if !has_dyn_callable_arg {
        return None;
    }

    let expected_param_tys = extract_expected_callable_param_tys(fn_args);
    let preferred_kinds = preferred_closure_kinds(ctx, parent_trait_def_id);
    let candidates = dyn_coercion::collect_dyn_trait_candidates(ctx, parent_trait_def_id);
    let mut resolved_bodies = candidates.iter().filter_map(|candidate| {
        let body = resolve_dyn_callable_candidate_body(candidate.concrete_ty, &preferred_kinds)?;
        if expected_param_tys
            .as_ref()
            .is_some_and(|expected| !callable_body_matches_expected_params(&body, expected))
        {
            return None;
        }
        Some(body)
    });
    let body = resolved_bodies.next()?;
    if resolved_bodies.next().is_some() {
        return None;
    }
    Some(body)
}

fn preferred_closure_kinds(
    ctx: &ChcCtx<'_, '_>,
    parent_trait_def_id: rustc_span::def_id::DefId,
) -> [ClosureKind; 3] {
    let trait_path = ctx.tcx.def_path_str(parent_trait_def_id);
    if trait_path.ends_with("::Fn") {
        [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce]
    } else if trait_path.ends_with("::FnMut") {
        [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce]
    } else {
        [ClosureKind::FnOnce, ClosureKind::FnMut, ClosureKind::Fn]
    }
}

fn extract_expected_callable_param_tys(
    fn_args: &rustc_public::ty::GenericArgs,
) -> Option<Vec<rustc_public::ty::Ty>> {
    fn_args.0.iter().rev().find_map(|arg| {
        let ty = arg.ty()?;
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = ty.kind() else {
            return None;
        };
        Some(fields)
    })
}

fn callable_body_matches_expected_params(
    body: &rustc_public::mir::Body,
    expected_param_tys: &[rustc_public::ty::Ty],
) -> bool {
    let arg_locals = body.arg_locals();
    if arg_locals.len() != expected_param_tys.len() + 1 {
        return false;
    }

    arg_locals
        .iter()
        .skip(1)
        .zip(expected_param_tys.iter())
        .all(|(local_decl, expected_ty)| local_decl.ty == *expected_ty)
}

fn resolve_dyn_callable_candidate_body(
    concrete_ty: rustc_public::ty::Ty,
    preferred_kinds: &[ClosureKind; 3],
) -> Option<rustc_public::mir::Body> {
    let mut inner = concrete_ty;
    for _ in 0..3 {
        let peeled = dyn_coercion::peel_pointer_like_wrapper_ty(inner);
        if peeled == inner {
            break;
        }
        inner = peeled;
    }

    match inner.kind() {
        TyKind::RigidTy(RigidTy::Closure(def, args)) => {
            for kind in preferred_kinds {
                if let Ok(instance) = Instance::resolve_closure(def, &args, kind.clone())
                    && let Some(body) = instance.body()
                {
                    return Some(body);
                }
            }
            None
        }
        TyKind::RigidTy(RigidTy::FnDef(def, fn_item_args)) => {
            let instance = Instance::resolve(def, &fn_item_args).ok()?;
            instance.body()
        }
        _ => None,
    }
}

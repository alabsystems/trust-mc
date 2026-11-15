// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared dyn-callable body resolution for closure dispatch.
//!
//! Part of #3638: keep boxed dyn `Fn*` calls on the closure dispatch lane.

use crate::callee_body::CalleeBody;
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
///
/// The caller walks the body UNCONDITIONALLY, so uniqueness must be exact
/// (design 3, `dyn_dispatch_scope.rs`):
///
/// * the candidates come from the receiver's principal trait, whose list the
///   stored vtable ids index: for `Box<dyn MyFn>` with `trait MyFn: Fn(..)`,
///   the `Fn` list named an unrelated closure coerced to `dyn Fn`
///   (`walker_dispatch_candidates_dual.rs::bug_subtrait_*`);
/// * a function item behind `&dyn Fn` is a candidate too. The closure-shape
///   test (`callable_body_matches_expected_params`) dropped it, so a closure
///   and a fn item behind one `&dyn Fn` left the closure "unique"
///   (`bug_ref_closure_then_fnitem`, `bug_closure_then_fnitem_value`);
/// * a candidate whose body cannot be resolved could be the one called;
/// * the harness's dyn-coercion universe must say the survivor is the
///   receiver's only runtime type, since a callable coerced in a callee is
///   not in the list.
pub(in crate::codegen_ay::chc) fn resolve_unique_dyn_callable_body(
    ctx: &ChcCtx<'_, '_>,
    fn_def: rustc_public::ty::FnDef,
    fn_args: &rustc_public::ty::GenericArgs,
) -> Option<rustc_public::mir::Body> {
    let method_def_id = rustc_internal::internal(ctx.tcx, fn_def.def_id());
    let method_trait_def_id = ctx.tcx.parent(method_def_id);
    if !ctx.tcx.is_trait(method_trait_def_id) {
        return None;
    }
    let dispatch_trait = super::super::dyn_dispatch_scope::dispatch_trait_for_call(
        ctx,
        method_trait_def_id,
        fn_args,
    )?;
    let parent_trait_def_id = dispatch_trait.def_id;

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
    let preferred_kinds = preferred_closure_kinds(ctx, method_trait_def_id);
    let candidates = dyn_coercion::collect_dyn_trait_candidates(ctx, parent_trait_def_id);
    let scope =
        super::super::dyn_dispatch_scope::DynDispatchScope::new(ctx, &dispatch_trait, &candidates);
    let mut unique: Option<(u64, rustc_public::mir::Body)> = None;
    for candidate in &candidates {
        let Some(body) = resolve_dyn_callable_candidate_body(candidate.concrete_ty, &preferred_kinds)
        else {
            // A candidate whose body cannot be resolved could be the one
            // called, unless the universe says it is never the runtime type
            // (a std type implementing `Fn` for its own use).
            if scope.may_be_runtime(candidate.vtable_id) {
                return None;
            }
            continue;
        };
        let fits = expected_param_tys.as_ref().is_none_or(|expected| {
            callable_body_matches_expected_params(&body, expected)
                || fn_item_body_matches_expected_params(&body, expected)
        });
        if !fits {
            continue;
        }
        if unique.is_some() {
            return None;
        }
        unique = Some((candidate.vtable_id, body));
    }
    let (vtable_id, body) = unique?;
    scope.is_sole_runtime(vtable_id).then_some(body)
}

/// A function item's body (no closure environment) whose parameters are the
/// callable's: a `&fn_item` behind `&dyn Fn(..)`.
fn fn_item_body_matches_expected_params(
    body: &rustc_public::mir::Body,
    expected_param_tys: &[rustc_public::ty::Ty],
) -> bool {
    let arg_locals = body.arg_locals();
    arg_locals.len() == expected_param_tys.len()
        && arg_locals
            .iter()
            .zip(expected_param_tys.iter())
            .all(|(local_decl, expected_ty)| local_decl.ty == *expected_ty)
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
                    && let Some(body) = instance.callee_body()
                {
                    return Some(body);
                }
            }
            None
        }
        TyKind::RigidTy(RigidTy::FnDef(def, fn_item_args)) => {
            let instance = Instance::resolve(def, &fn_item_args).ok()?;
            instance.callee_body()
        }
        _ => None,
    }
}

/// Can a closure or function-item candidate of type `concrete_ty` be called
/// with the argument tuple `args_tuple`? `None` when the candidate is neither,
/// or its body does not resolve.
///
/// Asked before `Instance::resolve(Fn*::call, [candidate, args])`, which
/// raises an internal compiler error on a signature mismatch: its
/// `catch_unwind` in `resolve_dispatch_bodies` stops the unwind, but the
/// error is already emitted and the compilation aborts
/// (`kani/DynTrait/nested_closures.rs`, where closures of three signatures
/// are candidates for one `dyn Fn` call). The comparison is the closure
/// lane's own (`callable_body_matches_expected_params`), on the body's
/// argument locals.
pub(in crate::codegen_ay::chc) fn fn_family_candidate_fits(
    concrete_ty: rustc_public::ty::Ty,
    args_tuple: rustc_public::ty::Ty,
) -> Option<bool> {
    let TyKind::RigidTy(RigidTy::Tuple(expected)) = args_tuple.kind() else { return None };
    if !matches!(
        concrete_ty.kind(),
        TyKind::RigidTy(RigidTy::Closure(..) | RigidTy::FnDef(..))
    ) {
        return None;
    }
    let body = resolve_dyn_callable_candidate_body(
        concrete_ty,
        &[ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce],
    )?;
    Some(
        callable_body_matches_expected_params(&body, &expected)
            || fn_item_body_matches_expected_params(&body, &expected),
    )
}
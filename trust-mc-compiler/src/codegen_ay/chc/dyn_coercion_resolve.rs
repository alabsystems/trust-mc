// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dyn-trait type resolution and substitution helpers.
//!
//! Functions that resolve concrete tail types from MIR unsizing casts
//! and replace `dyn Trait` with concrete types for layout queries.
//!
//! Extracted from `dyn_coercion.rs` — Part of #4206.

use std::collections::HashSet;

use rustc_middle::ty::TypeVisitableExt;
use rustc_public::CrateDef;
use rustc_public::mir::{CastKind, Rvalue};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use super::codegen_ctx::ChcCtx;
use super::dyn_coercion::{
    extract_concrete_tail_for_dyn, find_dyn_trait_tail_ty, peel_pointer_like_wrapper_ty,
};

/// Extract the principal trait DefId from a type that might be `dyn Trait` or
/// an ADT with a dyn Trait unsized tail.
pub(super) fn extract_dyn_trait_def_id(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_span::def_id::DefId> {
    use rustc_public::ty::ExistentialPredicate;

    let dyn_tail = find_dyn_trait_tail_ty(ctx, ty)?;
    let TyKind::RigidTy(RigidTy::Dynamic(ref preds, _)) = dyn_tail.kind() else {
        return None;
    };

    let principal = preds.first()?;
    match &principal.value {
        ExistentialPredicate::Trait(tref) => {
            Some(rustc_internal::internal(ctx.tcx, tref.def_id.def_id()))
        }
        // Part of #4097 D2: Handle auto-trait-only dyn types like `dyn Send`.
        // When no principal trait exists, the first predicate is an AutoTrait.
        // Return its DefId so collect_dyn_trait_candidates Phase 2 (MIR coercion
        // scan) can find concrete types assigned via Unsize casts.
        ExistentialPredicate::AutoTrait(trait_def) => {
            use rustc_public::CrateDef;
            Some(rustc_internal::internal(ctx.tcx, trait_def.def_id()))
        }
        _ => None,
    }
}

/// Resolve the unique concrete tail type used to unsize into `target_ty`
/// within the current MIR body.
///
/// Scans `PointerCoercion::Unsize` statements and returns the concrete tail
/// type when all matching coercion sites agree. This lets downstream layout
/// helpers recover `Outer<Inner>` from `Outer<dyn Trait>` even when the dyn-tail
/// target itself has no rustc layout.
pub(super) fn resolve_unique_concrete_dyn_tail_ty(
    ctx: &ChcCtx<'_, '_>,
    target_ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    let mut matches: HashSet<rustc_public::ty::Ty> = HashSet::new();
    let target_is_dyn = matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)));

    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            let rustc_public::mir::StatementKind::Assign(
                _,
                Rvalue::Cast(
                    CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
                    operand,
                    cast_target_ty,
                ),
            ) = &stmt.kind
            else {
                continue;
            };

            let cast_target_inner = if *cast_target_ty == target_ty {
                *cast_target_ty
            } else {
                peel_pointer_like_wrapper_ty(*cast_target_ty)
            };
            let matches_target = cast_target_inner == target_ty
                || (target_is_dyn && type_contains_dyn_tail(cast_target_inner, target_ty));
            if !matches_target {
                continue;
            }

            let Ok(src_ty) = operand.ty(ctx.body.locals()) else {
                continue;
            };
            let src_inner = peel_pointer_like_wrapper_ty(src_ty);
            let concrete_tail = extract_concrete_tail_for_dyn(src_inner, cast_target_inner);
            matches.insert(concrete_tail);
        }
    }

    if matches.len() == 1 {
        return matches.into_iter().next();
    }

    // Part of #4014: Fallback to trait implementation registry when the MIR
    // body scan finds no Unsize casts. This happens when the unsizing occurs
    // in a callee body (e.g., `new_furniture` calls `Rc::new(Table::new(..))`)
    // but the harness body only sees the `Rc<dyn Furniture>` return type.
    // If there is exactly one non-blanket, non-parametric implementor of the
    // trait, use that as the concrete tail type.
    let dyn_tail_ty = find_dyn_trait_tail_ty(ctx, target_ty)?;
    let trait_def_id = extract_dyn_trait_def_id(ctx, dyn_tail_ty)?;
    let trait_impls = ctx.tcx.trait_impls_of(trait_def_id);
    let mut impl_types: Vec<rustc_public::ty::Ty> = Vec::new();
    for impl_def_id in trait_impls.non_blanket_impls().values().flatten() {
        let impl_self_ty = ctx.tcx.type_of(*impl_def_id).skip_binder();
        if impl_self_ty.has_param() {
            continue;
        }
        impl_types.push(rustc_internal::stable(impl_self_ty));
    }
    if impl_types.len() == 1 {
        debug!(
            ?target_ty,
            concrete = ?impl_types[0],
            "resolve_unique_concrete_dyn_tail: trait-impl fallback (#4014)"
        );
        return Some(impl_types[0]);
    }
    None
}

pub(super) fn type_contains_dyn_tail(
    ty: rustc_public::ty::Ty,
    target_dyn_ty: rustc_public::ty::Ty,
) -> bool {
    if ty == target_dyn_ty {
        return true;
    }

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            type_contains_dyn_tail(inner, target_dyn_ty)
        }
        TyKind::RigidTy(RigidTy::Adt(_, args)) => args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(inner) => type_contains_dyn_tail(*inner, target_dyn_ty),
            _ => false,
        }),
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|field| type_contains_dyn_tail(*field, target_dyn_ty))
        }
        _ => false,
    }
}

/// Replace the first dyn-trait tail inside `ty` with a concrete type.
///
/// This is the type-level analogue of `extract_concrete_tail_for_dyn`: it turns
/// `dyn Trait` into `Inner`, or `Outer<dyn Trait>` into `Outer<Inner>`, so rustc
/// layout queries can succeed on the concrete surrogate type.
pub(super) fn replace_dyn_tail_with_concrete(
    ty: rustc_public::ty::Ty,
    concrete_ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Dynamic(..)) => Some(concrete_ty),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let mut replaced = false;
            let new_args = args
                .0
                .iter()
                .map(|arg| match arg {
                    GenericArgKind::Type(inner)
                        if !replaced
                            && matches!(inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) =>
                    {
                        replaced = true;
                        GenericArgKind::Type(concrete_ty)
                    }
                    GenericArgKind::Type(inner) if !replaced => {
                        if let Some(replaced_inner) =
                            replace_dyn_tail_with_concrete(*inner, concrete_ty)
                        {
                            replaced = true;
                            GenericArgKind::Type(replaced_inner)
                        } else {
                            arg.clone()
                        }
                    }
                    _ => arg.clone(),
                })
                .collect();
            replaced.then_some(rustc_public::ty::Ty::from_rigid_kind(RigidTy::Adt(
                def,
                rustc_public::ty::GenericArgs(new_args),
            )))
        }
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            let mut replaced = false;
            let new_fields = fields
                .iter()
                .map(|field| {
                    if !replaced && matches!(field.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                        replaced = true;
                        concrete_ty
                    } else if !replaced
                        && let Some(replaced_field) =
                            replace_dyn_tail_with_concrete(*field, concrete_ty)
                    {
                        replaced = true;
                        replaced_field
                    } else {
                        *field
                    }
                })
                .collect();
            replaced.then_some(rustc_public::ty::Ty::from_rigid_kind(RigidTy::Tuple(new_fields)))
        }
        _ => None,
    }
}

/// Normalize a type's dyn-trait tail to its unique concrete implementation.
///
/// When the current MIR body has a single concrete type that unsizes into
/// the dyn tail, this replaces the dyn tail so all consumers (heap access,
/// layout queries, dispatch, allocation) use a consistent concrete type.
///
/// Part of #3975: single source of truth for dyn-tail normalization.
pub(super) fn normalize_unique_dyn_tail_ty(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> rustc_public::ty::Ty {
    let ty = ctx.resolve_body_ty(ty);
    // Bare `dyn Trait` resolves directly to the concrete type.
    if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return resolve_unique_concrete_dyn_tail_ty(ctx, ty).unwrap_or(ty);
    }
    // For wrapper types with dyn-trait generic args (e.g., Wrapper<dyn Trait>),
    // resolve the concrete tail and substitute it into the wrapper structure.
    if let Some(concrete_tail) = resolve_unique_concrete_dyn_tail_ty(ctx, ty) {
        if let Some(normalized) = replace_dyn_tail_with_concrete(ty, concrete_tail) {
            return normalized;
        }
    }
    ty
}

/// Replace the first `dyn Trait` Self type in generic args with a concrete type.
///
/// Handles both bare `dyn Trait` and wrapped forms like `Box<dyn Trait>` or
/// `&dyn Trait`.
pub(super) fn replace_dyn_self(
    fn_args: &rustc_public::ty::GenericArgs,
    concrete_ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::GenericArgs> {
    let mut new_args: Vec<GenericArgKind> = Vec::new();
    let mut replaced = false;
    for arg in &fn_args.0 {
        match arg {
            GenericArgKind::Type(ty) if !replaced => {
                let effective_ty = peel_pointer_like_wrapper_ty(*ty);
                if matches!(effective_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                    new_args.push(GenericArgKind::Type(concrete_ty));
                    replaced = true;
                } else if let Some(replaced_ty) = replace_dyn_tail_with_concrete(*ty, concrete_ty) {
                    new_args.push(GenericArgKind::Type(replaced_ty));
                    replaced = true;
                } else {
                    new_args.push(arg.clone());
                }
            }
            _ => new_args.push(arg.clone()),
        }
    }
    replaced.then_some(rustc_public::ty::GenericArgs(new_args))
}

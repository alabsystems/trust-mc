// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::collections::HashMap;

use rustc_public::ty::{GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};

pub(super) fn generic_param_positions(args: &GenericArgs) -> HashMap<String, usize> {
    args.0
        .iter()
        .filter_map(|arg| {
            let ty = arg.ty()?;
            let TyKind::Param(param_ty) = ty.kind() else {
                return None;
            };
            if param_ty.name == "Self" { None } else { Some(param_ty.name) }
        })
        .enumerate()
        .map(|(idx, name)| (name, idx))
        .collect()
}

fn generic_args_alpha_equiv(
    old_args: &GenericArgs,
    new_args: &GenericArgs,
    old_param_positions: &HashMap<String, usize>,
    new_param_positions: &HashMap<String, usize>,
    self_binding: &mut Option<Ty>,
) -> bool {
    old_args.0.len() == new_args.0.len()
        && old_args.0.iter().zip(&new_args.0).all(|(old_arg, new_arg)| match (old_arg, new_arg) {
            (GenericArgKind::Type(old_ty), GenericArgKind::Type(new_ty)) => ty_alpha_equiv_bind(
                *old_ty,
                *new_ty,
                old_param_positions,
                new_param_positions,
                self_binding,
            ),
            _ => old_arg == new_arg,
        })
}

/// Alpha-equivalence with consistent `Self` substitution.
///
/// A trait default method resolved via `resolve_in_trait_impl` keeps the trait
/// identity signature (`&Self` = `TyKind::Param("Self")`), while the stub is
/// written against the concrete impl type (`&MyType`). Without this arm the
/// comparison errs and `dcx.abort_if_errors()` inside the codegen backend
/// escapes as exit 101 (fixme_stub_trait_default_method ICE).
///
/// `Param("Self")` on the OLD side binds to the first concrete new-side type it
/// meets; every later occurrence must match the SAME type (`fn(&Self, &Self)`
/// cannot validate against `fn(&A, &B)`), so the substitution is a genuine
/// consistent instantiation rather than a wildcard. Trait-bound satisfaction
/// stays checked at monomorphization, exactly like ordinary generic params.
pub(super) fn ty_alpha_equiv_bind(
    old_ty: Ty,
    new_ty: Ty,
    old_param_positions: &HashMap<String, usize>,
    new_param_positions: &HashMap<String, usize>,
    self_binding: &mut Option<Ty>,
) -> bool {
    if old_ty == new_ty {
        return true;
    }

    match (old_ty.kind(), new_ty.kind()) {
        (TyKind::Param(old_param), TyKind::Param(new_param)) => {
            old_param_positions.get(&old_param.name) == new_param_positions.get(&new_param.name)
        }
        // Consistent Self instantiation (trait default method vs concrete stub).
        (TyKind::Param(old_param), _) if old_param.name == "Self" => match self_binding {
            Some(bound) => *bound == new_ty,
            None => {
                *self_binding = Some(new_ty);
                true
            }
        },
        (TyKind::RigidTy(old_rigid), TyKind::RigidTy(new_rigid)) => match (old_rigid, new_rigid) {
            (RigidTy::Ref(_, old_inner, old_mut), RigidTy::Ref(_, new_inner, new_mut)) => {
                old_mut == new_mut
                    && ty_alpha_equiv_bind(
                        old_inner,
                        new_inner,
                        old_param_positions,
                        new_param_positions,
                        self_binding,
                    )
            }
            (RigidTy::RawPtr(old_inner, old_mut), RigidTy::RawPtr(new_inner, new_mut)) => {
                old_mut == new_mut
                    && ty_alpha_equiv_bind(
                        old_inner,
                        new_inner,
                        old_param_positions,
                        new_param_positions,
                        self_binding,
                    )
            }
            (RigidTy::Slice(old_elem), RigidTy::Slice(new_elem)) => ty_alpha_equiv_bind(
                old_elem,
                new_elem,
                old_param_positions,
                new_param_positions,
                self_binding,
            ),
            (RigidTy::Array(old_elem, old_len), RigidTy::Array(new_elem, new_len)) => {
                old_len == new_len
                    && ty_alpha_equiv_bind(
                        old_elem,
                        new_elem,
                        old_param_positions,
                        new_param_positions,
                        self_binding,
                    )
            }
            (RigidTy::Tuple(old_fields), RigidTy::Tuple(new_fields)) => {
                old_fields.len() == new_fields.len()
                    && old_fields.iter().zip(new_fields).all(|(old_field, new_field)| {
                        ty_alpha_equiv_bind(
                            *old_field,
                            new_field,
                            old_param_positions,
                            new_param_positions,
                            self_binding,
                        )
                    })
            }
            (RigidTy::Adt(old_def, old_args), RigidTy::Adt(new_def, new_args)) => {
                old_def == new_def
                    && generic_args_alpha_equiv(
                        &old_args,
                        &new_args,
                        old_param_positions,
                        new_param_positions,
                        self_binding,
                    )
            }
            (RigidTy::FnDef(old_def, old_args), RigidTy::FnDef(new_def, new_args)) => {
                old_def == new_def
                    && generic_args_alpha_equiv(
                        &old_args,
                        &new_args,
                        old_param_positions,
                        new_param_positions,
                        self_binding,
                    )
            }
            (RigidTy::Closure(old_def, old_args), RigidTy::Closure(new_def, new_args)) => {
                old_def == new_def
                    && generic_args_alpha_equiv(
                        &old_args,
                        &new_args,
                        old_param_positions,
                        new_param_positions,
                        self_binding,
                    )
            }
            _ => false,
        },
        _ => false,
    }
}

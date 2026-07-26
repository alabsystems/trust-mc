// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Body-local type resolution helpers for `ChcCtx`.
//!
//! Extracted from `codegen_ctx/mod.rs` per #3254 packet 1.

use rustc_middle::ty::{EarlyBinder, TypeVisitableExt, TypingEnv};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, GenericArgs, RigidTy, Ty, TyConst, TyConstKind, TyKind};

use super::ChcCtx;
use crate::codegen_ay::chc::decl::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn resolve_body_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> rustc_public::ty::Ty {
        let Some(instance) = self.current_instance else {
            return ty;
        };
        let internal_ty = rustc_internal::internal(self.tcx, ty);
        // When the instance has generic args, use rustc's full monomorphization
        // to resolve body-local types (handles nested generics, associated types,
        // and normalizations that manual substitution misses). When args are
        // empty (non-generic harness), only do this for types without residual
        // params. That preserves the #3705 panic fix while still revealing
        // args-empty async opaque futures to their hidden coroutine type.
        if !instance.args().0.is_empty() || !internal_ty.has_param() {
            let internal_instance = rustc_internal::internal(self.tcx, instance);
            let resolved_ty = rustc_internal::stable(
                internal_instance.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    TypingEnv::fully_monomorphized(),
                    EarlyBinder::bind(internal_ty),
                ),
            );
            if resolved_ty != ty {
                return resolved_ty;
            }
        }
        Self::resolve_body_ty_with_args(ty, &instance.args())
    }

    fn resolve_body_ty_with_args(ty: Ty, fn_args: &GenericArgs) -> Ty {
        match ty.kind() {
            rustc_public::ty::TyKind::Param(param_ty) => fn_args
                .0
                .get(param_ty.index as usize)
                .and_then(|arg| match arg {
                    GenericArgKind::Type(resolved_ty) => Some(*resolved_ty),
                    _ => None,
                })
                .unwrap_or(ty),
            rustc_public::ty::TyKind::RigidTy(rigid_ty) => {
                Self::resolve_body_rigid_ty(ty, rigid_ty, fn_args)
            }
            _ => ty,
        }
    }

    fn resolve_body_rigid_ty(ty: Ty, rigid_ty: RigidTy, fn_args: &GenericArgs) -> Ty {
        match rigid_ty {
            RigidTy::Array(elem_ty, len) => {
                let resolved_elem = Self::resolve_body_ty_with_args(elem_ty, fn_args);
                let resolved_len = Self::resolve_body_const_with_args(&len, fn_args);
                if resolved_elem == elem_ty && resolved_len == len {
                    ty
                } else {
                    Ty::from_rigid_kind(RigidTy::Array(resolved_elem, resolved_len))
                }
            }
            RigidTy::Slice(elem_ty) => {
                Self::rebuild_unary_rigid_ty(ty, elem_ty, fn_args, RigidTy::Slice)
            }
            RigidTy::Ref(region, pointee_ty, mutability) => {
                Self::rebuild_unary_rigid_ty(ty, pointee_ty, fn_args, |resolved_pointee| {
                    RigidTy::Ref(region, resolved_pointee, mutability)
                })
            }
            RigidTy::RawPtr(pointee_ty, mutability) => {
                Self::rebuild_unary_rigid_ty(ty, pointee_ty, fn_args, |resolved_pointee| {
                    RigidTy::RawPtr(resolved_pointee, mutability)
                })
            }
            RigidTy::Tuple(fields) => {
                let resolved_fields: Vec<_> = fields
                    .iter()
                    .map(|field_ty| Self::resolve_body_ty_with_args(*field_ty, fn_args))
                    .collect();
                if resolved_fields
                    .iter()
                    .zip(&fields)
                    .all(|(resolved, original)| resolved == original)
                {
                    ty
                } else {
                    Ty::from_rigid_kind(RigidTy::Tuple(resolved_fields))
                }
            }
            RigidTy::Adt(def, args) => {
                let Some(resolved_args) = Self::resolve_body_generic_args(&args, fn_args) else {
                    return ty;
                };
                Ty::from_rigid_kind(RigidTy::Adt(def, resolved_args))
            }
            RigidTy::FnDef(def, args) => {
                let Some(resolved_args) = Self::resolve_body_generic_args(&args, fn_args) else {
                    return ty;
                };
                Ty::from_rigid_kind(RigidTy::FnDef(def, resolved_args))
            }
            _ => ty,
        }
    }

    fn rebuild_unary_rigid_ty(
        original_ty: Ty,
        nested_ty: Ty,
        fn_args: &GenericArgs,
        rebuild: impl FnOnce(Ty) -> RigidTy,
    ) -> Ty {
        let resolved_nested = Self::resolve_body_ty_with_args(nested_ty, fn_args);
        if resolved_nested == nested_ty {
            original_ty
        } else {
            Ty::from_rigid_kind(rebuild(resolved_nested))
        }
    }

    fn resolve_body_generic_args(args: &GenericArgs, fn_args: &GenericArgs) -> Option<GenericArgs> {
        let resolved_args: Vec<_> = args
            .0
            .iter()
            .map(|arg| match arg {
                GenericArgKind::Type(arg_ty) => {
                    GenericArgKind::Type(Self::resolve_body_ty_with_args(*arg_ty, fn_args))
                }
                GenericArgKind::Const(arg_const) => {
                    GenericArgKind::Const(Self::resolve_body_const_with_args(arg_const, fn_args))
                }
                _ => arg.clone(),
            })
            .collect();
        (resolved_args != args.0).then_some(GenericArgs(resolved_args))
    }

    fn resolve_body_const_with_args(ty_const: &TyConst, fn_args: &GenericArgs) -> TyConst {
        match ty_const.kind() {
            TyConstKind::Param(param_const) => fn_args
                .0
                .get(param_const.index as usize)
                .and_then(|arg| match arg {
                    GenericArgKind::Const(resolved_const) => Some(resolved_const.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| ty_const.clone()),
            _ => ty_const.clone(),
        }
    }

    /// Resolve a body local's type with coroutine-aware call-destination fallback.
    ///
    /// Mirrors the state-var resolution at codegen_decl_state_vars_locals.rs:58-68.
    /// Use this in inline walker paths so destination sorts match state-var sorts.
    pub(in crate::codegen_ay::chc) fn resolve_inline_local_ty(
        &self,
        body: &rustc_public::mir::Body,
        local_idx: usize,
    ) -> Option<Ty> {
        let local_decl = body.locals().get(local_idx)?;
        let mut ty = self.resolve_body_ty(local_decl.ty);
        // Prefer the call destination type when the raw local type stays scalar
        // but the actual call result resolves to a richer sort. Async/coroutine
        // constructors are the motivating case, but some bodies keep the local
        // declared as an opaque scalar-looking shell even after monomorphization.
        if let Some(call_ty) = self.resolved_call_destination_ty_in(body, local_idx)
            && self.should_prefer_call_destination_ty(ty, call_ty)
        {
            ty = call_ty;
        }
        Some(ty)
    }

    fn should_prefer_call_destination_ty(&self, local_ty: Ty, call_ty: Ty) -> bool {
        if matches!(local_ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
            return false;
        }
        if matches!(call_ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
            return true;
        }

        let local_sort = ChcCtx::translate_ty(local_ty);
        let call_sort = ChcCtx::translate_ty(call_ty);
        matches!(
            (local_sort.as_ref(), call_sort.as_ref()),
            (Some(local_sort), Some(call_sort)) if local_sort.is_bitvec() && !call_sort.is_bitvec()
        )
    }

    /// Scan a body for a Call terminator writing to `local_idx` and resolve
    /// the callee output type. Parameterized over body so it works for both
    /// the harness body and inline callee bodies.
    fn resolved_call_destination_ty_in(
        &self,
        body: &rustc_public::mir::Body,
        local_idx: usize,
    ) -> Option<Ty> {
        body.blocks.iter().find_map(|block| {
            let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
                &block.terminator.kind
            else {
                return None;
            };
            if destination.local != local_idx {
                return None;
            }
            let func_ty = func.ty(body.locals()).ok()?;
            let output_ty = func_ty.kind().fn_sig()?.skip_binder().output();
            Some(self.resolve_body_ty(output_ty))
        })
    }
}

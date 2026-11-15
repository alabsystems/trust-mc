// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule A: the type of a field, and of a body local, is stated once.
//!
//! > A type is instantiated under the binder it was written in. A field's
//! > declared type is instantiated at its ADT's own arguments, and a
//! > body-local type at its instance's arguments. Each is then normalized
//! > with the `try_` normalizer under `TypingEnv::fully_monomorphized()`. A
//! > failure refuses (`None`) and never approximates. Every rustc query that
//! > panics on non-monomorphic input is reached only through this module.
//!
//! Why (design trust-mc-reds-final §3). The Trust standard library declares
//! `Atomic<T: AtomicPrimitive> { v: UnsafeCell<T::Storage> }`. A field's
//! DECLARED type (`FieldDef::ty`) is `UnsafeCell<<T as AtomicPrimitive>::Storage>`
//! with `T` free, under the ADT's binder. The encoder read field types four
//! ways, none of them an instantiation: two shallow `resolve_generic_ty`
//! copies (only a top-level `Param` replaced), a recursive copy that left
//! projections alone, and inline substitutions. Its parameter guards were
//! shallow too (none looked inside an `Alias`), so the projection reached
//! `FieldDef::ty_with_args`, `instantiate_mir_and_normalize_erasing_regions`
//! and `Instance::resolve_drop_in_place`, which normalize with rustc's
//! PANICKING normalizer (`normalize_erasing_regions.rs`, "Failed to
//! normalize ... maybe try to call `try_normalize_erasing_regions` instead"):
//! an internal compiler error that killed every harness of the file (CHC
//! `rc_shared_handle_dual.rs`, BMC `negative/frozen_views_indirect.rs`), or a
//! caught panic further on (`bvadd requires same BitVec sorts` after
//! `TyKind::Alias in translate_ty`).
//!
//! What this module provides:
//! - [`field_ty`]: a field's type at its ADT's arguments (the arguments must
//!   already be under the analysed body's binder: a caller holding a body-local
//!   ADT type runs [`body_ty`] on it first).
//! - [`body_ty`]: a body-local type at its instance's arguments.
//! - [`has_unresolved_params`]: the one parameter test, DEEP (through
//!   aliases), over type and const parameters only (lifetimes never block a
//!   query: every normalizer erases them).
//! - [`drop_in_place`] / [`drop_glue_body`]: the drop glue of a type, refused
//!   when the type has unresolved parameters.
//! - [`single_field_storage_ty`]: the storage type of a one-field ADT.
//!
//! Every function here is total: rustc's `instantiate` panics when a type
//! names a parameter its arguments do not supply (or supply at another kind),
//! so each instantiation first checks that the arguments FIT the type
//! ([`args_fit`]) and refuses otherwise.
//!
//! Enforcement (rung: test): `codegen_ay/test_mono_ty_single_rule.rs` forbids,
//! everywhere in `codegen_ay/` outside this module, the shallow resolvers,
//! `FieldDef::ty_with_args` and the other panicking normalizers,
//! `resolve_drop_in_place`, `.has_param()` (outside the impl-genericity
//! allowlist) and a bare `FieldDef::ty()` read. `scripts/check-trust-lane-build.sh`
//! runs it. Out of its scope: `kani_middle/` (16 `ty_with_args` calls and two
//! panicking normalizers, design residual 8).

use crate::callee_body::CalleeBody;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::{self as mty, GenericArgKind, TyCtxt, TypeVisitableExt, TypingEnv};
use rustc_public::mir::Body;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtDef, FieldDef, GenericArgs, Ty};

/// Whether every parameter `ty` names is supplied by `args` at the same kind.
/// `instantiate` panics (`bug!`) otherwise: a type from another body's binder,
/// or arguments of the wrong item.
fn args_fit<'tcx>(ty: mty::Ty<'tcx>, args: mty::GenericArgsRef<'tcx>) -> bool {
    let arg_kind = |index: u32| args.get(index as usize).map(|arg| arg.kind());
    ty.walk().all(|arg| match arg.kind() {
        GenericArgKind::Type(t) => match t.kind() {
            mty::Param(p) => matches!(arg_kind(p.index), Some(GenericArgKind::Type(_))),
            _ => true,
        },
        GenericArgKind::Lifetime(r) => match r.kind() {
            mty::ReEarlyParam(p) => matches!(arg_kind(p.index), Some(GenericArgKind::Lifetime(_))),
            _ => true,
        },
        GenericArgKind::Const(c) => match c.kind() {
            mty::ConstKind::Param(p) => matches!(arg_kind(p.index), Some(GenericArgKind::Const(_))),
            _ => true,
        },
    })
}

/// `declared` (written under the binder `args` instantiate) instantiated at
/// `args` and normalized, or `None`.
fn instantiate_and_normalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    declared: mty::Ty<'tcx>,
    args: mty::GenericArgsRef<'tcx>,
) -> Option<mty::Ty<'tcx>> {
    if !args_fit(declared, args) {
        return None;
    }
    tcx.try_instantiate_and_normalize_erasing_regions(
        args,
        TypingEnv::fully_monomorphized(),
        crate::rustc_compat::early_binder_bind(tcx, declared),
    )
    .ok()
}

/// The type of `field` at its ADT's arguments `args`: the declared type
/// instantiated and normalized. `None` when `args` do not fit the field's
/// type, or the type does not normalize (a projection of a parameter `args`
/// leave free: `field_ty(Atomic<T>.v, [T])`).
///
/// A field of a polymorphic ADT keeps the parameters `args` carry
/// (`field_ty(Option<T>.0, [T]) == T`): that is the right instantiation under
/// the caller's binder, and [`has_unresolved_params`] guards every query that
/// needs a monomorphic type.
pub(in crate::codegen_ay) fn field_ty(field: &FieldDef, args: &GenericArgs) -> Option<Ty> {
    mty::tls::with(|tcx| {
        let declared = rustc_internal::internal(tcx, field.ty());
        let args = rustc_internal::internal(tcx, args);
        instantiate_and_normalize(tcx, declared, args).map(rustc_internal::stable)
    })
}

/// A body-local type of `instance`'s body at `instance`'s arguments,
/// normalized. `None` when the type names a parameter the instance does not
/// supply (a type from another body's binder) or does not normalize.
pub(in crate::codegen_ay) fn body_ty(instance: Instance, ty: Ty) -> Option<Ty> {
    mty::tls::with(|tcx| {
        let internal_instance = rustc_internal::internal(tcx, instance);
        let internal_ty = rustc_internal::internal(tcx, ty);
        let args = internal_instance.args;
        if internal_instance.def.has_polymorphic_mir_body() && !args_fit(internal_ty, args) {
            return None;
        }
        internal_instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                tcx,
                TypingEnv::fully_monomorphized(),
                crate::rustc_compat::early_binder_bind(tcx, internal_ty),
            )
            .ok()
            .map(rustc_internal::stable)
    })
}

/// Whether `ty` still names a type or const parameter anywhere, inside an
/// alias included. Lifetime parameters do not count: every normalizer erases
/// regions first, so they never block a query.
pub(in crate::codegen_ay) fn has_unresolved_params(ty: Ty) -> bool {
    mty::tls::with(|tcx| rustc_internal::internal(tcx, ty).has_non_region_param())
}

/// The reason a CHC site records when it skips a drop whose glue
/// [`drop_in_place`] refused (the type still names a parameter): the drop's
/// effects are lost, so it is fail-closed (it is not in the audited SoundHavoc
/// list of `chc::codegen_ctx::fallback_soundness`, which a unit test holds).
pub(in crate::codegen_ay) const DROP_GLUE_UNRESOLVED: &str = "drop_glue_unresolved_params";

/// The drop glue (`drop_in_place::<ty>`) of a monomorphic `ty`; `None` when
/// `ty` has unresolved parameters, which `resolve_drop_in_place` cannot take.
pub(in crate::codegen_ay) fn drop_in_place(ty: Ty) -> Option<Instance> {
    (!has_unresolved_params(ty)).then(|| Instance::resolve_drop_in_place(ty))
}

/// The body of `ty`'s drop glue: `None` when `ty` has unresolved parameters
/// or the glue has no body (an empty shim).
pub(in crate::codegen_ay) fn drop_glue_body(ty: Ty) -> Option<Body> {
    drop_in_place(ty)?.callee_body()
}

/// The type of the only field of a one-variant, one-field ADT, at `args`.
pub(in crate::codegen_ay) fn single_field_storage_ty(
    def: AdtDef,
    args: &GenericArgs,
) -> Option<Ty> {
    let variants = def.variants();
    let [variant] = variants.as_slice() else { return None };
    let fields = variant.fields();
    let [field] = fields.as_slice() else { return None };
    field_ty(field, args)
}

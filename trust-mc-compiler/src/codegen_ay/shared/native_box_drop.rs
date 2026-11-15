// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native Box ownership and allocator identity for checked drop dispatch.

use super::{mono_ty, native_box_raw::native_box_raw_pointer_field};
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

/// Authenticate the complete native Global carrier, including fat metadata.
/// An arbitrary zero-sized allocator is not Global.
pub(crate) fn native_global_box_pointee(tcx: TyCtxt<'_>, ty: Ty) -> Option<Ty> {
    if !cfg!(all(trust_toolchain, version("1.101")))
        || crate::kani_middle::transform::unit_has_stubs()
        || mono_ty::has_unresolved_params(ty)
    {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
    let native = |id, path: &[&str]| {
        crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(tcx, id, path)
    };
    if !native(rustc_internal::internal(tcx, def.def_id()), &["boxed", "Box"]) {
        return None;
    }
    let [GenericArgKind::Type(inner), GenericArgKind::Type(allocator)] = args.0.as_slice() else {
        return None;
    };
    let TyKind::RigidTy(RigidTy::Adt(alloc, _)) = allocator.kind() else { return None };
    if !native(rustc_internal::internal(tcx, alloc.def_id()), &["alloc", "Global"]) {
        return None;
    }
    let variants = def.variants();
    let [variant] = variants.as_slice() else { return None };
    let fields = variant.fields();
    let [carrier, allocator_field] = fields.as_slice() else { return None };
    let carrier = mono_ty::field_ty(carrier, &args)?;
    let TyKind::RigidTy(RigidTy::Adt(raw, raw_args)) = carrier.kind() else { return None };
    let (_, pointer) = native_box_raw_pointer_field(tcx, raw, &raw_args)?;
    if raw_args.0.as_slice() != [GenericArgKind::Type(*inner)]
        || mono_ty::field_ty(allocator_field, &args)? != *allocator
        || LayoutOf::new(*allocator).size_of()? != 0
        || LayoutOf::new(ty).field_offset(0)? != 0
        || LayoutOf::new(ty).size_of()? != LayoutOf::new(pointer).size_of()?
    {
        return None;
    }
    Some(*inner)
}

/// The complete core::mem::drop boundary for an actual Global Box<dyn Trait>.
/// Box's own Drop method only deallocates; it is not this boundary.
pub(crate) fn native_global_dyn_box_drop_value(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> Option<Ty> {
    if !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
        tcx,
        rustc_internal::internal(tcx, instance.def.def_id()),
        &["mem", "drop"],
    ) {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let [input] = signature.inputs() else { return None };
    if !matches!(signature.output().kind(), TyKind::RigidTy(RigidTy::Tuple(types)) if types.is_empty())
        || !matches!(
            native_global_box_pointee(tcx, *input)?.kind(),
            TyKind::RigidTy(RigidTy::Dynamic(..))
        )
    {
        return None;
    }
    Some(*input)
}

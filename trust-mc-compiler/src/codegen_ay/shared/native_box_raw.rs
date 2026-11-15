// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;

/// Global's layout contract does not erase user allocator body effects.
pub(crate) fn native_bmc_has_custom_global_allocator(tcx: TyCtxt<'_>) -> bool {
    tcx.has_global_allocator(rustc_hir::def_id::LOCAL_CRATE)
        || tcx.crates(()).iter().any(|krate| tcx.has_global_allocator(*krate))
}

/// A real thin Global Box, with its actual default allocator and native
/// carrier ABI. No user wrapper, custom allocator or erased fat metadata.
pub(crate) fn native_thin_global_box_pointee(
    tcx: TyCtxt<'_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    if crate::kani_middle::transform::unit_has_stubs() {
        return None;
    }
    native_thin_global_box_layout(tcx, ty)
}

/// Authenticate the native layout only. This grants no custody or model
/// permission when stubs are active; callers must check those separately.
fn native_thin_global_box_layout(
    tcx: TyCtxt<'_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    use super::mono_ty;
    use crate::kani_middle::abi::LayoutOf;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if !cfg!(all(trust_toolchain, version("1.101"))) || mono_ty::has_unresolved_params(ty) {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
    if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
        tcx,
        rustc_internal::internal(tcx, def.def_id()),
        &["boxed", "Box"],
    ) {
        return None;
    }
    let [GenericArgKind::Type(pointee), GenericArgKind::Type(allocator)] = args.0.as_slice() else {
        return None;
    };
    let TyKind::RigidTy(RigidTy::Adt(allocator_def, _)) = allocator.kind() else { return None };
    if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
        tcx,
        rustc_internal::internal(tcx, allocator_def.def_id()),
        &["alloc", "Global"],
    ) {
        return None;
    }
    let variants = def.variants();
    let [variant] = variants.as_slice() else { return None };
    let fields = variant.fields();
    let [pointer, allocator_field] = fields.as_slice() else { return None };
    let pointer_ty = mono_ty::field_ty(pointer, &args)?;
    let TyKind::RigidTy(RigidTy::Adt(raw_def, raw_args)) = pointer_ty.kind() else { return None };
    let (_, raw_pointer) = native_thin_box_raw_pointer_field(tcx, raw_def, &raw_args)?;
    if raw_args.0.as_slice() != [GenericArgKind::Type(*pointee)]
        || mono_ty::field_ty(allocator_field, &args)? != *allocator
        || LayoutOf::new(*allocator).size_of()? != 0
        || LayoutOf::new(ty).field_offset(0)? != 0
        || LayoutOf::new(raw_pointer).size_of()? != 8
        || LayoutOf::new(ty).size_of()? != LayoutOf::new(raw_pointer).size_of()?
    {
        return None;
    }
    Some(*pointee)
}

/// The resolved native `Box<T, Global>::from_raw`, not a path-name shortcut.
pub(crate) fn native_bmc_box_from_raw(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> Option<(rustc_public::ty::Ty, rustc_public::ty::Ty)> {
    use rustc_public::mir::mono::InstanceKind;
    use rustc_public::ty::{RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if matches!(instance.kind, InstanceKind::Virtual { .. }) {
        return None;
    }
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    if id.is_local() || tcx.item_name(id).as_str() != "from_raw" {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let output = signature.output();
    let pointee = native_thin_global_box_pointee(tcx, output)?;
    let [input] = signature.inputs() else { return None };
    if !matches!(input.kind(), TyKind::RigidTy(RigidTy::RawPtr(inner, _)) if inner == pointee) {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Adt(box_def, _)) = output.kind() else { return None };
    if id.krate != rustc_internal::internal(tcx, box_def.def_id()).krate {
        return None;
    }
    let owner = tcx.parent(id);
    if !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
        || crate::rustc_compat::impl_opt_trait_ref(tcx, owner).is_some()
    {
        return None;
    }
    let self_ty =
        crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
    if !matches!(self_ty.kind(), rustc_middle::ty::Adt(adt, _)
        if adt.did() == rustc_internal::internal(tcx, box_def.def_id()))
    {
        return None;
    }
    Some((output, pointee))
}

/// Preserve the Drop terminator only when the compiler's actual pointee glue
/// is empty. A user destructor is never replaced by allocation bookkeeping.
pub(crate) fn native_bmc_box_drop_is_modeled(tcx: TyCtxt<'_>, ty: rustc_public::ty::Ty) -> bool {
    native_thin_global_box_pointee(tcx, ty).is_some_and(|pointee| {
        super::mono_ty::drop_in_place(pointee).is_some_and(|instance| instance.is_empty_shim())
    })
}

/// The native by-value drop function has no effect beyond its argument's
/// actual drop glue. Only a thin Global Box with empty pointee glue qualifies.
pub(crate) fn native_bmc_box_drop_value(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::ty::{RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
        tcx,
        rustc_internal::internal(tcx, instance.def.def_id()),
        &["mem", "drop"],
    ) {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let [input] = signature.inputs() else { return None };
    if !matches!(signature.output().kind(),TyKind::RigidTy(RigidTy::Tuple(types)) if types.is_empty())
        || !native_bmc_box_drop_is_modeled(tcx, *input)
    {
        return None;
    }
    Some(*input)
}

/// The pure ownership transfer from the actual native thin Global Box. The
/// allocator, receiver ABI and inherent method owner are all checked.
pub(crate) fn native_bmc_box_into_raw(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> Option<(rustc_public::ty::Ty, rustc_public::ty::Ty)> {
    if crate::kani_middle::transform::unit_has_stubs() {
        return None;
    }
    native_box_into_raw_identity(tcx, instance)
}

/// Identify the actual native API even when custody cannot be used. CHC
/// must retain the call and refuse at its checked boundary under active
/// stubs, instead of falling through to a generic pointer-identity handler.
pub(crate) fn native_box_into_raw_identity(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> Option<(rustc_public::ty::Ty, rustc_public::ty::Ty)> {
    use rustc_public::mir::mono::InstanceKind;
    use rustc_public::ty::{RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if matches!(instance.kind, InstanceKind::Virtual { .. }) {
        return None;
    }
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    if id.is_local() || tcx.opt_item_name(id)?.as_str() != "into_raw" {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let [input] = signature.inputs() else { return None };
    let pointee = native_thin_global_box_layout(tcx, *input)?;
    if !matches!(signature.output().kind(), TyKind::RigidTy(RigidTy::RawPtr(inner, _)) if inner == pointee)
    {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Adt(box_def, _)) = input.kind() else { return None };
    if id.krate != rustc_internal::internal(tcx, box_def.def_id()).krate {
        return None;
    }
    let owner = tcx.parent(id);
    if !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
        || crate::rustc_compat::impl_opt_trait_ref(tcx, owner).is_some()
    {
        return None;
    }
    let self_ty =
        crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
    if !matches!(self_ty.kind(), rustc_middle::ty::Adt(adt, _)
        if adt.did() == rustc_internal::internal(tcx, box_def.def_id()))
    {
        return None;
    }
    Some((*input, signature.output()))
}

/// The actual pointer field of the native BoxRaw representation. The
/// compiler changed Box's private carrier from Unique to BoxRaw; that name
/// alone authorizes neither pointer semantics nor a transparent memory key.
/// Dyn carriers use a data word with separately authenticated typed metadata;
/// the thin-only entry point below never grants access to that channel.
pub(in crate::codegen_ay) fn native_box_raw_pointer_field(
    tcx: TyCtxt<'_>,
    def: rustc_public::ty::AdtDef,
    args: &rustc_public::ty::GenericArgs,
) -> Option<(usize, rustc_public::ty::Ty)> {
    use super::mono_ty;
    use crate::kani_middle::abi::LayoutOf;
    use rustc_public::ty::{AdtKind, GenericArgKind, RigidTy, Ty, TyKind};
    use rustc_public::{CrateDef, rustc_internal};

    if def.kind() != AdtKind::Struct
        || !def.repr().flags.is_transparent
        || !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            tcx,
            rustc_internal::internal(tcx, def.def_id()),
            &["boxed", "BoxRaw"],
        )
    {
        return None;
    }
    let [GenericArgKind::Type(pointee)] = args.0.as_slice() else { return None };
    if !pointee.layout().ok()?.shape().is_sized()
        && !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
    {
        return None;
    }
    let variants = def.variants();
    let [variant] = variants.as_slice() else { return None };
    let fields = variant.fields();
    if fields.len() != 2 {
        return None;
    }
    let wrapper_ty = Ty::from_rigid_kind(RigidTy::Adt(def, args.clone()));
    let wrapper = LayoutOf::new(wrapper_ty);
    let mut pointer = None;
    for (index, field) in fields.iter().enumerate() {
        let field_ty = mono_ty::field_ty(field, args)?;
        let TyKind::RigidTy(RigidTy::Adt(field_def, field_args)) = field_ty.kind() else {
            return None;
        };
        if field_args.0.as_slice() != [GenericArgKind::Type(*pointee)] {
            return None;
        }
        let field_id = rustc_internal::internal(tcx, field_def.def_id());
        if crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
            tcx,
            field_id,
            &["ptr", "non_null", "NonNull"],
        ) {
            if pointer.is_some()
                || wrapper.field_offset(index)? != 0
                || LayoutOf::new(field_ty).size_of()? != wrapper.size_of()?
            {
                return None;
            }
            pointer = Some((index, field_ty));
        } else if !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
            tcx,
            field_id,
            &["marker", "PhantomData"],
        ) || LayoutOf::new(field_ty).size_of()? != 0
        {
            return None;
        }
    }
    pointer
}

/// The thin-only API remains a refusal boundary for callers that have no
/// metadata channel. A dyn carrier is authorized only by the checked path.
pub(in crate::codegen_ay) fn native_thin_box_raw_pointer_field(
    tcx: TyCtxt<'_>,
    def: rustc_public::ty::AdtDef,
    args: &rustc_public::ty::GenericArgs,
) -> Option<(usize, rustc_public::ty::Ty)> {
    use rustc_public::ty::GenericArgKind;
    let [GenericArgKind::Type(pointee)] = args.0.as_slice() else { return None };
    pointee.layout().ok()?.shape().is_sized().then_some(())?;
    native_box_raw_pointer_field(tcx, def, args)
}

/// Native wrapper views that carry a dyn pointer's data word and its separate
/// vtable binding. Authentication is by compiler definitions and real layout.
pub(in crate::codegen_ay) fn native_dyn_pointer_pointee(
    tcx: TyCtxt<'_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    native_dyn_pointer_pointee_bounded(tcx, ty, 0)
}

fn native_dyn_pointer_pointee_bounded(
    tcx: TyCtxt<'_>,
    ty: rustc_public::ty::Ty,
    depth: usize,
) -> Option<rustc_public::ty::Ty> {
    use super::mono_ty;
    use crate::kani_middle::abi::LayoutOf;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if depth > 32 {
        return None;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) =>
        {
            Some(pointee)
        }
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
            if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                Some(pointee)
            } else {
                native_dyn_pointer_pointee_bounded(tcx, pointee, depth + 1)
            }
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let GenericArgKind::Type(pointee) = *args.0.first()? else { return None };
            if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                return None;
            }
            if native_box_raw_pointer_field(tcx, def, &args).is_some() {
                return Some(pointee);
            }
            let wrapper = LayoutOf::new(ty);
            let fields = def.variants().first()?.fields();
            if def.is_box() {
                let field = mono_ty::field_ty(fields.first()?, &args)?;
                let TyKind::RigidTy(RigidTy::Adt(carrier, carrier_args)) = field.kind() else {
                    return None;
                };
                native_box_raw_pointer_field(tcx, carrier, &carrier_args)?;
                if wrapper.field_offset(0)? != 0
                    || LayoutOf::new(field).size_of()? != wrapper.size_of()?
                {
                    return None;
                }
                for field in fields.iter().skip(1) {
                    if LayoutOf::new(mono_ty::field_ty(field, &args)?).size_of()? != 0 {
                        return None;
                    }
                }
                return Some(pointee);
            }
            if crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
                tcx,
                rustc_internal::internal(tcx, def.def_id()),
                &["ptr", "non_null", "NonNull"],
            ) && fields.len() == 1
            {
                let field = mono_ty::field_ty(&fields[0], &args)?;
                if matches!(field.kind(), TyKind::RigidTy(RigidTy::RawPtr(inner, _)) if inner == pointee)
                    && wrapper.field_offset(0)? == 0
                    && LayoutOf::new(field).size_of()? == wrapper.size_of()?
                {
                    return Some(pointee);
                }
            }
            None
        }
        _ => None,
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Authenticate native allocation without granting initialized payload bytes.

use super::{mono_ty, native_box_drop::native_global_box_pointee};
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

#[derive(Clone, Copy)]
pub(crate) struct NativeUninitBox {
    pub boxed: Ty,
    pub maybe: Ty,
    pub payload: Ty,
    pub size: u64,
    pub align: u64,
}

/// Identity, layout and allocator are checked independently of payload validity.
pub(crate) fn native_uninit_box(tcx: TyCtxt<'_>, boxed: Ty) -> Option<NativeUninitBox> {
    let maybe = native_global_box_pointee(tcx, boxed)?;
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = maybe.kind() else { return None };
    if Some(rustc_internal::internal(tcx, def.def_id())) != tcx.lang_items().maybe_uninit() {
        return None;
    }
    let [GenericArgKind::Type(payload)] = args.0.as_slice() else { return None };
    if mono_ty::has_unresolved_params(*payload) {
        return None;
    }
    let size = u64::try_from(LayoutOf::new(*payload).size_of()?).ok()?;
    let align = u64::try_from(LayoutOf::new(*payload).align_of()?).ok()?;
    // The current native allocation certificate has no dangling-ZST or repeated
    // generation authority. Never manufacture a heap object for either case.
    if size == 0
        || size > u64::from(u32::MAX)
        || !align.is_power_of_two()
        || u64::try_from(LayoutOf::new(maybe).size_of()?).ok()? != size
        || u64::try_from(LayoutOf::new(maybe).align_of()?).ok()? != align
    {
        return None;
    }
    Some(NativeUninitBox { boxed, maybe, payload: *payload, size, align })
}

/// Exact inherent `Box<T, Global>::new_uninit`, not a user method with that name.
pub(crate) fn native_box_new_uninit(
    tcx: TyCtxt<'_>,
    instance: &Instance,
) -> Option<NativeUninitBox> {
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    if id.is_local() || tcx.item_name(id).as_str() != "new_uninit" {
        return None;
    }
    let sig = instance.ty().kind().fn_sig()?.skip_binder();
    if !sig.inputs().is_empty() {
        return None;
    }
    let native = native_uninit_box(tcx, sig.output())?;
    let TyKind::RigidTy(RigidTy::Adt(box_def, _)) = native.boxed.kind() else { return None };
    let box_id = rustc_internal::internal(tcx, box_def.def_id());
    let owner = tcx.parent(id);
    if id.krate != box_id.krate
        || !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
        || crate::rustc_compat::impl_opt_trait_ref(tcx, owner).is_some()
    {
        return None;
    }
    let self_ty =
        crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
    if !matches!(self_ty.kind(), rustc_middle::ty::Adt(adt, _) if adt.did() == box_id) {
        return None;
    }
    Some(native)
}

/// Allocation-site admission is shared by signature predeclaration and runtime
/// encoding. A rejected native site must not reserve a FIFO object for a later
/// allocator to consume under another region sort.
pub(crate) fn native_box_new_uninit_site(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    site: usize,
) -> Option<NativeUninitBox> {
    use rustc_public::mir::TerminatorKind;
    if crate::kani_middle::transform::unit_has_stubs()
        || super::native_box_raw::native_bmc_has_custom_global_allocator(tcx)
        || !native_allocation_site_is_single_execution(body, site)
    {
        return None;
    }
    let TerminatorKind::Call { func, args, destination, target, .. } =
        &body.blocks.get(site)?.terminator.kind
    else {
        return None;
    };
    if target.is_none() || !args.is_empty() || !destination.projection.is_empty() {
        return None;
    }
    let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func.ty(body.locals()).ok()?.kind() else {
        return None;
    };
    let instance = Instance::resolve(def, &substs).ok()?;
    let native = native_box_new_uninit(tcx, &instance)?;
    (body.locals().get(destination.local)?.ty == native.boxed).then_some(native)
}

pub(crate) fn native_allocation_site_is_single_execution(
    body: &rustc_public::mir::Body,
    site: usize,
) -> bool {
    let Some(block) = body.blocks.get(site) else {
        return false;
    };
    let mut pending = block.terminator.successors();
    let mut seen = std::collections::HashSet::new();
    let mut budget = 16_384usize;
    while let Some(next) = pending.pop() {
        let Some(left) = budget.checked_sub(1) else {
            return false;
        };
        budget = left;
        if next == site {
            return false;
        }
        if seen.insert(next) {
            let Some(block) = body.blocks.get(next) else {
                return false;
            };
            pending.extend(block.terminator.successors());
        }
    }
    true
}

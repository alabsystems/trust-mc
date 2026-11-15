// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact native Box callable protocol boundaries. These preserve real bodies;
//! they never replace the callable or its ownership/drop effects.

use super::native_box_drop::native_global_box_pointee;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::ty::{Abi, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeBoxCallKind {
    Fn,
    FnMut,
    FnOnce,
}

pub(crate) fn native_global_dyn_box_call(
    tcx: TyCtxt<'_>,
    instance: &Instance,
) -> Option<(Ty, NativeBoxCallKind)> {
    if matches!(instance.kind, InstanceKind::Virtual { .. }) {
        return None;
    }
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    let owner = tcx.parent(id);
    if id.is_local() || !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. }) {
        return None;
    }
    let implemented = crate::rustc_compat::skip_normalization(
        crate::rustc_compat::impl_opt_trait_ref(tcx, owner)?.instantiate_identity(),
    );
    let kind = if tcx.lang_items().fn_trait() == Some(implemented.def_id) {
        NativeBoxCallKind::Fn
    } else if tcx.lang_items().fn_mut_trait() == Some(implemented.def_id) {
        NativeBoxCallKind::FnMut
    } else if tcx.lang_items().fn_once_trait() == Some(implemented.def_id) {
        NativeBoxCallKind::FnOnce
    } else {
        return None;
    };
    let expected = match kind {
        NativeBoxCallKind::Fn => "call",
        NativeBoxCallKind::FnMut => "call_mut",
        NativeBoxCallKind::FnOnce => "call_once",
    };
    if tcx.item_name(id).as_str() != expected {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let [receiver, arguments] = signature.inputs() else {
        return None;
    };
    if signature.abi != Abi::RustCall
        || !matches!(arguments.kind(), TyKind::RigidTy(RigidTy::Tuple(_)))
    {
        return None;
    }
    let box_ty = match (kind, receiver.kind()) {
        (
            NativeBoxCallKind::Fn,
            TyKind::RigidTy(RigidTy::Ref(_, inner, rustc_public::mir::Mutability::Not)),
        ) => inner,
        (
            NativeBoxCallKind::FnMut,
            TyKind::RigidTy(RigidTy::Ref(_, inner, rustc_public::mir::Mutability::Mut)),
        ) => inner,
        (NativeBoxCallKind::FnOnce, _) => *receiver,
        _ => return None,
    };
    if !matches!(
        native_global_box_pointee(tcx, box_ty)?.kind(),
        TyKind::RigidTy(RigidTy::Dynamic(..))
    ) {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = box_ty.kind() else {
        return None;
    };
    let box_id = rustc_internal::internal(tcx, def.def_id());
    let self_ty =
        crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
    if id.krate != box_id.krate
        || !matches!(self_ty.kind(),rustc_middle::ty::Adt(adt,_) if adt.did()==box_id)
    {
        return None;
    }
    Some((box_ty, kind))
}

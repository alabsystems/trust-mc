// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Definition identity for the native array pointer walk.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

use super::{
    ChcCtx, OffsetCallAuthority, OffsetCallee, Operand, ProjectionElem, RefTarget, RigidTy, Rvalue,
    StatementKind, TyKind,
};

impl ChcCtx<'_, '_> {
    /// Calls that may contribute to a new exact array-span certificate must
    /// be the actual core operation, including its inherent receiver type.
    pub(super) fn native_offset_callee(&self, func: &Operand) -> Option<OffsetCallee> {
        use crate::kani_middle::std_abstraction::{
            is_sysroot_core_definition, is_sysroot_core_definition_at,
        };
        use rustc_public::mir::mono::{Instance, InstanceKind};
        use rustc_public::{CrateDef, rustc_internal};

        if crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        let ty = func.ty(self.body.locals()).ok()?;
        if crate::codegen_ay::shared::mono_ty::has_unresolved_params(ty) {
            return None;
        }
        let TyKind::RigidTy(RigidTy::FnDef(original, args)) = ty.kind() else { return None };
        let instance = Instance::resolve(original, &args).ok()?;
        if matches!(instance.kind, InstanceKind::Virtual { .. })
            || instance.def.def_id() != original.def_id()
            || crate::kani_middle::transform::instance_has_unit_stub(&instance)
        {
            return None;
        }
        let id = rustc_internal::internal(self.tcx, instance.def.def_id());
        if !is_sysroot_core_definition(self.tcx, id) {
            return None;
        }
        let name = self.tcx.item_name(id);
        let owner = self.tcx.parent(id);
        if matches!(self.tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. }) {
            if crate::rustc_compat::impl_opt_trait_ref(self.tcx, owner).is_some() {
                return None;
            }
            let self_ty = crate::rustc_compat::skip_normalization(
                self.tcx.type_of(owner).instantiate_identity(),
            );
            return match self_ty.kind() {
                rustc_middle::ty::RawPtr(..) => match name.as_str() {
                    "cast" | "cast_mut" | "cast_const" => Some(OffsetCallee::Identity),
                    "byte_add" | "wrapping_byte_add" => Some(OffsetCallee::BytesForward),
                    "byte_sub" | "wrapping_byte_sub" => Some(OffsetCallee::BytesBackward),
                    "byte_offset" | "wrapping_byte_offset" => Some(OffsetCallee::BytesSigned),
                    "add" | "wrapping_add" => Some(OffsetCallee::ElemsForward),
                    "sub" | "wrapping_sub" => Some(OffsetCallee::ElemsBackward),
                    "offset" | "wrapping_offset" => Some(OffsetCallee::ElemsSigned),
                    _ => None,
                },
                rustc_middle::ty::Slice(_) if matches!(name.as_str(), "as_ptr" | "as_mut_ptr") => {
                    Some(OffsetCallee::Identity)
                }
                _ => None,
            };
        }
        if is_sysroot_core_definition_at(self.tcx, id, &["intrinsics", "offset"]) {
            return Some(OffsetCallee::IntrinsicOffset);
        }
        if ["from_ref", "from_mut"].contains(&name.as_str())
            && is_sysroot_core_definition_at(self.tcx, id, &["ptr", name.as_str()])
            || ["from_raw_parts", "from_raw_parts_mut"].contains(&name.as_str())
                && is_sysroot_core_definition_at(self.tcx, id, &["ptr", "metadata", name.as_str()])
        {
            return Some(OffsetCallee::Identity);
        }
        None
    }
    /// A constant integer is trustworthy only while its own storage has no
    /// address that another operation could write. Unlike the pointer-only
    /// compatibility lane above, do not authorize an escape by a callee name.
    pub(super) fn integer_local_storage_is_addressed(&self, local: usize) -> bool {
        self.body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
            matches!(&statement.kind,
                StatementKind::Assign(_, Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place))
                    if place.local == local
                        && !matches!(place.projection.first(), Some(ProjectionElem::Deref)))
        })
    }

    /// The same bounded walk with native core call identity required at every
    /// call hop. New exact array views and span failures consume this version.
    pub(in crate::codegen_ay::chc) fn native_array_pointer_byte_offset(
        &self,
        ptr_local: usize,
        ref_target: &RefTarget,
    ) -> Option<i128> {
        if crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        self.store_pointer_referent_byte_offset_walk(
            ptr_local,
            ref_target,
            OffsetCallAuthority::NativeCore,
        )
    }
}

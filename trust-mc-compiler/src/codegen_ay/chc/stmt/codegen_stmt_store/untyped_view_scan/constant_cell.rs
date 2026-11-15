// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A seeded native byte view of one precisely located promoted constant.
//! The canonical typed-value codec is deliberately not a byte-image reader.

use super::{Origin, StaticRules};
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::shared::const_pointer::{ConstRead, Fixedness, TargetKey, target_bytes};
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, Ty, TyKind, UintTy};
use rustc_public::{CrateDef, rustc_internal};

impl StaticRules<'_, '_, '_> {
    /// Authenticate the resolved call in the Flow body's namespace. Only
    /// inherent raw pointer casts can carry new byte authority through a call. A user
    /// lookalike, indirect target, trait override or unit stub is opaque.
    pub(super) fn native_pointer_cast(&self, callee: Option<Ty>, leaf: &str) -> bool {
        let Some(ty) = callee else { return false };
        if !matches!(leaf, "cast" | "cast_mut" | "cast_const")
            || crate::kani_middle::transform::unit_has_stubs()
            || crate::codegen_ay::shared::mono_ty::has_unresolved_params(ty)
        {
            return false;
        }
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return false };
        let Ok(instance) = rustc_public::mir::mono::Instance::resolve(def, &args) else {
            return false;
        };
        if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. }) {
            return false;
        }
        let def = rustc_internal::internal(self.ctx.tcx, instance.def.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(self.ctx.tcx, def)
            || self.ctx.tcx.item_name(def).as_str() != leaf
        {
            return false;
        }
        let owner = self.ctx.tcx.parent(def);
        matches!(self.ctx.tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
            && crate::rustc_compat::impl_opt_trait_ref(self.ctx.tcx, owner).is_none()
            && crate::rustc_compat::skip_normalization(
                self.ctx.tcx.type_of(owner).instantiate_identity(),
            )
            .is_raw_ptr()
    }

    /// Preserve a location only through an actual native tuple field. Other
    /// projections keep their existing authority, but cannot grant a new raw
    /// byte view. In particular, no inactive enum payload offset is invented.
    pub(super) fn const_tuple_field_offset(
        &self,
        parent: Ty,
        index: usize,
        field: Ty,
        base: Option<u64>,
    ) -> Option<u64> {
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = parent.kind() else { return None };
        if fields.get(index) != Some(&field) {
            return None;
        }
        let layout = LayoutOf::new(parent);
        let offset = layout.field_offset(index)?;
        if offset.checked_add(LayoutOf::new(field).size_of()?)? > layout.size_of()? {
            return None;
        }
        base?.checked_add(u64::try_from(offset).ok()?)
    }

    /// This exact immutable address must already have an entry-rule byte
    /// constraint, under the registered u8 memory key and sort, equal to its
    /// initialized native data byte. A canonical Option/tuple cell, padding,
    /// relocation, new late view, mutable static or ambiguous address does
    /// not establish this fact. No memory or diagnostic state is changed.
    pub(super) fn seeded_const_byte(
        &self,
        origin: Option<Origin>,
        offset: Option<u64>,
        ty: Ty,
    ) -> bool {
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
            || !self.ctx.ref_resolution.object_seeding_closed
        {
            return false;
        }
        let (Some(Origin::Memory { id, static_image: false }), Some(offset)) = (origin, offset)
        else {
            return false;
        };
        let key = TargetKey::Memory(id);
        let Some(object) = self.ctx.global_object(&key) else { return false };
        if object.fixed != Some(Fixedness::Fixed)
            || object.size.is_none_or(|size| offset >= size)
            || offset > u64::from(u32::MAX)
        {
            return false;
        }
        let Some((bytes, Fixedness::Fixed)) = target_bytes(self.ctx.tcx, &key) else {
            return false;
        };
        let Some(byte) = usize::try_from(offset).ok().and_then(|at| bytes.read_uint_at(at, 1))
        else {
            return false;
        };
        let type_key = super::ChcCtx::type_key_for_ty(ty);
        let sort = Sort::bitvec(8);
        if self.ctx.heap_state.type_arrays.get(&*type_key).map(|(_, sort)| sort) != Some(&sort) {
            return false;
        }
        let expected = Expr::bitvec_const(byte, 8);
        self.ctx
            .ref_resolution
            .const_ref_entry_byte_seeds
            .get(&(object.obj_id, offset))
            .and_then(Option::as_ref)
            == Some(&expected)
    }
}

#[cfg(test)]
mod tests;

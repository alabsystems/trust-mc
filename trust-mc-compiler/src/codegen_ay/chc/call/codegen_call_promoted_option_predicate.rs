// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pure native Option predicates on typed nested fields of a promoted value.
//! The receiver remains its real address. Only the predicate reads the exact
//! initialized value; no pointer bits are decoded as an enum or new seed added.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{
    BorrowKind, Mutability, Operand, Place, ProjectionElem, Rvalue, StatementKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use super::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::chc::decl::global_objects::InitSite;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead, Fixedness, TargetKey};
use crate::kani_middle::abi::LayoutOf;

const MAX_HOPS: usize = 8;

fn shared_pointee(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, ty, Mutability::Not)) => Some(ty),
        _ => None,
    }
}

impl ChcCtx<'_, '_> {
    pub(super) fn promoted_option_predicate(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> Option<Expr> {
        let [receiver] = args else { return None };
        let (option_ty, is_none) = self.promoted_option_predicate_identity(func)?;
        if shared_pointee(receiver.ty(self.body.locals()).ok()?)? != option_ty {
            return None;
        }
        let (Operand::Copy(arg) | Operand::Move(arg)) = receiver else { return None };
        if !arg.projection.is_empty() {
            return None;
        }
        let place = self.promoted_option_receiver_place(arg.local, option_ty)?;
        let (root, constant) = self.promoted_option_constant_root(place.local, 0)?;
        let root_ty = shared_pointee(self.body.locals().get(root)?.ty)?;
        if constant.ty() != self.body.locals()[root].ty
            || !self.const_safe_value_supported(root_ty, 0)
            || !self.ref_resolution.object_seeding_closed
        {
            return None;
        }
        let bytes = const_pointer::const_bytes(&constant)?;
        let (reference, window) = const_pointer::fixed_pointee(self.tcx, &bytes, 0, root_ty)?;
        let key @ TargetKey::Memory(_) = reference.ptr.key()? else { return None };
        let object = self.global_object(&key)?;
        let recorded = self.ref_resolution.const_ref_objects.get(&root)?;
        if object.fixed != Some(Fixedness::Fixed)
            || recorded.obj_id != object.obj_id
            || recorded.offset != reference.ptr.offset()
            || recorded.ptr != Some(reference.ptr)
            || !self.ref_resolution.seeded_object_types.contains(&(object.obj_id, root_ty))
            || !self.ref_resolution.const_ref_values.contains_key(&root)
        {
            return None;
        }
        // The transactional decoder checks every active native field and its
        // canonical typed-memory capacity (Option<char>'s 33/32 mismatch refuses).
        let mut unused_seeds = Vec::new();
        let mut value = self.decode_const_safe_window(
            &window,
            root_ty,
            &mut unused_seeds,
            InitSite { obj_id: object.obj_id, base: reference.ptr.offset() },
        )?;
        let mut ty = root_ty;
        let mut offset = 0usize;
        for projection in &place.projection[1..] {
            let ProjectionElem::Field(index, field_ty) = projection else { return None };
            let TyKind::RigidTy(RigidTy::Tuple(fields)) = ty.kind() else { return None };
            if fields.get(*index) != Some(field_ty) {
                return None;
            }
            let layout = LayoutOf::new(ty);
            let field_offset = layout.field_offset(*index)?;
            if field_offset.checked_add(LayoutOf::new(*field_ty).size_of()?)? > layout.size_of()? {
                return None;
            }
            offset = offset.checked_add(field_offset)?;
            let ExprValue::DatatypeConstructor { args, .. } = value.value() else { return None };
            value = args.get(*index)?.clone();
            if value.sort() != &Self::translate_ty(*field_ty)? {
                return None;
            }
            ty = *field_ty;
        }
        if ty != option_ty
            || offset.checked_add(LayoutOf::new(option_ty).size_of()?)? > window.len()
        {
            return None;
        }
        let some = self.option_is_some(value);
        Some(if is_none { some.not() } else { some })
    }

    /// Resolve the actual item and instantiated receiver, never a path leaf,
    /// a matching datatype shape, or a user extension method. Active unit stubs
    /// make both the method body and its datatype authority unavailable.
    fn promoted_option_predicate_identity(&self, func: &Operand) -> Option<(Ty, bool)> {
        if crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
            func.ty(self.body.locals()).ok()?.kind()
        else {
            return None;
        };
        let instance = Instance::resolve(def, &generics).ok()?;
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            return None;
        }
        let def = rustc_internal::internal(self.tcx, instance.def.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(self.tcx, def) {
            return None;
        }
        let is_none = match self.tcx.item_name(def).as_str() {
            "is_none" => true,
            "is_some" => false,
            _ => return None,
        };
        let owner = self.tcx.parent(def);
        if !matches!(self.tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
            || crate::rustc_compat::impl_opt_trait_ref(self.tcx, owner).is_some()
        {
            return None;
        }
        let signature = instance.ty().kind().fn_sig()?.skip_binder();
        let [receiver_ty] = signature.inputs() else { return None };
        let option_ty = shared_pointee(*receiver_ty)?;
        let TyKind::RigidTy(RigidTy::Adt(option, _)) = option_ty.kind() else { return None };
        let native_self =
            crate::rustc_compat::skip_normalization(self.tcx.type_of(owner).instantiate_identity());
        if !matches!(native_self.kind(), rustc_middle::ty::Adt(adt, _)
            if adt.did() == rustc_internal::internal(self.tcx, option.def_id()))
        {
            return None;
        }
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
            self.tcx,
            rustc_internal::internal(self.tcx, option.def_id()),
            &["option", "Option"],
        ) || !matches!(signature.output().kind(), TyKind::RigidTy(RigidTy::Bool))
        {
            return None;
        }
        Some((option_ty, is_none))
    }

    fn promoted_option_unique_rhs(&self, local: usize) -> Option<&Rvalue> {
        if self.local_has_multiple_whole_definitions(local)
            || self.local_bytes_may_be_rewritten(local)
        {
            return None;
        }
        let mut found = None;
        for block in &self.body.blocks {
            for statement in &block.statements {
                if let StatementKind::Assign(lhs, rhs) = &statement.kind
                    && lhs.local == local
                {
                    if !lhs.projection.is_empty() || found.is_some() {
                        return None;
                    }
                    found = Some(rhs);
                }
            }
        }
        found
    }

    fn promoted_option_receiver_place(&self, mut local: usize, ty: Ty) -> Option<Place> {
        for _ in 0..MAX_HOPS {
            if shared_pointee(self.body.locals().get(local)?.ty)? != ty {
                return None;
            }
            match self.promoted_option_unique_rhs(local)? {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                    if place.projection.is_empty() =>
                {
                    local = place.local
                }
                Rvalue::Ref(_, BorrowKind::Shared, place)
                    if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) =>
                {
                    local = place.local;
                }
                Rvalue::Ref(_, BorrowKind::Shared, place)
                    if (3..=MAX_HOPS).contains(&place.projection.len())
                        && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                        && place.projection[1..]
                            .iter()
                            .all(|p| matches!(p, ProjectionElem::Field(..))) =>
                {
                    return Some(place.clone());
                }
                _ => return None,
            }
        }
        None
    }

    /// Preserve actual shared-reference type on every identity edge. Casts,
    /// arithmetic, projected carriers, aliases and CFG joins are not origins.
    fn promoted_option_constant_root(
        &self,
        local: usize,
        depth: usize,
    ) -> Option<(usize, rustc_public::ty::MirConst)> {
        if depth >= MAX_HOPS {
            return None;
        }
        let ty = self.body.locals().get(local)?.ty;
        shared_pointee(ty)?;
        match self.promoted_option_unique_rhs(local)? {
            Rvalue::Use(Operand::Constant(constant), ..) if constant.const_.ty() == ty => {
                Some((local, constant.const_.clone()))
            }
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                if place.projection.is_empty() && self.body.locals().get(place.local)?.ty == ty =>
            {
                self.promoted_option_constant_root(place.local, depth + 1)
            }
            Rvalue::Ref(_, BorrowKind::Shared, place)
                if matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                    && self.body.locals().get(place.local)?.ty == ty =>
            {
                self.promoted_option_constant_root(place.local, depth + 1)
            }
            _ => None,
        }
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;

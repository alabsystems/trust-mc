// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A primitive store to a native Vec buffer does not write the Vec header.
//! This is identity and pointer provenance, not transparent-layout permission.

use rustc_public::mir::mono::Instance;
use rustc_public::mir::{CastKind, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

use super::ChcCtx;
use crate::codegen_ay::chc::codegen_ctx::RefTarget;

impl ChcCtx<'_, '_> {
    /// The whole owner whose buffer a same-element primitive store addresses.
    /// Only whole pointer copies and mutability casts preserve this custody.
    /// Other producers, projected owners and aggregates retain existing refusal.
    pub(in crate::codegen_ay::chc) fn native_vec_primitive_store_owner(
        &self,
        mut pointer: usize,
        target: &RefTarget,
        store_ty: Ty,
    ) -> Option<usize> {
        // Getter semantics must retain transitive unit replacements as well.
        if crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        if !target.projections.is_empty() {
            return None;
        }
        let element = self.resolve_body_ty(store_ty);
        if !matches!(
            element.kind(),
            TyKind::RigidTy(
                RigidTy::Bool
                    | RigidTy::Char
                    | RigidTy::Int(_)
                    | RigidTy::Uint(_)
                    | RigidTy::Float(_)
            )
        ) || element.layout().ok()?.shape().size.bytes() == 0
        {
            return None;
        }
        let owner_ty = self.resolve_body_ty(self.body.locals().get(target.local)?.ty);
        let TyKind::RigidTy(RigidTy::Adt(owner, args)) = owner_ty.kind() else { return None };
        let owner_def = rustc_internal::internal(self.tcx, owner.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            self.tcx,
            owner_def,
            &["vec", "Vec"],
        ) || !matches!(args.0.first(), Some(GenericArgKind::Type(ty))
            if self.resolve_body_ty(*ty) == element)
        {
            return None;
        }
        let raw_element = |ty: Ty| match self.resolve_body_ty(ty).kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Some(self.resolve_body_ty(inner)),
            _ => None,
        };
        let whole = |op: &Operand| match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        let mut seen = std::collections::HashSet::new();
        for _ in 0..16 {
            if !seen.insert(pointer)
                || raw_element(self.body.locals().get(pointer)?.ty) != Some(element)
                || self.local_bytes_may_be_rewritten(pointer)
            {
                return None;
            }
            // A pointee write (*pointer = value) is not a definition of the
            // pointer value. Count whole/direct projected writers only; the
            // byte-rewrite guard above separately rejects aliases that can
            // replace the pointer's own bytes.
            let writes_pointer_value = |place: &rustc_public::mir::Place| {
                place.local == pointer
                    && !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
            };
            let mut producer = None;
            for block in &self.body.blocks {
                for statement in &block.statements {
                    if let StatementKind::Assign(lhs, rhs) = &statement.kind
                        && writes_pointer_value(lhs)
                    {
                        if !lhs.projection.is_empty() || producer.is_some() {
                            return None;
                        }
                        producer = Some((Some(rhs), None));
                    }
                }
                if let TerminatorKind::Call { destination, func, args, .. } = &block.terminator.kind
                    && writes_pointer_value(destination)
                {
                    if !destination.projection.is_empty() || producer.is_some() {
                        return None;
                    }
                    producer = Some((None, Some((func, args))));
                }
            }
            let (rhs, call) = producer?;
            if let Some(rhs) = rhs {
                pointer = match rhs {
                    Rvalue::Use(op, ..) | Rvalue::Cast(CastKind::PtrToPtr, op, _) => whole(op)?,
                    _ => return None,
                };
                continue;
            }
            let (func, args) = call?;
            let [receiver] = args.as_slice() else { return None };
            let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
                func.ty(self.body.locals()).ok()?.kind()
            else {
                return None;
            };
            let instance = Instance::resolve(def, &generics).ok()?;
            if crate::kani_middle::transform::instance_has_unit_stub(&instance) {
                return None;
            }
            let def = rustc_internal::internal(self.tcx, instance.def.def_id());
            if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition(self.tcx, def)
                || !matches!(self.tcx.item_name(def).as_str(), "as_ptr" | "as_mut_ptr")
            {
                return None;
            }
            let implementation = self.tcx.parent(def);
            if !matches!(self.tcx.def_kind(implementation), rustc_hir::def::DefKind::Impl { .. })
                || crate::rustc_compat::impl_opt_trait_ref(self.tcx, implementation).is_some()
            {
                return None;
            }
            let native_self = crate::rustc_compat::skip_normalization(
                self.tcx.type_of(implementation).instantiate_identity(),
            );
            if !matches!(native_self.kind(), rustc_middle::ty::Adt(adt, _) if adt.did() == owner_def)
            {
                return None;
            }
            let signature = instance.ty().kind().fn_sig()?.skip_binder();
            let [input] = signature.inputs() else { return None };
            if !matches!(self.resolve_body_ty(*input).kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                if self.resolve_body_ty(inner) == owner_ty)
                || raw_element(signature.output()) != Some(element)
            {
                return None;
            }
            let receiver = whole(receiver)?;
            if self.local_bytes_may_be_rewritten(receiver) {
                return None;
            }
            let mut borrowed = None;
            for block in &self.body.blocks {
                if matches!(&block.terminator.kind, TerminatorKind::Call { destination, .. }
                    if destination.local == receiver)
                {
                    return None;
                }
                for statement in &block.statements {
                    if let StatementKind::Assign(lhs, rhs) = &statement.kind
                        && lhs.local == receiver
                    {
                        if !lhs.projection.is_empty() || borrowed.is_some() {
                            return None;
                        }
                        let Rvalue::Ref(_, _, place) = rhs else { return None };
                        borrowed = Some(place);
                    }
                }
            }
            let place = borrowed?;
            return (place.local == target.local && place.projection.is_empty())
                .then_some(target.local);
        }
        None
    }
}

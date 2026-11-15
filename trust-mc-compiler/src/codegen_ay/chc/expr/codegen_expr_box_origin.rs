// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Recover a thin Box address only from its actual native allocation producer.

use super::ChcCtx;
use crate::codegen_ay::chc::decl::codegen_types::CodegenTypes;
use crate::codegen_ay::shared::{mono_ty, native_box_raw::native_thin_box_raw_pointer_field};
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

impl ChcCtx<'_, '_> {
    /// A host fat-Box cast peels the native carrier from this exact owner.
    /// Its data word comes from the authenticated allocation birth, never a
    /// projection of the payload value or a same-sort local. Return the
    /// existing validity obligations together with the recovered address.
    pub(in crate::codegen_ay::chc) fn checked_host_native_dyn_box_deref(
        &mut self,
        operand: &Operand,
        target: Ty,
    ) -> Option<super::codegen_expr_box_deref::CheckedBoxDeref> {
        let (carrier, target, origin) = self.host_native_dyn_box_deref_origin(operand, target)?;
        let address =
            Expr::bitvec_const(origin.allocation, 32).concat(Expr::bitvec_const(0u32, 32));
        self.checked_native_box_deref_with_origin(carrier, target, address, Some(&origin))
    }

    pub(in crate::codegen_ay::chc) fn host_native_dyn_box_deref_origin(
        &self,
        operand: &Operand,
        target: Ty,
    ) -> Option<(Ty, Ty, crate::codegen_ay::chc::call::native_dyn_origin::NativeDynOrigin)> {
        if !self.inline_walk_frames.is_empty() || self.native_box_uses_custom_allocator() {
            return None;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
        let [ProjectionElem::Field(0, field)] = place.projection.as_slice() else {
            return None;
        };
        let boxed =
            self.normalized_box_ty(self.resolve_body_ty(self.body.locals().get(place.local)?.ty))?;
        let dynamic =
            crate::codegen_ay::shared::native_box_drop::native_global_box_pointee(self.tcx, boxed)?;
        if !matches!(dynamic.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
            return None;
        }
        let target = self.normalized_box_ty(self.resolve_body_ty(target))?;
        if !matches!(target.kind(), TyKind::RigidTy(RigidTy::RawPtr(inner, _)) if inner == dynamic)
        {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = boxed.kind() else { return None };
        let carrier = mono_ty::field_ty(def.variants().first()?.fields().first()?, &args)?;
        if self.normalized_box_ty(self.resolve_body_ty(*field))?
            != self.normalized_box_ty(carrier)?
            || LayoutOf::new(boxed).field_offset(0)? != 0
            || LayoutOf::new(boxed).size_of()? != LayoutOf::new(carrier).size_of()?
        {
            return None;
        }
        let owner =
            Operand::Copy(rustc_public::mir::Place { local: place.local, projection: vec![] });
        let origin = self.host_native_dyn_origin(&owner)?;
        // A native zero-sized Box has no allocation birth. The constant
        // callable shim has its own closed certificate; it grants no general
        // host payload address through this route.
        if self.get_type_size(origin.concrete)? == 0 {
            return None;
        }
        self.native_box_allocation_is_acyclic(origin.allocation).then_some(())?;
        Some((carrier, target, origin))
    }

    pub(in crate::codegen_ay::chc) fn checked_host_native_thin_box_drop(
        &mut self,
        place: &rustc_public::mir::Place,
    ) -> Option<super::codegen_expr_box_deref::CheckedBoxDeref> {
        if !place.projection.is_empty() {
            return None;
        }
        let boxed =
            self.normalized_box_ty(self.resolve_body_ty(place.ty(self.body.locals()).ok()?))?;
        let pointee = crate::codegen_ay::shared::native_box_raw::native_thin_global_box_pointee(
            self.tcx, boxed,
        )?;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = boxed.kind() else { return None };
        let carrier = mono_ty::field_ty(def.variants().first()?.fields().first()?, &args)?;
        let target =
            Ty::from_rigid_kind(RigidTy::RawPtr(pointee, rustc_public::mir::Mutability::Mut));
        let operand = Operand::Copy(rustc_public::mir::Place {
            local: place.local,
            projection: vec![ProjectionElem::Field(0, carrier)],
        });
        let address = self.host_native_thin_box_address(&operand, target)?;
        self.checked_native_box_deallocation(carrier, target, address)
    }

    /// A user's allocator has effects outside the default allocation model.
    /// A zero-sized Box does not call it.
    pub(in crate::codegen_ay::chc) fn native_box_uses_custom_allocator(&self) -> bool {
        crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(self.tcx)
    }

    pub(in crate::codegen_ay::chc) fn host_native_thin_box_address(
        &self,
        operand: &Operand,
        target: Ty,
    ) -> Option<Expr> {
        // Host local indices have no meaning inside an inline frame.
        if !self.inline_walk_frames.is_empty() {
            return None;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
        let [ProjectionElem::Field(0, field)] = place.projection.as_slice() else {
            return None;
        };
        let boxed =
            self.normalized_box_ty(self.resolve_body_ty(self.body.locals().get(place.local)?.ty))?;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = boxed.kind() else { return None };
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = self.normalized_box_ty(target)?.kind()
        else {
            return None;
        };
        if !def.is_box() || args.0.first() != Some(&GenericArgKind::Type(pointee)) {
            return None;
        }
        let carrier = mono_ty::field_ty(def.variants().first()?.fields().first()?, &args)?;
        if self.normalized_box_ty(*field)? != self.normalized_box_ty(carrier)?
            || LayoutOf::new(boxed).field_offset(0)? != 0
            || LayoutOf::new(boxed).size_of()? != LayoutOf::new(carrier).size_of()?
        {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Adt(raw, raw_args)) = carrier.kind() else { return None };
        native_thin_box_raw_pointer_field(self.tcx, raw, &raw_args)?;
        // Box::new of a ZST uses a dangling pointer rather than an allocation.
        // The legacy allocator model's synthetic object cannot establish its
        // native address or ownership, even when its alignment is sufficient.
        if self.get_type_size(pointee)? == 0 || self.native_box_uses_custom_allocator() {
            return None;
        }
        let allocation =
            self.unique_host_box_birth(place.local, boxed, pointee, &mut Vec::new())?;
        self.native_box_allocation_is_acyclic(allocation).then_some(())?;
        Some(Expr::bitvec_const(allocation, 32).concat(Expr::bitvec_const(0u32, 32)))
    }

    /// Require one whole definition, exact native Box copies, and no exposed
    /// carrier storage. A first producer, same-width value, alias or join does
    /// not establish this value's allocation identity.
    fn unique_host_box_birth(
        &self,
        local: usize,
        boxed: Ty,
        pointee: Ty,
        seen: &mut Vec<usize>,
    ) -> Option<u32> {
        if seen.len() >= 32
            || seen.contains(&local)
            || self.normalized_box_ty(self.resolve_body_ty(self.body.locals().get(local)?.ty))?
                != boxed
        {
            return None;
        }
        seen.push(local);
        let mut source = None;
        let mut allocation = None;
        let mut defined = false;
        let mut budget = 16_384usize;
        for (site, block) in self.body.blocks.iter().enumerate() {
            budget = budget.checked_sub(1)?;
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                if defined || !destination.projection.is_empty() {
                    return None;
                }
                defined = true;
                // assume_init changes the type and transfers this exact native
                // allocation. Payload validity is independently required at
                // the checked call boundary; it is not inferred here.
                let transferred: Option<u32> = {
                    #[cfg(all(trust_toolchain, version("1.101")))]
                    {
                        self.native_initialized_box_birth(func, args, boxed, pointee, seen)
                    }
                    #[cfg(not(all(trust_toolchain, version("1.101"))))]
                    {
                        None
                    }
                };
                if let Some(id) = transferred {
                    allocation = Some(id);
                } else {
                    let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
                        func.ty(self.body.locals()).ok()?.kind()
                    else {
                        return None;
                    };
                    let initialized = args.len() == 1
                        && self.tcx.is_diagnostic_item(
                            rustc_span::sym::box_new,
                            rustc_internal::internal(self.tcx, def.def_id()),
                        )
                        && self.detect_stub(func)
                            == Some(crate::codegen_ay::stubs::StubKind::BoxNew)
                        && self.normalized_box_ty(
                            self.resolve_body_ty(args[0].ty(self.body.locals()).ok()?),
                        )? == pointee;
                    let uninitialized = if args.is_empty()
                        && let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                            func.ty(self.body.locals()).ok()?.kind()
                        && let Ok(instance) = rustc_public::mir::mono::Instance::resolve(def, &args)
                    {
                        crate::codegen_ay::native_box_new_uninit(self.tcx, &instance)
                            .is_some_and(|native| native.boxed == boxed && native.maybe == pointee)
                    } else {
                        false
                    };
                    if !initialized && !uninitialized {
                        return None;
                    }
                    let id = *self.known_alloc_ids.get(&local)?;
                    if self.heap_state.alloc_block.get(&id) != Some(&site) {
                        return None;
                    }
                    allocation = Some(id);
                }
            }
            for statement in &block.statements {
                budget = budget.checked_sub(1)?;
                if let StatementKind::Assign(destination, rhs) = &statement.kind {
                    if matches!(rhs, Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                        if place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref)))
                    {
                        return None;
                    }
                    if destination.local != local {
                        continue;
                    }
                    if defined || !destination.projection.is_empty() {
                        return None;
                    }
                    defined = true;
                    let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rhs else {
                        return None;
                    };
                    if !place.projection.is_empty() {
                        return None;
                    }
                    source = Some(place.local);
                }
            }
        }
        allocation.or_else(|| self.unique_host_box_birth(source?, boxed, pointee, seen))
    }

    #[cfg(all(trust_toolchain, version("1.101")))]
    fn native_initialized_box_birth(
        &self,
        func: &Operand,
        args: &[Operand],
        boxed: Ty,
        pointee: Ty,
        seen: &mut Vec<usize>,
    ) -> Option<u32> {
        use crate::codegen_ay::shared::native_box_init::{NativeInitKind, native_init_boundary};
        let [Operand::Copy(input) | Operand::Move(input)] = args else {
            return None;
        };
        if !input.projection.is_empty() {
            return None;
        }
        let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func.ty(self.body.locals()).ok()?.kind()
        else {
            return None;
        };
        let instance = rustc_public::mir::mono::Instance::resolve(def, &substs).ok()?;
        let boundary = native_init_boundary(self.tcx, &instance)?;
        if !matches!(boundary.kind, NativeInitKind::BoxSized)
            || boundary.output != boxed
            || boundary.payload != pointee
            || input.ty(self.body.locals()).ok()? != boundary.input
        {
            return None;
        }
        let native = crate::codegen_ay::shared::native_box_uninit::native_uninit_box(
            self.tcx,
            boundary.input,
        )?;
        if native.payload != pointee {
            return None;
        }
        self.unique_host_box_birth(input.local, boundary.input, native.maybe, seen)
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Positive origins from actual native Box allocation and unsizing producers.

use super::{ChcCtx, NativeDynOrigin, plain};
use crate::codegen_ay::shared::native_box_raw::native_dyn_pointer_pointee;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::{Body, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};

pub(super) fn definition(body: &Body, local: usize) -> Option<&Rvalue> {
    let mut definition = None;
    let mut budget = 16_384usize;
    for block in &body.blocks {
        budget = budget.checked_sub(1)?;
        if matches!(&block.terminator.kind, TerminatorKind::Call { destination, .. } if destination.local == local)
        {
            return None;
        }
        for statement in &block.statements {
            budget = budget.checked_sub(1)?;
            if let StatementKind::Assign(place, rhs) = &statement.kind
                && place.local == local
            {
                if !place.projection.is_empty() || definition.is_some() {
                    return None;
                }
                definition = Some(rhs);
            }
        }
    }
    definition
}

impl ChcCtx<'_, '_> {
    fn native_box_payload(&self, ty: Ty) -> Option<Ty> {
        let ty = self.normalized_box_ty(self.resolve_body_ty(ty))?;
        crate::codegen_ay::shared::native_box_drop::native_global_box_pointee(self.tcx, ty)
    }

    pub(in crate::codegen_ay::chc) fn native_dyn_origin_matches(
        &self,
        origin: &NativeDynOrigin,
        ty: Ty,
    ) -> bool {
        self.normalized_box_ty(self.resolve_body_ty(ty))
            .and_then(|ty| native_dyn_pointer_pointee(self.tcx, ty))
            == Some(origin.dynamic)
    }

    /// Only a unique actual allocator result can recover an original address.
    /// No element bits or first-producer pointer tracing authorize recovery.
    fn host_box_allocation(&self, local: usize, seen: &mut Vec<usize>) -> Option<(u32, bool)> {
        if local <= self.body.arg_locals().len()
            || seen.len() >= 32
            || seen.contains(&local)
            || self.host_native_dyn_unmodeled_exposure(local)
        {
            return None;
        }
        seen.push(local);
        let payload = self.native_box_payload(self.body.locals().get(local)?.ty)?;
        let mut source = None;
        let mut allocation = None;
        let mut budget = 16_384usize;
        for (site, block) in self.body.blocks.iter().enumerate() {
            budget = budget.checked_sub(1)?;
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                if !destination.projection.is_empty()
                    || allocation.is_some()
                    || source.is_some()
                    || !self.native_box_new(func)
                    || args.len() != 1
                    || self.normalized_box_ty(args.first()?.ty(self.body.locals()).ok()?)?
                        != payload
                {
                    return None;
                }
                let item = match payload.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                    _ => payload,
                };
                // The callable shortcut may omit a reference-to-function-item
                // shim only for an actual compiler constant of that exact type.
                // Captures and arbitrary runtime reference payloads need reads
                // and validity checks that this certificate does not replace.
                let constant_callable = matches!(item.kind(), TyKind::RigidTy(RigidTy::FnDef(..)))
                    && args.first().is_some_and(|arg| {
                        self.constant_callable_operand(arg, payload, &mut Vec::new())
                    });
                allocation =
                    self.known_alloc_ids.get(&local).copied().map(|id| (id, constant_callable));
                if self.heap_state.alloc_block.get(&allocation?.0) != Some(&site) {
                    return None;
                }
            }
            for statement in &block.statements {
                budget = budget.checked_sub(1)?;
                if let StatementKind::Assign(place, rhs) = &statement.kind
                    && place.local == local
                {
                    if !place.projection.is_empty() || allocation.is_some() || source.is_some() {
                        return None;
                    }
                    let Rvalue::Use(operand, ..) = rhs else { return None };
                    let place = plain(operand)?;
                    if !place.projection.is_empty() {
                        return None;
                    }
                    if self.native_box_payload(self.body.locals().get(place.local)?.ty)? != payload
                    {
                        return None;
                    }
                    source = Some(place.local);
                }
            }
        }
        allocation.or_else(|| self.host_box_allocation(source?, seen))
    }

    /// The native frontend reborrows a promoted `&fn item` through MIR locals
    /// before Box::new. Follow only exact copies and genuine reborrows of a
    /// compiler constant; a cast, call result, projection or exposed reference
    /// carrier is not a constant function-item payload.
    fn constant_callable_operand(
        &self,
        operand: &Operand,
        expected: Ty,
        seen: &mut Vec<usize>,
    ) -> bool {
        if operand.ty(self.body.locals()).ok().and_then(|ty| self.normalized_box_ty(ty))
            != Some(expected)
        {
            return false;
        }
        if let Operand::Constant(constant) = operand {
            return match expected.kind() {
                TyKind::RigidTy(RigidTy::FnDef(..)) => true,
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    if matches!(inner.kind(), TyKind::RigidTy(RigidTy::FnDef(..))) =>
                {
                    let Some(bytes) =
                        crate::codegen_ay::shared::const_pointer::const_bytes(&constant.const_)
                    else {
                        return false;
                    };
                    crate::codegen_ay::shared::const_pointer::fixed_pointee(
                        self.tcx, &bytes, 0, inner,
                    )
                    .is_some()
                        && self.get_type_size(inner) == Some(0)
                        && self.get_type_align(inner) == Some(1)
                }
                _ => false,
            };
        }
        let Some(place) = plain(operand) else { return false };
        if !place.projection.is_empty() || seen.len() >= 32 || seen.contains(&place.local) {
            return false;
        }
        seen.push(place.local);
        let mut budget = 16_384usize;
        if self.body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
            let Some(left) = budget.checked_sub(1) else { return true };
            budget = left;
            matches!(&statement.kind, StatementKind::Assign(_, Rvalue::Ref(_, _, source) | Rvalue::AddressOf(_, source))
                if source.local == place.local && !matches!(source.projection.first(), Some(ProjectionElem::Deref)))
        }) { return false; }
        match definition(self.body, place.local) {
            Some(Rvalue::Use(source, ..)) => self.constant_callable_operand(source, expected, seen),
            Some(Rvalue::Ref(_, _, source))
                if matches!(source.projection.as_slice(), [ProjectionElem::Deref]) =>
            {
                self.constant_callable_operand(
                    &Operand::Copy(rustc_public::mir::Place {
                        local: source.local,
                        projection: vec![],
                    }),
                    expected,
                    seen,
                )
            }
            _ => false,
        }
    }

    fn native_box_new(&self, operand: &Operand) -> bool {
        use rustc_public::CrateDef;
        let Some(ty) = operand.ty(self.body.locals()).ok() else { return false };
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind() else { return false };
        self.tcx.is_diagnostic_item(
            rustc_span::sym::box_new,
            rustc_public::rustc_internal::internal(self.tcx, def.def_id()),
        ) && self.detect_stub(operand) == Some(crate::codegen_ay::stubs::StubKind::BoxNew)
    }

    fn from_native_unsize(
        &self,
        body: &Body,
        local: usize,
        rhs: &Rvalue,
        frame: u64,
    ) -> Option<NativeDynOrigin> {
        let Rvalue::Cast(
            rustc_public::mir::CastKind::PointerCoercion(
                rustc_public::mir::PointerCoercion::Unsize,
            ),
            operand,
            target,
        ) = rhs
        else {
            return None;
        };
        let dynamic = self.native_box_payload(*target)?;
        if !matches!(dynamic.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
            return None;
        }
        let source_box = self.normalized_box_ty(operand.ty(body.locals()).ok()?)?;
        let concrete = self.native_box_payload(source_box)?;
        let TyKind::RigidTy(RigidTy::Adt(source_def, source_args)) = source_box.kind() else {
            return None;
        };
        let carrier = crate::codegen_ay::shared::mono_ty::field_ty(
            source_def.variants().first()?.fields().first()?,
            &source_args,
        )?;
        if !concrete.layout().ok()?.shape().is_sized() {
            return None;
        }
        let source = plain(operand)?;
        if !source.projection.is_empty() {
            return None;
        }
        // Inline allocations whose allocator contract has not been retained
        // are not upgraded by a concrete type or a matching pointer width.
        let (allocation, constant_callable) = if frame == 0 {
            self.host_box_allocation(source.local, &mut Vec::new())?
        } else {
            return None;
        };
        let vtable =
            super::super::dyn_coercion::resolve_dyn_target_vtable_id(self, dynamic, concrete)?;
        Some(NativeDynOrigin {
            dynamic,
            concrete,
            carrier,
            vtable,
            allocation,
            constant_callable,
            origin: (frame, local),
        })
    }

    pub(in crate::codegen_ay::chc) fn host_native_dyn_origin(
        &self,
        operand: &Operand,
    ) -> Option<NativeDynOrigin> {
        let place = plain(operand)?;
        if !place.projection.is_empty() {
            return None;
        }
        self.host_native_dyn_local(place.local, &mut Vec::new())
    }

    fn host_native_dyn_local(
        &self,
        local: usize,
        seen: &mut Vec<usize>,
    ) -> Option<NativeDynOrigin> {
        if local <= self.body.arg_locals().len()
            || seen.len() >= 32
            || seen.contains(&local)
            || self.host_native_dyn_unmodeled_exposure(local)
        {
            return None;
        }
        seen.push(local);
        let rhs = definition(self.body, local)?;
        let origin = self.from_native_unsize(self.body, local, rhs, 0).or_else(|| {
            let Rvalue::Use(operand, ..) = rhs else { return None };
            let source = plain(operand)?;
            if !source.projection.is_empty() {
                return None;
            }
            self.host_native_dyn_local(source.local, seen)
        })?;
        self.native_dyn_origin_matches(&origin, self.body.locals().get(local)?.ty).then_some(origin)
    }

    /// Exhaust the actual whole-value definitions of this native owner. This
    /// is a closed set of typed births, never the trait's global implementors.
    /// Each vtable must select one allocation: same-type allocation joins
    /// require a data-address phi that this certificate does not fabricate.
    pub(in crate::codegen_ay::chc) fn host_native_dyn_drop_origins(
        &self,
        operand: &Operand,
    ) -> Option<Vec<NativeDynOrigin>> {
        let place = plain(operand)?;
        if !place.projection.is_empty() {
            return None;
        }
        let mut origins = Vec::new();
        self.collect_native_dyn_drop_origins(
            place.local,
            &mut Vec::new(),
            &mut 16_384,
            &mut origins,
        )?;
        (!origins.is_empty()).then_some(origins)
    }

    fn collect_native_dyn_drop_origins(
        &self,
        local: usize,
        path: &mut Vec<usize>,
        budget: &mut usize,
        origins: &mut Vec<NativeDynOrigin>,
    ) -> Option<()> {
        if local <= self.body.arg_locals().len()
            || path.len() >= 32
            || path.contains(&local)
            || self.host_native_dyn_unmodeled_exposure(local)
        {
            return None;
        }
        let ty = self.normalized_box_ty(self.resolve_body_ty(self.body.locals().get(local)?.ty))?;
        let dynamic = self.native_box_payload(ty)?;
        if !matches!(dynamic.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
            return None;
        }
        path.push(local);
        let mut defined = false;
        for block in &self.body.blocks {
            *budget = budget.checked_sub(1)?;
            if matches!(&block.terminator.kind,TerminatorKind::Call{destination,..} if destination.local==local)
            {
                return None;
            }
            for statement in &block.statements {
                *budget = budget.checked_sub(1)?;
                let StatementKind::Assign(place, rhs) = &statement.kind else {
                    continue;
                };
                if place.local != local {
                    continue;
                }
                if !place.projection.is_empty() {
                    return None;
                }
                defined = true;
                if let Some(origin) = self.from_native_unsize(self.body, local, rhs, 0) {
                    if origin.dynamic != dynamic {
                        return None;
                    }
                    if let Some(previous) =
                        origins.iter().find(|previous| previous.vtable == origin.vtable)
                    {
                        if previous.dynamic != origin.dynamic
                            || previous.concrete != origin.concrete
                            || previous.carrier != origin.carrier
                            || previous.allocation != origin.allocation
                        {
                            return None;
                        }
                    } else {
                        if origins.len() >= 64 {
                            return None;
                        }
                        origins.push(origin);
                    }
                } else {
                    let Rvalue::Use(source, ..) = rhs else {
                        return None;
                    };
                    let source = plain(source)?;
                    if !source.projection.is_empty()
                        || self.normalized_box_ty(
                            self.resolve_body_ty(self.body.locals().get(source.local)?.ty),
                        )? != ty
                    {
                        return None;
                    }
                    self.collect_native_dyn_drop_origins(source.local, path, budget, origins)?;
                }
            }
        }
        path.pop();
        defined.then_some(())
    }
}

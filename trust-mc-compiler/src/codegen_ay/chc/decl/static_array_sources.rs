// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Closed producers for borrowed references into static arrays. Facts describe
//! origins only; the actual address always travels in a CHC relation slot.
use super::ChcCtx;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstTarget, TargetKey};
use crate::rustc_public_bridge::IndexedVal;
use rustc_public::CrateDef;
use rustc_public::mir::{
    CastKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use std::collections::HashSet;

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn borrowed_slice_item_ty(&self, mut ty: Ty) -> Option<Ty> {
        while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() {
            ty = inner;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(
            self.tcx,
            rustc_public::rustc_internal::internal(self.tcx, def.def_id()),
        ) || !def.name().contains("slice")
            || !matches!(def.name().rsplit("::").next(), Some("Iter"))
        {
            return None;
        }
        let elem = args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })?;
        // This location model is for the Atomic scalar store/RMW lane. Other
        // interior-mutability families keep their existing guards and models.
        let TyKind::RigidTy(RigidTy::Adt(atomic, atomic_args)) = elem.kind() else { return None };
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(
            self.tcx,
            rustc_public::rustc_internal::internal(self.tcx, atomic.def_id()),
        ) || !atomic.name().contains("sync::atomic")
            || atomic.name().rsplit("::").next() != Some("Atomic")
        {
            return None;
        }
        let scalar = atomic_args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })?;
        matches!(scalar.kind(), TyKind::RigidTy(RigidTy::Uint(_) | RigidTy::Int(_) | RigidTy::Bool))
            .then_some(elem)
    }

    pub(in crate::codegen_ay::chc) fn core_method(&self, op: &Operand, method: &str) -> bool {
        matches!(op.ty(self.body.locals()).ok().map(|ty| ty.kind()),
            Some(TyKind::RigidTy(RigidTy::FnDef(def, _)))
                if crate::kani_middle::std_abstraction::is_sysroot_core_definition(
                    self.tcx,
                    rustc_public::rustc_internal::internal(self.tcx, def.def_id()),
                ) && def.name().rsplit("::").next() == Some(method))
    }

    /// Borrowed iterator storage may be mutated only by its next operation.
    /// Reject adapters, opaque consumers, aggregates, raw access and partial
    /// assignments rather than pretending they preserve ptr/len/cursor.
    pub(in crate::codegen_ay::chc) fn static_iterator_uses_closed(&self) -> bool {
        let carries = |op: &Operand| {
            op.ty(self.body.locals())
                .ok()
                .is_some_and(|ty| self.borrowed_slice_item_ty(ty).is_some())
        };
        for block in &self.body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rhs) => {
                        let mut used = HashSet::new();
                        Self::collect_rvalue_used_locals(rhs, &mut used);
                        if used.iter().any(|i| {
                            self.borrowed_slice_item_ty(self.body.locals()[*i].ty).is_some()
                        }) && !matches!(rhs, Rvalue::Use(..) | Rvalue::Ref(..))
                        {
                            return false;
                        }
                        if self.borrowed_slice_item_ty(self.body.locals()[lhs.local].ty).is_some()
                            && !lhs.projection.is_empty()
                        {
                            return false;
                        }
                        match rhs {
                            Rvalue::Use(op, ..)
                                if carries(op)
                                    && (!lhs.projection.is_empty()
                                        || self
                                            .borrowed_slice_item_ty(
                                                self.body.locals()[lhs.local].ty,
                                            )
                                            .is_none()
                                        || lhs.local == 0) =>
                            {
                                return false;
                            }
                            Rvalue::Ref(_, _, p)
                                if self
                                    .borrowed_slice_item_ty(self.body.locals()[p.local].ty)
                                    .is_some()
                                    && !lhs.projection.is_empty() =>
                            {
                                return false;
                            }
                            Rvalue::Aggregate(_, ops) if ops.iter().any(carries) => return false,
                            Rvalue::Cast(_, op, _) if carries(op) => return false,
                            Rvalue::AddressOf(_, p)
                                if self
                                    .borrowed_slice_item_ty(self.body.locals()[p.local].ty)
                                    .is_some() =>
                            {
                                return false;
                            }
                            _ => {}
                        }
                    }
                    StatementKind::Intrinsic(_) => return false,
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    if args.iter().any(carries)
                        && self.core_method(func, "next")
                        && self.static_next_sources(destination.local, 16).is_none()
                    {
                        return false;
                    }
                    if args.iter().any(carries)
                        && !(args.len() == 1
                            && (self.core_method(func, "next")
                                || self.core_method(func, "into_iter")))
                    {
                        return false;
                    }
                    if self
                        .borrowed_slice_item_ty(self.body.locals()[destination.local].ty)
                        .is_some()
                        && !destination.projection.is_empty()
                    {
                        return false;
                    }
                }
                TerminatorKind::InlineAsm { .. } => return false,
                _ => {}
            }
        }
        true
    }

    pub(in crate::codegen_ay::chc) fn borrowed_static_next_sources(
        &self,
        local: usize,
    ) -> Option<HashSet<TargetKey>> {
        if self.track_level < crate::args::ChcTrackLevel::Mem
            || self.int_lift
            || !self.static_iterator_uses_closed()
        {
            return None;
        }
        self.static_next_sources(local, 16)
    }

    fn static_next_sources(&self, local: usize, depth: usize) -> Option<HashSet<TargetKey>> {
        let depth = depth.checked_sub(1)?;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = self.body.locals().get(local)?.ty.kind()
        else {
            return None;
        };
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(
            self.tcx,
            rustc_public::rustc_internal::internal(self.tcx, def.def_id()),
        ) || def.trimmed_name() != "Option"
        {
            return None;
        }
        let GenericArgKind::Type(payload) = args.0.first()? else { return None };
        let TyKind::RigidTy(RigidTy::Ref(_, item, _)) = payload.kind() else { return None };
        if !self.ty_has_interior_mut(item) || local <= self.body.arg_locals().len() {
            return None;
        }
        let mut sources = HashSet::new();
        let mut seen = false;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, _) if lhs.local == local => return None,
                    StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                        return None;
                    }
                    StatementKind::Assign(_, Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p))
                        if p.local == local =>
                    {
                        return None;
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                if !destination.projection.is_empty()
                    || args.len() != 1
                    || !self.core_method(func, "next")
                    || self.borrowed_slice_item_ty(args[0].ty(self.body.locals()).ok()?)? != item
                {
                    return None;
                }
                sources.extend(self.static_iterator_sources(&args[0], depth)?);
                seen = true;
            }
        }
        (seen && !sources.is_empty()).then_some(sources)
    }

    pub(in crate::codegen_ay::chc) fn static_iterator_sources(
        &self,
        op: &Operand,
        depth: usize,
    ) -> Option<HashSet<TargetKey>> {
        let depth = depth.checked_sub(1)?;
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
        if !p.projection.is_empty() || p.local <= self.body.arg_locals().len() {
            return None;
        }
        self.borrowed_slice_item_ty(self.body.locals().get(p.local)?.ty)?;
        let mut sources = HashSet::new();
        let mut seen = false;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.local == p.local
                {
                    if !lhs.projection.is_empty() {
                        return None;
                    }
                    let source = match rhs {
                        Rvalue::Use(op, ..) => self.static_iterator_sources(op, depth)?,
                        Rvalue::Ref(_, _, base) if base.projection.is_empty() => {
                            self.static_iterator_sources(&Operand::Copy(base.clone()), depth)?
                        }
                        _ => return None,
                    };
                    sources.extend(source);
                    seen = true;
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == p.local
            {
                if !destination.projection.is_empty() || args.len() != 1 {
                    return None;
                }
                let source = if self.core_method(func, "iter") {
                    self.static_base_pointer_sources(&args[0], depth, false)?
                } else if self.core_method(func, "into_iter") {
                    self.static_iterator_sources(&args[0], depth)?
                } else {
                    return None;
                };
                let item = self.borrowed_slice_item_ty(self.body.locals()[p.local].ty)?;
                for key in &source {
                    let TargetKey::Static(def) = key else { return None };
                    let TyKind::RigidTy(RigidTy::Array(elem, _)) = def.ty().kind() else {
                        return None;
                    };
                    if !super::static_path::same_ty_modulo_regions(elem, item) {
                        return None;
                    }
                }
                sources.extend(source);
                seen = true;
            }
        }
        (seen && !sources.is_empty()).then_some(sources)
    }

    pub(in crate::codegen_ay::chc) fn borrowed_static_next_bound(
        &self,
        local: usize,
    ) -> Option<u64> {
        self.borrowed_static_next_sources(local)?
            .iter()
            .map(|key| {
                let TargetKey::Static(def) = key else { return None };
                let TyKind::RigidTy(RigidTy::Array(_, n)) = def.ty().kind() else { return None };
                n.eval_target_usize().ok()
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .max()
    }

    pub(in crate::codegen_ay::chc) fn static_pointer_sources(
        &self,
        op: &Operand,
        depth: usize,
    ) -> Option<HashSet<TargetKey>> {
        self.static_base_pointer_sources(op, depth, true)
    }

    fn static_base_pointer_sources(
        &self,
        op: &Operand,
        depth: usize,
        allow_item: bool,
    ) -> Option<HashSet<TargetKey>> {
        let depth = depth.checked_sub(1)?;
        if let Operand::Constant(c) = op {
            if !matches!(
                c.const_.ty().kind(),
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
            ) {
                return None;
            }
            let bytes = const_pointer::const_bytes(&c.const_)?;
            let ptr = bytes.stored_pointer(0)?;
            let ConstTarget::Static(def) = ptr.kind() else { return None };
            let TyKind::RigidTy(RigidTy::Array(_, len)) = def.ty().kind() else { return None };
            let len = len.eval_target_usize().ok()?;
            return (len > 0 && len <= 256).then(|| HashSet::from([TargetKey::Static(def)]));
        }
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
        if matches!(
            p.projection.as_slice(),
            [ProjectionElem::Downcast(variant), ProjectionElem::Field(0, _)] if variant.to_index() == 1
        ) {
            return if allow_item && self.static_iterator_uses_closed() {
                self.static_next_sources(p.local, depth)
            } else {
                None
            };
        }
        if !p.projection.is_empty() || p.local == 0 || p.local <= self.body.arg_locals().len() {
            return None;
        }
        let mut sources = HashSet::new();
        let mut seen = false;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(_, Rvalue::Ref(_, _, b) | Rvalue::AddressOf(_, b))
                        if b.local == p.local
                            && !matches!(b.projection.first(), Some(ProjectionElem::Deref)) =>
                    {
                        return None;
                    }
                    StatementKind::SetDiscriminant { place, .. } if place.local == p.local => {
                        return None;
                    }
                    _ => {}
                }
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.local == p.local
                {
                    if !lhs.projection.is_empty() {
                        return None;
                    }
                    let source = match rhs {
                        Rvalue::Use(op, ..) => {
                            self.static_base_pointer_sources(op, depth, allow_item)?
                        }
                        Rvalue::Cast(CastKind::PtrToPtr, op, _) => {
                            self.static_base_pointer_sources(op, depth, allow_item)?
                        }
                        Rvalue::Cast(
                            CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
                            op,
                            target,
                        ) => {
                            let (
                                TyKind::RigidTy(RigidTy::Ref(_, a, _)),
                                TyKind::RigidTy(RigidTy::Ref(_, b, _)),
                            ) = (op.ty(self.body.locals()).ok()?.kind(), target.kind())
                            else {
                                return None;
                            };
                            let (
                                TyKind::RigidTy(RigidTy::Array(a, _)),
                                TyKind::RigidTy(RigidTy::Slice(b)),
                            ) = (a.kind(), b.kind())
                            else {
                                return None;
                            };
                            if !super::static_path::same_ty_modulo_regions(a, b) {
                                return None;
                            }
                            self.static_base_pointer_sources(op, depth, allow_item)?
                        }
                        Rvalue::Ref(_, _, b) | Rvalue::AddressOf(_, b) => {
                            let [ProjectionElem::Deref, rest @ ..] = b.projection.as_slice() else {
                                return None;
                            };
                            if !rest.iter().all(|e| {
                                matches!(
                                    e,
                                    ProjectionElem::Field(..)
                                        | ProjectionElem::Index(_)
                                        | ProjectionElem::ConstantIndex { .. }
                                )
                            }) {
                                return None;
                            }
                            self.static_base_pointer_sources(
                                &Operand::Copy(Place { local: b.local, projection: vec![] }),
                                depth,
                                allow_item,
                            )?
                        }
                        _ => return None,
                    };
                    sources.extend(source);
                    seen = true;
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { destination, .. } if destination.local == p.local => {
                    return None;
                }
                TerminatorKind::InlineAsm { .. } => return None,
                _ => {}
            }
        }
        (seen && !sources.is_empty()).then_some(sources)
    }
}

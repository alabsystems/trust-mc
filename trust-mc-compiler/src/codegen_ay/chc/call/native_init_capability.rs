// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deferred allocation provides storage, never initialized T values. Until a
//! general initialized-byte/provenance plane covers raw accesses, admit only
//! the closed native Box initialization/transfer protocol and empty drop.

use super::{
    ChcCtx,
    native_init_custody::{operands, place},
};
use crate::codegen_ay::shared::{
    mono_ty,
    native_box_init::native_init_boundary,
    native_box_raw::{native_bmc_box_drop_is_modeled, native_bmc_box_drop_value},
    native_box_uninit::native_uninit_box,
};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::mir::{
    CastKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind, mono::Instance,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::HashSet;

impl ChcCtx<'_, '_> {
    pub(super) fn native_uninit_allocation_custody(
        &self,
        local: usize,
        address: &Expr,
    ) -> Option<HashSet<usize>> {
        if !self.inline_walk_frames.is_empty() || crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        let Some(boxed) = self.body.locals().get(local).map(|l| l.ty) else {
            return None;
        };
        let Some(native) = native_uninit_box(self.tcx, boxed) else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = boxed.kind() else {
            return None;
        };
        let Some(carrier) = def
            .variants()
            .first()
            .and_then(|v| v.fields().first().and_then(|f| mono_ty::field_ty(f, &args)))
        else {
            return None;
        };
        let target =
            Ty::from_rigid_kind(RigidTy::RawPtr(native.maybe, rustc_public::mir::Mutability::Mut));
        let mut owners = HashSet::new();
        let mut budget = 16_384usize;
        for (index, decl) in self.body.locals().iter().enumerate() {
            let Some(left) = budget.checked_sub(1) else {
                return None;
            };
            budget = left;
            if decl.ty != boxed {
                continue;
            }
            let op = Operand::Copy(Place {
                local: index,
                projection: vec![ProjectionElem::Field(0, carrier)],
            });
            if self.host_native_thin_box_address(&op, target).as_ref() == Some(address) {
                owners.insert(index);
            }
        }
        if !owners.contains(&local) {
            return None;
        }
        let mut pointers = Vec::new();
        let mut stores = Vec::new();
        for (site, block) in self.body.blocks.iter().enumerate() {
            let Some(left) = budget.checked_sub(1) else {
                return None;
            };
            budget = left;
            match &block.terminator.kind {
                TerminatorKind::InlineAsm { .. } => return None,
                TerminatorKind::Call { func, args, destination, .. } => {
                    if owners.contains(&destination.local) && site != self.current_encode_bb {
                        return None;
                    }
                    if args.iter().any(|op| place(op).is_some_and(|p| owners.contains(&p.local))) {
                        let Ok(ty) = func.ty(self.body.locals()) else {
                            return None;
                        };
                        let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = ty.kind() else {
                            return None;
                        };
                        let Ok(instance) = Instance::resolve(def, &substs) else {
                            return None;
                        };
                        let allowed = native_init_boundary(self.tcx, &instance)
                            .is_some_and(|b| b.input == boxed)
                            || native_bmc_box_drop_value(self.tcx, &instance) == Some(boxed);
                        if !allowed
                            || !matches!(args.as_slice(),[Operand::Copy(p)|Operand::Move(p)] if p.projection.is_empty()&&owners.contains(&p.local))
                        {
                            return None;
                        }
                    }
                }
                TerminatorKind::Drop { place: p, .. } if owners.contains(&p.local) => {
                    if !p.projection.is_empty() || !native_bmc_box_drop_is_modeled(self.tcx, boxed)
                    {
                        return None;
                    }
                }
                TerminatorKind::Return if owners.contains(&0) => return None,
                _ => {}
            }
            for statement in &block.statements {
                let Some(left) = budget.checked_sub(1) else {
                    return None;
                };
                budget = left;
                match &statement.kind {
                    // This capability grants no untracked byte-copy, assembly
                    // or other opaque memory effects, even before transfer.
                    StatementKind::Intrinsic(_) => return None,
                    StatementKind::SetDiscriminant { place: p, .. }
                        if owners.contains(&p.local) =>
                    {
                        return None;
                    }
                    StatementKind::Assign(lhs, rhs) => {
                        if owners.contains(&lhs.local)
                            && (!lhs.projection.is_empty()
                                || !matches!(rhs,Rvalue::Use(op,..) if place(op).is_some_and(|p|p.projection.is_empty()&&owners.contains(&p.local))))
                        {
                            return None;
                        }
                        if matches!(rhs,Rvalue::Ref(_,_,p)|Rvalue::AddressOf(_,p)|Rvalue::Reborrow(_,_,p)|Rvalue::CopyForDeref(p)|Rvalue::Discriminant(p)|Rvalue::Len(p) if owners.contains(&p.local))
                        {
                            return None;
                        }
                        if operands(rhs).is_some_and(|ops| {
                            ops.iter()
                                .any(|op| place(op).is_some_and(|p| owners.contains(&p.local)))
                        }) {
                            match rhs {
                                Rvalue::Use(op, ..)
                                    if lhs.projection.is_empty()
                                        && owners.contains(&lhs.local)
                                        && place(op).is_some_and(|p| {
                                            p.projection.is_empty() && owners.contains(&p.local)
                                        }) => {}
                                Rvalue::Cast(CastKind::BoxDerefTransmute, op, actual)
                                    if lhs.projection.is_empty()
                                        && self
                                            .native_init_pointer_owner(lhs.local)
                                            .is_some_and(|p| owners.contains(&p.local))
                                        && self
                                            .host_native_thin_box_address(op, *actual)
                                            .as_ref()
                                            == Some(address) =>
                                {
                                    pointers.push(lhs.local)
                                }
                                _ => return None,
                            }
                        }
                        if matches!(
                            lhs.projection.as_slice(),
                            [
                                ProjectionElem::Deref,
                                ProjectionElem::Field(1, _),
                                ProjectionElem::Field(0, _)
                            ]
                        ) && self
                            .native_init_pointer_owner(lhs.local)
                            .is_some_and(|p| owners.contains(&p.local))
                        {
                            stores.push(lhs.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        if pointers.len() > 32 || stores.len() > 32 {
            return None;
        }
        // No derived payload pointers: only typed copies, a checked unsafe
        // consumer (which independently requires initialization), or empty
        // drop remain. A raw pointer protocol must close every pointer use.
        let closed = pointers.into_iter().all(|pointer| {
            self.native_init_pointer_is_closed(pointer, None, address)
                || stores
                    .iter()
                    .any(|store| self.native_init_pointer_is_closed(pointer, Some(store), address))
        });
        if !closed {
            return None;
        }
        let mut authorized = owners.clone();
        for index in 0..self.body.locals().len() {
            let Some(left) = budget.checked_sub(1) else {
                return None;
            };
            budget = left;
            if self.native_init_pointer_owner(index).is_some_and(|p| owners.contains(&p.local)) {
                authorized.insert(index);
            }
        }
        Some(authorized)
    }
}

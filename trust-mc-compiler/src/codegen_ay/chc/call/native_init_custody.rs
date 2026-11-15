// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Checked ownership transfer at the native unsafe initialization boundaries.
//! A certificate is made by a real whole-payload write, not by the helper's
//! unsafe precondition or a later reconstruction of its source locals.

use super::ChcCtx;
use crate::codegen_ay::shared::{mono_ty, native_box_init::native_init_boundary};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    CastKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::HashSet;

pub(super) fn scalar(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)
        )
    )
}
pub(super) fn operands(rhs: &Rvalue) -> Option<Vec<&Operand>> {
    Some(match rhs {
        Rvalue::Use(op, ..)
        | Rvalue::Cast(_, op, _)
        | Rvalue::Repeat(op, _)
        | Rvalue::UnaryOp(_, op) => vec![op],
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => vec![a, b],
        Rvalue::Aggregate(_, values) => values.iter().collect(),
        _ => return None,
    })
}
pub(super) fn place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        _ => None,
    }
}
fn numeric(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_)))
}
fn address_observation(rhs: &Rvalue, pointers: &HashSet<usize>) -> bool {
    matches!(rhs,Rvalue::Cast(CastKind::Transmute|CastKind::PointerExposeAddress,op,target)
        if matches!(target.kind(),TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::Usize)))
        && place(op).is_some_and(|p|p.projection.is_empty()&&pointers.contains(&p.local)))
}

impl ChcCtx<'_, '_> {
    /// Require the genuine compiler-created BoxDerefTransmute producer. A raw
    /// pointer of the same width, a reborrow, or a user cast is not custody.
    pub(super) fn native_init_pointer_owner(&self, local: usize) -> Option<Place> {
        self.native_init_pointer_owner_at(local, &mut Vec::new())
    }
    fn native_init_pointer_owner_at(&self, local: usize, seen: &mut Vec<usize>) -> Option<Place> {
        if seen.len() >= 32 || seen.contains(&local) {
            return None;
        }
        seen.push(local);
        let maybe = match self.body.locals().get(local)?.ty.kind() {
            TyKind::RigidTy(
                RigidTy::RawPtr(inner, _)
                | RigidTy::Ref(_, inner, rustc_public::mir::Mutability::Mut),
            ) => inner,
            _ => return None,
        };
        crate::codegen_ay::shared::native_box_init::native_maybe_uninit_payload(self.tcx, maybe)?;
        let mut found = None;
        let mut budget = 16_384usize;
        for block in &self.body.blocks {
            if matches!(&block.terminator.kind,TerminatorKind::Call{destination,..} if destination.local==local)
            {
                return None;
            }
            for statement in &block.statements {
                budget = budget.checked_sub(1)?;
                let StatementKind::Assign(lhs, rhs) = &statement.kind else {
                    continue;
                };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                if found.is_some() {
                    return None;
                }
                let owner = match rhs {
                    Rvalue::Cast(CastKind::BoxDerefTransmute, op, target) => {
                        if *target != self.body.locals()[local].ty {
                            return None;
                        }
                        let p = place(op)?;
                        let [ProjectionElem::Field(0, _)] = p.projection.as_slice() else {
                            return None;
                        };
                        let owner = Place { local: p.local, projection: vec![] };
                        let native =
                            crate::codegen_ay::shared::native_box_uninit::native_uninit_box(
                                self.tcx,
                                owner.ty(self.body.locals()).ok()?,
                            )?;
                        if native.maybe != maybe {
                            return None;
                        }
                        owner
                    }
                    Rvalue::Use(op, ..) => {
                        let p = place(op)?;
                        if !p.projection.is_empty()
                            || p.ty(self.body.locals()).ok()? != self.body.locals()[local].ty
                        {
                            return None;
                        }
                        self.native_init_pointer_owner_at(p.local, seen)?
                    }
                    Rvalue::Ref(_, rustc_public::mir::BorrowKind::Mut { .. }, p)
                        if p.projection.as_slice() == [ProjectionElem::Deref] =>
                    {
                        if !matches!(self.body.locals()[local].ty.kind(),TyKind::RigidTy(RigidTy::Ref(_,inner,rustc_public::mir::Mutability::Mut)) if inner==maybe)
                            || p.ty(self.body.locals()).ok()? != maybe
                        {
                            return None;
                        }
                        self.native_init_pointer_owner_at(p.local, seen)?
                    }
                    _ => return None,
                };
                found = Some(owner);
            }
        }
        found
    }
    fn native_init_maybe_borrow(
        &self,
        lhs: &Place,
        rhs: &Rvalue,
        pointers: &HashSet<usize>,
    ) -> bool {
        if !lhs.projection.is_empty() {
            return false;
        }
        let Rvalue::Ref(_, rustc_public::mir::BorrowKind::Mut { .. }, p) = rhs else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, maybe, rustc_public::mir::Mutability::Mut)) =
            self.body.locals()[lhs.local].ty.kind()
        else {
            return false;
        };
        p.projection.as_slice() == [ProjectionElem::Deref]
            && pointers.contains(&p.local)
            && p.ty(self.body.locals()).ok() == Some(maybe)
            && crate::codegen_ay::shared::native_box_init::native_maybe_uninit_payload(
                self.tcx, maybe,
            )
            .is_some()
    }

    fn native_init_is_maybe_write_call(&self, func: &Operand) -> bool {
        (|| {
            let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                func.ty(self.body.locals()).ok()?.kind()
            else {
                return None;
            };
            let instance = Instance::resolve(def, &args).ok()?;
            crate::codegen_ay::native_maybe_uninit_write(self.tcx, &instance)
        })()
        .is_some()
    }

    /// The derived payload pointer may only initialize its payload and perform
    /// the compiler's address/null/alignment observations. Any escaping alias,
    /// rebind, call, pointer arithmetic or later dereference closes this lane.
    pub(super) fn native_init_pointer_is_closed(
        &self,
        local: usize,
        store: Option<&Place>,
        address: &Expr,
    ) -> bool {
        let mut pointers = HashSet::from([local]);
        let mut owners = HashSet::new();
        let mut work = 16_384usize;
        // Enumerate every exact typed owner and native derived pointer of this
        // birth, including aliases created after the initializing statement.
        for local in 0..self.body.locals().len() {
            let Some(left) = work.checked_sub(1) else {
                return false;
            };
            work = left;
            let boxed = self.body.locals()[local].ty;
            let Some(native) =
                crate::codegen_ay::shared::native_box_uninit::native_uninit_box(self.tcx, boxed)
            else {
                continue;
            };
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = boxed.kind() else {
                return false;
            };
            let Some(carrier) = def
                .variants()
                .first()
                .and_then(|v| v.fields().first().and_then(|f| mono_ty::field_ty(f, &args)))
            else {
                return false;
            };
            let target = Ty::from_rigid_kind(RigidTy::RawPtr(
                native.maybe,
                rustc_public::mir::Mutability::Mut,
            ));
            let operand =
                Operand::Copy(Place { local, projection: vec![ProjectionElem::Field(0, carrier)] });
            if self.host_native_thin_box_address(&operand, target).as_ref() == Some(address) {
                owners.insert(local);
            }
        }
        for block in &self.body.blocks {
            for statement in &block.statements {
                let Some(left) = work.checked_sub(1) else {
                    return false;
                };
                work = left;
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Cast(CastKind::BoxDerefTransmute, op, target),
                ) = &statement.kind
                    && place(op).is_some_and(|p| owners.contains(&p.local))
                    && self.host_native_thin_box_address(op, *target).as_ref() == Some(address)
                {
                    if !lhs.projection.is_empty() {
                        return false;
                    }
                    pointers.insert(lhs.local);
                }
            }
        }
        loop {
            let mut changed = false;
            for block in &self.body.blocks {
                for statement in &block.statements {
                    let Some(left) = work.checked_sub(1) else {
                        return false;
                    };
                    work = left;
                    let StatementKind::Assign(lhs, rhs) = &statement.kind else {
                        continue;
                    };
                    if matches!(rhs,Rvalue::Use(op,..)|Rvalue::Cast(CastKind::PtrToPtr,op,_) if place(op).is_some_and(|p|p.projection.is_empty()&&pointers.contains(&p.local)))
                        || self.native_init_maybe_borrow(lhs, rhs, &pointers)
                    {
                        if !lhs.projection.is_empty() {
                            return false;
                        }
                        changed |= pointers.insert(lhs.local);
                    }
                }
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                    && self.native_init_is_maybe_write_call(func)
                    && args
                        .first()
                        .and_then(place)
                        .is_some_and(|p| p.projection.is_empty() && pointers.contains(&p.local))
                {
                    if !destination.projection.is_empty() {
                        return false;
                    }
                    changed |= pointers.insert(destination.local);
                }
            }
            if !changed {
                break;
            }
        }
        // Held MIR observes addresses with ptr->usize Transmute. Keep all its
        // numeric descendants closed: no pointer reconstruction or escape.
        let mut numbers = HashSet::new();
        loop {
            let mut changed = false;
            for block in &self.body.blocks {
                for statement in &block.statements {
                    let Some(left) = work.checked_sub(1) else {
                        return false;
                    };
                    work = left;
                    let StatementKind::Assign(lhs, rhs) = &statement.kind else {
                        continue;
                    };
                    if address_observation(rhs, &pointers)
                        || operands(rhs).is_some_and(|ops| {
                            ops.iter()
                                .any(|op| place(op).is_some_and(|p| numbers.contains(&p.local)))
                        })
                    {
                        if !lhs.projection.is_empty() || !numeric(self.body.locals()[lhs.local].ty)
                        {
                            return false;
                        }
                        if !address_observation(rhs, &pointers)
                            && !matches!(
                                rhs,
                                Rvalue::Use(..)
                                    | Rvalue::UnaryOp(..)
                                    | Rvalue::BinaryOp(..)
                                    | Rvalue::CheckedBinaryOp(..)
                                    | Rvalue::Cast(CastKind::IntToInt, _, _)
                            )
                        {
                            return false;
                        }
                        changed |= numbers.insert(lhs.local);
                    }
                    if matches!(rhs,Rvalue::Ref(_,_,p)|Rvalue::AddressOf(_,p)|Rvalue::Reborrow(_,_,p)|Rvalue::CopyForDeref(p)|Rvalue::Discriminant(p)|Rvalue::Len(p) if numbers.contains(&p.local))
                    {
                        return false;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut definitions = HashSet::new();
        let mut consumer = None;
        for (site, block) in self.body.blocks.iter().enumerate() {
            if !super::native_init_observers::supported(&block.terminator.kind, &numbers) {
                return false;
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
                let write = self.native_init_is_maybe_write_call(func)
                    && matches!(args.as_slice(),[receiver,_] if place(receiver).is_some_and(|p|p.projection.is_empty()&&pointers.contains(&p.local)))
                    && args.get(1).is_some_and(|value| {
                        !place(value).is_some_and(|p| {
                            pointers.contains(&p.local) || numbers.contains(&p.local)
                        })
                    });
                if !write
                    && (pointers.contains(&destination.local)
                        || args.iter().any(|op| {
                            place(op).is_some_and(|p| {
                                pointers.contains(&p.local) || numbers.contains(&p.local)
                            })
                        }))
                {
                    return false;
                }
                if args.iter().any(|op| place(op).is_some_and(|p| owners.contains(&p.local))) {
                    let native = (|| {
                        let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                            func.ty(self.body.locals()).ok()?.kind()
                        else {
                            return None;
                        };
                        let instance = Instance::resolve(def, &args).ok()?;
                        native_init_boundary(self.tcx, &instance)
                    })();
                    if native.is_none()
                        || consumer.replace(site).is_some()
                        || !matches!(args.as_slice(),[Operand::Copy(p)|Operand::Move(p)] if p.projection.is_empty()&&owners.contains(&p.local))
                    {
                        return false;
                    }
                }
            }
            if matches!(&block.terminator.kind,TerminatorKind::Drop{place,..} if owners.contains(&place.local))
            {
                return false;
            }
            if matches!(block.terminator.kind, TerminatorKind::Return)
                && (pointers.contains(&0) || numbers.contains(&0))
            {
                return false;
            }
            for statement in &block.statements {
                let Some(left) = work.checked_sub(1) else {
                    return false;
                };
                work = left;
                let StatementKind::Assign(lhs, rhs) = &statement.kind else {
                    continue;
                };
                if matches!(rhs,Rvalue::Ref(_,_,p)|Rvalue::AddressOf(_,p)|Rvalue::Reborrow(_,_,p)|Rvalue::CopyForDeref(p)|Rvalue::Len(p)|Rvalue::Discriminant(p) if owners.contains(&p.local))
                {
                    return false;
                }
                if operands(rhs).is_some_and(|ops| {
                    ops.iter().any(|op| place(op).is_some_and(|p| owners.contains(&p.local)))
                }) {
                    let allowed = match rhs {
                        Rvalue::Use(op, ..) => place(op).is_some_and(|p| {
                            p.projection.is_empty()
                                && owners.contains(&p.local)
                                && lhs.projection.is_empty()
                                && owners.contains(&lhs.local)
                        }),
                        Rvalue::Cast(CastKind::BoxDerefTransmute, op, target) => {
                            self.host_native_thin_box_address(op, *target).as_ref() == Some(address)
                                && lhs.projection.is_empty()
                        }
                        _ => false,
                    };
                    if !allowed {
                        return false;
                    }
                }
                if pointers.contains(&lhs.local) {
                    if lhs.projection.is_empty() {
                        if !definitions.insert(lhs.local) {
                            return false;
                        }
                    } else if Some(lhs) != store {
                        return false;
                    }
                }
                if self.native_init_maybe_borrow(lhs, rhs, &pointers) {
                    continue;
                }
                match rhs {
                    Rvalue::Ref(_, _, p)
                    | Rvalue::AddressOf(_, p)
                    | Rvalue::Reborrow(_, _, p)
                    | Rvalue::CopyForDeref(p)
                    | Rvalue::Discriminant(p)
                    | Rvalue::Len(p)
                        if pointers.contains(&p.local) =>
                    {
                        return false;
                    }
                    Rvalue::Use(op, ..)
                    | Rvalue::Cast(CastKind::PtrToPtr | CastKind::PointerExposeAddress, op, _)
                        if place(op).is_some_and(|p| {
                            p.projection.is_empty() && pointers.contains(&p.local)
                        }) => {}
                    _ if address_observation(rhs, &pointers) => {}
                    _ => {
                        if operands(rhs).is_some_and(|ops| {
                            ops.into_iter()
                                .any(|op| place(op).is_some_and(|p| pointers.contains(&p.local)))
                        }) {
                            return false;
                        }
                    }
                }
            }
        }
        let Some(consumer) = consumer else {
            return false;
        };
        let mut pending = self.body.blocks[consumer].terminator.successors();
        let mut after = HashSet::new();
        while let Some(site) = pending.pop() {
            let Some(left) = work.checked_sub(1) else {
                return false;
            };
            work = left;
            if site == consumer {
                return false;
            }
            if after.insert(site) {
                let Some(block) = self.body.blocks.get(site) else {
                    return false;
                };
                pending.extend(block.terminator.successors());
            }
        }
        for site in after {
            for statement in &self.body.blocks[site].statements {
                let Some(left) = work.checked_sub(1) else {
                    return false;
                };
                work = left;
                if let StatementKind::Assign(lhs, rhs) = &statement.kind
                    && (pointers.contains(&lhs.local)
                        || operands(rhs).is_some_and(|ops| {
                            ops.iter()
                                .any(|op| place(op).is_some_and(|p| owners.contains(&p.local)))
                        })
                        || operands(rhs).is_some_and(|ops| {
                            ops.iter().any(|op| {
                                place(op).is_some_and(|p| {
                                    pointers.contains(&p.local) || numbers.contains(&p.local)
                                })
                            })
                        }))
                {
                    return false;
                }
            }
        }
        true
    }
}

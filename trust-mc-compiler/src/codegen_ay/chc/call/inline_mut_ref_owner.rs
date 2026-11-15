// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A referent value does not identify the cell to which writes belong.
//! Keep typed host ownership beside frame-local references and RustCall fields;
//! never reconstruct it from a value's bits, equality, or a unique sort.

use super::ChcCtx;
use rustc_public::mir::Mutability;
use rustc_public::mir::{
    AggregateKind, Body, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};

pub(in crate::codegen_ay::chc) const MUT_REF_OWNER_UNRESOLVED: &str =
    "fn_trait_mut_ref_owner_unresolved";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct InlineMutRefOwner {
    pub local: usize,
    pub pointee: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct InlineMutRefArg {
    pub owner: InlineMutRefOwner,
    pub referent_value: bool,
    pub value_mark: Option<super::super::heap_state::HeapWriteMark>,
}

fn plain_operand(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

/// Only a single actual MIR producer is evidence. In particular, a global
/// points-at entry left by one arm or an earlier reference assignment is not.
fn single_assignment(body: &Body, local: usize) -> Option<&Rvalue> {
    let mut found = None;
    for block in &body.blocks {
        if matches!(&block.terminator.kind, TerminatorKind::Call { destination, .. }
            if destination.local == local && destination.projection.is_empty())
        {
            return None;
        }
        for statement in &block.statements {
            if let StatementKind::Assign(place, rhs) = &statement.kind
                && place.local == local
                && place.projection.is_empty()
            {
                if found.is_some() {
                    return None;
                }
                found = Some(rhs);
            }
        }
    }
    found
}

/// Taking the address of the reference variable permits writes to the carrier
/// through an alias even when it has only one whole-local MIR assignment.
fn carrier_address_exposed(body: &Body, local: usize) -> bool {
    body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
        matches!(&statement.kind, StatementKind::Assign(_, Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place))
            if place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref)))
    })
}

impl ChcCtx<'_, '_> {
    fn owner_matches_ref_ty(&self, owner: &InlineMutRefOwner, ty: Ty) -> bool {
        matches!(self.resolve_body_ty(ty).kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Mut))
            if self.resolve_body_ty(pointee) == owner.pointee)
    }

    /// Establish a plain host cell from the actual borrow producer, checking
    /// the existing host ref-target identity as well. Projected owners and
    /// references whose own address escaped are deliberately unsupported.
    pub(in crate::codegen_ay::chc) fn host_mut_ref_owner(
        &self,
        operand: &Operand,
    ) -> Option<InlineMutRefOwner> {
        let local = plain_operand(operand)?;
        self.host_mut_ref_owner_local(local, &mut Vec::new())
    }

    fn host_mut_ref_owner_local(
        &self,
        local: usize,
        visiting: &mut Vec<usize>,
    ) -> Option<InlineMutRefOwner> {
        if visiting.len() >= 32
            || visiting.contains(&local)
            || carrier_address_exposed(self.body, local)
        {
            return None;
        }
        let ty = self.resolve_body_ty(self.body.locals().get(local)?.ty);
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Mut)) = ty.kind() else {
            return None;
        };
        let pointee = self.resolve_body_ty(pointee);
        visiting.push(local);
        let owner = match single_assignment(self.body, local)? {
            Rvalue::Ref(_, _, place) if place.projection.is_empty() => {
                let target_ty = self.resolve_body_ty(self.body.locals().get(place.local)?.ty);
                (target_ty == pointee).then_some(InlineMutRefOwner { local: place.local, pointee })
            }
            Rvalue::Ref(_, _, place)
                if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) =>
            {
                self.host_mut_ref_owner_local(place.local, visiting)
            }
            Rvalue::Use(source, ..) => {
                self.host_mut_ref_owner_local(plain_operand(source)?, visiting)
            }
            Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                self.host_mut_ref_owner_local(place.local, visiting)
            }
            _ => None,
        }?;
        let target = self.ref_resolution.ref_targets.get(&local)?;
        (target.local == owner.local && target.projections.is_empty() && owner.pointee == pointee)
            .then_some(owner)
    }

    pub(in crate::codegen_ay::chc) fn inline_operand_mut_ref_owner(
        &self,
        operand: &Operand,
    ) -> Option<InlineMutRefOwner> {
        self.inline_walk_frames.last()?.mut_ref_owners.get(&plain_operand(operand)?)?.clone()
    }

    fn inline_mut_ref_arg(&self, operand: &Operand) -> Option<InlineMutRefArg> {
        let owner = self.inline_operand_mut_ref_owner(operand)?;
        if self.inline_walk_operand_is_referent(operand) {
            let local = plain_operand(operand)?;
            if self.inline_walk_written_since_mark()
                && !self.inline_walk_read_exempt_after_rebinds(local)
            {
                self.record_sound_fallback_reason("fn_trait_mut_ref_owner_value_stale");
                return None;
            }
            Some(InlineMutRefArg {
                owner,
                referent_value: true,
                value_mark: Some(self.heap_state.write_mark()),
            })
        } else if self.inline_walk_operand_is_address(operand) {
            Some(InlineMutRefArg { owner, referent_value: false, value_mark: None })
        } else {
            None
        }
    }

    pub(in crate::codegen_ay::chc) fn inline_rustcall_mut_ref_args(
        &self,
        operand: &Operand,
    ) -> Vec<Option<InlineMutRefArg>> {
        self.inline_walk_frames
            .last()
            .and_then(|frame| frame.rustcall_mut_ref_args.get(&plain_operand(operand)?))
            .cloned()
            .flatten()
            .unwrap_or_default()
    }

    /// The outer walk still holds entry-time referent terms. Until an exact
    /// overlay refreshes them, a later RustCall must not reuse those values.
    pub(in crate::codegen_ay::chc) fn invalidate_inline_mut_ref_owner_values(
        &mut self,
        host_local: usize,
    ) {
        for frame in &mut self.inline_walk_frames {
            for (&local, owner) in &frame.mut_ref_owners {
                if owner.as_ref().is_some_and(|owner| owner.local == host_local) {
                    frame.referent_unknown.insert(local);
                }
            }
            for args in frame.rustcall_mut_ref_args.values_mut() {
                if args.as_ref().is_some_and(|args| {
                    args.iter().flatten().any(|arg| arg.owner.local == host_local)
                }) {
                    *args = None;
                }
            }
        }
    }

    pub(in crate::codegen_ay::chc) fn host_rustcall_mut_ref_args(
        &self,
        operand: &Operand,
    ) -> Vec<Option<InlineMutRefArg>> {
        fn fields<'a>(body: &'a Body, operand: &Operand, depth: usize) -> Option<&'a [Operand]> {
            if depth == 0 {
                return None;
            }
            let local = plain_operand(operand)?;
            if carrier_address_exposed(body, local) || body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
                matches!(&statement.kind, StatementKind::Assign(place, _) if place.local == local && !place.projection.is_empty())
            }) { return None; }
            match single_assignment(body, local)? {
                Rvalue::Aggregate(AggregateKind::Tuple, fields) => Some(fields),
                Rvalue::Use(source, ..) => fields(body, source, depth - 1),
                _ => None,
            }
        }
        fields(self.body, operand, 32)
            .unwrap_or_default()
            .iter()
            .map(|operand| {
                self.host_mut_ref_owner(operand).map(|owner| InlineMutRefArg {
                    owner,
                    referent_value: false,
                    value_mark: None,
                })
            })
            .collect()
    }

    /// Facts only lose precision after conflicting/unknown writes. Frames are
    /// shared by speculative branch arms, so last-writer-wins is unsound here.
    pub(in crate::codegen_ay::chc) fn note_inline_mut_ref_assignment(
        &mut self,
        body: &Body,
        local: usize,
        rhs: Option<&Rvalue>,
    ) {
        self.note_inline_readonly_ref_assignment(body, local, rhs);
        // A borrow of the carrier itself can replace its reference through an
        // alias; a reborrow through its Deref preserves the pointee identity.
        if let Some(Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)) = rhs
            && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
            && let Some(frame) = self.inline_walk_frames.last_mut()
            && frame.mut_ref_owners.contains_key(&place.local)
        {
            frame.mut_ref_owners.insert(place.local, None);
            frame.referent_unknown.insert(place.local);
        }
        if !body.locals().get(local).is_some_and(|decl| {
            matches!(
                self.resolve_body_ty(decl.ty).kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut) | RigidTy::Tuple(_))
            )
        }) {
            return;
        }
        let owner = rhs
            .and_then(|rhs| match rhs {
                Rvalue::Use(operand, ..) => self.inline_operand_mut_ref_owner(operand),
                Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                    self.inline_operand_mut_ref_owner(&Operand::Copy(place.clone()))
                }
                Rvalue::Ref(_, _, place)
                    if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) =>
                {
                    self.inline_operand_mut_ref_owner(&Operand::Copy(rustc_public::mir::Place {
                        local: place.local,
                        projection: vec![],
                    }))
                }
                _ => None,
            })
            .filter(|owner| {
                body.locals()
                    .get(local)
                    .is_some_and(|decl| self.owner_matches_ref_ty(owner, decl.ty))
            });
        let fields = rhs.and_then(|rhs| match rhs {
            Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                Some(operands.iter().map(|operand| self.inline_mut_ref_arg(operand)).collect())
            }
            Rvalue::Use(operand, ..) => self
                .inline_walk_frames
                .last()?
                .rustcall_mut_ref_args
                .get(&plain_operand(operand)?)?
                .clone(),
            _ => None,
        });
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            let entry = frame.mut_ref_owners.entry(local).or_insert_with(|| owner.clone());
            if *entry != owner {
                *entry = None;
            }
            let entry = frame.rustcall_mut_ref_args.entry(local).or_insert_with(|| fields.clone());
            if *entry != fields {
                *entry = None;
            }
        }
    }
}

#[cfg(test)]
mod tests;

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Whether the operand an aggregate placed in a pointer-typed field is still
//! the field's value where a pointer is loaded out of it
//! (`pointer_field_value_source`, deref_mem.rs).
//!
//! A TYPED store of a pointer into the field (`h.p = &mut y`, `*pp = q`,
//! `mem::replace(&mut h.p, ..)`) fails closed where it is made
//! (`pointer_stored_into_aggregate_rebinds_target`,
//! `pointer_stored_through_deref_rebinds_target`). The field's bytes can also
//! change without one: a store of another type through a pointer cast from an
//! address of the field (`*(addr_of_mut!(h.p) as *mut usize) = q as usize`),
//! or a byte copy over the owner (`ptr::copy_nonoverlapping(&h2, &mut h, 1)`).
//! Neither is a pointer store, so the aggregate's operand was trusted after
//! it and the store through `*h.p` was placed on the OLD referent: both safe
//! twins were certified Genuine (review of fix/chc-lost-writes, 2026-09-27).
//!
//! The rule below is decided from the MIR alone. Every pointer that may
//! address the owner's bytes is followed from where it is made: a borrow
//! (shared or mutable) or a raw address of the owner or of a place in it,
//! and every copy or reborrow of such a pointer. A SHARED borrow is followed
//! too: writing through a pointer cast from one is undefined behaviour, but
//! the oracle does not flag it and executes the write (`&h as *const H as
//! *mut H`, then a `usize` store into `p`, was a clean missed bug and its
//! safe twin a Genuine false certificate; review follow-up, 2026-09-27).
//! Such a pointer may only be read through, copied or reborrowed, compared,
//! or used for a typed store into a field other than the pointer field.
//! Anything else — a cast, a call argument, an aggregate operand (a closure
//! capture), an intrinsic, a store into the pointer field or over the whole
//! owner — answers `true`, and so does a direct store into the owner's
//! pointer field or a call writing it. A pointer into the field's REFERENT
//! (`&mut *h.p`) addresses another object and is not followed. The fields of
//! a union overlap, so a union owner always answers `true`.
//!
//! The same walk answers the question for a WHOLE local
//! (`local_bytes_may_be_rewritten`): the local an aggregate's pointer operand
//! was copied from (`let mut a = &mut *bx; .. HR { p: a, .. }`) and every
//! owner a copy chain passes through (`let h2 = h;`). A copy of an owner
//! carries the bytes the ORIGINAL owner held when it was copied, so an
//! untyped rewrite of `h.p` before `let h2 = h` changes `h2.p` too; and a
//! rewrite of `a` before the aggregate changes the operand's value. Both
//! were certified Genuine on safe programs when only the final owner was
//! checked (review of fix/chc-lost-writes round 6, 2026-09-27). For a whole
//! local every store through a followed pointer counts, whatever it names.

use std::collections::HashMap;

use rustc_public::mir::visit::{
    Location, MirVisitor, PlaceContext, statement_location, terminator_location,
};
use rustc_public::mir::{
    BinOp, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use tracing::debug;

use super::super::ChcCtx;

/// Which bytes of the owner a followed pointer may address.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reach {
    /// The owner itself (or a part the walk does not resolve).
    Whole,
    /// The pointer field.
    PointerField,
    /// Another field, which does not overlap the pointer field.
    Sibling,
}

impl Reach {
    fn join(self, other: Reach) -> Reach {
        if self == other { self } else { Reach::Whole }
    }
}

/// Every place one rvalue or terminator mentions.
struct Places(Vec<Place>);

impl MirVisitor for Places {
    fn visit_place(&mut self, place: &Place, _ptx: PlaceContext, _location: Location) {
        self.0.push(place.clone());
    }
}

fn has_deref(projection: &[ProjectionElem]) -> bool {
    projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// What a pointer to `place` may address of `owner`, given the followed
    /// pointers in `reach`; `None` when it addresses none of the owner's bytes.
    fn place_reach_of_owner(
        reach: &HashMap<usize, Reach>,
        owner: usize,
        field_idx: Option<usize>,
        place: &Place,
    ) -> Option<Reach> {
        let (base, rest) = if place.local == owner {
            (Reach::Whole, place.projection.as_slice())
        } else {
            let [ProjectionElem::Deref, rest @ ..] = place.projection.as_slice() else {
                return None;
            };
            (*reach.get(&place.local)?, rest)
        };
        // A further dereference leaves the owner for the object a field points to.
        if has_deref(rest) {
            return None;
        }
        Some(match (base, rest.first()) {
            (_, None) => base,
            (Reach::Whole, Some(ProjectionElem::Field(j, _))) => match field_idx {
                Some(f) if *j == f => Reach::PointerField,
                Some(_) => Reach::Sibling,
                // The whole local's bytes are the question: a pointer to any
                // part of it may rewrite them.
                None => Reach::Whole,
            },
            (Reach::Whole, Some(_)) => Reach::Whole,
            (other, Some(_)) => other,
        })
    }

    /// May the bytes of `owner`'s pointer field `field_idx` change without a
    /// typed pointer store into it? See the module documentation.
    pub(in crate::codegen_ay::chc) fn pointer_field_bytes_may_be_rewritten(
        &self,
        owner: usize,
        field_idx: usize,
    ) -> bool {
        self.owner_bytes_may_be_rewritten(owner, Some(field_idx))
    }

    /// May any byte of `local` change other than by a whole definition of
    /// it (`local = ..`)? See the module documentation.
    pub(in crate::codegen_ay::chc) fn local_bytes_may_be_rewritten(&self, local: usize) -> bool {
        self.owner_bytes_may_be_rewritten(local, None)
    }

    /// The walk behind both questions: `field_idx` names the pointer field
    /// whose bytes matter, `None` the whole owner.
    fn owner_bytes_may_be_rewritten(&self, owner: usize, field_idx: Option<usize>) -> bool {
        let body = self.body;

        // The fields of a union overlap: a store into any of them may rewrite
        // the pointer field's bytes.
        if let Some(decl) = body.locals().get(owner)
            && let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)) =
                decl.ty.kind()
            && def.kind() == rustc_public::ty::AdtKind::Union
        {
            debug!(owner, ?field_idx, "CHC: a union's pointer field may be rewritten by any field");
            return true;
        }

        // Follow every pointer that may address the owner's bytes.
        let mut reach: HashMap<usize, Reach> = HashMap::new();
        loop {
            let mut changed = false;
            for block in &body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rv) = &stmt.kind else { continue };
                    if !lhs.projection.is_empty() {
                        continue;
                    }
                    let found = match rv {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            Self::place_reach_of_owner(&reach, owner, field_idx, place)
                        }
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                        | Rvalue::CopyForDeref(place)
                            if place.projection.is_empty() =>
                        {
                            reach.get(&place.local).copied()
                        }
                        _ => None,
                    };
                    if let Some(found) = found {
                        let joined = reach.get(&lhs.local).map_or(found, |r| r.join(found));
                        if reach.insert(lhs.local, joined) != Some(joined) {
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // A store into `place`: may it write the pointer field's bytes?
        // A whole-owner definition is the aggregate itself; a second one is
        // refused by `pointer_field_value_source`'s single-definition gate.
        let store_may_rewrite = |place: &Place| -> bool {
            if place.local == owner {
                return !has_deref(&place.projection)
                    && match place.projection.first() {
                        None => false,
                        Some(ProjectionElem::Field(j, _)) => field_idx.is_none_or(|f| *j == f),
                        Some(_) => true,
                    };
            }
            let Some(&base) = reach.get(&place.local) else { return false };
            let [ProjectionElem::Deref, rest @ ..] = place.projection.as_slice() else {
                // Redefining the followed pointer itself.
                return false;
            };
            if has_deref(rest) {
                return false;
            }
            match (base, rest.first()) {
                (Reach::Sibling, _) => false,
                (Reach::Whole, Some(ProjectionElem::Field(j, _))) => {
                    field_idx.is_none_or(|f| *j == f)
                }
                _ => true,
            }
        };
        let is_followed_whole =
            |place: &Place| place.projection.is_empty() && reach.contains_key(&place.local);
        let refuse = |why: &str| {
            debug!(owner, ?field_idx, why, "CHC: a pointer field's bytes may change untyped");
            true
        };

        for (bb, block) in body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let location = statement_location(body, &bb, si);
                match &stmt.kind {
                    StatementKind::Assign(lhs, rv) => {
                        if store_may_rewrite(lhs) {
                            return refuse("store into the pointer field or over the owner");
                        }
                        let mut places = Places(Vec::new());
                        places.visit_rvalue(rv, location);
                        if !places.0.iter().any(|p| is_followed_whole(p)) {
                            continue;
                        }
                        let plain_copy = lhs.projection.is_empty()
                            && matches!(
                                rv,
                                Rvalue::Use(Operand::Copy(_) | Operand::Move(_), ..)
                                    | Rvalue::CopyForDeref(_)
                            );
                        let comparison = matches!(
                            rv,
                            Rvalue::BinaryOp(
                                BinOp::Eq
                                    | BinOp::Ne
                                    | BinOp::Lt
                                    | BinOp::Le
                                    | BinOp::Gt
                                    | BinOp::Ge
                                    | BinOp::Cmp,
                                ..
                            )
                        );
                        if !plain_copy && !comparison {
                            return refuse("a pointer to the owner escapes the walk");
                        }
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType { .. }
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop => {}
                    _ => {
                        let mut places = Places(Vec::new());
                        places.visit_statement(stmt, location);
                        if places.0.iter().any(|p| p.local == owner || reach.contains_key(&p.local))
                        {
                            return refuse("an intrinsic or discriminant write reaches the owner");
                        }
                    }
                }
            }
            let location = terminator_location(body, &bb);
            match &block.terminator.kind {
                TerminatorKind::Drop { .. } => {}
                TerminatorKind::Call { args, destination, .. } => {
                    if store_may_rewrite(destination) {
                        return refuse("a call writes the pointer field or the owner");
                    }
                    let passes_pointer = args.iter().any(|arg| {
                        matches!(arg, Operand::Copy(p) | Operand::Move(p) if is_followed_whole(p))
                    });
                    if passes_pointer {
                        return refuse("a pointer to the owner is passed to a call");
                    }
                }
                _ => {
                    let mut places = Places(Vec::new());
                    places.visit_terminator(&block.terminator, location);
                    if places.0.iter().any(|p| is_followed_whole(p)) {
                        return refuse("a pointer to the owner reaches a terminator");
                    }
                }
            }
        }
        false
    }
}

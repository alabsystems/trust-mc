// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An enum whose one payload is a shared reference to a scalar keeps the
//! POINTEE's value in its payload slot (fix/chc-false-certificates, 2026-09-27).
//!
//! `translate_ty` gives `Option<&u8>` the payload sort `u8`: a VALUE slot. The
//! aggregate `_4 = Option::Some(copy _5)` used to put the reference itself
//! there, truncated to the slot's width, and a read of the pointee through the
//! unwrapped payload then loaded the typed memory at the zero-extended
//! truncation. For `let o = if b { Some(&m) } else { Some(&n) }` that was
//! `mem_u8[0]`, a cell no rule writes: `option_ref_payload_join_safe` was a
//! false certificate, and its `_a`/`_b_must_fail` twins were Genuine only by
//! that free cell (review_r17_aggregate_field_join.rs). A single producer hid
//! the defect, because the reference's points-at edge was copied with the
//! enum; two producers make the edge ambiguous and it is dropped.
//!
//! - The aggregate stores the pointee's value, read through the reference at
//!   the aggregate ([`ChcCtx::value_semantic_ref_payload`]; a pointee the
//!   translation cannot read is a fresh value, booked).
//! - A read of the pointee through the payload is that value. Two shapes
//!   reach it ([`ChcCtx::try_resolve_value_payload_deref`]): the place
//!   `(*((L as Some).0))` directly (`Option::copied` after inlining), and
//!   `*r` for a reference local `r` whose every definition copies such a
//!   payload (`if let Some(r) = o`, or the `Option::unwrap`/`expect` stub,
//!   which returns the payload), whose register therefore holds the payload
//!   value widened to the pointer's width.
//!
//! Both need every value of `L` to come from such an aggregate
//! ([`ChcCtx::value_slot_local`]): no argument, no call result, no partial or
//! mutable write, only aggregates and whole copies of other such locals.
//!
//! # Only a pointee nothing else writes
//!
//! The value read at the aggregate stands for every later read of the pointee
//! through the payload. That holds only when no write can reach the pointee
//! while the reference lives. No lane checks aliasing, and Kani and a debug
//! build read the WRITTEN value, so a program whose write is undefined aliasing
//! behaviour still has to see it: the first cut read `G` once and proved
//! `assert!(*o.unwrap() == 1)` after `G = 2` for `o = Some(&*addr_of!(G))`
//! (third review of fix/chc-false-certificates, 2026-09-27: `al_static_write_
//! reads_old_bug`, `al_cell_bug`, `op_static_callee_write_bug`, clean proofs
//! where main and Kani fail), and a pointee freed after the aggregate lost its
//! use-after-free check (`dg_heap_uaf_bug`, SUCCESSFUL on main and the branch).
//! So the aggregate stores the value only when every definition of the payload
//! reference is a shared borrow of a place rooted at a body local that
//! dereferences nothing but other such references, whose storage is never
//! borrowed mutably, never taken
//! by raw address, and never borrowed into a reference the body casts to a raw
//! pointer ([`ChcCtx::value_payload_pointee_frozen`]); such a local changes only
//! by its own assignments, which the borrow checker forbids while the reference
//! lives. Any other pointee — behind a raw pointer, a `Box`, the heap, a static,
//! a `Cell`, an argument — is a fresh value, booked
//! `enum_ref_payload_pointee_not_frozen`: no clean proof, no certified
//! counterexample.
//!
//! # Only the slots that could never hold the address
//!
//! The rewrite applies only when the payload slot is NARROWER than a pointer
//! (`u8`, `u16`, `u32`, `i32`, `char`, `bool`, ...): there the reference was
//! truncated, so no reader could get the address back. A slot of 64 bits or
//! more (`u64`, `usize`, `f64`, `u128`, or a general enum's `&u64` field, whose
//! slot is the pointer sort itself) held the WHOLE pointer, and every reader
//! that uses the payload as an address — `ptr::eq`, `as *const`, a closure
//! that receives it, the enum moved into an array, a `Vec`, a tuple or a
//! struct — was exact there. Storing the value in such a slot read the value
//! as an address: `ptr::eq(o.unwrap(), &m)` for `o = Some(&m)` with `m: u64`
//! FAILED certified Genuine, and its `should_panic` twin passed (second review
//! of fix/chc-false-certificates, 2026-09-27: `v64_ptr_eq_safe`,
//! `e3_ptr_eq_safe`, `arr_opt_safe`, ...).
//!
//! # A narrow payload that escapes fails closed
//!
//! In a narrow slot neither the value nor the truncated reference serves a
//! reader that wants the address. The value is exact only while every reader
//! is one of the shapes above; [`ChcCtx::book_escaping_ref_payloads`] checks that
//! for every local an aggregate builds, once per body: its whole copies (recursively), the
//! references taken out of its payload and their copies and reborrows, read
//! only the pointee (`*r`, `(*((L as Some).0))`), the discriminant, or feed
//! `Option::unwrap` / `expect`; a shared borrow of it only feeds `is_some` /
//! `is_none` or its discriminant. Anything else — the payload reference
//! compared, cast, passed to a call or a closure (`map`, `filter`,
//! `unwrap_unchecked`, a user function), the enum borrowed for another method,
//! moved into an aggregate or mixed with a call result (`a.iter().next()`) —
//! books `enum_ref_payload_escapes`, a fail-closed reason: no clean proof, and
//! a counterexample is not certified.

use std::collections::HashSet;

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::visit::{
    Location, MirVisitor, PlaceContext, statement_location, terminator_location,
};
use rustc_public::mir::{
    AggregateKind, BorrowKind, Mutability, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use tracing::debug;

use rustc_public::CrateDef;

use crate::rustc_public_bridge::IndexedVal;

use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name};
use crate::codegen_ay::chc::codegen_ctx::Havoc;

/// Whether a payload slot of `sort` is narrower than a pointer: the reference
/// stored there was truncated, so no reader could have got the address back.
fn slot_narrower_than_pointer(sort: &Sort) -> bool {
    sort.is_bool() || sort.bitvec_width().is_some_and(|bits| bits < POINTER_WIDTH)
}

/// Every place of one statement or terminator whose base local is `target`,
/// and whether `target` indexes a projection there.
struct TargetPlaces {
    target: usize,
    places: Vec<Place>,
    index_use: bool,
}

impl TargetPlaces {
    fn new(target: usize) -> Self {
        Self { target, places: Vec::new(), index_use: false }
    }

    fn is_empty(&self) -> bool {
        self.places.is_empty() && !self.index_use
    }
}

impl MirVisitor for TargetPlaces {
    fn visit_place(&mut self, place: &Place, _ptx: PlaceContext, _location: Location) {
        if place.local == self.target {
            self.places.push(place.clone());
        }
        if place
            .projection
            .iter()
            .any(|elem| matches!(elem, ProjectionElem::Index(local) if *local == self.target))
        {
            self.index_use = true;
        }
    }
}

/// Whether `ty` is a scalar a value slot can hold for a reference to it.
fn is_value_slot_scalar(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_) | RigidTy::Char | RigidTy::Bool
        )
    )
}

/// The pointee of a shared reference type to a value-slot scalar.
fn shared_scalar_pointee(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Not))
            if is_value_slot_scalar(pointee) =>
        {
            Some(pointee)
        }
        _ => None,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The constructor index whose one field is the value-semantic reference
    /// payload of the enum local `local_idx` (state index `vec_idx`), when the
    /// local is such an enum: one payload slot, exactly one variant with fields,
    /// that variant's only field a shared reference to an integer, float, `char`
    /// or `bool`, and the slot's sort the pointee's sort AND narrower than a
    /// pointer (`Option<&u8>` is `(is_some, u8)`; `Option<&u64>` keeps the
    /// pointer). Every other variant has no field.
    pub(in crate::codegen_ay::chc) fn value_semantic_ref_enum(
        &self,
        local_idx: usize,
        vec_idx: usize,
    ) -> Option<usize> {
        let layout = self.flatten.enum_bv_layouts.get(&local_idx)?;
        if layout.max_payload_slots != 1 {
            return None;
        }
        let ty = self.resolve_body_ty(self.body.locals().get(local_idx)?.ty);
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        if def.kind() != AdtKind::Enum {
            return None;
        }
        let mut ref_ctor = None;
        for (ctor_idx, variant) in def.variants_iter().enumerate() {
            match variant.fields().as_slice() {
                [] => {}
                [field] if ref_ctor.is_none() => {
                    let field_ty = self.resolve_body_ty(mono_ty::field_ty(field, &args)?);
                    let pointee = shared_scalar_pointee(field_ty)?;
                    let pointee_sort = Self::translate_ty(pointee)?;
                    let (_, slot_sort) = self.state_var_mgr.state_vars.get(vec_idx + 1)?;
                    // A slot of the pointer's width or wider held the whole
                    // reference, which every address reader needs (module
                    // documentation): only a narrower slot is rewritten.
                    if *slot_sort != pointee_sort || !slot_narrower_than_pointer(slot_sort) {
                        return None;
                    }
                    ref_ctor = Some(ctor_idx);
                }
                _ => return None,
            }
        }
        ref_ctor
    }

    /// The payload a value-semantic reference slot (state index `slot_idx`) of
    /// `local_idx` stores for `operand`: the pointee's value read through it at
    /// the aggregate. `None` only when the slot has no sort; a pointee the
    /// translation cannot read is a FRESH value, booked
    /// `enum_ref_payload_value_unresolved` (the reference truncated into the
    /// slot was a value nothing tied to the pointee's).
    pub(in crate::codegen_ay::chc) fn value_semantic_ref_payload(
        &mut self,
        local_idx: usize,
        operand: &Operand,
        slot_idx: usize,
        modified: &HashSet<usize>,
    ) -> Option<Expr> {
        let (_, slot_sort) = self.state_var_mgr.output_state_vars.get(slot_idx).cloned()?;
        // The value read here stands for every later read of the pointee
        // through the payload, so the pointee must be one no write can reach
        // while the reference lives (module documentation, "Only a pointee
        // nothing else writes"). Any other pointee is a fresh value, booked.
        if let Operand::Copy(place) | Operand::Move(place) = operand
            && !self.value_payload_pointee_frozen(place)
        {
            debug!(
                local_idx,
                ?operand,
                "value-semantic enum payload: pointee may change; fresh value"
            );
            let booked = self.record_sound_fallback_reason("enum_ref_payload_pointee_not_frozen");
            return Some(Havoc::booked(
                booked,
                chc_fresh_name("__enum_ref_payload_value"),
                slot_sort,
            ));
        }
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            let mut projection = place.projection.clone();
            projection.push(ProjectionElem::Deref);
            let pointee = Place { local: place.local, projection };
            if let Some(value) = self.translate_place_with_deref(&pointee, modified)
                && *value.sort() == slot_sort
            {
                debug!(
                    local_idx,
                    ?operand,
                    "value-semantic enum payload: stored the pointee value"
                );
                return Some(value);
            }
        }
        debug!(local_idx, ?operand, "value-semantic enum payload: pointee unreadable; fresh value");
        let booked = self.record_sound_fallback_reason("enum_ref_payload_value_unresolved");
        Some(Havoc::booked(booked, chc_fresh_name("__enum_ref_payload_value"), slot_sort))
    }

    /// Whether the reference `reference` (an aggregate's payload operand) can
    /// only point at a place whose value no write reaches while it lives
    /// (module documentation, "Only a pointee nothing else writes"): every
    /// definition of the reference local, through whole copies and shared
    /// borrows through another reference (`&(*q)`, `&((*q) as Some).0` in an
    /// inlined `as_ref`, `q` held to the same rule), is a shared borrow `&P`
    /// of a place `P` that
    ///
    /// - is rooted at a body local (not an argument, not the return place),
    /// - dereferences nothing (no raw pointer, `Box`, heap cell or static, whose
    ///   pointee a raw pointer, `Cell::set`, a free or a static write can change
    ///   behind the shared reference), and
    /// - whose local's own storage is never borrowed mutably, never taken by raw
    ///   address (`&raw mut`, `&raw const`, `addr_of!`), and never handed out
    ///   through a shared borrow that is then cast to a raw pointer.
    ///
    /// Such a local changes only by its own assignments, which the borrow
    /// checker forbids while the shared reference lives.
    fn value_payload_pointee_frozen(&self, reference: &Place) -> bool {
        if !reference.projection.is_empty() {
            return false;
        }
        let arg_count = self.body.arg_locals().len();
        let is_body_local = |local: usize| local != 0 && local > arg_count;
        let mut pending = vec![reference.local];
        let mut seen: HashSet<usize> = HashSet::new();
        let mut roots: HashSet<usize> = HashSet::new();
        while let Some(r) = pending.pop() {
            if !seen.insert(r) {
                continue;
            }
            if !is_body_local(r) {
                return false;
            }
            let mut defined = false;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    match &stmt.kind {
                        StatementKind::Assign(lhs, rhs) if lhs.local == r => {
                            if !lhs.projection.is_empty() {
                                return false;
                            }
                            defined = true;
                            match rhs {
                                Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                                    if src.projection.is_empty() =>
                                {
                                    pending.push(src.local);
                                }
                                // A place behind another reference (`&(*q)`,
                                // or `&((*q) as Some).0` in an inlined
                                // `as_ref`): `q` is held to the same rule, so
                                // it too borrows a frozen body local.
                                Rvalue::Ref(_, BorrowKind::Shared, src)
                                    if matches!(
                                        src.projection.first(),
                                        Some(ProjectionElem::Deref)
                                    ) && !src.projection[1..]
                                        .iter()
                                        .any(|p| matches!(p, ProjectionElem::Deref)) =>
                                {
                                    pending.push(src.local);
                                }
                                Rvalue::Ref(_, BorrowKind::Shared, src)
                                    if is_body_local(src.local)
                                        && !src
                                            .projection
                                            .iter()
                                            .any(|p| matches!(p, ProjectionElem::Deref)) =>
                                {
                                    roots.insert(src.local);
                                }
                                _ => return false,
                            }
                        }
                        StatementKind::SetDiscriminant { place, .. } if place.local == r => {
                            return false;
                        }
                        _ => {}
                    }
                }
                match &block.terminator.kind {
                    TerminatorKind::Call { destination, .. } if destination.local == r => {
                        return false;
                    }
                    TerminatorKind::InlineAsm { .. } => return false,
                    _ => {}
                }
            }
            if !defined {
                return false;
            }
        }
        roots.iter().all(|&root| self.pointee_local_only_shared_reads(root))
    }

    /// Whether the body local `root` is never borrowed mutably, never taken by
    /// raw address, and never borrowed shared into a reference that (through
    /// copies and reborrows) is cast to a raw pointer or taken by raw address:
    /// no pointer the body builds can write it.
    fn pointee_local_only_shared_reads(&self, root: usize) -> bool {
        let own = |place: &Place| {
            place.local == root && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
        };
        // The shared borrows of `root`, closed under copies and reborrows.
        let mut borrows: HashSet<usize> = HashSet::new();
        let mut changed = true;
        while changed {
            changed = false;
            for stmt in self.body.blocks.iter().flat_map(|b| b.statements.iter()) {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                match rhs {
                    Rvalue::Ref(_, kind, place) if own(place) => {
                        if !matches!(kind, BorrowKind::Shared) {
                            return false;
                        }
                        if borrows.insert(lhs.local) {
                            changed = true;
                        }
                    }
                    Rvalue::AddressOf(_, place) if own(place) => return false,
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                        if src.projection.is_empty() && borrows.contains(&src.local) =>
                    {
                        if borrows.insert(lhs.local) {
                            changed = true;
                        }
                    }
                    Rvalue::Ref(_, BorrowKind::Shared, src)
                        if matches!(src.projection.first(), Some(ProjectionElem::Deref))
                            && borrows.contains(&src.local) =>
                    {
                        if borrows.insert(lhs.local) {
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        !self.body.blocks.iter().flat_map(|b| b.statements.iter()).any(|stmt| match &stmt.kind {
            StatementKind::Assign(
                _,
                Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _),
            ) => src.projection.is_empty() && borrows.contains(&src.local),
            StatementKind::Assign(_, Rvalue::AddressOf(_, src)) => {
                borrows.contains(&src.local)
                    && matches!(src.projection.first(), Some(ProjectionElem::Deref))
            }
            _ => false,
        })
    }

    /// Whether every value `local` ever holds comes from an aggregate that
    /// stored its pointee value (module documentation): a value-semantic
    /// reference enum, not an argument, written only by whole-local enum
    /// aggregates, constants and whole copies of other such locals, never
    /// borrowed mutably, never a call's destination.
    pub(in crate::codegen_ay::chc) fn value_slot_local(&self, local: usize) -> bool {
        self.value_slot_local_rec(local, &mut HashSet::new(), false)
    }

    /// `typed`: judge the local by its TYPE ([`Self::narrow_ref_option_ctor`])
    /// rather than by its flattened value slot, for the escape analysis that
    /// covers the datatype encoding too.
    fn value_slot_local_rec(
        &self,
        local: usize,
        visiting: &mut HashSet<usize>,
        typed: bool,
    ) -> bool {
        // A cycle of whole copies adds no value from elsewhere: every value in
        // the cycle still enters it through a checked write.
        if !visiting.insert(local) {
            return true;
        }
        let arg_count = self.body.arg_locals().len();
        if local == 0 || (1..=arg_count).contains(&local) {
            return false;
        }
        if typed {
            if self.narrow_ref_option_ctor(self.body.locals()[local].ty).is_none() {
                return false;
            }
        } else {
            let Some(vec_idx) = self.try_state_idx_for_local(local) else { return false };
            if self.value_semantic_ref_enum(local, vec_idx).is_none() {
                return false;
            }
        }
        for block in &self.body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rhs) if lhs.local == local => {
                        if !lhs.projection.is_empty() {
                            return false;
                        }
                        match rhs {
                            Rvalue::Aggregate(AggregateKind::Adt(..), _) => {}
                            // A constant `Option<&T>` decodes its payload as the
                            // pointee's value too (expr/codegen_expr_constant_payload.rs),
                            // and `None` has none.
                            Rvalue::Use(Operand::Constant(_), ..) => {}
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                                if src.projection.is_empty() =>
                            {
                                if !self.value_slot_local_rec(src.local, visiting, typed) {
                                    return false;
                                }
                            }
                            _ => return false,
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                        return false;
                    }
                    StatementKind::Assign(_, Rvalue::Ref(_, kind, place))
                        if place.local == local && !matches!(kind, BorrowKind::Shared) =>
                    {
                        return false;
                    }
                    StatementKind::Assign(_, Rvalue::AddressOf(kind, place))
                        if place.local == local && kind.to_mutable_lossy() == Mutability::Mut =>
                    {
                        return false;
                    }
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { destination, .. } if destination.local == local => {
                    return false;
                }
                TerminatorKind::InlineAsm { .. } => return false,
                _ => {}
            }
        }
        true
    }

    /// Whether every definition of the reference local `r` copies the payload
    /// of a value-slot enum (`copy ((L as Some).0)`), or copies or shares
    /// another such reference (`copy q`, `&(*q)`), and nothing else writes it:
    /// its register then holds a pointee VALUE, widened to the pointer's width
    /// by the assignment's coercion.
    fn value_payload_ref_local(&self, r: usize, visiting: &mut HashSet<usize>) -> bool {
        if !visiting.insert(r) {
            return true;
        }
        let arg_count = self.body.arg_locals().len();
        if r == 0 || (1..=arg_count).contains(&r) {
            return false;
        }
        let mut defined = false;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rhs) if lhs.local == r => {
                        if !lhs.projection.is_empty() {
                            return false;
                        }
                        let ok = match rhs {
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
                                match src.projection.as_slice() {
                                    [] => self.value_payload_ref_local(src.local, visiting),
                                    [
                                        ProjectionElem::Downcast(variant),
                                        ProjectionElem::Field(0, _),
                                    ] => {
                                        self.value_slot_local(src.local)
                                            && self.try_state_idx_for_local(src.local).and_then(
                                                |vi| self.value_semantic_ref_enum(src.local, vi),
                                            ) == Some(variant.to_index())
                                    }
                                    _ => false,
                                }
                            }
                            Rvalue::Ref(_, BorrowKind::Shared, src) => {
                                matches!(src.projection.as_slice(), [ProjectionElem::Deref])
                                    && self.value_payload_ref_local(src.local, visiting)
                            }
                            _ => false,
                        };
                        if !ok {
                            return false;
                        }
                        defined = true;
                    }
                    StatementKind::SetDiscriminant { place, .. } if place.local == r => {
                        return false;
                    }
                    StatementKind::Assign(_, Rvalue::Ref(_, kind, place))
                        if place.local == r && !matches!(kind, BorrowKind::Shared) =>
                    {
                        return false;
                    }
                    StatementKind::Assign(_, Rvalue::AddressOf(kind, place))
                        if place.local == r && kind.to_mutable_lossy() == Mutability::Mut =>
                    {
                        return false;
                    }
                    _ => {}
                }
            }
            match &block.terminator.kind {
                // The `Option::unwrap`/`expect` stub returns the payload itself.
                TerminatorKind::Call { func, args, destination, .. } if destination.local == r => {
                    let unwraps_payload = destination.projection.is_empty()
                        && func.ty(self.body.locals()).ok().is_some_and(|ty| {
                            matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnDef(def, _))
                            if {
                                let name = def.name();
                                name.contains("option::Option::<")
                                    && (name.ends_with(">::unwrap")
                                        || name.ends_with(">::expect"))
                            })
                        });
                    match args.first() {
                        Some(Operand::Copy(src) | Operand::Move(src))
                            if unwraps_payload
                                && src.projection.is_empty()
                                && self.value_slot_local(src.local) =>
                        {
                            defined = true;
                        }
                        _ => return false,
                    }
                }
                TerminatorKind::InlineAsm { .. } => return false,
                _ => {}
            }
        }
        defined
    }

    /// Whether the callee of `func` is `Option::<_>::<method>` for one of
    /// `methods`.
    fn callee_is_option_method(&self, func: &Operand, methods: &[&str]) -> bool {
        func.ty(self.body.locals()).ok().is_some_and(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => {
                let name = def.name();
                name.contains("option::Option::<")
                    && methods.iter().any(|method| {
                        name.strip_suffix(method).is_some_and(|head| head.ends_with(">::"))
                    })
            }
            _ => false,
        })
    }

    /// Whether the callee of `func` is `core::panicking::assert_failed`, the
    /// diverging failure path of `assert_eq!` / `assert_ne!`: it formats its
    /// operands for the panic message and never returns, so nothing it reads
    /// reaches a verdict.
    fn callee_is_assert_failed(&self, func: &Operand) -> bool {
        func.ty(self.body.locals()).ok().is_some_and(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => {
                def.name().ends_with("panicking::assert_failed")
            }
            _ => false,
        })
    }

    /// Whether the callee of `func` is `<Option<_> as PartialEq>::eq` or `ne`:
    /// the trait method (`PartialEq::eq` with an `Option` self type) or the
    /// impl's.
    fn callee_is_option_partial_eq(&self, func: &Operand) -> bool {
        func.ty(self.body.locals()).ok().is_some_and(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
                let name = def.name();
                let is_eq_method = name.ends_with("PartialEq::eq")
                    || name.ends_with("PartialEq::ne")
                    || (name.contains(" as std::cmp::PartialEq>::")
                        && (name.ends_with(">::eq") || name.ends_with(">::ne")));
                let self_is_option = name.contains("option::Option<")
                    || matches!(args.0.first(), Some(rustc_public::ty::GenericArgKind::Type(ty))
                        if matches!(self.resolve_body_ty(*ty).kind(),
                            TyKind::RigidTy(RigidTy::Adt(adt, _))
                                if adt.kind() == AdtKind::Enum
                                    && adt.trimmed_name() == "Option"));
                is_eq_method && self_is_option
            }
            _ => false,
        })
    }

    /// Whether the callee of `func` is a function item of the crate under
    /// verification: its reference parameters are bound by the inline walker
    /// to the referent the caller's cascade resolves (`*r`), not to `r`'s bits.
    fn callee_is_local_fn(&self, func: &Operand) -> bool {
        func.ty(self.body.locals()).ok().is_some_and(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def.krate().is_local,
            _ => false,
        })
    }

    /// The payload constructor of `ty` when it is an enum like `Option<&T>` —
    /// one variant whose only field is a shared reference to a scalar `T` whose
    /// sort is narrower than a pointer, every other variant fieldless (module
    /// documentation): the payload can never hold the reference's address,
    /// flattened or not.
    fn narrow_ref_option_ctor(&self, ty: Ty) -> Option<usize> {
        let ty = self.resolve_body_ty(ty);
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        // Judged by SHAPE, as `value_semantic_ref_enum` judges the slot: any enum
        // whose one payload field is a shared reference to a narrow scalar, not
        // only `Option`. Keyed on the name, a user enum `MyOpt::Yes(&m)` moved
        // into an array or a tuple kept the value in the slot and every reader
        // there took it for the reference (third review: `ea_custom_u8_arr_val_
        // safe`, `ea_custom_u8_arr_ptr_eq_safe`, `ce_arr_ptr_eq_safe` FAILED
        // certified Genuine on main and the branch).
        // Only the `Option`-like shape (two variants, one fieldless): the arm of
        // `translate_ty` that gives the payload the POINTEE's sort
        // (`codegen_types_adt_sort.rs`). A general enum keeps the reference.
        if def.kind() != AdtKind::Enum || def.variants_iter().count() != 2 {
            return None;
        }
        let mut ref_ctor = None;
        for (ctor_idx, variant) in def.variants_iter().enumerate() {
            match variant.fields().as_slice() {
                [] => {}
                [field] if ref_ctor.is_none() => {
                    let pointee = shared_scalar_pointee(
                        self.resolve_body_ty(mono_ty::field_ty(field, &args)?),
                    )?;
                    if !slot_narrower_than_pointer(&Self::translate_ty(pointee)?) {
                        return None;
                    }
                    ref_ctor = Some(ctor_idx);
                }
                _ => return None,
            }
        }
        ref_ctor
    }

    /// Whether the by-value `Option<&T>` local `local`, `T` a scalar of a
    /// pointer's width or wider, may hold the reference's ADDRESS in its
    /// payload: some statement builds it (or a local it is a whole copy of)
    /// with the payload variant. The aggregate keeps the whole reference in
    /// such a slot (module documentation), while the inline walker reads an
    /// `Option<&T>` parameter value-semantically as `Option<T>`
    /// (`deref_ref_ty_sized_only`): `o.is_some_and(|r| *r == 5)` compared the
    /// address with 5 and FAILED certified Genuine (review probe sp_vrp64.rs
    /// `v64_is_some_and_safe`).
    pub(in crate::codegen_ay::chc) fn wide_ref_option_may_hold_address(
        &self,
        local: usize,
    ) -> bool {
        self.wide_ref_option_may_hold_address_rec(local, &mut HashSet::new())
    }

    fn wide_ref_option_may_hold_address_rec(
        &self,
        local: usize,
        seen: &mut HashSet<usize>,
    ) -> bool {
        if !seen.insert(local) {
            return false;
        }
        let Some(ty) = self.body.locals().get(local).map(|decl| self.resolve_body_ty(decl.ty))
        else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return false };
        if def.kind() != AdtKind::Enum || def.trimmed_name() != "Option" {
            return false;
        }
        let payload_ctor = def.variants_iter().enumerate().find_map(|(ctor_idx, variant)| {
            let fields = variant.fields();
            let [field] = fields.as_slice() else { return None };
            // A field type Rule A refuses (`mono_ty::field_ty`) may be the
            // reference: the argument is refused (fail closed).
            let Some(field_ty) = mono_ty::field_ty(field, &args) else { return Some(ctor_idx) };
            let pointee = shared_scalar_pointee(self.resolve_body_ty(field_ty))?;
            let sort = Self::translate_ty(pointee)?;
            (!slot_narrower_than_pointer(&sort)).then_some(ctor_idx)
        });
        let Some(payload_ctor) = payload_ctor else { return false };
        self.body.blocks.iter().flat_map(|block| block.statements.iter()).any(|stmt| {
            match &stmt.kind {
                StatementKind::Assign(lhs, rhs)
                    if lhs.local == local && lhs.projection.is_empty() =>
                {
                    match rhs {
                        Rvalue::Aggregate(AggregateKind::Adt(_, variant, ..), _) => {
                            variant.to_index() == payload_ctor
                        }
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                            if src.projection.is_empty() =>
                        {
                            self.wide_ref_option_may_hold_address_rec(src.local, seen)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        })
    }

    /// Book a fail-closed reason when a narrow `Option<&scalar>` payload of
    /// this body may reach a reader that takes it for the reference's address
    /// (module documentation, "A narrow payload that escapes fails closed").
    /// Once per body, over every local but the return place (whose readers
    /// are in the caller, which checks its own receiving local):
    ///
    /// - a local some statement builds with the payload variant (an aggregate
    ///   the encoder stored the pointee's VALUE for, in either the flattened
    ///   or the datatype encoding) must be written only by aggregates and
    ///   whole copies ([`Self::value_slot_local`] on the type) and read only
    ///   by the admitted shapes ([`Self::payload_enum_closed`]);
    /// - any other such local (a call result, an argument) must not hand a
    ///   reference out of its payload to an ADDRESS reader: a pointer cast, or
    ///   anything but an admitted value reader ([`Self::payload_call_result_readers_closed`]).
    pub(in crate::codegen_ay::chc) fn book_escaping_ref_payloads(&self) {
        for local in 1..self.body.locals().len() {
            // The new borrowed-static slot is an address. A move into an
            // enum/aggregate using the old value convention still escapes.
            if self.borrowed_static_next_sources(local).is_some() {
                if !self.address_payload_enum_contained(local, &mut HashSet::new()) {
                    self.record_sound_fallback_reason("enum_ref_payload_escapes");
                }
                continue;
            }
            let Some(ctor) = self.narrow_ref_option_ctor(self.body.locals()[local].ty) else {
                continue;
            };
            let aggregate_built =
                self.body.blocks.iter().flat_map(|b| b.statements.iter()).any(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(lhs, Rvalue::Aggregate(
                        AggregateKind::Adt(_, variant, ..), _))
                        if lhs.local == local && variant.to_index() == ctor)
                });
            let escapes = if self.local_keeps_payload_address(local) {
                // A flattened local whose payload slot is pointer-wide (a user
                // `Option`-like enum takes the general enum layout) holds the
                // whole reference, so every reader of it is exact. The datatype
                // an array, a tuple, a struct field or a callee parameter gives
                // the same enum truncates the payload to the pointee's width
                // (`codegen_types_adt_sort.rs`, the `Option`-like arm): a move
                // there escapes.
                !self.address_payload_enum_contained(local, &mut HashSet::new())
            } else if aggregate_built {
                !(self.value_slot_local_rec(local, &mut HashSet::new(), true)
                    && self.payload_enum_closed(local, ctor, &mut HashSet::new(), false))
            } else {
                !self.payload_call_result_readers_closed(local, ctor)
            };
            if escapes {
                debug!(
                    local,
                    aggregate_built, "CHC: a narrow Option<&scalar> payload escapes; fail closed"
                );
                self.record_sound_fallback_reason("enum_ref_payload_escapes");
                return;
            }
        }
    }

    /// Whether `local` is a flattened enum whose one payload slot is as wide as
    /// a pointer or wider: it keeps the whole reference, not a value.
    fn local_keeps_payload_address(&self, local: usize) -> bool {
        let Some(layout) = self.flatten.enum_bv_layouts.get(&local) else { return false };
        if layout.max_payload_slots != 1 {
            return false;
        }
        let Some(vec_idx) = self.try_state_idx_for_local(local) else { return false };
        self.state_var_mgr
            .state_vars
            .get(vec_idx + 1)
            .is_some_and(|(_, sort)| !slot_narrower_than_pointer(sort))
    }

    /// Whether the whole value of the address-keeping enum `local` stays in
    /// address-keeping locals: it is never an aggregate's operand (an array, a
    /// tuple, a struct or an enum built from it), never stored into a place
    /// with a projection (a field, an element, a pointee), never a call's
    /// argument, and its whole copies are address-keeping locals of which the
    /// same holds. Its payload read, discriminant, borrows and drops are
    /// exact.
    fn address_payload_enum_contained(&self, local: usize, seen: &mut HashSet<usize>) -> bool {
        if !seen.insert(local) {
            return true;
        }
        let is_whole = |op: &Operand| {
            matches!(op, Operand::Copy(place) | Operand::Move(place)
                if place.local == local && place.projection.is_empty())
        };
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                match rhs {
                    Rvalue::Use(op, ..) if is_whole(op) => {
                        if !lhs.projection.is_empty()
                            || !self.local_keeps_payload_address(lhs.local)
                            || !self.address_payload_enum_contained(lhs.local, seen)
                        {
                            return false;
                        }
                    }
                    Rvalue::Aggregate(_, operands) if operands.iter().any(is_whole) => {
                        return false;
                    }
                    Rvalue::Cast(_, op, _) | Rvalue::Repeat(op, _) if is_whole(op) => {
                        return false;
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { args, .. } = &block.terminator.kind
                && args.iter().any(is_whole)
            {
                return false;
            }
        }
        true
    }

    /// The readers of the enum `local` (payload constructor `ref_ctor`) are
    /// all admitted: its discriminant; a whole copy into another local whose
    /// readers are admitted (and whose writes are, as `value_slot_local`
    /// checks); a reference out of its payload whose readers are admitted
    /// ([`Self::payload_ref_closed`]); `Option::unwrap` / `expect`, whose
    /// result is such a reference; the pointee read `(*((local as V).0))`; a
    /// shared borrow that only reaches the discriminant.
    ///
    /// `call_defined`: a call that writes the whole local is a definition (a
    /// call result's producer), not a reader.
    fn payload_enum_closed(
        &self,
        local: usize,
        ref_ctor: usize,
        seen: &mut HashSet<usize>,
        call_defined: bool,
    ) -> bool {
        if !seen.insert(local) {
            return true;
        }
        let is_payload = |place: &Place| {
            matches!(place.projection.as_slice(),
                [ProjectionElem::Downcast(v), ProjectionElem::Field(0, _)] if v.to_index() == ref_ctor)
        };
        let is_value_read = |place: &Place| {
            matches!(place.projection.as_slice(),
                [ProjectionElem::Downcast(v), ProjectionElem::Field(0, _), ProjectionElem::Deref]
                    if v.to_index() == ref_ctor)
        };
        // An operand reading the pointee, or a field of it, by value.
        let is_value_operand = |place: &Place| match place.projection.as_slice() {
            [
                ProjectionElem::Downcast(v),
                ProjectionElem::Field(0, _),
                ProjectionElem::Deref,
                rest @ ..,
            ] => {
                v.to_index() == ref_ctor
                    && rest.iter().all(|p| matches!(p, ProjectionElem::Field(..)))
            }
            _ => false,
        };
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let mut mentions = TargetPlaces::new(local);
                mentions.visit_statement(stmt, statement_location(self.body, &bb, si));
                if mentions.is_empty() {
                    continue;
                }
                if mentions.index_use {
                    return false;
                }
                let closed = match &stmt.kind {
                    // A write, checked by `value_slot_local`.
                    StatementKind::Assign(lhs, _) if lhs.local == local => {
                        lhs.projection.is_empty() && mentions.places.len() == 1
                    }
                    StatementKind::Assign(lhs, rhs) => {
                        let lhs_whole = lhs.projection.is_empty();
                        match rhs {
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                                if src.local == local && lhs_whole =>
                            {
                                if src.projection.is_empty() {
                                    self.payload_enum_closed(
                                        lhs.local,
                                        ref_ctor,
                                        seen,
                                        call_defined,
                                    )
                                } else if is_payload(src) {
                                    self.payload_ref_closed(lhs.local, seen)
                                } else {
                                    is_value_read(src)
                                }
                            }
                            Rvalue::Discriminant(place)
                                if place.local == local && place.projection.is_empty() =>
                            {
                                true
                            }
                            Rvalue::Ref(_, BorrowKind::Shared, place)
                                if place.local == local
                                    && place.projection.is_empty()
                                    && lhs_whole =>
                            {
                                self.payload_borrow_reads_discriminant_only(lhs.local, local)
                            }
                            // `&(*((local as V).0))` reborrows the payload
                            // reference itself.
                            Rvalue::Ref(_, BorrowKind::Shared, place)
                                if place.local == local && is_value_read(place) && lhs_whole =>
                            {
                                self.payload_ref_closed(lhs.local, seen)
                            }
                            // Any other borrow or address of it (`&raw const
                            // (*((local as V).0))` is the payload reference's
                            // own ADDRESS value) reaches an address reader.
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                                if place.local == local =>
                            {
                                false
                            }
                            // Operands only: a place here is read by value.
                            _ => mentions.places.iter().all(is_value_operand),
                        }
                    }
                    StatementKind::PlaceMention(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::AscribeUserType { .. } => true,
                    _ => false,
                };
                if !closed {
                    return false;
                }
            }
            let mut mentions = TargetPlaces::new(local);
            mentions.visit_terminator(&block.terminator, terminator_location(self.body, &bb));
            if mentions.is_empty() {
                continue;
            }
            if mentions.index_use {
                return false;
            }
            let closed = match &block.terminator.kind {
                TerminatorKind::Call { destination, .. } if destination.local == local => {
                    call_defined && destination.projection.is_empty() && mentions.places.len() == 1
                }
                TerminatorKind::Call { func, args, destination, .. }
                    if self.callee_is_option_method(func, &["unwrap", "expect"])
                        && matches!(args.first(), Some(Operand::Copy(src) | Operand::Move(src))
                            if src.local == local && src.projection.is_empty())
                        && mentions.places.len() == 1
                        && destination.projection.is_empty() =>
                {
                    self.payload_ref_closed(destination.local, seen)
                }
                // `Option::copied` / `cloned` read the pointee and return it by
                // value: no reference leaves.
                TerminatorKind::Call { func, args, .. }
                    if self.callee_is_option_method(func, &["copied", "cloned"])
                        && matches!(args.as_slice(), [Operand::Copy(src) | Operand::Move(src)]
                            if src.local == local && src.projection.is_empty()) =>
                {
                    true
                }
                TerminatorKind::Drop { place, .. } => {
                    place.projection.is_empty() && mentions.places.len() == 1
                }
                _ => mentions.places.iter().all(is_value_operand),
            };
            if !closed {
                return false;
            }
        }
        true
    }

    /// [`Self::payload_enum_closed`] for a reference `r` taken out of such a
    /// payload: every use other than a definition reads the pointee (`*r`),
    /// hands `r` on to another such reference (a whole copy or a shared
    /// reborrow `&(*r)`), or passes it to a function of the crate under
    /// verification that the kani inliner LEFT a call (`#[inline(never)]`),
    /// whose inline binding reads `*r` through the caller's cascade. A crate
    /// function the inliner inlined is not a call here: its parameter is a
    /// whole copy of `r` and its body's statements are checked as the caller's
    /// own, so `fn read_raw(r: &u8) -> u8 { unsafe { *(r as *const u8) } }`
    /// escapes at its `&raw const (*r)` (whose null check reads the address a
    /// narrow slot does not hold; third review: `lf_read_raw_safe` fails
    /// closed, a measured precision cost). A definition's source is not this function's question: a
    /// pointee read the value lanes do not resolve fails closed on its own
    /// ([`Self::deref_of_narrow_payload_ref_unresolved`]).
    fn payload_ref_closed(&self, r: usize, seen: &mut HashSet<usize>) -> bool {
        if !seen.insert(r) {
            return true;
        }
        let arg_count = self.body.arg_locals().len();
        if r == 0 || (1..=arg_count).contains(&r) {
            return false;
        }
        let is_deref =
            |place: &Place| matches!(place.projection.as_slice(), [ProjectionElem::Deref]);
        // An operand reading the pointee, or a field of it, by value (`(*r)`,
        // `((*r).0)` of an iterator element struct).
        let is_deref_read = |place: &Place| match place.projection.as_slice() {
            [ProjectionElem::Deref, rest @ ..] => {
                rest.iter().all(|p| matches!(p, ProjectionElem::Field(..)))
            }
            _ => false,
        };
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let mut mentions = TargetPlaces::new(r);
                mentions.visit_statement(stmt, statement_location(self.body, &bb, si));
                if mentions.is_empty() {
                    continue;
                }
                if mentions.index_use {
                    return false;
                }
                let closed = match &stmt.kind {
                    StatementKind::Assign(lhs, _) if lhs.local == r => {
                        lhs.projection.is_empty() && mentions.places.len() == 1
                    }
                    StatementKind::Assign(lhs, rhs) => {
                        let lhs_whole = lhs.projection.is_empty();
                        match rhs {
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                                if src.local == r && src.projection.is_empty() && lhs_whole =>
                            {
                                self.payload_ref_closed(lhs.local, seen)
                            }
                            Rvalue::Ref(_, BorrowKind::Shared, src)
                                if src.local == r && is_deref(src) && lhs_whole =>
                            {
                                self.payload_ref_closed(lhs.local, seen)
                            }
                            // `&raw const (*r)` is `r`'s own ADDRESS value (the
                            // coercion `ptr::eq(r, ..)` inlines to), and `&r`
                            // lets `r` escape: address readers.
                            Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                                if src.local == r =>
                            {
                                false
                            }
                            // Operands only: `(*r)` here is read by value.
                            _ => mentions.places.iter().all(is_deref_read),
                        }
                    }
                    StatementKind::PlaceMention(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::AscribeUserType { .. } => true,
                    _ => false,
                };
                if !closed {
                    return false;
                }
            }
            let mut mentions = TargetPlaces::new(r);
            mentions.visit_terminator(&block.terminator, terminator_location(self.body, &bb));
            if mentions.is_empty() {
                continue;
            }
            if mentions.index_use {
                return false;
            }
            let closed = match &block.terminator.kind {
                // A definition (`r = unwrap(o)`).
                TerminatorKind::Call { destination, .. } if destination.local == r => {
                    destination.projection.is_empty() && mentions.places.len() == 1
                }
                TerminatorKind::Call { func, args, .. } if self.callee_is_local_fn(func) => {
                    args.iter().all(|arg| match arg {
                        Operand::Copy(place) | Operand::Move(place) if place.local == r => {
                            place.projection.is_empty() || is_deref(place)
                        }
                        _ => true,
                    }) && mentions.places.iter().all(|p| p.projection.is_empty() || is_deref(p))
                }
                _ => mentions.places.iter().all(is_deref_read),
            };
            if !closed {
                return false;
            }
        }
        true
    }

    /// Whether the shared borrow `t = &enum_local` only reaches the enum by
    /// value: every use is `discriminant(*t)`, the argument of
    /// `Option::is_some` / `is_none` or of `<Option<_> as PartialEq>::eq` /
    /// `ne` (which compare the pointees by value) or of the diverging
    /// `assert_failed`, a whole copy or shared reborrow into another such
    /// borrow, or an operand of a tuple whose matching field is read only into
    /// another such borrow (`assert_eq!(first(&a), None)` builds
    /// `(&left, &right)` and matches it apart).
    fn payload_borrow_reads_discriminant_only(&self, t: usize, enum_local: usize) -> bool {
        let _ = enum_local;
        self.payload_borrow_closed(t, &mut HashSet::new())
    }

    fn payload_borrow_closed(&self, t: usize, seen: &mut HashSet<usize>) -> bool {
        if !seen.insert(t) {
            return true;
        }
        let arg_count = self.body.arg_locals().len();
        if t == 0 || (1..=arg_count).contains(&t) {
            return false;
        }
        let whole = |op: &Operand| {
            matches!(op, Operand::Copy(place) | Operand::Move(place)
                if place.local == t && place.projection.is_empty())
        };
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let mut mentions = TargetPlaces::new(t);
                mentions.visit_statement(stmt, statement_location(self.body, &bb, si));
                if mentions.is_empty() {
                    continue;
                }
                if mentions.index_use {
                    return false;
                }
                let closed = match &stmt.kind {
                    // A definition.
                    StatementKind::Assign(lhs, _) if lhs.local == t => {
                        lhs.projection.is_empty() && mentions.places.len() == 1
                    }
                    StatementKind::Assign(_, Rvalue::Discriminant(place)) => {
                        place.local == t
                            && matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                    }
                    StatementKind::Assign(lhs, Rvalue::Use(op, ..))
                        if whole(op) && lhs.projection.is_empty() =>
                    {
                        self.payload_borrow_closed(lhs.local, seen)
                    }
                    // A shared reborrow `&(*t)` is the same borrow.
                    StatementKind::Assign(lhs, Rvalue::Ref(_, BorrowKind::Shared, src))
                        if src.local == t
                            && matches!(src.projection.as_slice(), [ProjectionElem::Deref])
                            && lhs.projection.is_empty() =>
                    {
                        self.payload_borrow_closed(lhs.local, seen)
                    }
                    StatementKind::Assign(lhs, Rvalue::Aggregate(AggregateKind::Tuple, ops))
                        if lhs.projection.is_empty() && mentions.places.len() == 1 =>
                    {
                        match ops.iter().position(|op| whole(op)) {
                            Some(idx) => {
                                self.payload_borrow_tuple_field_closed(lhs.local, idx, seen)
                            }
                            None => false,
                        }
                    }
                    StatementKind::PlaceMention(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::AscribeUserType { .. } => true,
                    _ => false,
                };
                if !closed {
                    return false;
                }
            }
            let mut mentions = TargetPlaces::new(t);
            mentions.visit_terminator(&block.terminator, terminator_location(self.body, &bb));
            if mentions.is_empty() {
                continue;
            }
            let closed = match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    destination.local != t
                        && !mentions.index_use
                        && ((self.callee_is_option_method(func, &["is_some", "is_none"])
                            && matches!(args.as_slice(), [Operand::Copy(src) | Operand::Move(src)]
                                if src.local == t && src.projection.is_empty()))
                            // `<Option<&T> as PartialEq>::eq` / `ne` compare the
                            // pointees by VALUE (`assert_eq!(v.first(), None)`).
                            || ((self.callee_is_option_partial_eq(func)
                                || self.callee_is_assert_failed(func))
                                && args.iter().all(|arg| match arg {
                                    Operand::Copy(src) | Operand::Move(src) => {
                                        src.local != t || src.projection.is_empty()
                                    }
                                    _ => true,
                                })))
                }
                TerminatorKind::Drop { place, .. } => {
                    place.local == t && place.projection.is_empty()
                }
                _ => false,
            };
            if !closed {
                return false;
            }
        }
        true
    }

    /// Whether the tuple `agg`, whose field `idx` holds a borrow of the enum,
    /// is read only field by field, and field `idx` only into a borrow held to
    /// [`Self::payload_borrow_closed`].
    fn payload_borrow_tuple_field_closed(
        &self,
        agg: usize,
        idx: usize,
        seen: &mut HashSet<usize>,
    ) -> bool {
        let arg_count = self.body.arg_locals().len();
        if agg == 0 || (1..=arg_count).contains(&agg) {
            return false;
        }
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let mut mentions = TargetPlaces::new(agg);
                mentions.visit_statement(stmt, statement_location(self.body, &bb, si));
                if mentions.is_empty() {
                    continue;
                }
                if mentions.index_use {
                    return false;
                }
                let closed = match &stmt.kind {
                    StatementKind::Assign(lhs, _) if lhs.local == agg => {
                        lhs.projection.is_empty() && mentions.places.len() == 1
                    }
                    StatementKind::Assign(
                        lhs,
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..),
                    ) if src.local == agg && lhs.projection.is_empty() => {
                        match src.projection.as_slice() {
                            [ProjectionElem::Field(field, _)] if *field == idx => {
                                self.payload_borrow_closed(lhs.local, seen)
                            }
                            [ProjectionElem::Field(..)] => true,
                            _ => false,
                        }
                    }
                    StatementKind::PlaceMention(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::AscribeUserType { .. } => true,
                    _ => false,
                };
                if !closed {
                    return false;
                }
            }
            let mut mentions = TargetPlaces::new(agg);
            mentions.visit_terminator(&block.terminator, terminator_location(self.body, &bb));
            if mentions.is_empty() {
                continue;
            }
            let closed = matches!(&block.terminator.kind,
                TerminatorKind::Drop { place, .. } if place.local == agg && place.projection.is_empty());
            if !closed {
                return false;
            }
        }
        true
    }

    /// Whether every reader of the enum `local` (payload constructor
    /// `ref_ctor`) that a CALL defines is an admitted value reader
    /// ([`Self::payload_enum_closed`], with call definitions admitted): the slot
    /// of a call result may hold the pointee's value (the slice iterator stub
    /// stores the ELEMENT, an inlined `first()` or crate function stores the
    /// narrow value), so a reader that wants the reference's address must not
    /// reach it.
    ///
    /// An allowlist: a reader it does not name — the enum or its payload
    /// handed to `Option::map` / `is_some_and` / `filter` and their closures,
    /// to `core::hint::black_box` or any other call, moved into a struct, a
    /// tuple or an array — is an escape. The denylist it replaces (casts,
    /// `&raw const (*r)`, `core::ptr` and raw-pointer methods, over the payload
    /// references reached without a call) missed all of those: `a.iter().next()
    /// .map(|r| r as *const u8 as usize)` FAILED certified Genuine where Kani
    /// proves it, and its `should_panic` twin passed (third review of
    /// fix/chc-false-certificates, 2026-09-27: `it_map_addr_safe`,
    /// `first_map_ptr_eq_safe`, `it_blackbox_safe`, `it_struct64_ptr_eq_safe`).
    pub(in crate::codegen_ay::chc) fn payload_call_result_readers_closed(
        &self,
        local: usize,
        ref_ctor: usize,
    ) -> bool {
        self.payload_enum_closed(local, ref_ctor, &mut HashSet::new(), true)
    }

    /// Whether `r` may hold a narrow `Option<&scalar>` payload rather than an
    /// address: some definition copies such a payload, is `Option::unwrap` /
    /// `expect` / `unwrap_unchecked` of such an enum, or copies or reborrows
    /// such a reference. A pointee read through it that the value lanes did
    /// not resolve would load typed memory at the VALUE.
    pub(in crate::codegen_ay::chc) fn deref_of_narrow_payload_ref_unresolved(
        &self,
        r: usize,
    ) -> bool {
        let narrow_ref = self.body.locals().get(r).is_some_and(|decl| {
            shared_scalar_pointee(self.resolve_body_ty(decl.ty))
                .and_then(Self::translate_ty)
                .is_some_and(|sort| slot_narrower_than_pointer(&sort))
        });
        if !narrow_ref {
            return false;
        }
        let mut visiting = HashSet::new();
        self.ref_may_hold_narrow_payload(r, &mut visiting)
    }

    fn ref_may_hold_narrow_payload(&self, r: usize, visiting: &mut HashSet<usize>) -> bool {
        if !visiting.insert(r) || r >= self.body.locals().len() {
            return false;
        }
        let narrow_enum = |local: usize| {
            self.body.locals().get(local).and_then(|decl| self.narrow_ref_option_ctor(decl.ty))
        };
        self.body.blocks.iter().any(|block| {
            block.statements.iter().any(|stmt| match &stmt.kind {
                StatementKind::Assign(lhs, rhs) if lhs.local == r && lhs.projection.is_empty() => {
                    match rhs {
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
                            match src.projection.as_slice() {
                                [] => self.ref_may_hold_narrow_payload(src.local, visiting),
                                [ProjectionElem::Downcast(v), ProjectionElem::Field(0, _)] => {
                                    narrow_enum(src.local) == Some(v.to_index())
                                }
                                _ => false,
                            }
                        }
                        Rvalue::Ref(_, BorrowKind::Shared, src) => {
                            matches!(src.projection.as_slice(), [ProjectionElem::Deref])
                                && self.ref_may_hold_narrow_payload(src.local, visiting)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }) || matches!(&block.terminator.kind, TerminatorKind::Call { func, args, destination, .. }
                if destination.local == r
                    && self.callee_is_option_method(func, &["unwrap", "expect", "unwrap_unchecked"])
                    && matches!(args.first(), Some(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() && narrow_enum(src.local).is_some()))
        })
    }

    /// The pointee read `*place` resolves to when the pointer came out of a
    /// value-semantic reference payload (module documentation), or `None`.
    pub(in crate::codegen_ay::chc) fn try_resolve_value_payload_deref(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified: &HashSet<usize>,
    ) -> Option<Expr> {
        match place.projection.as_slice() {
            [
                ProjectionElem::Downcast(variant),
                ProjectionElem::Field(0, field_ty),
                ProjectionElem::Deref,
            ] => {
                let pointee = shared_scalar_pointee(self.resolve_body_ty(*field_ty))?;
                let vec_idx = self.try_state_idx_for_local(local_idx)?;
                if self.value_semantic_ref_enum(local_idx, vec_idx)? != variant.to_index()
                    || !self.value_slot_local(local_idx)
                {
                    return None;
                }
                let payload =
                    Place { local: local_idx, projection: place.projection[..2].to_vec() };
                let value = self.translate_place_with_modified(&payload, modified)?;
                let sort = Self::translate_ty(pointee)?;
                (*value.sort() == sort).then(|| {
                    debug!(local_idx, "CHC: deref of a value-semantic payload: the payload value");
                    value
                })
            }
            [ProjectionElem::Deref] => {
                let ty = self.resolve_body_ty(self.body.locals().get(local_idx)?.ty);
                let pointee = shared_scalar_pointee(ty)?;
                if !self.value_payload_ref_local(local_idx, &mut HashSet::new()) {
                    return None;
                }
                let sort = Self::translate_ty(pointee)?;
                let register = self.translate_place_with_modified(
                    &Place { local: local_idx, projection: Vec::new() },
                    modified,
                )?;
                let value = if *register.sort() == sort {
                    register
                } else {
                    let width = register.sort().bitvec_width()?;
                    match sort.bitvec_width() {
                        Some(bits) if bits <= width => {
                            if bits == width {
                                register
                            } else {
                                register.extract(bits - 1, 0)
                            }
                        }
                        None if sort.is_bool() => register.ne(Expr::bitvec_const(0u64, width)),
                        _ => return None,
                    }
                };
                debug!(local_idx, "CHC: deref of a copied value-semantic payload: its register");
                Some(value)
            }
            _ => None,
        }
    }

    /// Fail closed when the reference an index stub returned reaches a reader
    /// that takes it for an ADDRESS. `Index::index` / `IndexMut::index_mut` /
    /// `get_unchecked` put the ELEMENT in the reference's register
    /// (`call::codegen_call_slice_index`: the element is the `const_ref_values`
    /// entry the pointee reads resolve to, and the register's value), so a cast
    /// of it read the element: `&v[1] as *const u8 as usize == 3` for `v =
    /// vec![2u8, 3, 4]` was a clean proof where Kani fails the assertion, its
    /// `should_panic` twin passed, and `ptr::eq(&v[1], v.as_ptr().add(1))`
    /// FAILED certified Genuine (on main c22e1022e and the branch alike;
    /// found probing the third review's address findings, 2026-09-28). Checked
    /// once every block is translated, by allowlist
    /// ([`Self::index_value_ref_closed`]).
    pub(in crate::codegen_ay::chc) fn book_escaping_index_value_refs(&self) {
        let mut dests: Vec<usize> =
            self.ref_resolution.index_value_ref_dests.iter().copied().collect();
        dests.sort_unstable();
        for r in dests {
            if !self.index_value_ref_closed(r, &mut HashSet::new()) {
                debug!(r, "CHC: an index result holding the element reaches an address reader");
                self.record_sound_fallback_reason("index_ref_value_escapes");
                return;
            }
        }
    }

    /// Whether every reader of the index result `r`, whose register holds the
    /// element, is admitted: its definition; a read of the element or a field
    /// of it by value (`(*r)`, `((*r).0)`); a store through it (`(*r) = v`,
    /// the `IndexMut` write the collection lane propagates); a whole copy, or
    /// a reborrow of the element or a field of it (`&(*r)`, `&mut (*r)`,
    /// `&((*r).0)`), into a local held to the same rule; a tuple field read
    /// only into such a local (`assert_eq!` builds `(&left, &right)`); the
    /// diverging `assert_failed`; a function of the crate under verification
    /// the kani inliner left a call; a drop. Anything else — a cast, `&raw
    /// const (*r)`, a comparison of the reference itself, any other call or a
    /// move into an aggregate — is an escape.
    fn index_value_ref_closed(&self, r: usize, seen: &mut HashSet<usize>) -> bool {
        if !seen.insert(r) {
            return true;
        }
        let arg_count = self.body.arg_locals().len();
        if r == 0 || (1..=arg_count).contains(&r) {
            return false;
        }
        let is_deref_read = |place: &Place| match place.projection.as_slice() {
            [ProjectionElem::Deref, rest @ ..] => {
                rest.iter().all(|p| matches!(p, ProjectionElem::Field(..)))
            }
            _ => false,
        };
        let whole = |op: &Operand| {
            matches!(op, Operand::Copy(place) | Operand::Move(place)
                if place.local == r && place.projection.is_empty())
        };
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let mut mentions = TargetPlaces::new(r);
                mentions.visit_statement(stmt, statement_location(self.body, &bb, si));
                if mentions.is_empty() {
                    continue;
                }
                if mentions.index_use {
                    return false;
                }
                let closed = match &stmt.kind {
                    StatementKind::Assign(lhs, _) if lhs.local == r => {
                        if lhs.projection.is_empty() {
                            mentions.places.len() == 1
                        } else {
                            mentions.places.iter().all(is_deref_read)
                        }
                    }
                    StatementKind::Assign(lhs, rhs) => {
                        let lhs_whole = lhs.projection.is_empty();
                        match rhs {
                            Rvalue::Use(op, ..) if whole(op) && lhs_whole => {
                                self.index_value_ref_closed(lhs.local, seen)
                            }
                            Rvalue::Ref(_, _, src)
                                if src.local == r && is_deref_read(src) && lhs_whole =>
                            {
                                self.index_value_ref_closed(lhs.local, seen)
                            }
                            Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                                if src.local == r =>
                            {
                                false
                            }
                            Rvalue::Aggregate(AggregateKind::Tuple, ops)
                                if lhs_whole
                                    && mentions
                                        .places
                                        .iter()
                                        .all(|p| p.projection.is_empty() || is_deref_read(p)) =>
                            {
                                ops.iter().enumerate().filter(|(_, op)| whole(op)).all(
                                    |(idx, _)| {
                                        self.index_value_ref_tuple_field_closed(
                                            lhs.local, idx, seen,
                                        )
                                    },
                                )
                            }
                            _ => mentions.places.iter().all(is_deref_read),
                        }
                    }
                    StatementKind::PlaceMention(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::AscribeUserType { .. } => true,
                    _ => false,
                };
                if !closed {
                    return false;
                }
            }
            let mut mentions = TargetPlaces::new(r);
            mentions.visit_terminator(&block.terminator, terminator_location(self.body, &bb));
            if mentions.is_empty() {
                continue;
            }
            if mentions.index_use {
                return false;
            }
            let closed = match &block.terminator.kind {
                TerminatorKind::Call { destination, .. } if destination.local == r => {
                    destination.projection.is_empty() && mentions.places.len() == 1
                }
                TerminatorKind::Call { func, .. }
                    if self.callee_is_local_fn(func) || self.callee_is_assert_failed(func) =>
                {
                    mentions.places.iter().all(|p| p.projection.is_empty() || is_deref_read(p))
                }
                TerminatorKind::Drop { place, .. } => {
                    place.projection.is_empty() && mentions.places.len() == 1
                }
                _ => mentions.places.iter().all(is_deref_read),
            };
            if !closed {
                return false;
            }
        }
        true
    }

    /// Whether the tuple `agg`, whose field `idx` holds an index result, is
    /// read only field by field, and field `idx` only into a local held to
    /// [`Self::index_value_ref_closed`].
    fn index_value_ref_tuple_field_closed(
        &self,
        agg: usize,
        idx: usize,
        seen: &mut HashSet<usize>,
    ) -> bool {
        let arg_count = self.body.arg_locals().len();
        if agg == 0 || (1..=arg_count).contains(&agg) {
            return false;
        }
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let mut mentions = TargetPlaces::new(agg);
                mentions.visit_statement(stmt, statement_location(self.body, &bb, si));
                if mentions.is_empty() {
                    continue;
                }
                if mentions.index_use {
                    return false;
                }
                let closed = match &stmt.kind {
                    StatementKind::Assign(lhs, _) if lhs.local == agg => {
                        lhs.projection.is_empty() && mentions.places.len() == 1
                    }
                    StatementKind::Assign(
                        lhs,
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..),
                    ) if src.local == agg && lhs.projection.is_empty() => {
                        match src.projection.as_slice() {
                            [ProjectionElem::Field(field, _)] if *field == idx => {
                                self.index_value_ref_closed(lhs.local, seen)
                            }
                            [ProjectionElem::Field(..)] => true,
                            _ => false,
                        }
                    }
                    StatementKind::PlaceMention(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::AscribeUserType { .. } => true,
                    _ => false,
                };
                if !closed {
                    return false;
                }
            }
            let mut mentions = TargetPlaces::new(agg);
            mentions.visit_terminator(&block.terminator, terminator_location(self.body, &bb));
            if mentions.is_empty() {
                continue;
            }
            let closed = matches!(&block.terminator.kind,
                TerminatorKind::Drop { place, .. } if place.local == agg && place.projection.is_empty());
            if !closed {
                return false;
            }
        }
        true
    }
}

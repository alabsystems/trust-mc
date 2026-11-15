// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The global-object lane of the offset-provenance walk: the static or
//! constant allocation a pointer local provably points into, and the access
//! bound a dereference through it must meet.
//!
//! `heap_access_checks` bounds an access only when the address's obj_id lane
//! folds to a constant. A pointer derived from a constant pointer
//! (`let p: *const u32 = &V;` is `_1 = &raw const (*_2)` with
//! `_2 = const {&V}`) and then moved (`p.add(1)`) reaches its dereference
//! through block-crossing state variables, so its obj_id lane is opaque and
//! no bound was ever stated. On main these out-of-bounds reads failed only by
//! accident: the use-after-scope check read `_2`'s `StorageDead` as the death
//! of the pointee and staged a constant-false obligation (which also failed
//! every SAFE dereference through such a pointer). Once that false obligation
//! was removed (`ref_target_through_constant`), `*p.add(1)` past a static
//! proved clean on the CHC lane where Kani reports "dereference failure:
//! pointer outside object bounds".
//!
//! This lane states the real bound. The walk is the shared fail-closed
//! provenance walk (`provenance_terminal_with`), ending at a constant pointer
//! whose target is a minted global object (`decl::global_objects`) of known
//! byte length. Its hop precondition is "written exactly once, directly":
//! the local has one whole-local definition and no other write can reach it
//! (its own storage's address is never taken and no projection of it is
//! written). The CHC lane addresses a global object as `concat(obj_id, k)`
//! with `k` the byte offset into the WHOLE allocation, so the bound is the
//! allocation's extent however far into it the constant points.

use std::cell::RefCell;
use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Body, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::codegen_stmt_rvalue_offset::OffsetProvenanceStep;
use crate::args::ChcTrackLevel;

/// Locals some statement can write OTHER than through one whole-local
/// assignment: the local's own storage has its address taken (`&x`,
/// `&raw mut x`, `&x.f`; a place whose first projection is not a `Deref`), or
/// a projection of it is written (`x.f = ..`, `SetDiscriminant`, a
/// call destination with a projection). A local outside this set with one
/// whole-local definition holds that definition's value wherever it is live.
pub(super) fn locals_written_indirectly(body: &Body) -> HashSet<usize> {
    locals_written_indirectly_with(body, &|_| false)
}

/// [`locals_written_indirectly`], except that a SHARED borrow of a whole
/// local for which `freeze(local)` holds is not a write: nothing may write a
/// `Freeze` value through a shared reference (`let pp = &p; *(*pp).add(1)`).
pub(super) fn locals_written_indirectly_with(
    body: &Body,
    freeze: &dyn Fn(usize) -> bool,
) -> HashSet<usize> {
    use rustc_public::mir::BorrowKind;
    let mut out = HashSet::new();
    let own_storage = |place: &rustc_public::mir::Place| {
        !matches!(place.projection.first(), Some(ProjectionElem::Deref))
    };
    for bb in &body.blocks {
        for stmt in &bb.statements {
            match &stmt.kind {
                StatementKind::Assign(lhs, rhs) => {
                    if !lhs.projection.is_empty() && own_storage(lhs) {
                        out.insert(lhs.local);
                    }
                    let shared_freeze = matches!(
                        rhs,
                        Rvalue::Ref(_, BorrowKind::Shared, place)
                            if place.projection.is_empty() && freeze(place.local)
                    );
                    if let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rhs
                        && own_storage(place)
                        && !shared_freeze
                    {
                        out.insert(place.local);
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    out.insert(place.local);
                }
                _ => {}
            }
        }
        match &bb.terminator.kind {
            TerminatorKind::Call { destination, .. }
                if !destination.projection.is_empty() && own_storage(destination) =>
            {
                out.insert(destination.local);
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                out.extend(operands.iter().filter_map(|op| op.out_place.as_ref()).map(|p| p.local));
            }
            _ => {}
        }
    }
    out
}

/// One hop of the exact-offset walk (`const_pointer_delta`).
enum DeltaStep {
    /// From `.0`, displaced by `.1` bytes.
    Through(usize, i128),
    /// The constant pointer itself, at this byte offset into its object.
    Constant(i128),
}

/// What a pointer local provably derives from, through the provenance walk
/// from a constant pointer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum ConstProvenance {
    /// The global object `obj_id` of `size` bytes (a static or constant
    /// memory).
    Object { obj_id: u32, size: u32 },
    /// A bare integer address with no provenance (`0x1000 as *const u32`,
    /// `NonNull::dangling()`): no access through it is in any allocation
    /// (Kani: "dereference failure: invalid integer address").
    Integer,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// `(obj_id, byte_length)` of the global object (a static, or constant
    /// memory) that pointer local `local` provably points into: the
    /// provenance walk from `local` ends at a constant pointer whose target is
    /// a minted global object of known length. `None` for anything else
    /// (fail-open: no bound is invented).
    pub(in crate::codegen_ay::chc) fn const_object_provenance_for_local(
        &self,
        local: usize,
    ) -> Option<(u32, u32)> {
        match self.const_provenance_for_local(local)? {
            ConstProvenance::Object { obj_id, size } => Some((obj_id, size)),
            ConstProvenance::Integer => None,
        }
    }

    /// [`Self::const_object_provenance_for_local`], also answering for a
    /// pointer that derives from a constant INTEGER address.
    pub(in crate::codegen_ay::chc) fn const_provenance_for_local(
        &self,
        local: usize,
    ) -> Option<ConstProvenance> {
        if self.int_lift || self.track_level < ChcTrackLevel::Mem {
            return None;
        }
        let visited = RefCell::new(Vec::new());
        let terminal = self.provenance_terminal_with(
            local,
            &|hop| {
                visited.borrow_mut().push(hop);
                self.encode.raw_single_assign_locals.contains(&hop)
            },
            true,
        )?;
        let key = match terminal {
            OffsetProvenanceStep::ConstRef(_, Some(key))
            | OffsetProvenanceStep::ConstRawPtr(Some(key), _) => Some(key),
            OffsetProvenanceStep::ConstRawPtr(None, true) => None,
            _ => return None,
        };
        // The walk reached a constant: the precondition's second half, once,
        // over every local it passed through.
        let indirect = self.const_lane_written_indirectly();
        if visited.borrow().iter().any(|hop| indirect.contains(hop)) {
            debug!(local, "const-object lane: refused (a walked local is written indirectly)");
            return None;
        }
        let Some(key) = key else {
            debug!(local, "const-object lane: resolved a constant integer address");
            return Some(ConstProvenance::Integer);
        };
        let object = self.global_object(&key)?;
        let size = u32::try_from(object.size?).ok()?;
        debug!(local, obj_id = object.obj_id, size, "const-object lane: resolved global object");
        Some(ConstProvenance::Object { obj_id: object.obj_id, size })
    }

    /// The obligations an `access_size`-byte access at `addr` through the
    /// pointer `ptr_local` (of provenance `provenance`) must meet. When the
    /// access starts `displacement` bytes past the pointer and the pointer's
    /// own offset into the object is a constant ([`Self::const_pointer_delta`]),
    /// the bound folds: nothing for an access inside the object, an
    /// unconditional failure for one outside it. A symbolic bound on a
    /// block-crossing pointer costs the solver an invariant over the pointer's
    /// value; `PTR += 1` on a `static mut` (`modifies/global_pass.rs`) went
    /// from 5 s to 17 s on it.
    pub(in crate::codegen_ay::chc) fn const_provenance_checks(
        &self,
        provenance: ConstProvenance,
        ptr_local: usize,
        addr: Option<&Expr>,
        access_size: u32,
        displacement: Option<u64>,
    ) -> Vec<Expr> {
        match provenance {
            ConstProvenance::Object { obj_id, size } => {
                if let Some(displacement) = displacement
                    && let Some(delta) = self.const_pointer_delta(ptr_local)
                {
                    let start = delta + i128::from(displacement);
                    let inside = start >= 0 && start + i128::from(access_size) <= i128::from(size);
                    debug!(
                        ptr_local,
                        start, access_size, size, inside, "const-object lane: folded"
                    );
                    return if inside { Vec::new() } else { vec![Expr::bool_const(false)] };
                }
                addr.map(|addr| self.object_span_checks(addr, access_size, size, obj_id))
                    .unwrap_or_default()
            }
            ConstProvenance::Integer => vec![Expr::bool_const(false)],
        }
    }

    /// The locals the global-object lane must refuse as hops
    /// ([`locals_written_indirectly_with`]): a shared borrow of a `Freeze`
    /// local does not count.
    pub(super) fn const_lane_written_indirectly(&self) -> HashSet<usize> {
        locals_written_indirectly_with(self.body, &|local| {
            self.body.locals().get(local).is_some_and(|decl| {
                !crate::codegen_ay::foreign_defs::ty_has_interior_mut(self.tcx, decl.ty)
            })
        })
    }

    /// `local`'s one definition copies a FIELD of an aggregate local out
    /// (`_6 = copy (_1.0)`, `_6 = copy ((_1.0: H).1)`), and each aggregate on
    /// the way is built by one whole-local struct or tuple aggregate
    /// (`_1 = H { p: move _2 }`, `_1 = (move _2, const 0_u8)`); or `local`
    /// IS a one-field struct (`NonNull { pointer: move _5 }`); or it reads a
    /// value through a shared reference (`copy (*_3)` with `_3 = &_1`,
    /// [`Self::shared_borrow_source`]). Returns the locals passed through and
    /// the operand `local`'s pointer was built from. The caller holds every
    /// local passed through to its own hop precondition (one definition,
    /// never written through a projection, address never taken but by a
    /// shared borrow of a `Freeze` value), which is what makes the field
    /// still hold that operand.
    pub(super) fn pointer_field_source(
        &self,
        local: usize,
    ) -> Option<(Vec<usize>, rustc_public::mir::Operand)> {
        use rustc_public::mir::{AggregateKind, Operand};
        let whole_def = |target: usize| {
            self.body.blocks.iter().flat_map(|bb| &bb.statements).find_map(|stmt| {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rhs)
                        if lhs.local == target && lhs.projection.is_empty() =>
                    {
                        Some(rhs)
                    }
                    _ => None,
                }
            })
        };
        let struct_kind = |kind: &AggregateKind| match kind {
            AggregateKind::Tuple => true,
            AggregateKind::Adt(def, _, _, _, None) => {
                def.kind() == rustc_public::ty::AdtKind::Struct
            }
            _ => false,
        };
        let src = match whole_def(local) {
            Some(Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)) => src,
            // A one-field struct IS its field (`NonNull { pointer: p }`, which
            // `NonNull::new_unchecked` inlines to).
            Some(Rvalue::Aggregate(kind, ops)) if struct_kind(kind) && ops.len() == 1 => {
                return Some((Vec::new(), ops[0].clone()));
            }
            _ => return None,
        };
        if src.projection.is_empty() {
            return None;
        }
        // `_6 = copy (*_3)` with `_3 = &_1`: the value of `_1`, which the
        // shared borrow cannot change (`let pp = &p; *(*pp).add(1)`).
        // `_6 = copy ((*_4).0)` with `_4 = &_1`: a field of the struct
        // `_1` the shared borrow names (`let r = &h; *r.p.add(1)`).
        let (mut aggregate, mut aggregates, fields) = match src.projection.as_slice() {
            [ProjectionElem::Deref] => return self.shared_borrow_source(src.local),
            [ProjectionElem::Deref, fields @ ..] => {
                let (through, borrowed) = self.shared_borrow_source(src.local)?;
                let (Operand::Copy(x) | Operand::Move(x)) = borrowed else { return None };
                (x.local, through, fields)
            }
            fields => (src.local, Vec::new(), fields),
        };
        let mut operand = None;
        for (i, elem) in fields.iter().enumerate() {
            let ProjectionElem::Field(idx, _) = elem else { return None };
            if let Some(Operand::Copy(p) | Operand::Move(p)) = &operand {
                if !p.projection.is_empty() {
                    return None;
                }
                aggregate = p.local;
            } else if i > 0 {
                return None;
            }
            aggregates.push(aggregate);
            let Some(Rvalue::Aggregate(kind, ops)) = whole_def(aggregate) else {
                return None;
            };
            if !struct_kind(kind) {
                return None;
            }
            operand = Some(ops.get(*idx)?.clone());
        }
        Some((aggregates, operand?))
    }

    /// `r` holds a SHARED borrow of a whole local `x` (`_3 = &_1`, or a copy
    /// of such a reference: an inlined callee's `self` is `_13 = move _8`):
    /// `([r, .., x], copy x)`, the value `*r` reads, with every local passed
    /// through.
    fn shared_borrow_source(&self, r: usize) -> Option<(Vec<usize>, rustc_public::mir::Operand)> {
        use rustc_public::mir::{BorrowKind, Operand, Place};
        let def_of = |target: usize| {
            self.body.blocks.iter().flat_map(|bb| &bb.statements).find_map(|stmt| {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rhs)
                        if lhs.local == target && lhs.projection.is_empty() =>
                    {
                        Some(rhs)
                    }
                    _ => None,
                }
            })
        };
        let mut through = vec![r];
        let mut r = r;
        for _ in 0..8 {
            match def_of(r)? {
                Rvalue::Ref(_, BorrowKind::Shared, borrowed) if borrowed.projection.is_empty() => {
                    let x = borrowed.local;
                    through.push(x);
                    return Some((
                        through,
                        Operand::Copy(Place { local: x, projection: Vec::new() }),
                    ));
                }
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                    if src.projection.is_empty() && !through.contains(&src.local) =>
                {
                    r = src.local;
                    through.push(r);
                }
                _ => return None,
            }
        }
        None
    }

    /// `local` is the destination of a call that passes the pointer through
    /// unchanged: `NonNull::new_unchecked(p)`, `as_ptr(n)`, `cast(n)`
    /// (`NonNull` is `repr(transparent)` over the pointer), `as_ref(&n)`,
    /// whose receiver is a shared borrow of the `NonNull` local `n`, or an
    /// atomic's `from_ptr(p)`. Returns the locals passed through and the
    /// operand whose value `local` holds.
    pub(super) fn nonnull_call_source(
        &self,
        local: usize,
    ) -> Option<(Vec<usize>, rustc_public::mir::Operand)> {
        use rustc_public::mir::Operand;
        let (func, args) = self.body.blocks.iter().find_map(|bb| match &bb.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. }
                if destination.local == local && destination.projection.is_empty() =>
            {
                Some((func, args))
            }
            _ => None,
        })?;
        let path = self.resolve_callee_path(func)?;
        let arg = args.first()?.clone();
        // `AtomicU32::from_ptr(p)` is `&*p.cast()` (an atomic is
        // `repr(C, align)` over its scalar): the reference holds `p`.
        if path.contains("sync::atomic") && path.ends_with("::from_ptr") {
            return Some((Vec::new(), arg));
        }
        if !path.contains("NonNull") {
            return None;
        }
        if path.ends_with("::new_unchecked")
            || path.ends_with("::as_ptr")
            || path.ends_with("::cast")
        {
            return Some((Vec::new(), arg));
        }
        if path.ends_with("::as_ref") {
            let (Operand::Copy(r) | Operand::Move(r)) = &arg else { return None };
            if !r.projection.is_empty() {
                return None;
            }
            return self.shared_borrow_source(r.local);
        }
        None
    }

    /// The exact byte offset, from its object's base, of the pointer `start`
    /// holds: the provenance walk with every hop's displacement a constant (a
    /// copy, a pointer cast, a reborrow `&(*p).f` / `&(*p)[k]` at a constant
    /// field or element offset, `add` / `sub` / `offset`, their `byte_` and
    /// `wrapping_` forms and the Kani offset model by a constant count),
    /// ending at a constant pointer, whose own offset is its relocation's.
    /// `None` when any hop's displacement is not a constant, or the walk
    /// leaves the hops it understands.
    pub(in crate::codegen_ay::chc) fn const_pointer_delta(&self, start: usize) -> Option<i128> {
        let indirect = self.const_lane_written_indirectly();
        let mut local = start;
        let mut delta: i128 = 0;
        let mut seen = HashSet::from([local]);
        for _ in 0..32 {
            if !self.encode.raw_single_assign_locals.contains(&local) || indirect.contains(&local) {
                return None;
            }
            match self.const_pointer_delta_step(local)? {
                DeltaStep::Through(src, step) => {
                    delta = delta.checked_add(step)?;
                    if !seen.insert(src) {
                        return None;
                    }
                    local = src;
                }
                DeltaStep::Constant(offset) => return delta.checked_add(offset),
            }
        }
        None
    }

    /// One hop of [`Self::const_pointer_delta`]: the unique definition of
    /// `local`.
    fn const_pointer_delta_step(&self, local: usize) -> Option<DeltaStep> {
        use rustc_public::mir::{AggregateKind, CastKind, Operand};
        let operand_local = |op: &Operand| match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        };
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                return match rhs {
                    // A pointer copied out of an aggregate's field: the
                    // operand the field was built from, with every aggregate
                    // on the way held to the same precondition as a hop.
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                        if !src.projection.is_empty() =>
                    {
                        let indirect = self.const_lane_written_indirectly();
                        let (aggregates, operand) = self.pointer_field_source(local)?;
                        if aggregates.iter().any(|aggregate| {
                            !self.encode.raw_single_assign_locals.contains(aggregate)
                                || indirect.contains(aggregate)
                        }) {
                            return None;
                        }
                        match operand {
                            Operand::Constant(c) => {
                                use crate::codegen_ay::shared::const_pointer::ConstRead;
                                let ptr = crate::codegen_ay::shared::const_pointer::const_bytes(
                                    &c.const_,
                                )
                                .and_then(|bytes| bytes.stored_pointer(0))?;
                                Some(DeltaStep::Constant(i128::from(ptr.offset())))
                            }
                            op => Some(DeltaStep::Through(operand_local(&op)?, 0)),
                        }
                    }
                    Rvalue::Use(Operand::Constant(c), ..) => {
                        let ptr = crate::codegen_ay::shared::const_pointer::const_bytes(&c.const_)
                            .and_then(|bytes| {
                                use crate::codegen_ay::shared::const_pointer::ConstRead;
                                bytes.stored_pointer(0)
                            })?;
                        Some(DeltaStep::Constant(i128::from(ptr.offset())))
                    }
                    Rvalue::Use(op, ..) => Some(DeltaStep::Through(operand_local(op)?, 0)),
                    Rvalue::Cast(
                        CastKind::PtrToPtr
                        | CastKind::PointerCoercion(_)
                        | CastKind::Transmute
                        | CastKind::Subtype,
                        op,
                        _,
                    ) => Some(DeltaStep::Through(operand_local(op)?, 0)),
                    Rvalue::Aggregate(AggregateKind::RawPtr(..), ops) => {
                        Some(DeltaStep::Through(operand_local(ops.first()?)?, 0))
                    }
                    Rvalue::Aggregate(..) => {
                        let (through, operand) = self.pointer_field_source(local)?;
                        if !through.is_empty() {
                            return None;
                        }
                        Some(DeltaStep::Through(operand_local(&operand)?, 0))
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        let [ProjectionElem::Deref, rest @ ..] = place.projection.as_slice() else {
                            return None;
                        };
                        let offset = self.constant_projection_offset(place.local, rest)?;
                        Some(DeltaStep::Through(place.local, offset))
                    }
                    _ => None,
                };
            }
            let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            if destination.local != local || !destination.projection.is_empty() {
                continue;
            }
            if let Some((through, operand)) = self.nonnull_call_source(local) {
                let indirect = self.const_lane_written_indirectly();
                if through.iter().any(|hop| {
                    !self.encode.raw_single_assign_locals.contains(hop) || indirect.contains(hop)
                }) {
                    return None;
                }
                return Some(DeltaStep::Through(operand_local(&operand)?, 0));
            }
            let path = self.resolve_callee_path(func)?;
            let base = operand_local(args.first()?)?;
            let pointer_api = path.contains("const_ptr") || path.contains("mut_ptr");
            let elem_size = || {
                let ty = args.first()?.ty(self.body.locals()).ok()?;
                let pointee = Self::deref_pointee_ty(ty)?;
                i128::try_from(self.get_type_size(pointee)?).ok()
            };
            let count = || self.const_count_operand(args.get(1)?);
            let ends = |names: &[&str]| names.iter().any(|n| path.ends_with(n));
            return if (path.ends_with("::as_ptr") || path.ends_with("::as_mut_ptr"))
                && path.contains("slice")
                || path.contains("from_raw_parts")
            {
                Some(DeltaStep::Through(base, 0))
            } else if path.contains("rustc_intrinsics::offset")
                || pointer_api
                    && ends(&["::add", "::offset", "::wrapping_add", "::wrapping_offset"])
            {
                Some(DeltaStep::Through(base, count()?.checked_mul(elem_size()?)?))
            } else if pointer_api && ends(&["::sub", "::wrapping_sub"]) {
                Some(DeltaStep::Through(base, count()?.checked_mul(elem_size()?)?.checked_neg()?))
            } else if pointer_api
                && ends(&[
                    "::byte_add",
                    "::byte_offset",
                    "::wrapping_byte_add",
                    "::wrapping_byte_offset",
                ])
            {
                Some(DeltaStep::Through(base, count()?))
            } else if pointer_api && ends(&["::byte_sub", "::wrapping_byte_sub"]) {
                Some(DeltaStep::Through(base, count()?.checked_neg()?))
            } else {
                None
            };
        }
        None
    }

    /// The byte offset of the projections `rest` into the pointee of the
    /// pointer `base` (fields at their layout offset, constant array
    /// elements), when every step is a constant.
    fn constant_projection_offset(&self, base: usize, rest: &[ProjectionElem]) -> Option<i128> {
        let mut ty = Self::deref_pointee_ty(self.body.locals().get(base)?.ty)?;
        let mut offset: i128 = 0;
        for elem in rest {
            match elem {
                ProjectionElem::Field(idx, field_ty) => {
                    let field_offset =
                        crate::kani_middle::abi::LayoutOf::new(ty).field_offset(*idx)?;
                    offset = offset.checked_add(i128::try_from(field_offset).ok()?)?;
                    ty = *field_ty;
                }
                ProjectionElem::ConstantIndex { offset: index, from_end: false, .. } => {
                    let (elem_ty, size) = self.indexed_element(ty)?;
                    offset = offset.checked_add(i128::from(*index).checked_mul(size)?)?;
                    ty = elem_ty;
                }
                // `&ARR[1]` is `_5 = const 1_usize; .. &(*_4)[_5]`.
                ProjectionElem::Index(index_local) => {
                    let index = self.const_index_local_value(*index_local)?;
                    let (elem_ty, size) = self.indexed_element(ty)?;
                    offset = offset.checked_add(i128::from(index).checked_mul(size)?)?;
                    ty = elem_ty;
                }
                _ => return None,
            }
        }
        Some(offset)
    }

    /// The element type of an array or slice and its size.
    fn indexed_element(&self, ty: rustc_public::ty::Ty) -> Option<(rustc_public::ty::Ty, i128)> {
        let (TyKind::RigidTy(RigidTy::Array(elem_ty, _))
        | TyKind::RigidTy(RigidTy::Slice(elem_ty))) = ty.kind()
        else {
            return None;
        };
        Some((elem_ty, i128::try_from(self.get_type_size(elem_ty)?).ok()?))
    }

    /// A pointer-arithmetic count: a constant operand, or a local whose one
    /// definition is a constant; read as the `isize` it is passed as.
    fn const_count_operand(&self, op: &rustc_public::mir::Operand) -> Option<i128> {
        use rustc_public::mir::Operand;
        let constant = match op {
            Operand::Constant(c) => c.clone(),
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                if !self.encode.raw_single_assign_locals.contains(&p.local) {
                    return None;
                }
                self.body.blocks.iter().flat_map(|bb| &bb.statements).find_map(
                    |stmt| match &stmt.kind {
                        StatementKind::Assign(lhs, Rvalue::Use(Operand::Constant(c), ..))
                            if lhs.local == p.local && lhs.projection.is_empty() =>
                        {
                            Some(c.clone())
                        }
                        _ => None,
                    },
                )?
            }
            _ => return None,
        };
        let value = crate::codegen_ay::shared::const_pointer::const_uint(&constant.const_)?;
        let value = u64::try_from(value).ok()?;
        Some(i128::from(value as i64))
    }

    /// The access bound for `access_size` bytes at `addr`, a pointer whose
    /// provenance walk resolved to an object of `alloc_size` bytes: the span
    /// `[offset, offset + access_size)` neither wraps the 32-bit offset lane
    /// nor leaves the object. A pointer moved BELOW the object's base borrows
    /// from the obj_id lane and leaves an offset near 2^32, which the bound
    /// refuses. ONE obligation, `offset <= alloc_size - access_size`
    /// (unsigned), which is both halves at once: it was two (`offset +
    /// access_size >= offset` and `offset + access_size <= alloc_size`), and
    /// each is a property row the solver proves on its own; over a count a
    /// callee writes through memory (`r3_count.rs`) the no-wrap row alone ran
    /// out of budget. An access larger than the object is unconditionally
    /// outside it.
    ///
    /// The span is checked in the object's own lane, as the stack and heap
    /// bound is (`provenance_deref_bound_checks`): the address's high 32 bits
    /// must be `obj_id`. Only the low 32 bits are the offset this bound reads,
    /// so a step of 2^32 bytes moves the lane and leaves the offset in the
    /// object: `*(&V as *const u32).wrapping_byte_add(k)` with `k == 2^32` (a
    /// symbolic count, so the bound does not fold) was a clean proof where
    /// Kani reports a pointer outside object bounds, on main dd0d949a9 too
    /// (`const_pointer_live_lane_dual.rs`). The lane joins the offset bound
    /// in its one obligation.
    pub(in crate::codegen_ay::chc) fn object_span_checks(
        &self,
        addr: &Expr,
        access_size: u32,
        alloc_size: u32,
        obj_id: u32,
    ) -> Vec<Expr> {
        let Some((lane, offset)) = self.split_pointer(addr) else {
            return Vec::new();
        };
        let Some(last_start) = alloc_size.checked_sub(access_size) else {
            return vec![Expr::bool_const(false)];
        };
        let in_bounds = offset.bvule(Expr::bitvec_const(u128::from(last_start), 32));
        let in_lane = lane.eq(Expr::bitvec_const(u128::from(obj_id), 32));
        let in_lane =
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&in_lane).unwrap_or(in_lane);
        if in_lane == Expr::bool_const(true) {
            vec![in_bounds]
        } else {
            vec![in_lane.and(in_bounds)]
        }
    }

    /// Stage the object bound for a dereference `*p`, `(*p).f`, `(*p)[k]`
    /// (a read at the top of the deref cascade, a store at the top of the
    /// projection assignment), whichever lane later resolves it: the
    /// const-ref value lane (`const_ref_values`, which selects an element of
    /// the constant array without touching memory), the static register
    /// lanes (#428) and the memory lane alike. Mirrors
    /// `emit_raw_ptr_null_deref_check`, staged at the same two sites. The
    /// access is the bytes the place touches, through a raw pointer or a
    /// reference (`codegen_stmt_rvalue_offset_const_access.rs`).
    pub(in crate::codegen_ay::chc) fn emit_const_object_deref_bound_check(
        &mut self,
        place: &rustc_public::mir::Place,
        modified_locals: &HashSet<usize>,
    ) {
        self.emit_const_object_access_bound_check(place, modified_locals);
    }

    /// Push each obligation not already staged in this block.
    pub(in crate::codegen_ay::chc) fn push_pending_checks_dedup(&mut self, checks: Vec<Expr>) {
        for check in checks {
            if !self.heap_state.pending_checks.contains(&check) {
                self.heap_state.pending_checks.push(check);
            }
        }
    }

    /// `&*p` into a global object asserts that the pointee is
    /// dereferenceable (Kani: "dereference failure: pointer invalid",
    /// reported at the reborrow even when the reference is never read). The
    /// use-after-scope check used to stage a constant-false obligation here
    /// for every pointer reached through a constant; this states the object
    /// bound instead. `Rvalue::Ref` with exactly `[Deref]`, as Kani checks:
    /// `&raw const (*p)` is not UB, and Kani checks a projected reborrow
    /// `&(*p).f` / `&(*p)[k]` only where the reference is used. Those uses
    /// are bounded where they happen: a read or store through the reference
    /// walks back through the reborrow with the field's or element's offset
    /// (`const_pointer_delta`), and an atomic call model bounds its receiver
    /// (`emit_const_object_receiver_bound`).
    pub(in crate::codegen_ay::chc) fn emit_const_object_reborrow_check(
        &mut self,
        place: &rustc_public::mir::Place,
        modified_locals: &HashSet<usize>,
    ) {
        if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) {
            self.emit_const_object_access_bound_check(place, modified_locals);
        }
    }
}

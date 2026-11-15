// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The bound on every ACCESS through a pointer into a static or a constant
//! allocation: a read, a store or a reference made from a dereference place
//! `(*p)`, `(*p).f`, `(*p)[k]`, of a raw pointer or a reference, wherever the
//! global-object lane (`codegen_stmt_rvalue_offset_const_object.rs`) knows
//! the object `p` points into.
//!
//! Round 2 of fix/chc-atomic-as-ptr-live staged that bound only for exactly
//! `(*p)` of a raw pointer whose walk passed through bare copies, so three
//! kinds of out-of-bounds access through a constant pointer proved clean on
//! the CHC lane where Kani reports "dereference failure: pointer outside
//! object bounds" (the round-3 review's critical finding):
//!
//! * a pointer held in a struct or tuple field (`H { p: &V }.p.add(1)`): the
//!   walk refused the field hop;
//! * a reference made by transmute (`transmute::<_, &u32>(p.add(1))`): the
//!   base is a reference, not a raw pointer;
//! * a projected reborrow `&(*p)[1]` / `&(*p).y` past an atomic static: only
//!   `[Deref]` was bounded.
//!
//! On main those were failed only by the use-after-scope check, which read
//! the constant temp's `StorageDead` as the death of the static (a
//! constant-false obligation, which certified safe twins Genuine too).
//! `ref_target_through_constant` removed that obligation. The rule now: the
//! skip holds only where this lane bounded the access; anywhere else the
//! access fails closed ([`ChcCtx::bound_access_through_constant_or_fail_close`]).

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_stmt_rvalue_offset_const_object::ConstProvenance;

/// Fail-closed reason: an access through a pointer into a static or a
/// constant allocation that the global-object lane could not bound (the walk
/// to the constant failed, or no address to bound was available), at a site
/// where the use-after-scope check no longer stands in for the bound.
pub(in crate::codegen_ay::chc) const DEREF_THROUGH_CONSTANT_UNBOUNDED: &str =
    "deref_through_constant_unbounded";

/// The bytes a dereference place touches, relative to the pointer it
/// dereferences.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum DerefExtent {
    /// `size` bytes, `displacement` bytes past the pointer.
    Bytes { displacement: u64, size: u32 },
    /// Nothing to bound: a zero-sized access, or an unsized prefix (a slice,
    /// `str` or `dyn` pointee) whose extent the slice-metadata lanes bound.
    Nothing,
}

/// What [`ChcCtx::stage_const_object_access_bound`] did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum ConstAccessBound {
    /// The bound is staged, or folded to nothing because the access is
    /// provably inside the object.
    Bounded,
    /// No bytes to bound ([`DerefExtent::Nothing`]).
    Nothing,
    /// The place is not a dereference of a pointer the lane resolves to a
    /// global object.
    NoProvenance,
    /// The lane resolved the object but has no address to bound (and the
    /// pointer's offset is not a compile-time constant).
    Unbounded,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The pointer a dereference place `(*p)…` dereferences and the bytes it
    /// touches: the projections after the leading `Deref` that move by a
    /// constant (a field, a constant index, an index local whose one
    /// definition is a constant) are followed, and the extent is the type
    /// reached. A symbolic index, a downcast, a subslice or a further deref
    /// stops there: the access lies inside the prefix reached so far, so the
    /// prefix's bytes are bounded (never less than the access touches).
    pub(in crate::codegen_ay::chc) fn deref_access_extent(
        &self,
        place: &Place,
    ) -> Option<(usize, DerefExtent)> {
        let [ProjectionElem::Deref, rest @ ..] = place.projection.as_slice() else {
            return None;
        };
        let mut ty = match self.body.locals().get(place.local)?.ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _) | RigidTy::Ref(_, pointee, _)) => pointee,
            _ => return None,
        };
        let mut displacement: u64 = 0;
        let element = |ty: Ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, _) | RigidTy::Slice(elem_ty)) => {
                Some((elem_ty, self.get_type_size(elem_ty)? as u64))
            }
            _ => None,
        };
        for elem in rest {
            let step = match elem {
                ProjectionElem::Field(idx, field_ty) => {
                    let offset = crate::kani_middle::abi::LayoutOf::new(ty).field_offset(*idx);
                    offset.map(|offset| (*field_ty, offset as u64))
                }
                ProjectionElem::ConstantIndex { offset: index, from_end: false, .. } => element(ty)
                    .and_then(|(elem_ty, size)| Some((elem_ty, index.checked_mul(size)?))),
                ProjectionElem::Index(index_local) => {
                    self.const_index_local_value(*index_local).and_then(|index| {
                        let (elem_ty, size) = element(ty)?;
                        Some((elem_ty, index.checked_mul(size)?))
                    })
                }
                ProjectionElem::OpaqueCast(cast_ty) => Some((*cast_ty, 0)),
                _ => None,
            };
            let Some((next_ty, offset)) = step else { break };
            displacement = displacement.checked_add(offset)?;
            ty = next_ty;
        }
        let extent = match self.get_type_size(ty) {
            Some(0) => DerefExtent::Nothing,
            Some(size) => DerefExtent::Bytes { displacement, size: u32::try_from(size).ok()? },
            None if matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str | RigidTy::Dynamic(..))
            ) =>
            {
                DerefExtent::Nothing
            }
            None => return None,
        };
        Some((place.local, extent))
    }

    /// The value of an index local whose one definition is a constant
    /// (`_6 = const 1_usize; .. (*_1)[_6]`).
    pub(super) fn const_index_local_value(&self, local: usize) -> Option<u64> {
        use rustc_public::mir::{Operand, Rvalue, StatementKind};
        if !self.encode.raw_single_assign_locals.contains(&local) {
            return None;
        }
        let constant = self.body.blocks.iter().flat_map(|bb| &bb.statements).find_map(|stmt| {
            match &stmt.kind {
                StatementKind::Assign(lhs, Rvalue::Use(Operand::Constant(c), ..))
                    if lhs.local == local && lhs.projection.is_empty() =>
                {
                    Some(c.clone())
                }
                _ => None,
            }
        })?;
        let value = crate::codegen_ay::shared::const_pointer::const_uint(&constant.const_)?;
        u64::try_from(value).ok()
    }

    /// The address pointer local `local` holds in this block, 64 bits wide:
    /// a wide pointer's data word (`concat(len, data)`) for a slice or `str`.
    fn const_access_pointer_expr(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let width = crate::codegen_ay::types::POINTER_WIDTH;
        let expr = self.const_access_pointer_value(local, modified_locals)?;
        match expr.sort().bitvec_width() {
            Some(w) if w == width => Some(expr),
            Some(w) if w == 2 * width => Some(expr.extract(width - 1, 0)),
            _ => None,
        }
    }

    fn const_access_pointer_value(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let ptr_expr = if modified_locals.contains(&local) {
            self.encode
                .local_expr_env
                .get(&local)
                .cloned()
                .or_else(|| self.resolve_local_expr(local, modified_locals))
        } else {
            self.resolve_local_expr(local, modified_locals)
        };
        ptr_expr
    }

    /// Stage the object bound for the access a dereference place makes (a
    /// read, a store, or a reference made from it) through a pointer the
    /// global-object lane resolves. See the module documentation.
    pub(in crate::codegen_ay::chc) fn stage_const_object_access_bound(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> ConstAccessBound {
        let Some((ptr_local, extent)) = self.deref_access_extent(place) else {
            return ConstAccessBound::NoProvenance;
        };
        self.stage_const_object_bound_for(ptr_local, extent, modified_locals)
    }

    /// [`Self::stage_const_object_access_bound`] for an access of `extent`
    /// through the pointer local `ptr_local`.
    fn stage_const_object_bound_for(
        &mut self,
        ptr_local: usize,
        extent: DerefExtent,
        modified_locals: &HashSet<usize>,
    ) -> ConstAccessBound {
        let Some(provenance) = self.const_provenance_for_local(ptr_local) else {
            return ConstAccessBound::NoProvenance;
        };
        let DerefExtent::Bytes { displacement, size } = extent else {
            return ConstAccessBound::Nothing;
        };
        let checks = match provenance {
            ConstProvenance::Integer => Some(vec![Expr::bool_const(false)]),
            ConstProvenance::Object { obj_id, size: object_size } => {
                match self.const_pointer_delta(ptr_local) {
                    Some(delta) => {
                        let start = delta + i128::from(displacement);
                        let inside =
                            start >= 0 && start + i128::from(size) <= i128::from(object_size);
                        debug!(
                            ptr_local,
                            start, size, object_size, inside, "const-object access: folded"
                        );
                        Some(if inside { Vec::new() } else { vec![Expr::bool_const(false)] })
                    }
                    None => {
                        // The span from the pointer to the end of the access:
                        // `[off, off + displacement + size)` inside the object
                        // is the access's own bound, since `off` is unsigned.
                        let span = u32::try_from(displacement)
                            .ok()
                            .and_then(|displacement| displacement.checked_add(size));
                        match (span, self.const_access_pointer_expr(ptr_local, modified_locals)) {
                            (Some(span), Some(ptr)) => {
                                Some(self.object_span_checks(&ptr, span, object_size, obj_id))
                                    .filter(|checks| !checks.is_empty())
                            }
                            _ => None,
                        }
                    }
                }
            }
        };
        let Some(checks) = checks else {
            debug!(ptr_local, ?provenance, "CHC: const-object access not boundable");
            return ConstAccessBound::Unbounded;
        };
        self.push_pending_checks_dedup(checks);
        debug!(ptr_local, displacement, size, ?provenance, "CHC: const-object access bound");
        ConstAccessBound::Bounded
    }

    /// [`Self::stage_const_object_access_bound`] at a read or a store (the
    /// top of the deref cascade and of the projection store) or at a
    /// reference made from a dereference place. A pointer the lane resolves
    /// but cannot bound fails closed.
    pub(in crate::codegen_ay::chc) fn emit_const_object_access_bound_check(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) {
        if !self.memory_safety_checks {
            return;
        }
        if self.stage_const_object_access_bound(place, modified_locals)
            == ConstAccessBound::Unbounded
        {
            warn!(
                local = place.local,
                "CHC: access into a global object not bounded — fail closed"
            );
            self.record_sound_fallback_reason(DEREF_THROUGH_CONSTANT_UNBOUNDED);
        }
    }

    /// A reference made by `transmute` from a pointer into a global object
    /// (`transmute::<*const u32, &u32>(p.add(1))`) must be dereferenceable,
    /// exactly as a reborrow `&*p` must: a call model that later reads through
    /// it (`r.load(..)`) makes no dereference in this body that the read-side
    /// bound would see.
    pub(in crate::codegen_ay::chc) fn emit_const_object_transmuted_ref_check(
        &mut self,
        source_local: usize,
        target_ty: Ty,
        modified_locals: &HashSet<usize>,
    ) {
        if !self.memory_safety_checks
            || !matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)))
            || !matches!(
                self.body.locals().get(source_local).map(|decl| decl.ty.kind()),
                Some(TyKind::RigidTy(RigidTy::RawPtr(..)))
            )
        {
            return;
        }
        let TyKind::RigidTy(RigidTy::Ref(_, target_pointee, _)) = target_ty.kind() else {
            return;
        };
        // The reference's own pointee is what it must be valid for.
        let extent = match self.get_type_size(target_pointee) {
            Some(0) => return,
            Some(size) => match u32::try_from(size) {
                Ok(size) => DerefExtent::Bytes { displacement: 0, size },
                Err(_) => return,
            },
            None => return,
        };
        if self.stage_const_object_bound_for(source_local, extent, modified_locals)
            == ConstAccessBound::Unbounded
        {
            warn!(
                source_local,
                "CHC: transmuted reference into a global object not bounded — fail closed"
            );
            self.record_sound_fallback_reason(DEREF_THROUGH_CONSTANT_UNBOUNDED);
        }
    }

    /// The receiver of a call model that reads or writes through it (an
    /// atomic's `load`, `store`, `fetch_add`, ...): a reference or a raw
    /// pointer whose pointee is the bytes the model touches. A reference made
    /// by a projected reborrow (`&(*p).y`, `&(*p)[1]`) is bounded HERE, where
    /// Kani reports the access, not where it is made.
    pub(in crate::codegen_ay::chc) fn emit_const_object_receiver_bound(
        &mut self,
        receiver: Option<&rustc_public::mir::Operand>,
        modified_locals: &HashSet<usize>,
    ) {
        use rustc_public::mir::Operand;
        let Some(Operand::Copy(receiver) | Operand::Move(receiver)) = receiver else {
            return;
        };
        if !receiver.projection.is_empty() {
            return;
        }
        let place = Place { local: receiver.local, projection: vec![ProjectionElem::Deref] };
        self.emit_const_object_access_bound_check(&place, modified_locals);
    }

    /// At a reference made from a PROJECTED place `&(*p).f` whose target
    /// `ref_target_through_constant` exempts from the use-after-scope check:
    /// the reference is bounded where it is used
    /// ([`Self::emit_const_object_reborrow_check`]), which needs the
    /// global-object lane to resolve `p`. Where it cannot, the reborrow fails
    /// closed.
    pub(in crate::codegen_ay::chc) fn require_const_provenance_or_fail_close(
        &mut self,
        place: &Place,
    ) {
        if !self.memory_safety_checks {
            return;
        }
        if self.deref_access_extent(place).is_none()
            || self.const_provenance_for_local(place.local).is_none()
        {
            warn!(
                local = place.local,
                "CHC: reborrow through a constant pointer the global-object lane cannot walk — fail closed"
            );
            self.record_sound_fallback_reason(DEREF_THROUGH_CONSTANT_UNBOUNDED);
        }
    }

    /// At a site where `ref_target_through_constant` skips the
    /// use-after-scope obligation (the target is a constant pointer's
    /// pointee, which never dies): the skip is sound only when this lane
    /// bounded the access. If it did not (the walk to the constant failed,
    /// or there was no address to bound), the access fails closed: no
    /// verdict rests on it, and no counterexample from it is certified.
    pub(in crate::codegen_ay::chc) fn bound_access_through_constant_or_fail_close(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) {
        if !self.memory_safety_checks {
            return;
        }
        match self.stage_const_object_access_bound(place, modified_locals) {
            ConstAccessBound::Bounded | ConstAccessBound::Nothing => {}
            outcome @ (ConstAccessBound::NoProvenance | ConstAccessBound::Unbounded) => {
                warn!(
                    local = place.local,
                    ?outcome,
                    "CHC: access through a constant pointer the global-object lane did not bound — fail closed"
                );
                self.record_sound_fallback_reason(DEREF_THROUGH_CONSTANT_UNBOUNDED);
            }
        }
    }
}

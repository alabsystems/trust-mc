// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice side-table propagation for statement-level reborrows.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

/// Derive exact Subslice length metadata without conflating MIR's two `to`
/// meanings.
///
/// With `from_end=true`, `to` is a trailing count and the result is
/// `source_len - from - to`. With `from_end=false`, `to` is an absolute end
/// index and the result is the source-independent constant `to - from`.
/// Invalid or overflowing static bounds fail closed.
pub(in crate::codegen_ay::chc) fn projected_subslice_len(
    source_len: Expr,
    from: u64,
    to: u64,
    from_end: bool,
) -> Option<Expr> {
    let source_len_const = match source_len.value() {
        ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok(),
        _ => None,
    };
    if from_end {
        let removed = from.checked_add(to)?;
        if source_len_const.is_some_and(|length| removed > length) {
            return None;
        }
        if removed == 0 {
            Some(source_len)
        } else {
            Some(source_len.bvsub(Expr::bitvec_const(removed as u128, POINTER_WIDTH)))
        }
    } else {
        let length = to.checked_sub(from)?;
        if source_len_const.is_some_and(|source_length| to > source_length) {
            return None;
        }
        Some(Expr::bitvec_const(length as u128, POINTER_WIDTH))
    }
}

pub(in crate::codegen_ay::chc) enum RefMetadataOffsetMode {
    Copy,
    Accumulate(Expr),
    Remove,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Drop the lossy reference/slice facts that can otherwise survive from a
    /// different CFG producer of the same local. This is deliberately broader
    /// than `subslice_len`: backing values, offsets, and referent identities are
    /// authority-bearing together.
    pub(in crate::codegen_ay::chc) fn clear_path_insensitive_ref_metadata(&mut self, local: usize) {
        self.ref_resolution.clear_path_insensitive_ref_metadata(local);
    }

    /// [`Self::clear_path_insensitive_ref_metadata`] for the destination of a
    /// borrow `dest = &place` (or `&raw place`) whose borrowed local or
    /// destination has several producers, keeping the one fact that holds on
    /// every path: WHICH storage the borrow names.
    ///
    /// A place with no `Deref` and no index projection names the same storage
    /// whatever statement produced the borrowed local's VALUE, so the points-at
    /// edge the pre-pass recorded for a sole-producer `dest` stays exact, and
    /// reads and writes through it use that local's own path-sensitive state.
    /// What one producer alone decides (a decoded constant, a slice length or
    /// offset, collection or allocation facts) is dropped as before.
    ///
    /// Dropping the edge as well sent every use of a borrowed joined local to
    /// the address lane: `core::mem::swap(&mut o, &mut q)` could not name its
    /// targets and left both locals unchanged, and a later `o == None`, read
    /// through typed memory refreshed from that stale state, was proved false
    /// (tools/soundness-duals/negative/review_r18_mutate_then_compare.rs).
    pub(in crate::codegen_ay::chc) fn clear_borrow_metadata_keeping_exact_edge(
        &mut self,
        dest: usize,
        place: &Place,
    ) {
        let names_fixed_storage = place
            .projection
            .iter()
            .all(|proj| matches!(proj, ProjectionElem::Field(..) | ProjectionElem::Downcast(_)));
        let kept = self.ref_resolution.ref_targets.get(&dest).cloned().filter(|target| {
            names_fixed_storage
                && target.local == place.local
                && target.projections == place.projection
                // A single producer, or several that are all this same borrow
                // (loop unwinding duplicates `_14 = &mut _12` into every copy of
                // the body). Either way the reference names this one place on
                // every path; dropping the edge here left `Iterator::next`
                // reading the reference's raw pointer and failing closed.
                && (!self.local_has_multiple_whole_definitions(dest)
                    || self.whole_definitions_all_borrow_place(dest, place))
        });
        self.clear_path_insensitive_ref_metadata(dest);
        if let Some(target) = kept {
            debug!(
                dest,
                referent = place.local,
                "borrow of a multi-producer local: exact points-at edge kept, value facts dropped"
            );
            self.ref_resolution.ref_targets.insert(dest, target);
        }
    }

    /// Record that `dest` loses the VALUE fact (`const_ref_values` or
    /// `const_ref_slice_views`) that `source` carries, because the copy is not
    /// the unique path-insensitive producer of `dest`.
    ///
    /// A value fact stands in for the referent: the `Option<&T>` returned by the
    /// slice `Iterator::next` stub stores the ELEMENT in its payload slot, not an
    /// address, and `*payload` resolves only through `const_ref_values`. Once the
    /// fact is gone, `dest`'s state variable still holds that element, and the
    /// Mem-level load would select the typed memory array at an "address" equal to
    /// the element's value: a cell no rule wrote, whose free value was certified
    /// Genuine (expected/loop-backedge/test.rs, where loop unwinding gives
    /// `_11 = copy ((_5 as Some).0)` one producer per unwound copy). The deref
    /// cascade fails closed for such a local instead.
    fn record_dropped_deref_value_fact(
        &mut self,
        source_local: usize,
        dest_local: usize,
        source: &'static str,
    ) {
        let resolution = &self.ref_resolution;
        if resolution.const_ref_values.contains_key(&source_local)
            || resolution.const_ref_slice_views.contains_key(&source_local)
        {
            debug!(
                source_local,
                dest_local, source, "propagate_ref_metadata: value fact dropped for an ambiguous producer"
            );
            self.ref_resolution.deref_value_fact_dropped.insert(dest_local);
        }
    }

    /// Propagate statement-level ref side tables across Copy/Move/Cast/Offset assignments.
    pub(in crate::codegen_ay::chc) fn propagate_ref_metadata(
        &mut self,
        source_local: usize,
        dest_local: usize,
        bb_idx: usize,
        source: &'static str,
        mark_forwarded: bool,
        offset_mode: RefMetadataOffsetMode,
    ) {
        if !self.path_insensitive_metadata_copy_is_unique(source_local, dest_local) {
            // Identical unwound copies of the same payload copy agree on the
            // slot fact; `keep_agreeing_payload_value_fact` keeps it only when it
            // holds on every path (codegen_stmt_payload_value_fact.rs).
            if let Some(fact) = self.keep_agreeing_payload_value_fact(source_local, dest_local) {
                self.clear_path_insensitive_ref_metadata(dest_local);
                debug!(
                    source_local,
                    dest_local, source, "propagate_ref_metadata: agreeing producers keep the payload value fact"
                );
                self.ref_resolution.const_ref_values.insert(dest_local, fact);
                return;
            }
            self.record_dropped_deref_value_fact(source_local, dest_local, source);
            self.clear_path_insensitive_ref_metadata(dest_local);
            // Exception for the EXACT points-at edge only: when every producer
            // of `dest` is this same copy of `source`, and `source`'s edge is
            // path-insensitive, `dest` names that place on every path. Value
            // facts stay dropped. Without this, the unwound `_21 = copy _15`
            // before `RangeIteratorImpl::spec_next(move _21)` lost the edge
            // and the range advance failed closed
            // (expected/loop-backedge/test.rs: RangeSpecNext translation failed).
            if self.whole_definitions_all_same_copy_of(dest_local, source_local)
                && let Some(ref_target) =
                    self.ref_resolution.ref_targets.get(&source_local).cloned()
            {
                debug!(
                    source_local,
                    dest_local, source, "propagate_ref_metadata: identical-copy producers keep the exact edge"
                );
                self.ref_resolution.ref_targets.insert(dest_local, ref_target);
                if mark_forwarded {
                    self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
                }
                return;
            }
            debug!(
                source_local,
                dest_local, source, "propagate_ref_metadata: ambiguous whole-local producer"
            );
            return;
        }
        let mut copied_any = false;
        let mut copied_ref_target = false;
        let mut copied_value = false;
        let mut copied_discriminant = false;
        let mut copied_promoted_obj_id = false;
        let mut copied_len = false;
        let mut copied_slice_view = false;

        if let Some(ref_target) = self.ref_resolution.ref_targets.get(&source_local).cloned() {
            self.ref_resolution.ref_targets.insert(dest_local, ref_target);
            copied_any = true;
            copied_ref_target = true;
        } else {
            self.ref_resolution.ref_targets.remove(&dest_local);
            self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
        }
        if copied_ref_target && mark_forwarded {
            self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
            copied_any = true;
        }
        // A reference INTO a collection element keeps denoting that element
        // through every copy/reborrow/cast. Without carrying the record, the
        // copy falls back to the minted symbolic address and reads a memory
        // array the collection was never stored into.
        if let Some(elem_ref) =
            self.ref_resolution.collection_elem_field_refs.get(&source_local).cloned()
        {
            self.ref_resolution.collection_elem_field_refs.insert(dest_local, elem_ref);
            copied_any = true;
        } else if self.ref_resolution.collection_index_refs.contains_key(&source_local) {
            self.ref_resolution.collection_elem_field_refs.insert(
                dest_local,
                crate::codegen_ay::chc::codegen_ctx::types::CollectionElemFieldRef {
                    base_ref_local: source_local,
                    elem_fields: Vec::new(),
                },
            );
            copied_any = true;
        } else {
            self.ref_resolution.collection_elem_field_refs.remove(&dest_local);
        }
        // D10: a value fact (and a discriminant fact) describes exactly one
        // window. `Copy` is a zero delta: copied. A KNOWN nonzero delta
        // (`Accumulate`) re-indexes an array fact and re-decodes any other at
        // the moved window; an unknown one (`Remove`) carries no fact, and the
        // memory path (seeded whole, D2) answers.
        let known_delta: Option<i128> = match &offset_mode {
            RefMetadataOffsetMode::Copy => Some(0),
            RefMetadataOffsetMode::Accumulate(addend) => {
                Self::const_usize_from_expr(addend).and_then(|d| i128::try_from(d).ok())
            }
            RefMetadataOffsetMode::Remove => None,
        };
        let moved_value =
            known_delta.and_then(|d| self.moved_const_value_fact(source_local, dest_local, d));
        if let Some(value) = moved_value {
            self.ref_resolution.const_ref_values.insert(dest_local, value);
            copied_any = true;
            copied_value = true;
        } else {
            self.ref_resolution.const_ref_values.remove(&dest_local);
        }
        if known_delta == Some(0)
            && let Some(&discr) = self.ref_resolution.const_ref_discriminants.get(&source_local)
        {
            self.ref_resolution.const_ref_discriminants.insert(dest_local, discr);
            copied_any = true;
            copied_discriminant = true;
        } else {
            self.ref_resolution.const_ref_discriminants.remove(&dest_local);
        }
        if let Some(object) =
            known_delta.and_then(|d| self.moved_const_ref_object(source_local, d))
        {
            self.ref_resolution.const_ref_objects.insert(dest_local, object);
            copied_any = true;
            copied_promoted_obj_id = true;
        } else {
            self.ref_resolution.const_ref_objects.remove(&dest_local);
        }
        if let Some(len) = self.ref_resolution.subslice_len.get(&source_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len);
            copied_any = true;
            copied_len = true;
        } else {
            self.ref_resolution.subslice_len.remove(&dest_local);
        }
        if let Some(slice_view) =
            self.ref_resolution.const_ref_slice_views.get(&source_local).cloned()
        {
            self.ref_resolution.const_ref_slice_views.insert(dest_local, slice_view);
            copied_any = true;
            copied_slice_view = true;
        } else {
            self.ref_resolution.const_ref_slice_views.remove(&dest_local);
        }

        let offset_action = match offset_mode {
            RefMetadataOffsetMode::Copy => {
                if let Some(offset) =
                    self.ref_resolution.subslice_offset.get(&source_local).cloned()
                {
                    self.ref_resolution.subslice_offset.insert(dest_local, offset);
                    copied_any = true;
                    "copy"
                } else {
                    self.ref_resolution.subslice_offset.remove(&dest_local);
                    "none"
                }
            }
            RefMetadataOffsetMode::Accumulate(addend) => {
                let combined_offset = self
                    .ref_resolution
                    .subslice_offset
                    .get(&source_local)
                    .cloned()
                    .map(|prev| prev.bvadd(addend.clone()))
                    .unwrap_or(addend);
                self.ref_resolution.subslice_offset.insert(dest_local, combined_offset);
                copied_any = true;
                "accumulate"
            }
            RefMetadataOffsetMode::Remove => {
                self.ref_resolution.subslice_offset.remove(&dest_local);
                "remove"
            }
        };

        if copied_any || offset_action == "remove" {
            debug!(
                bb_idx,
                source,
                source_local,
                dest_local,
                copied_ref_target,
                copied_value,
                copied_discriminant,
                copied_promoted_obj_id,
                copied_len,
                copied_slice_view,
                offset_action,
                marked_forwarded = copied_ref_target && mark_forwarded,
                "propagate_ref_metadata"
            );
        }
    }

    /// Part of #3495: Propagate slice backing metadata through Deref reborrows.
    ///
    /// This covers both:
    /// - identity reborrows like `_dst = &(*_src)` where the source already carries
    ///   slice backing metadata, and
    /// - Deref+Subslice projections that need offset/length adjustment.
    pub(in crate::codegen_ay::chc) fn propagate_subslice_metadata(
        &mut self,
        ref_place: &Place,
        dest_local: usize,
    ) {
        if !self.path_insensitive_metadata_copy_is_unique(ref_place.local, dest_local) {
            // Same rule as the rvalue lane: the borrow still names fixed storage.
            self.clear_borrow_metadata_keeping_exact_edge(dest_local, ref_place);
            return;
        }
        if let [ProjectionElem::Deref, ProjectionElem::Field(field_idx, field_ty)] =
            &ref_place.projection[..]
            && matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Str | RigidTy::Slice(_)))
        {
            let source_local = ref_place.local;
            if let Some(val) = self.ref_resolution.const_ref_values.get(&source_local).cloned() {
                self.ref_resolution.const_ref_values.insert(dest_local, val);
            } else {
                self.ref_resolution.const_ref_values.remove(&dest_local);
            }
            if let Some(len) = self.ref_resolution.subslice_len.get(&source_local).cloned() {
                self.ref_resolution.subslice_len.insert(dest_local, len);
            } else {
                self.ref_resolution.subslice_len.remove(&dest_local);
            }

            let source_ty = self.body.locals()[source_local].ty;
            let container_ty = match source_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
                _ => source_ty,
            };
            let field_offset = self.get_field_offset(container_ty, *field_idx).unwrap_or(0);
            let mut offset_expr = Expr::bitvec_const(field_offset as i128, POINTER_WIDTH);
            if let Some(existing_offset) =
                self.ref_resolution.subslice_offset.get(&source_local).cloned()
            {
                offset_expr = existing_offset.bvadd(offset_expr);
            }
            if field_offset > 0 || self.ref_resolution.subslice_offset.contains_key(&source_local) {
                self.ref_resolution.subslice_offset.insert(dest_local, offset_expr);
            } else {
                self.ref_resolution.subslice_offset.remove(&dest_local);
            }
            debug!(
                source_local,
                dest_local,
                field_idx,
                field_offset,
                "propagate_subslice_metadata: custom-DST tail field reborrow"
            );
            return;
        }

        if ref_place.projection.len() == 1
            && matches!(ref_place.projection[0], ProjectionElem::Deref)
        {
            let source_local: usize = ref_place.local;
            if let Some(val) = self.ref_resolution.const_ref_values.get(&source_local).cloned() {
                self.ref_resolution.const_ref_values.insert(dest_local, val);
            } else {
                self.ref_resolution.const_ref_values.remove(&dest_local);
            }
            if let Some(slice_view) =
                self.ref_resolution.const_ref_slice_views.get(&source_local).cloned()
            {
                self.ref_resolution.const_ref_slice_views.insert(dest_local, slice_view);
            } else {
                self.ref_resolution.const_ref_slice_views.remove(&dest_local);
            }
            if let Some(offset) = self.ref_resolution.subslice_offset.get(&source_local).cloned() {
                self.ref_resolution.subslice_offset.insert(dest_local, offset);
            } else {
                self.ref_resolution.subslice_offset.remove(&dest_local);
            }
            if let Some(len) = self.ref_resolution.subslice_len.get(&source_local).cloned() {
                self.ref_resolution.subslice_len.insert(dest_local, len);
            } else {
                self.ref_resolution.subslice_len.remove(&dest_local);
            }
            // `&*p` denotes the SAME place as `p`, so it inherits p's
            // ref_target too — not just the slice metadata. Without this the
            // referent is lost exactly when the reborrow is captured by a
            // contract closure: the `ensures` reads through a capture with no
            // recorded provenance and falls back to a stale typed-memory
            // select (`function-contract/history/copy_pass`).
            //
            // GATED ON THE REFERENT BEING `Freeze`, and the gate is
            // load-bearing. Binding the reborrow to the referent's SCALAR
            // state var is sound only while every write refreshes that scalar.
            // Under interior mutability it does not: `UnsafeCell::get()` hands
            // out a `*mut T`, the store lands in typed memory, the scalar is
            // never refreshed, and an `ensures` reading through the reborrow
            // observes the PRE-state — a violated postcondition gets PROVED.
            // The UNGATED form of this hunk shipped as 04d646293 and was
            // reverted for exactly that false proof.
            //
            // Ask about the REFERENT, not the pointer: `&T` is itself always
            // `Freeze` (the reference value holds no `UnsafeCell`), so testing
            // `source_ty` answers the wrong question and lets
            // `&UnsafeCell<u32>` straight through — MEASURED. The sibling
            // `arg_is_writable_pointer` peels the same way.
            //
            // Receipts: `tools/soundness-duals/dual_uc_ensures.rs` referent is
            // `UnsafeCell<u32>` (im=true -> blocked, MUST fail);
            // `copy_pass` referent is `u32` (im=false -> propagates).
            // `ty_has_interior_mut` fails toward `true` for unresolved params,
            // so the gate errs toward dropping provenance — precision, never
            // soundness.
            let source_ty = self.body.locals()[source_local].ty;
            let referent_ty = match source_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
                _ => source_ty,
            };
            if !crate::codegen_ay::foreign_defs::ty_has_interior_mut(self.tcx, referent_ty) {
                let carried_ref_target =
                    self.ref_resolution.ref_targets.get(&source_local).cloned();
                match carried_ref_target {
                    Some(rt) => {
                        self.ref_resolution.ref_targets.insert(dest_local, rt);
                    }
                    None => {
                        self.ref_resolution.ref_targets.remove(&dest_local);
                    }
                }
            }
            debug!(
                source_local,
                dest_local, "propagate_subslice_metadata: deref identity reborrow"
            );
            return;
        }
        if ref_place.projection.len() < 2
            || !ref_place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
        {
            return;
        }
        let subslice = ref_place.projection.iter().rev().find_map(|p| {
            if let ProjectionElem::Subslice { from, to, from_end } = p {
                Some((*from, *to, *from_end))
            } else {
                None
            }
        });
        let Some((from, to, from_end)) = subslice else {
            return;
        };
        let source_local: usize = ref_place.local;

        if let Some(val) = self.ref_resolution.const_ref_values.get(&source_local).cloned() {
            self.ref_resolution.const_ref_values.insert(dest_local, val);
            debug!(
                source_local,
                dest_local, from, to, "propagate_subslice_metadata: const_ref_values"
            );
        }

        let existing_offset = self.ref_resolution.subslice_offset.get(&source_local).cloned();
        if from > 0 || existing_offset.is_some() {
            let new_offset = if from > 0 {
                let from_bv = Expr::bitvec_const(from as i128, POINTER_WIDTH);
                if let Some(prev) = existing_offset { prev.bvadd(from_bv) } else { from_bv }
            } else {
                existing_offset.expect("invariant: checked is_some in guard")
            };
            self.ref_resolution.subslice_offset.insert(dest_local, new_offset);
            debug!(source_local, dest_local, from, "propagate_subslice_metadata: subslice_offset");
        }

        if let Some(src_len) = self.ref_resolution.subslice_len.get(&source_local).cloned() {
            match projected_subslice_len(src_len, from, to, from_end) {
                Some(new_len) => {
                    self.ref_resolution.subslice_len.insert(dest_local, new_len);
                    debug!(
                        source_local,
                        dest_local, from, to, from_end, "propagate_subslice_metadata: subslice_len"
                    );
                }
                None => {
                    self.ref_resolution.const_ref_values.remove(&dest_local);
                    self.ref_resolution.const_ref_slice_views.remove(&dest_local);
                    self.ref_resolution.subslice_offset.remove(&dest_local);
                    self.ref_resolution.subslice_len.remove(&dest_local);
                    debug!(
                        source_local,
                        dest_local,
                        from,
                        to,
                        from_end,
                        "propagate_subslice_metadata: invalid bounds; dropping length authority"
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_bindings::Expr;

    use super::projected_subslice_len;
    use crate::codegen_ay::types::POINTER_WIDTH;

    #[test]
    fn absolute_end_and_trailing_count_have_distinct_lengths() {
        let source_len = Expr::bitvec_const(5u64, POINTER_WIDTH);

        assert_eq!(
            projected_subslice_len(source_len.clone(), 1, 3, false),
            Some(Expr::bitvec_const(2u64, POINTER_WIDTH))
        );
        assert_eq!(
            projected_subslice_len(source_len.clone(), 1, 3, true),
            Some(source_len.bvsub(Expr::bitvec_const(4u64, POINTER_WIDTH)))
        );
    }

    #[test]
    fn zero_zero_is_empty_only_for_absolute_end_polarity() {
        let source_len = Expr::bitvec_const(5u64, POINTER_WIDTH);

        assert_eq!(
            projected_subslice_len(source_len.clone(), 0, 0, false),
            Some(Expr::bitvec_const(0u64, POINTER_WIDTH))
        );
        assert_eq!(projected_subslice_len(source_len.clone(), 0, 0, true), Some(source_len));
    }

    #[test]
    fn invalid_or_overflowing_bounds_fail_closed() {
        let source_len = Expr::bitvec_const(5u64, POINTER_WIDTH);

        assert_eq!(projected_subslice_len(source_len.clone(), 3, 1, false), None);
        assert_eq!(projected_subslice_len(source_len.clone(), 0, 6, false), None);
        assert_eq!(projected_subslice_len(source_len.clone(), 3, 3, true), None);
        assert_eq!(projected_subslice_len(source_len, u64::MAX, 1, true), None);
    }
}

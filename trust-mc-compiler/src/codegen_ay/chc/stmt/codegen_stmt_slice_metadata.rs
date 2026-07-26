// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice side-table propagation for statement-level reborrows.

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

pub(in crate::codegen_ay::chc) enum RefMetadataOffsetMode {
    Copy,
    Accumulate(Expr),
    Remove,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
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
        }
        if copied_ref_target && mark_forwarded {
            self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
            copied_any = true;
        }
        if let Some(value) = self.ref_resolution.const_ref_values.get(&source_local).cloned() {
            self.ref_resolution.const_ref_values.insert(dest_local, value);
            copied_any = true;
            copied_value = true;
        }
        if let Some(&discr) = self.ref_resolution.const_ref_discriminants.get(&source_local) {
            self.ref_resolution.const_ref_discriminants.insert(dest_local, discr);
            copied_any = true;
            copied_discriminant = true;
        }
        if let Some(promoted_obj_id) =
            self.ref_resolution.const_ref_promoted_obj_ids.get(&source_local).copied()
        {
            self.ref_resolution.const_ref_promoted_obj_ids.insert(dest_local, promoted_obj_id);
            copied_any = true;
            copied_promoted_obj_id = true;
        }
        if let Some(len) = self.ref_resolution.subslice_len.get(&source_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len);
            copied_any = true;
            copied_len = true;
        }
        if let Some(slice_view) =
            self.ref_resolution.const_ref_slice_views.get(&source_local).cloned()
        {
            self.ref_resolution.const_ref_slice_views.insert(dest_local, slice_view);
            copied_any = true;
            copied_slice_view = true;
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
        let Some((from, to, _from_end)) = subslice else {
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
            let adj = from + to;
            let new_len = if adj > 0 {
                let adj_bv = Expr::bitvec_const(adj as i128, POINTER_WIDTH);
                src_len.bvsub(adj_bv)
            } else {
                src_len
            };
            self.ref_resolution.subslice_len.insert(dest_local, new_len);
            debug!(source_local, dest_local, from, to, "propagate_subslice_metadata: subslice_len");
        }
    }
}

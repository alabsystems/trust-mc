// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Assignment helpers: ref metadata propagation and flattened-local encoding.
//!
//! Extracted from `codegen_stmt/mod.rs` — Part of #4206.

use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::mir::{BinOp, Operand, Place, ProjectionElem, Rvalue};

use crate::args::ChcTrackLevel;

use super::super::ChcCtx;
use super::super::codegen_stmt_slice_metadata::RefMetadataOffsetMode;
use super::StmtAccumulator;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// D1: Propagate ref metadata (ref_targets, const_ref_values, subslice metadata,
    /// call_forwarded_raw_ptrs) through Copy/Move/Cast/Offset assignments.
    ///
    /// Covers aggregate-field-source, enum-payload-field, call-forwarded-copy-cast,
    /// general copy-cast, and ptr-offset propagation paths.
    pub(in crate::codegen_ay::chc) fn propagate_ref_metadata_for_assign(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
        local_idx: usize,
        bb_idx: usize,
        modified: &HashSet<usize>,
        aggregate_field_sources: &HashMap<(usize, usize), usize>,
    ) {
        if !lhs.projection.is_empty() {
            return;
        }
        self.known_stack_addr_exprs.remove(&local_idx);
        // Part of #3452: Propagate call_forwarded_raw_ptrs and ref_targets
        // through Copy/Move/Cast of raw pointer locals. When a call handler
        // (e.g., UnsafeCell::get) sets ref_targets for a destination local,
        // subsequent copies or casts of that local must inherit the
        // ref_target so that later dereferences can resolve through
        // ref_targets instead of the memory path.
        //
        // MIR chain: UnsafeCell::get → _24 (call_forwarded)
        //            _23 = Cast(Misc, move _24, *mut bool) → needs propagation
        //            _62 = Use(Move(_23))                  → needs propagation
        let src_place = match rhs {
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => Some(src),
            Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => Some(src),
            _ => None,
        };
        if let Some(src) = src_place {
            if src.projection.is_empty()
                && let Some(addr) = self.known_stack_addr_expr(src.local)
            {
                self.known_stack_addr_exprs.insert(local_idx, addr);
            }
            if src.projection.len() == 1
                && let ProjectionElem::Field(field_idx, _) = src.projection[0]
                && let Some(&source_local) = aggregate_field_sources.get(&(src.local, field_idx))
            {
                self.propagate_ref_metadata(
                    source_local,
                    local_idx,
                    bb_idx,
                    "aggregate-field-source",
                    false,
                    RefMetadataOffsetMode::Copy,
                );
            }
            // Handle Deref+Field projection chains for closure captures.
            // When _28 = Copy((*_22).field(0)):
            //   projection = [Deref, Field(0, _)]
            //   Follow *_22 through ref_targets to find target local (e.g., _12),
            //   then look up aggregate_field_sources[(12, 0)] to find field source.
            // This enables ref_target propagation through MIR-inlined FnMut closure
            // bodies where captures are accessed via deref of &mut closure_env.
            if src.projection.len() == 2
                && matches!(src.projection[0], ProjectionElem::Deref)
                && let ProjectionElem::Field(field_idx, _) = src.projection[1]
            {
                let deref_target =
                    self.ref_resolution.ref_targets.get(&src.local).map(|rt| rt.local);
                if let Some(target_local) = deref_target {
                    let afs_result = aggregate_field_sources.get(&(target_local, field_idx));
                    if let Some(&source_local) = afs_result {
                        self.propagate_ref_metadata(
                            source_local,
                            local_idx,
                            bb_idx,
                            "deref-aggregate-field-source",
                            false,
                            RefMetadataOffsetMode::Copy,
                        );
                    }
                }
            }
            // Part of #4101: Handle deref-load of a reference whose target has
            // const_ref_values. When _X = Copy(*_Y) and _Y has ref_targets
            // pointing to local Z which has const_ref_values, propagate from Z
            // to _X. This covers the SIMD as_array() pattern:
            //   _6 = as_array(...)       → const_ref_values[6] seeded
            //   _5 = Ref(Shared, _6)     → _5 is &_6, ref_targets[5] → 6
            //   _11 = Move(_5)           → ref_targets[11] → 6
            //   _13 = Copy(*_11)         → deref-load, needs const_ref_values[6]→13
            if src.projection.len() == 1 && matches!(src.projection[0], ProjectionElem::Deref) {
                let deref_target =
                    self.ref_resolution.ref_targets.get(&src.local).map(|rt| rt.local);
                if let Some(target_local) = deref_target {
                    self.propagate_ref_metadata(
                        target_local,
                        local_idx,
                        bb_idx,
                        "deref-load",
                        false,
                        RefMetadataOffsetMode::Copy,
                    );
                }
            }
            if src.projection.last().is_some_and(|proj| matches!(proj, ProjectionElem::Field(0, _)))
                && src.projection.iter().any(|proj| matches!(proj, ProjectionElem::Downcast(_)))
                && (self.ref_resolution.const_ref_values.contains_key(&src.local)
                    || self
                        .ref_resolution
                        .const_ref_slice_views
                        .contains_key(&src.local)
                    // Part of #4101: Also propagate ref_targets through
                    // enum payload extraction. When Option::Some(ptr) wraps
                    // a pointer with ref_targets, unwrap (Downcast+Field(0))
                    // must carry the ref_target to the extracted local.
                    || self
                        .ref_resolution
                        .ref_targets
                        .contains_key(&src.local))
            {
                self.propagate_ref_metadata(
                    src.local,
                    local_idx,
                    bb_idx,
                    "enum-payload-field",
                    false,
                    RefMetadataOffsetMode::Copy,
                );
            }
            let src_local: usize = src.local;
            let is_fwd = self.ref_resolution.call_forwarded_raw_ptrs.contains(&src_local);
            if src.projection.is_empty() && is_fwd {
                self.propagate_ref_metadata(
                    src_local,
                    local_idx,
                    bb_idx,
                    "call-forwarded-copy-cast",
                    true,
                    RefMetadataOffsetMode::Copy,
                );
            }
            // Part of #3698: Propagate ref_targets, const_ref_values,
            // and subslice metadata through Copy/Move/Cast even when
            // the source is NOT a call_forwarded raw pointer. This
            // covers mem::transmute between compatible reference types
            // (e.g., &[u8] → &Inner{inner: [u8]}), simple local copies,
            // and raw-pointer casts following pointer arithmetic. Once a
            // raw pointer local has a precise referent, register-level
            // copies/casts of that local must preserve the metadata so
            // downstream copy/deref paths can keep using ref_targets.
            if src.projection.is_empty() && !is_fwd {
                self.propagate_ref_metadata(
                    src_local,
                    local_idx,
                    bb_idx,
                    "copy-cast",
                    true,
                    RefMetadataOffsetMode::Copy,
                );
            }
        }

        if let Rvalue::BinaryOp(BinOp::Offset, base_op, offset_op)
        | Rvalue::CheckedBinaryOp(BinOp::Offset, base_op, offset_op) = rhs
            && let Operand::Copy(base_place) | Operand::Move(base_place) = base_op
            && base_place.projection.is_empty()
        {
            let base_local = base_place.local;
            let offset_mode = if let Some(offset_expr) = self
                .translate_operand_with_modified(offset_op, modified)
                .and_then(|expr| Self::const_usize_from_expr(&expr))
                .map(|offset| {
                    Expr::bitvec_const(offset as u64, crate::codegen_ay::types::POINTER_WIDTH)
                }) {
                RefMetadataOffsetMode::Accumulate(offset_expr)
            } else {
                RefMetadataOffsetMode::Remove
            };
            self.propagate_ref_metadata(
                base_local,
                local_idx,
                bb_idx,
                "ptr-offset",
                true,
                offset_mode,
            );
        }
    }

    /// D2: Encode a flattened local assignment (vtable capture, discriminant
    /// propagation, Mem-level memory mirroring).
    ///
    /// Called when `lhs` is a non-projected flattened tuple local. Handles
    /// patterns 1-5 via `try_encode_flattened_local_assign`, then captures
    /// vtable discriminants and mirrors to type-indexed memory at Mem level.
    pub(in crate::codegen_ay::chc) fn try_encode_flattened_assignment(
        &mut self,
        lhs: &Place,
        rhs: &'body Rvalue,
        local_idx: usize,
        _bb_idx: usize,
        modified: &mut HashSet<usize>,
        constraints: &mut Vec<Expr>,
        last_constraint_for_local: &mut HashMap<usize, usize>,
    ) {
        // Part of #2214: Flattened locals get special assignment handling.
        // When the destination is a flattened local and the rvalue is
        // CheckedBinaryOp, Aggregate, Adt, or Copy/Move of another flattened local,
        // we assign the N fields to separate scalar state vars instead of
        // constructing a Datatype expression.
        // See codegen_stmt_flatten.rs for the full dispatch logic.

        // try_encode_flattened_local_assign handles patterns 1-5:
        // CheckedBinaryOp, Aggregate, Adt (Option/Result), Copy/Move
        // (flat-to-flat), and Copy/Move with field projections (#3048).
        // Returns false only when no pattern matched — local is marked
        // modified (unconstrained) in that case too.
        let _handled = {
            let mut acc = StmtAccumulator::new(modified, constraints, last_constraint_for_local);
            self.try_encode_flattened_local_assign(local_idx, rhs, &mut acc)
        };
        let rhs_expr = self.translate_rvalue_with_modified(rhs, modified, Some(local_idx));
        let mut captured_flattened_vtable = false;
        if let Some(vtable_constraint) = self.try_capture_unsize_coercion_vtable(rhs, local_idx) {
            constraints.push(vtable_constraint);
            captured_flattened_vtable = true;
        } else if let Some(ref rhs_expr) = rhs_expr
            && let Some(vtable_constraint) = self.capture_vtable_discriminant(local_idx, rhs_expr)
        {
            constraints.push(vtable_constraint);
            captured_flattened_vtable = true;
        }
        if !captured_flattened_vtable {
            let propagated =
                super::super::codegen_stmt_assign_simple::extract_vtable_source_local(rhs)
                    .and_then(|src_local| self.propagate_vtable_discriminant(src_local, local_idx));
            if let Some(vtable_constraint) = propagated {
                constraints.push(vtable_constraint);
            } else if let Some(vtable_constraint) =
                self.try_capture_wrapper_deref_vtable(rhs, local_idx)
            {
                // Part of #3871: flattened locals can still receive
                // a thin-pointer deref-load for wrapper-dyn values,
                // so recover the unique wrapped vtable side-channel.
                constraints.push(vtable_constraint);
            }
        }
        // Part of #3096: At Mem level, mirror flattened value to
        // type-indexed memory so reference-based access (e.g.,
        // &Option<T> in PartialEq) reads correct values. Without
        // this, the memory at the local's address is unconstrained
        // — deref loads through &T produce spurious CTREX.
        if self.track_level >= ChcTrackLevel::Mem {
            let local_place = Place { local: lhs.local, projection: vec![] };
            if let Some(addr_expr) = self.translate_ref_to_address(&local_place, modified) {
                if let Some(rhs_expr) = rhs_expr {
                    let local_ty = self.body.locals()[local_idx].ty;
                    let memory_store_value = self
                        .translate_place_with_modified(&local_place, modified)
                        .unwrap_or_else(|| rhs_expr.clone());
                    let prev_suppress = self.suppress_heap_store_checks;
                    self.suppress_heap_store_checks = true;
                    if let Some(store_constraint) =
                        self.build_memory_store(addr_expr.clone(), memory_store_value, local_ty)
                    {
                        constraints.push(store_constraint);
                    }
                    self.mirror_aggregate_field_stores_to_memory(
                        rhs,
                        local_ty,
                        modified,
                        addr_expr.clone(),
                        constraints,
                    );
                    self.mirror_array_elements_to_flat_memory(
                        &rhs_expr,
                        local_ty,
                        &addr_expr,
                        constraints,
                    );
                    self.suppress_heap_store_checks = prev_suppress;
                }
            }
        }
    }
}

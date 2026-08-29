// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BFS worklist engine for constant-reference value propagation.
//!
//! Propagates const_ref_values through Copy/Move, Cast, Field projection,
//! Reborrow, and DerefField chains. Extracted from codegen_decl_ref_const_values.rs
//! per #4147 (large-file decomposition).
//!
//! Moved into codegen_decl_ref_const_values/collect.rs per #3694
//! (collect/provenance-first module split).

use std::collections::{HashMap, HashSet, VecDeque};

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

#[derive(Copy, Clone)]
pub(in crate::codegen_ay::chc::decl) enum ConstRefValuePropagationKind {
    CopyMove,
    Cast,
    /// Field projection from a datatype source (Part of #3235).
    /// The usize is the field index in the first constructor.
    Field(usize),
    /// Reborrow: `_dest = &(*_src)` — preserves const_ref_values from source.
    /// Part of #4070: assert!() macro temporaries reborrow promoted constant
    /// references through `&(*_N)` patterns that the CopyMove/Cast/Field
    /// propagation doesn't cover.
    Reborrow,
    /// DerefField: `_dest = &((*_src).field_idx)` — extracts a field from
    /// the dereferenced promoted constant. Part of #4070: derived PartialEq
    /// on tuples creates references to individual fields of the promoted
    /// constant tuple, e.g., `_38 = &((*_33).1: bool)` where _33 points to
    /// `(3u8, true)`. The propagated value is the field extraction.
    DerefField(usize),
}

#[derive(Copy, Clone)]
pub(in crate::codegen_ay::chc::decl) struct ConstRefValuePropagationCandidate {
    pub(in crate::codegen_ay::chc::decl) dest_local: usize,
    pub(in crate::codegen_ay::chc::decl) kind: ConstRefValuePropagationKind,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc::decl) fn build_const_ref_value_propagation_candidates(
        &self,
    ) -> HashMap<usize, Vec<ConstRefValuePropagationCandidate>> {
        let mut by_src: HashMap<usize, Vec<ConstRefValuePropagationCandidate>> = HashMap::new();
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                Self::collect_propagation_candidate(lhs.local, rhs, &mut by_src);
            }
        }
        by_src
    }

    /// Classify a single `Assign` rvalue into zero or more propagation candidates.
    fn collect_propagation_candidate(
        dest_local: usize,
        rhs: &Rvalue,
        by_src: &mut HashMap<usize, Vec<ConstRefValuePropagationCandidate>>,
    ) {
        // Copy/Move: `_dest = Copy/Move(_src)`.
        if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rhs
            && place.projection.is_empty()
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::CopyMove,
            });
        }
        // Part of #2173: Cast propagation (Transmute, PtrToPtr, etc.).
        if let Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) = rhs
            && place.projection.is_empty()
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::Cast,
            });
        }
        // Part of #3235: Field projection propagation.
        // `_dest = Copy/Move(_src.field)` — makes field extraction transitive.
        if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rhs
            && place.projection.len() == 1
            && let rustc_public::mir::ProjectionElem::Field(field_idx, _) = place.projection[0]
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::Field(field_idx),
            });
        }
        // Part of #4070: Reborrow and DerefField from Ref/AddressOf rvalues.
        Self::collect_ref_propagation_candidate(dest_local, rhs, by_src);
    }

    /// Collect Reborrow and DerefField propagation candidates from Ref/AddressOf.
    fn collect_ref_propagation_candidate(
        dest_local: usize,
        rhs: &Rvalue,
        by_src: &mut HashMap<usize, Vec<ConstRefValuePropagationCandidate>>,
    ) {
        let place: &Place = match rhs {
            Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p) => p,
            _ => return,
        };
        if place.projection.len() == 1
            && matches!(place.projection[0], rustc_public::mir::ProjectionElem::Deref)
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::Reborrow,
            });
        }
        // `_dest = &((*_src).field_idx)` — derived PartialEq on tuples.
        if place.projection.len() == 2
            && matches!(place.projection[0], rustc_public::mir::ProjectionElem::Deref)
            && let rustc_public::mir::ProjectionElem::Field(field_idx, _) = place.projection[1]
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::DerefField(field_idx),
            });
        }
    }

    fn enqueue_const_ref_value_local(
        queue: &mut VecDeque<usize>,
        queued: &mut HashSet<usize>,
        local: usize,
    ) {
        if queued.insert(local) {
            queue.push_back(local);
        }
    }

    /// Compute the propagated value for a single candidate, or None to skip.
    fn compute_propagated_value(
        src_value: &Expr,
        candidate: &ConstRefValuePropagationCandidate,
        src_local: usize,
    ) -> Option<Expr> {
        match candidate.kind {
            ConstRefValuePropagationKind::CopyMove => {
                debug!(
                    "Pass4.2 propagate const_ref_value: _{} = _{} -> {:?}",
                    candidate.dest_local, src_local, src_value
                );
                Some(src_value.clone())
            }
            ConstRefValuePropagationKind::Cast => {
                debug!(
                    "Pass4.2 cast const_ref_value: _{} = Cast(_{}) -> {:?}",
                    candidate.dest_local, src_local, src_value
                );
                Some(src_value.clone())
            }
            ConstRefValuePropagationKind::Reborrow => {
                debug!(
                    "Pass4.2 reborrow const_ref_value: _{} = &(*_{}) -> {:?}",
                    candidate.dest_local, src_local, src_value
                );
                Some(src_value.clone())
            }
            ConstRefValuePropagationKind::Field(field_idx)
            | ConstRefValuePropagationKind::DerefField(field_idx) => {
                Self::extract_field_from_propagation(src_value, candidate, src_local, field_idx)
            }
        }
    }

    /// Extract a datatype field from a propagation source value.
    fn extract_field_from_propagation(
        src_value: &Expr,
        candidate: &ConstRefValuePropagationCandidate,
        src_local: usize,
        field_idx: usize,
    ) -> Option<Expr> {
        let ay_bindings::SortInner::Datatype(dt) = src_value.sort().inner() else {
            return None;
        };
        let cons = dt.constructors.first()?;
        let field = cons.fields.get(field_idx)?;
        let extracted = src_value.clone().field_select(&dt.name, &field.name, field.sort.clone());
        debug!(
            dest_local = candidate.dest_local,
            src_local,
            field_name = %field.name,
            "Pass4.3 field/deref_field const_ref_value (worklist)"
        );
        Some(extracted)
    }

    pub(in crate::codegen_ay::chc::decl) fn propagate_const_ref_values_worklist(
        &mut self,
        by_src: &HashMap<usize, Vec<ConstRefValuePropagationCandidate>>,
    ) {
        let mut queue: VecDeque<usize> =
            self.ref_resolution.const_ref_values.keys().copied().collect();
        let mut queued: HashSet<usize> =
            self.ref_resolution.const_ref_values.keys().copied().collect();

        while let Some(src_local) = queue.pop_front() {
            queued.remove(&src_local);
            let Some(src_value) = self.ref_resolution.const_ref_values.get(&src_local).cloned()
            else {
                continue;
            };
            let Some(candidates) = by_src.get(&src_local) else { continue };
            for candidate in candidates {
                if !self.path_insensitive_metadata_copy_is_unique(src_local, candidate.dest_local) {
                    self.clear_path_insensitive_ref_metadata(candidate.dest_local);
                    continue;
                }
                if self.ref_resolution.const_ref_values.contains_key(&candidate.dest_local) {
                    continue;
                }
                let Some(propagated_value) =
                    Self::compute_propagated_value(&src_value, candidate, src_local)
                else {
                    continue;
                };
                self.ref_resolution.const_ref_values.insert(candidate.dest_local, propagated_value);
                self.propagate_metadata(src_local, candidate.dest_local);
                Self::enqueue_const_ref_value_local(&mut queue, &mut queued, candidate.dest_local);
            }
        }
    }

    /// Copy subslice_len and promoted_obj_id from source to destination local.
    fn propagate_metadata(&mut self, src_local: usize, dest_local: usize) {
        // Part of #3495: Propagate subslice_len through Copy/Move/Cast.
        if let Some(len) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len);
        }
        // Part of #4070: Propagate promoted_obj_id through all candidate kinds.
        if let Some(&obj_id) = self.ref_resolution.const_ref_promoted_obj_ids.get(&src_local) {
            self.ref_resolution.const_ref_promoted_obj_ids.insert(dest_local, obj_id);
        }
    }

    /// Collects scalar values from constant references to primitive types.
    ///
    /// Part of #1919: When we see `_ref = const &0u8`, the allocation contains a
    /// pointer with provenance. We follow it to read the pointee value and record
    /// a AY expression. This enables `translate_place_with_deref` to resolve
    /// `(*_ref)` for promoted constant references that aren't tracked in ref_targets.
    pub(in crate::codegen_ay::chc) fn collect_const_ref_values(&mut self) {
        // Pass 4.1: Direct constant reference assignments to scalar types
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && let Rvalue::Use(Operand::Constant(const_op)) = rhs
                {
                    self.try_collect_single_const_ref(lhs.local, const_op);
                }
            }
        }

        // Pass 4.2+4.3: Propagate through Copy/Move, Cast, and Field projections.
        let propagation_candidates = self.build_const_ref_value_propagation_candidates();
        self.propagate_const_ref_values_worklist(&propagation_candidates);

        debug!(
            count = self.ref_resolution.const_ref_values.len(),
            memory_inits_count = self.ref_resolution.const_ref_memory_inits.len(),
            "CHC: collected constant reference values"
        );
    }

    /// Attempt to extract and record a const-ref value for one assignment.
    fn try_collect_single_const_ref(
        &mut self,
        dest_local: usize,
        const_op: &rustc_public::mir::ConstOperand,
    ) {
        if self.local_has_multiple_whole_definitions(dest_local) {
            self.clear_path_insensitive_ref_metadata(dest_local);
            return;
        }
        let mir_const = &const_op.const_;
        let ty = mir_const.ty();
        debug!("Pass4.1 scan: _{} = Use(Const), ty={:?}", dest_local, ty.kind());
        if self.ref_resolution.const_ref_values.contains_key(&dest_local) {
            return;
        }
        let TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _)) = ty.kind() else {
            return;
        };
        let Some(promoted_obj_id) = self.heap_state.next_promoted_const_obj_id() else {
            return;
        };
        let promoted_addr = self.heap_state.promoted_const_address_for(promoted_obj_id);
        Self::record_promoted_alloc_address(
            mir_const.kind().clone(),
            &promoted_addr,
            &mut self.ref_resolution.promoted_const_alloc_addresses,
        );
        let mut local_memory_inits = Vec::new();
        let mut nested_str_len: Option<usize> = None;
        let expr = Self::try_extract_with_fallbacks(
            mir_const,
            inner_ty,
            &promoted_addr,
            &mut local_memory_inits,
            promoted_obj_id,
            &mut nested_str_len,
        );
        let Some(expr) = expr else { return };
        debug!("Pass4 const_ref_value: _{} = {:?}", dest_local, expr);
        if !local_memory_inits.is_empty() {
            self.ref_resolution.const_ref_promoted_obj_ids.insert(dest_local, promoted_obj_id);
            self.ref_resolution.const_ref_memory_inits.extend(local_memory_inits);
        }
        self.ref_resolution.const_ref_values.insert(dest_local, expr);
        self.record_subslice_len(dest_local, inner_ty, mir_const, nested_str_len);
    }

    /// Try scalar extraction, then nested-str, then nested-ref fallbacks.
    fn try_extract_with_fallbacks(
        mir_const: &rustc_public::ty::MirConst,
        inner_ty: rustc_public::ty::Ty,
        promoted_addr: &Expr,
        memory_inits: &mut Vec<(std::sync::Arc<str>, ay_bindings::Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
        nested_str_len: &mut Option<usize>,
    ) -> Option<Expr> {
        // Primary: direct scalar/composite extraction.
        if let Some(expr) = Self::extract_scalar_from_const_ref(
            mir_const.kind().clone(),
            inner_ty,
            memory_inits,
            promoted_obj_id,
        ) {
            return Some(expr);
        }
        // Fallback 1: nested `&&str` (Part of #3607).
        if let TyKind::RigidTy(RigidTy::Ref(_, nested_inner_ty, _)) = inner_ty.kind()
            && matches!(nested_inner_ty.kind(), TyKind::RigidTy(RigidTy::Str))
        {
            if let Some((expr, len)) = Self::extract_nested_str_from_const_ref(
                mir_const.kind().clone(),
                memory_inits,
                promoted_obj_id,
            ) {
                *nested_str_len = Some(len);
                return Some(expr);
            }
        }
        // Fallback 2: nested `&&[T; N]` (Part of #3632).
        if let TyKind::RigidTy(RigidTy::Ref(_, nested_inner_ty, _)) = inner_ty.kind() {
            let _ = Self::extract_nested_ref_from_const_ref(
                mir_const.kind().clone(),
                nested_inner_ty,
                memory_inits,
                promoted_obj_id,
            );
            return Some(promoted_addr.clone());
        }
        None
    }

    /// Record subslice_len for slice, str, and nested-str inner types.
    fn record_subslice_len(
        &mut self,
        dest_local: usize,
        inner_ty: rustc_public::ty::Ty,
        mir_const: &rustc_public::ty::MirConst,
        nested_str_len: Option<usize>,
    ) {
        // Part of #3495: Record slice length for PtrMetadata resolution.
        if let TyKind::RigidTy(RigidTy::Slice(elem_ty)) = inner_ty.kind() {
            if let Some(ebw) = Self::const_elem_byte_width(elem_ty).filter(|&w| w > 0) {
                if let Some(alloc_bytes) = Self::const_alloc_byte_count(mir_const.kind().clone()) {
                    let len_expr = Expr::bitvec_const((alloc_bytes / ebw) as u128, POINTER_WIDTH);
                    self.ref_resolution.subslice_len.insert(dest_local, len_expr);
                }
            }
        }
        // Part of #3617: Record subslice_len for promoted `&str`.
        if let TyKind::RigidTy(RigidTy::Str) = inner_ty.kind() {
            if let Some(alloc_bytes) = Self::const_alloc_byte_count(mir_const.kind().clone()) {
                let len_expr = Expr::bitvec_const(alloc_bytes as u128, POINTER_WIDTH);
                self.ref_resolution.subslice_len.insert(dest_local, len_expr);
            }
        }
        if let Some(nested_len) = nested_str_len {
            let len_expr = Expr::bitvec_const(nested_len as u128, POINTER_WIDTH);
            self.ref_resolution.subslice_len.insert(dest_local, len_expr);
        }
    }
}

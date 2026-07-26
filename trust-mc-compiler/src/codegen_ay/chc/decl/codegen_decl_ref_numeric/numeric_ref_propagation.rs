// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_public::mir::{
    AggregateKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::{ChcCtx, RefTarget};

#[derive(Clone)]
enum NumericRefPropagationKind {
    CopyMove,
    TransitiveDeref,
    DerefProjectedCopy {
        proj_suffix: Vec<ProjectionElem>,
    },
    Reborrow,
    Cast,
    PointerMaterialization {
        callee_path: String,
    },
    /// `dest = kani::internal::untracked_deref(arg)` where `arg: &T` — the hook
    /// returns a bit-copy of `*arg`, so `dest`'s referent is the referent of the
    /// reference VALUE stored at `arg`'s pointee. Contract shims (modifies
    /// replace/havoc lowering) route every `write_any` pointer through this
    /// call; without this edge the whole chain is unresolvable (FC unknown
    /// cluster, Shape A).
    UntrackedDerefCall,
}

#[derive(Clone)]
pub(super) struct NumericRefPropagationCandidate {
    dest_local: usize,
    src_local: usize,
    kind: NumericRefPropagationKind,
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub(super) enum NumericRefPropagationMode {
    CopyMoveOnly,
    FullPass15,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn propagated_ref_target(&self, local_idx: usize) -> Option<RefTarget> {
        self.ref_resolution
            .ref_targets
            .get(&local_idx)
            .cloned()
            .or_else(|| {
                (self.ref_resolution.ref_arg_pointee_idx.contains_key(&local_idx)
                    || self.ref_resolution.coroutine_root_map.contains_key(&local_idx))
                .then(|| RefTarget::with_projections(local_idx, vec![]))
            })
            .or_else(|| {
                self.ref_resolution
                    .static_ref_to_state_idx
                    .contains_key(&local_idx)
                    .then(|| RefTarget::with_projections(local_idx, vec![ProjectionElem::Deref]))
            })
    }

    fn source_local_for_copy_move_ref_target(
        &self,
        place: &Place,
        field_sources: &HashMap<(usize, usize), usize>,
    ) -> Option<usize> {
        if place.projection.is_empty() {
            return Some(place.local);
        }

        if place.projection.len() == 1
            && let ProjectionElem::Field(field_idx, _) = place.projection[0]
        {
            if let Some(&src) = field_sources.get(&(place.local, field_idx)) {
                return Some(src);
            }
            // Part of #3807: recognize wrapper-arg field copies like `copy (_pin_arg.0)`
            // so the copied local enters the propagation pipeline with the wrapper arg
            // as its source. This bridges Pin<&mut Coroutine> arg fields into ref_targets.
            if self
                .ref_resolution
                .arg_wrapper_field_pointee_idx
                .contains_key(&(place.local, field_idx))
            {
                return Some(place.local);
            }
        }
        None
    }

    fn add_numeric_ref_candidate(
        candidates: &mut Vec<NumericRefPropagationCandidate>,
        by_src: &mut HashMap<usize, Vec<usize>>,
        dest_local: usize,
        src_local: usize,
        kind: NumericRefPropagationKind,
    ) {
        let idx = candidates.len();
        candidates.push(NumericRefPropagationCandidate { dest_local, src_local, kind });
        by_src.entry(src_local).or_default().push(idx);
    }

    pub(super) fn build_numeric_ref_propagation_candidates(
        &self,
        field_sources: &HashMap<(usize, usize), usize>,
        mode: NumericRefPropagationMode,
    ) -> (Vec<NumericRefPropagationCandidate>, HashMap<usize, Vec<usize>>) {
        let mut candidates: Vec<NumericRefPropagationCandidate> = Vec::new();
        let mut by_src: HashMap<usize, Vec<usize>> = HashMap::new();

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                let dest_local: usize = lhs.local;

                if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::CopyForDeref(place) = rhs
                {
                    if let Some(src_local) =
                        self.source_local_for_copy_move_ref_target(place, field_sources)
                    {
                        Self::add_numeric_ref_candidate(
                            &mut candidates,
                            &mut by_src,
                            dest_local,
                            src_local,
                            NumericRefPropagationKind::CopyMove,
                        );
                    }
                    if mode == NumericRefPropagationMode::FullPass15
                        && place.projection.len() > 1
                        && matches!(place.projection[0], ProjectionElem::Deref)
                    {
                        // Part of #1739 (Bug 3b): deref+field chains in Pass 1.5
                        let mut supported_suffix = true;
                        for proj in &place.projection[1..] {
                            match proj {
                                ProjectionElem::Field(_, _)
                                | ProjectionElem::Downcast(_)
                                | ProjectionElem::Index(_)
                                | ProjectionElem::ConstantIndex { .. } => {}
                                _ => {
                                    supported_suffix = false;
                                    break;
                                }
                            }
                        }
                        if supported_suffix {
                            Self::add_numeric_ref_candidate(
                                &mut candidates,
                                &mut by_src,
                                dest_local,
                                place.local,
                                NumericRefPropagationKind::DerefProjectedCopy {
                                    proj_suffix: place.projection[1..].to_vec(),
                                },
                            );
                        }
                    } else if mode == NumericRefPropagationMode::FullPass15
                        && place.projection.len() == 1
                        && matches!(place.projection[0], ProjectionElem::Deref)
                    {
                        Self::add_numeric_ref_candidate(
                            &mut candidates,
                            &mut by_src,
                            dest_local,
                            place.local,
                            NumericRefPropagationKind::TransitiveDeref,
                        );
                    }
                }

                if mode != NumericRefPropagationMode::FullPass15 {
                    continue;
                }

                if let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rhs
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                {
                    Self::add_numeric_ref_candidate(
                        &mut candidates,
                        &mut by_src,
                        dest_local,
                        place.local,
                        NumericRefPropagationKind::Reborrow,
                    );
                }

                if let Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) = rhs
                    && place.projection.is_empty()
                {
                    Self::add_numeric_ref_candidate(
                        &mut candidates,
                        &mut by_src,
                        dest_local,
                        place.local,
                        NumericRefPropagationKind::Cast,
                    );
                }
            }

            // Contract-shim untracked_deref call crossing (FC modifies Shape A).
            // Collected in BOTH modes: the arg's ref_target frequently only
            // appears after Pass 2 (deref-through-ref), so the PostPass2
            // (CopyMoveOnly) run must also see these candidates.
            if let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind
                && self.detect_kani_hook(func)
                    == Some(crate::kani_middle::kani_functions::KaniHook::UntrackedDeref)
                && args.len() == 1
                && let Some(Operand::Copy(place) | Operand::Move(place)) = args.first()
                && place.projection.is_empty()
                && destination.projection.is_empty()
            {
                Self::add_numeric_ref_candidate(
                    &mut candidates,
                    &mut by_src,
                    destination.local,
                    place.local,
                    NumericRefPropagationKind::UntrackedDerefCall,
                );
            }

            if mode != NumericRefPropagationMode::FullPass15 {
                continue;
            }

            // Part of #2110: preserve referent identity through slice pointer
            // materialization calls (`as_ptr`, `as_mut_ptr`).
            if let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind
                && let Some(callee_path) = self.resolve_callee_path(func)
                && matches!(callee_path.rsplit("::").next(), Some("as_ptr" | "as_mut_ptr"))
                && let Some(Operand::Copy(place) | Operand::Move(place)) = args.first()
                && place.projection.is_empty()
            {
                Self::add_numeric_ref_candidate(
                    &mut candidates,
                    &mut by_src,
                    destination.local,
                    place.local,
                    NumericRefPropagationKind::PointerMaterialization { callee_path },
                );
            }
        }

        (candidates, by_src)
    }

    fn enqueue_numeric_ref_local(
        queue: &mut VecDeque<usize>,
        queued: &mut HashSet<usize>,
        local: usize,
    ) {
        if queued.insert(local) {
            queue.push_back(local);
        }
    }

    fn insert_numeric_ref_target(
        &mut self,
        dest_local: usize,
        target: RefTarget,
        queue: &mut VecDeque<usize>,
        queued: &mut HashSet<usize>,
    ) {
        if dest_local != target.local || !target.projections.is_empty() {
            self.ref_resolution.ref_targets.insert(dest_local, target);
            Self::enqueue_numeric_ref_local(queue, queued, dest_local);
        }
    }

    fn apply_numeric_ref_candidate(
        &mut self,
        candidate_idx: usize,
        candidates: &[NumericRefPropagationCandidate],
        field_sources: &HashMap<(usize, usize), usize>,
        phase_label: &str,
        deferred_transitive: &mut HashMap<usize, Vec<usize>>,
        queue: &mut VecDeque<usize>,
        queued: &mut HashSet<usize>,
    ) {
        let candidate = &candidates[candidate_idx];
        let dest_local = candidate.dest_local;
        if self.ref_resolution.ref_targets.contains_key(&dest_local) {
            return;
        }

        match &candidate.kind {
            NumericRefPropagationKind::CopyMove => {
                if let Some(src_target) = self.propagated_ref_target(candidate.src_local) {
                    debug!(
                        "{phase_label} copy/move ref: {dest_local} from local {} -> {}",
                        candidate.src_local, src_target.local
                    );
                    self.insert_numeric_ref_target(dest_local, src_target, queue, queued);
                }
            }
            NumericRefPropagationKind::TransitiveDeref => {
                // Part of #2090: transitive deref inherits target through resolved ref local.
                if let Some(src_target) = self.propagated_ref_target(candidate.src_local) {
                    let resolved_local = src_target.local;
                    if let Some(transitive_target) = self.propagated_ref_target(resolved_local) {
                        debug!(
                            "{phase_label} transitive deref: {} = Copy/Move(*{}) -> *{} -> {}",
                            dest_local,
                            candidate.src_local,
                            resolved_local,
                            transitive_target.local
                        );
                        self.insert_numeric_ref_target(
                            dest_local,
                            transitive_target,
                            queue,
                            queued,
                        );
                    } else {
                        deferred_transitive.entry(resolved_local).or_default().push(candidate_idx);
                    }
                }
            }
            NumericRefPropagationKind::DerefProjectedCopy { proj_suffix } => {
                if let Some(src_target) = self.propagated_ref_target(candidate.src_local) {
                    let mut combined_projs = src_target.projections.clone();
                    combined_projs.extend(proj_suffix.clone());
                    debug!(
                        "{phase_label} deref+projection copy: {} = Copy((*{}).proj) -> {}",
                        dest_local, candidate.src_local, src_target.local
                    );
                    self.insert_numeric_ref_target(
                        dest_local,
                        RefTarget::with_projections(src_target.local, combined_projs),
                        queue,
                        queued,
                    );
                }
            }
            NumericRefPropagationKind::Reborrow => {
                if let Some(src_target) = self.propagated_ref_target(candidate.src_local) {
                    debug!(
                        "{phase_label} reborrow ref: {} = &(*{}) -> {}",
                        dest_local, candidate.src_local, src_target.local
                    );
                    self.insert_numeric_ref_target(dest_local, src_target, queue, queued);
                }
            }
            NumericRefPropagationKind::Cast => {
                if let Some(src_target) = self.propagated_ref_target(candidate.src_local) {
                    debug!(
                        "{phase_label} cast ref: {} = Cast({}) -> {}",
                        dest_local, candidate.src_local, src_target.local
                    );
                    self.insert_numeric_ref_target(dest_local, src_target, queue, queued);
                }
            }
            NumericRefPropagationKind::PointerMaterialization { callee_path } => {
                if let Some(src_target) = self.propagated_ref_target(candidate.src_local) {
                    debug!(
                        "{phase_label} call ref: {} = {}({}) -> {}",
                        dest_local, callee_path, candidate.src_local, src_target.local
                    );
                    self.insert_numeric_ref_target(dest_local, src_target, queue, queued);
                }
            }
            NumericRefPropagationKind::UntrackedDerefCall => {
                // `dest = untracked_deref(arg)` with `arg: &T`: dest is a bit-copy
                // of `*arg`, so dest's referent is the referent of the reference
                // value stored at arg's pointee place.
                //
                // Soundness: only resolve when every hop is definite; otherwise
                // leave `dest` unresolved (downstream write_any stays fail-closed
                // via kani_write_any_slim_target_unresolved).
                let Some(arg_target) = self.propagated_ref_target(candidate.src_local) else {
                    return;
                };
                if arg_target.projections.is_empty() {
                    // Pointee is a plain local holding a reference: inherit its target.
                    if let Some(value_target) = self.propagated_ref_target(arg_target.local) {
                        debug!(
                            "{phase_label} untracked_deref: {} = untracked_deref({}) -> *{} -> {}",
                            dest_local, candidate.src_local, arg_target.local, value_target.local
                        );
                        self.insert_numeric_ref_target(dest_local, value_target, queue, queued);
                    } else {
                        deferred_transitive
                            .entry(arg_target.local)
                            .or_default()
                            .push(candidate_idx);
                    }
                } else {
                    // Pointee is a reference-typed field reached through a chain
                    // of aggregate Field projections (closure envs wrap the shim
                    // captures, so `&s.target` appears as `&env.0.1`). Walk the
                    // aggregate field_sources hop by hop; the FINAL field must be
                    // reference/pointer-typed and every hop must be definite.
                    let mut cur_local = arg_target.local;
                    let mut resolved_chain = true;
                    let last_idx = arg_target.projections.len() - 1;
                    for (i, proj) in arg_target.projections.iter().enumerate() {
                        let ProjectionElem::Field(field_idx, field_ty) = proj else {
                            resolved_chain = false;
                            break;
                        };
                        if i == last_idx
                            && !matches!(
                                field_ty.kind(),
                                TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _))
                            )
                        {
                            resolved_chain = false;
                            break;
                        }
                        let Some(&field_src) = field_sources.get(&(cur_local, *field_idx)) else {
                            resolved_chain = false;
                            break;
                        };
                        cur_local = field_src;
                    }
                    if resolved_chain {
                        // The reference value stored at the projected field came
                        // from `cur_local` (aggregate operand chain).
                        if let Some(value_target) = self.propagated_ref_target(cur_local) {
                            debug!(
                                "{phase_label} untracked_deref: {} = untracked_deref({}) -> \
                                 ({} proj-chain from {}) -> {}",
                                dest_local,
                                candidate.src_local,
                                arg_target.local,
                                cur_local,
                                value_target.local
                            );
                            self.insert_numeric_ref_target(dest_local, value_target, queue, queued);
                        } else {
                            deferred_transitive.entry(cur_local).or_default().push(candidate_idx);
                        }
                    }
                    // Any other shape: fail-closed (no ref_targets entry).
                }
            }
        }
    }

    pub(super) fn propagate_numeric_ref_targets_worklist(
        &mut self,
        candidates: &[NumericRefPropagationCandidate],
        by_src: &HashMap<usize, Vec<usize>>,
        field_sources: &HashMap<(usize, usize), usize>,
        phase_label: &str,
    ) {
        let mut queued: HashSet<usize> = self.ref_resolution.ref_targets.keys().copied().collect();
        queued.extend(self.ref_resolution.ref_arg_pointee_idx.keys().copied());
        queued.extend(self.ref_resolution.coroutine_root_map.keys().copied());
        let mut queue: VecDeque<usize> = queued.iter().copied().collect();
        let mut deferred_transitive: HashMap<usize, Vec<usize>> = HashMap::new();

        while let Some(src_local) = queue.pop_front() {
            queued.remove(&src_local);

            if let Some(candidate_indices) = by_src.get(&src_local) {
                for &candidate_idx in candidate_indices {
                    self.apply_numeric_ref_candidate(
                        candidate_idx,
                        candidates,
                        field_sources,
                        phase_label,
                        &mut deferred_transitive,
                        &mut queue,
                        &mut queued,
                    );
                }
            }

            if let Some(candidate_indices) = deferred_transitive.remove(&src_local) {
                for candidate_idx in candidate_indices {
                    self.apply_numeric_ref_candidate(
                        candidate_idx,
                        candidates,
                        field_sources,
                        phase_label,
                        &mut deferred_transitive,
                        &mut queue,
                        &mut queued,
                    );
                }
            }
        }
    }

    /// Collect aggregate field sources (Tuple/ADT) for transitive ref resolution.
    pub(in crate::codegen_ay::chc) fn collect_aggregate_field_sources(
        &self,
    ) -> HashMap<(usize, usize), usize> {
        let mut field_sources: HashMap<(usize, usize), usize> = HashMap::new();
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, Rvalue::Aggregate(kind, operands)) = &stmt.kind
                else {
                    continue;
                };
                match kind {
                    AggregateKind::Tuple | AggregateKind::Adt(..) | AggregateKind::Closure(..) => {}
                    _ => continue,
                }
                let agg_local: usize = lhs.local;
                for (field_idx, operand) in operands.iter().enumerate() {
                    if let Operand::Copy(place) | Operand::Move(place) = operand
                        && place.projection.is_empty()
                    {
                        field_sources.insert((agg_local, field_idx), place.local);
                    }
                }
            }
        }
        // Propagate field_sources through simple copy/move chains so moved Pin
        // aggregates retain their field source locals (Part of #3807).
        let mut copy_map: Vec<(usize, usize)> = Vec::new();
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
                ) = &stmt.kind
                    && place.projection.is_empty()
                    && lhs.projection.is_empty()
                {
                    copy_map.push((lhs.local, place.local));
                }
            }
        }
        for _ in 0..copy_map.len().min(8) {
            let mut new_entries = Vec::new();
            for &(dest, src) in &copy_map {
                let src_fields: Vec<_> = field_sources
                    .iter()
                    .filter(|&(&(local, _), _)| local == src)
                    .map(|(&(_, field_idx), &src_local)| (field_idx, src_local))
                    .collect();
                for (field_idx, src_local) in src_fields {
                    if !field_sources.contains_key(&(dest, field_idx)) {
                        new_entries.push(((dest, field_idx), src_local));
                    }
                }
            }
            if new_entries.is_empty() {
                break;
            }
            for (key, val) in new_entries {
                field_sources.insert(key, val);
            }
        }
        field_sources
    }
    /// Resolve ref_targets pointing to reference-typed ADT fields through aggregate
    /// field sources. Enables nested deref chains like `(*(*ref).inner).val`.
    pub(super) fn resolve_adt_field_ref_targets(
        &mut self,
        field_sources: &HashMap<(usize, usize), usize>,
    ) {
        // Collect updates to apply (avoid mutating ref_targets while iterating).
        let updates: Vec<(usize, RefTarget)> = self
            .ref_resolution
            .ref_targets
            .iter()
            .filter_map(|(&local, target)| {
                // Only handle single-Field projection pointing to a reference type.
                if target.projections.len() != 1 {
                    return None;
                }
                let field_idx = match target.projections[0] {
                    ProjectionElem::Field(idx, field_ty) => {
                        // Check if the field type is a reference/pointer.
                        if !matches!(
                            field_ty.kind(),
                            TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _))
                        ) {
                            return None;
                        }
                        idx
                    }
                    _ => return None,
                };

                // Look up the aggregate field source for this field.
                let &src_local = field_sources.get(&(target.local, field_idx))?;
                // If the source local has a ref_target, use it.
                let src_target = self.ref_resolution.ref_targets.get(&src_local)?;
                debug!(
                    local,
                    target_struct = target.local,
                    field_idx,
                    src_local,
                    resolved_target = src_target.local,
                    "Pass2.5: resolved ADT field ref_target through aggregate field source"
                );
                Some((local, src_target.clone()))
            })
            .collect();
        for (local, new_target) in updates {
            self.ref_resolution.ref_targets.insert(local, new_target);
        }
    }
}

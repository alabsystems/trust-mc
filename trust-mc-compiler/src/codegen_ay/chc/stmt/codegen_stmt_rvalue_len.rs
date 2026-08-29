// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rvalue::Len translation and length resolution helpers for CHC encoding.
//!
//! Extracted from `codegen_stmt_rvalue.rs` per #3920 to reduce merge-conflict
//! contention. Contains the Len arm body and three length resolution strategies:
//! - conflict-sticky MIR provenance for array-backed slices and subslices
//! - unanimous range-call side metadata
//! - `try_resolve_len_from_datatype`: extract fld_len from Vec/Slice Datatypes

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{
    CastKind, Operand, Place, PointerCoercion, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::ChcCtx;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::codegen_stmt_projection::{UnknownProjectionPolicy, collect_field_projections};

const MAX_SLICE_LEN_PROVENANCE_STEPS: usize = 128;

/// Conflict-sticky evidence for one concrete slice length.
///
/// `Absent` means no authority-bearing producer was found. `Conflict` means a
/// producer was cyclic or over budget, two exact producers disagreed, or an
/// unresolved producer competed with exact evidence. Once conflicted, later
/// exact evidence can never recover a length: doing so would choose one CFG
/// predecessor and under-approximate the others.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SliceLenEvidence {
    Absent,
    Exact(u64),
    Conflict,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SliceCarrierEvidence {
    NotCarrier,
    Carrier,
    Conflict,
}

impl SliceLenEvidence {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Conflict, _) | (_, Self::Conflict) => Self::Conflict,
            (Self::Absent, evidence) | (evidence, Self::Absent) => evidence,
            (Self::Exact(lhs), Self::Exact(rhs)) if lhs == rhs => Self::Exact(lhs),
            (Self::Exact(_), Self::Exact(_)) => Self::Conflict,
        }
    }
}

fn exact_subslice_len(source_length: u64, from: u64, to: u64, from_end: bool) -> SliceLenEvidence {
    let length = if from_end {
        source_length.checked_sub(from).and_then(|remaining| remaining.checked_sub(to))
    } else if to <= source_length {
        to.checked_sub(from)
    } else {
        None
    };
    length.map_or(SliceLenEvidence::Conflict, SliceLenEvidence::Exact)
}

fn merge_unanimous_len_expr(candidate: &mut Option<Expr>, next: &Expr) -> Result<(), ()> {
    if candidate.as_ref().is_some_and(|known| known != next) {
        return Err(());
    }
    candidate.get_or_insert_with(|| next.clone());
    Ok(())
}

fn finish_slice_len_evidence(
    evidence: SliceLenEvidence,
    saw_definition: bool,
    saw_unresolved_definition: bool,
) -> SliceLenEvidence {
    if !saw_definition {
        SliceLenEvidence::Absent
    } else if saw_unresolved_definition && matches!(evidence, SliceLenEvidence::Exact(_)) {
        SliceLenEvidence::Conflict
    } else {
        evidence
    }
}

/// A `RangeFull` index is an identity operation, but it cannot CREATE length
/// authority. In particular, a path-insensitive side table may contain one
/// predecessor's length even when the source local is absent or conflicting in
/// the MIR provenance walk. Poison those cases so the destination cannot revive
/// the stale candidate later.
fn range_full_slice_len_evidence(source: SliceLenEvidence) -> SliceLenEvidence {
    match source {
        SliceLenEvidence::Exact(length) => SliceLenEvidence::Exact(length),
        SliceLenEvidence::Absent | SliceLenEvidence::Conflict => SliceLenEvidence::Conflict,
    }
}

#[cfg(test)]
mod slice_len_evidence_tests {
    use ay_bindings::Expr;

    use super::{
        POINTER_WIDTH, SliceLenEvidence, exact_subslice_len, finish_slice_len_evidence,
        merge_unanimous_len_expr, range_full_slice_len_evidence,
    };

    #[test]
    fn exact_evidence_is_unanimous_and_order_independent() {
        use SliceLenEvidence::{Absent, Exact};

        assert_eq!(Absent.merge(Exact(4)), Exact(4));
        assert_eq!(Exact(4).merge(Absent), Exact(4));
        assert_eq!(Exact(4).merge(Exact(4)), Exact(4));
    }

    #[test]
    fn disagreement_and_unknown_producers_are_sticky_conflicts() {
        use SliceLenEvidence::{Absent, Conflict, Exact};

        assert_eq!(Exact(4).merge(Exact(8)), Conflict);
        assert_eq!(Exact(8).merge(Exact(4)), Conflict);
        assert_eq!(Conflict.merge(Exact(4)), Conflict);
        assert_eq!(Exact(4).merge(Conflict), Conflict);
        assert_eq!(Conflict.merge(Conflict), Conflict);
        assert_eq!(finish_slice_len_evidence(Exact(4), true, true), Conflict);
        // All-unresolved evidence belongs to a disjoint metadata lane; it does
        // not become a conflict until it competes with an exact candidate.
        assert_eq!(finish_slice_len_evidence(Absent, true, true), Absent);
    }

    #[test]
    fn subslice_polarity_and_checked_arithmetic_are_exact() {
        use SliceLenEvidence::{Conflict, Exact};

        // `from_end=true`: source_length - from - to.
        assert_eq!(exact_subslice_len(8, 2, 1, true), Exact(5));
        // `from_end=false`: `to` is an absolute end bound.
        assert_eq!(exact_subslice_len(8, 2, 5, false), Exact(3));
        assert_eq!(exact_subslice_len(4, 5, 0, true), Conflict);
        assert_eq!(exact_subslice_len(8, 5, 2, false), Conflict);
        assert_eq!(exact_subslice_len(8, 2, 9, false), Conflict);
    }

    #[test]
    fn side_table_candidates_must_be_structurally_unanimous() {
        let four = Expr::bitvec_const(4, POINTER_WIDTH);
        let eight = Expr::bitvec_const(8, POINTER_WIDTH);
        let mut candidate = None;

        assert_eq!(merge_unanimous_len_expr(&mut candidate, &four), Ok(()));
        assert_eq!(merge_unanimous_len_expr(&mut candidate, &four), Ok(()));
        assert_eq!(candidate, Some(four));
        assert_eq!(merge_unanimous_len_expr(&mut candidate, &eight), Err(()));
    }

    #[test]
    fn range_full_preserves_only_exact_source_authority() {
        use SliceLenEvidence::{Absent, Conflict, Exact};

        assert_eq!(range_full_slice_len_evidence(Exact(4)), Exact(4));
        assert_eq!(range_full_slice_len_evidence(Absent), Conflict);
        assert_eq!(range_full_slice_len_evidence(Conflict), Conflict);
    }
}

fn exact_array_len_from_ty(mut ty: Ty) -> SliceLenEvidence {
    // Index trait receivers routinely add one reference layer (`&&[T; N]`).
    // Peel a bounded chain rather than silently losing the array's type-level
    // authority after the first layer.
    for _ in 0..8 {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, const_len)) => {
                return const_len
                    .eval_target_usize()
                    .ok()
                    .map_or(SliceLenEvidence::Conflict, SliceLenEvidence::Exact);
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => ty = inner,
            _ => return SliceLenEvidence::Absent,
        }
    }
    // Exhausting the peel budget means the type was not classified. It is not
    // evidence that no array exists below the reference chain, so fail closed
    // rather than permitting a side table to revive length authority.
    SliceLenEvidence::Conflict
}

fn slice_carrier_evidence_from_ty(mut ty: Ty) -> SliceCarrierEvidence {
    for _ in 0..8 {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(_)) => return SliceCarrierEvidence::Carrier,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty = inner,
            // A raw pointer is not an identity-bearing reference chain. Its
            // pointee may still be a slice, but following whole-local reference
            // producers through it would invent provenance across unsafe code.
            TyKind::RigidTy(RigidTy::RawPtr(..)) => return SliceCarrierEvidence::NotCarrier,
            _ => return SliceCarrierEvidence::NotCarrier,
        }
    }
    SliceCarrierEvidence::Conflict
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate `Rvalue::Len(place)` to a CHC expression.
    ///
    /// Tries five strategies in order:
    /// 1. Compile-time array length for `[T; N]`
    /// 2. Unanimous MIR provenance through Unsize, copies, refs, and subslices
    /// 3. Unanimous range-call side metadata
    /// 4. Extract `fld_len` from Vec/Slice Datatype state variable
    /// 5. Fallback: fresh unconstrained symbolic usize (sound over-approximation)
    ///
    /// Part of #3920: extracted from `translate_rvalue_with_modified`.
    pub(in crate::codegen_ay::chc) fn translate_rvalue_len(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Part of #1888: Rvalue::Len returns usize.
        // For fixed-size arrays [T; N], use the compile-time constant length.
        // For slices, we would need fat pointer metadata (not yet supported).
        let ty = place.ty(self.body.locals()).ok();

        if let Some(ty) = &ty
            && let TyKind::RigidTy(RigidTy::Array(_, const_len)) = ty.kind()
            && let Some(len) = const_len.eval_target_usize().ok()
        {
            debug!(?place, len, "CHC: Rvalue::Len on array - compile-time length");
            return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
        }

        // Recover an exact length only when every MIR producer agrees. A
        // conflict is sticky: do not let a later, lossy side table or datatype
        // path revive one predecessor's length.
        match self.resolve_slice_len_evidence_for_place(place) {
            Ok(Some(len)) => {
                debug!(
                    ?place,
                    len, "CHC: Rvalue::Len on slice - recovered authenticated exact length"
                );
                return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
            }
            Err(()) => {
                warn!(
                    ?place,
                    "CHC Rvalue::Len has conflicting provenance - using fresh symbolic usize"
                );
                return Some(self.fresh_symbolic_len("rvalue_len_conflicting_provenance"));
            }
            Ok(None) => {}
        }

        // Try to recover length from call-registered subslice_len side table.
        // When MIR has `Len(*_x)` and `_x` was the destination of a Range-based
        // slice index call (`codegen_call_slice_range`), the subslice length
        // was registered in `ref_resolution.subslice_len[_x]`.
        // This handles the slice-of-slice pattern: `&array[2..5]` then `&slice1[1..2]`
        // where `_x` is the result of the Range index call, not a MIR Subslice projection.
        match self.try_resolve_len_from_call_subslice(place) {
            Ok(Some(len_expr)) => {
                debug!(
                    ?place,
                    "CHC: Rvalue::Len on slice - recovered unanimous call-registered subslice_len"
                );
                return Some(len_expr);
            }
            Err(()) => {
                warn!(
                    ?place,
                    "CHC Rvalue::Len has conflicting side-table provenance - using fresh symbolic usize"
                );
                return Some(self.fresh_symbolic_len("rvalue_len_conflicting_side_table"));
            }
            Ok(None) => {}
        }

        // Part of #3084: Try to extract fld_len from Vec/Slice Datatype.
        if let Some(len_expr) = self.try_resolve_len_from_datatype(place, modified_locals) {
            debug!(?place, "CHC: Rvalue::Len on Vec/Slice - extracted fld_len from Datatype");
            return Some(len_expr);
        }

        // Part of #3099: Fallback for slices and other dynamic-length
        // types. Return a fresh unconstrained symbolic bitvec of
        // POINTER_WIDTH (usize). This is a SOUND over-approximation:
        // the symbolic length is universally quantified over all
        // possible usize values, so any PROOF that holds under this
        // model also holds for the actual length. Reclassified from
        // chc_fallback (DEMOTED) to place_translation_drop
        // (SOUND_APPROXIMATION) — avoids false demotion and
        // eliminates the double-counting that occurred when returning
        // None triggered the self-loop handler's record_fallback().
        warn!(?place, "CHC Rvalue::Len fallback: fresh symbolic usize (sound over-approximation)");
        Some(self.fresh_symbolic_len("rvalue_len_fallback"))
    }

    fn fresh_symbolic_len(&mut self, reason: &'static str) -> Expr {
        self.record_sound_fallback_reason(reason);
        let len_name = chc_fresh_name("__len_nondet");
        declare_pending_var(len_name, ptr_sort())
    }

    /// Resolve a `Len` place without erasing the distinction between no
    /// evidence and contradictory evidence.
    ///
    /// `Ok(Some(n))` is the sole authority-bearing result. `Ok(None)` allows
    /// callers to try a disjoint representation (for example a Vec datatype).
    /// `Err(())` is a sticky conflict and callers must fail closed immediately.
    pub(in crate::codegen_ay::chc) fn resolve_slice_len_evidence_for_place(
        &self,
        place: &Place,
    ) -> Result<Option<u64>, ()> {
        if place.projection.len() != 1 || !matches!(place.projection[0], ProjectionElem::Deref) {
            return Ok(None);
        }
        let place_ty = place.ty(self.body.locals()).map_err(|_| ())?;
        if !matches!(place_ty.kind(), TyKind::RigidTy(RigidTy::Slice(_))) {
            // This resolver authenticates array-backed slices only. Keep Vec,
            // str, and other representation-specific lanes disjoint so their
            // dedicated metadata/datatype resolvers remain available.
            return Ok(None);
        }
        self.resolve_slice_len_evidence_for_local(place.local)
    }

    pub(in crate::codegen_ay::chc) fn resolve_slice_len_evidence_for_local(
        &self,
        local: usize,
    ) -> Result<Option<u64>, ()> {
        let mut visiting = HashSet::new();
        let mut steps = 0;
        match self.slice_len_evidence_for_local(local, &mut visiting, &mut steps) {
            SliceLenEvidence::Exact(length) => Ok(Some(length)),
            SliceLenEvidence::Absent => Ok(None),
            SliceLenEvidence::Conflict => {
                warn!(local, "CHC: conflicting slice-length provenance - refusing to guess");
                Err(())
            }
        }
    }

    /// Return the unique authenticated array length behind a slice-reference local.
    ///
    /// The walk joins every whole-local producer across every basic block:
    /// concrete array-to-slice `Unsize` casts, `Move`/`Copy` chains, reborrows,
    /// and subslices. It never returns the first match. Differing lengths, a
    /// provenance cycle, resource exhaustion, or an unresolved producer that
    /// competes with exact evidence poison the whole result. This is essential
    /// because selecting one predecessor's length under-approximates the CFG and
    /// can prove an assertion about the wrong cell.
    ///
    /// Returns `None` for both absent and conflicting evidence. Callers must fail
    /// closed on `None`; only [`SliceLenEvidence::Exact`] crosses this boundary.
    pub(in crate::codegen_ay::chc) fn try_resolve_slice_len_for_local(
        &self,
        local: usize,
    ) -> Option<u64> {
        self.resolve_slice_len_evidence_for_local(local).ok().flatten()
    }

    fn slice_len_evidence_for_local(
        &self,
        local: usize,
        visiting: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> SliceLenEvidence {
        if *steps >= MAX_SLICE_LEN_PROVENANCE_STEPS {
            return SliceLenEvidence::Conflict;
        }
        *steps += 1;
        if !visiting.insert(local) {
            return SliceLenEvidence::Conflict;
        }

        // An array (or pointer/reference to one) carries its length in its type;
        // no value-flow reconstruction is needed or allowed to weaken that fact.
        let declared = self
            .body
            .locals()
            .get(local)
            .map_or(SliceLenEvidence::Absent, |decl| exact_array_len_from_ty(decl.ty));
        if matches!(declared, SliceLenEvidence::Exact(_) | SliceLenEvidence::Conflict) {
            visiting.remove(&local);
            return declared;
        }

        let mut evidence = SliceLenEvidence::Absent;
        let mut saw_definition = false;
        let mut saw_unresolved_definition = false;
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                saw_definition = true;
                let producer = self.slice_len_evidence_from_rvalue(rhs, visiting, steps);
                if matches!(producer, SliceLenEvidence::Absent) {
                    saw_unresolved_definition = true;
                } else {
                    evidence = evidence.merge(producer);
                }
            }
        }

        // Call destinations are whole-local definitions too. Omitting them
        // lets one exact statement producer outrank an unknown call producer,
        // and lets RangeFull copy a stale path-insensitive side-table length
        // from a conflicting source into a singly-defined destination.
        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind
            else {
                continue;
            };
            if destination.local != local || !destination.projection.is_empty() {
                continue;
            }
            saw_definition = true;
            let producer = self.slice_len_evidence_from_call(func, args, visiting, steps);
            if matches!(producer, SliceLenEvidence::Absent) {
                saw_unresolved_definition = true;
            } else {
                evidence = evidence.merge(producer);
            }
        }

        // An unresolved predecessor is harmless when this whole resolver has
        // no evidence (a disjoint side-table lane may know the value), but it
        // must poison a competing exact candidate.
        evidence = finish_slice_len_evidence(evidence, saw_definition, saw_unresolved_definition);

        // `ref_targets` is a lossy map (several analysis passes may refine or
        // overwrite it), so it is never positive length authority. It can still
        // reject an exact MIR derivation when its independently resolved target
        // has a different exact length. Nonempty projections are deliberately
        // incomparable here: their length may differ from the base object.
        if let SliceLenEvidence::Exact(length) = evidence
            && let Some(target) = self.ref_resolution.ref_targets.get(&local)
            && target.projections.is_empty()
        {
            match self.slice_len_evidence_for_local(target.local, visiting, steps) {
                SliceLenEvidence::Exact(target_length) if target_length != length => {
                    evidence = SliceLenEvidence::Conflict;
                }
                SliceLenEvidence::Conflict => evidence = SliceLenEvidence::Conflict,
                SliceLenEvidence::Absent | SliceLenEvidence::Exact(_) => {}
            }
        }

        visiting.remove(&local);
        evidence
    }

    fn slice_len_evidence_from_call(
        &self,
        func: &Operand,
        args: &[Operand],
        visiting: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> SliceLenEvidence {
        // Every call is a whole-local definition. An unrecognized call must
        // poison this provenance lane; returning Absent would allow a lossy,
        // path-insensitive metadata table to recreate an exact length later.
        let Some(slice_arg) = self.authenticated_core_range_full_source(func, args) else {
            return SliceLenEvidence::Conflict;
        };

        let source = match slice_arg {
            Operand::Copy(source) | Operand::Move(source) if source.projection.is_empty() => {
                self.slice_len_evidence_for_local(source.local, visiting, steps)
            }
            _ => slice_arg
                .ty(self.body.locals())
                .ok()
                .map_or(SliceLenEvidence::Conflict, exact_array_len_from_ty),
        };
        range_full_slice_len_evidence(source)
    }

    fn slice_len_evidence_from_rvalue(
        &self,
        rhs: &Rvalue,
        visiting: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> SliceLenEvidence {
        match rhs {
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), source, _) => source
                .ty(self.body.locals())
                .ok()
                .map_or(SliceLenEvidence::Conflict, exact_array_len_from_ty),
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source))
                if source.projection.is_empty() =>
            {
                self.slice_len_evidence_for_local(source.local, visiting, steps)
            }
            Rvalue::CopyForDeref(source) if source.projection.is_empty() => {
                self.slice_len_evidence_for_local(source.local, visiting, steps)
            }
            Rvalue::Ref(_, _, source) | Rvalue::AddressOf(_, source) => {
                self.slice_len_evidence_from_place(source, visiting, steps)
            }
            // This may be a producer authenticated by a disjoint metadata
            // lane. It becomes a conflict if another predecessor yields an
            // exact array length; otherwise preserve `Absent` for that lane.
            _ => SliceLenEvidence::Absent,
        }
    }

    fn slice_len_evidence_from_place(
        &self,
        place: &Place,
        visiting: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> SliceLenEvidence {
        if place.projection.is_empty() {
            let Ok(place_ty) = place.ty(self.body.locals()) else {
                return SliceLenEvidence::Conflict;
            };
            let typed = exact_array_len_from_ty(place_ty);
            if !matches!(typed, SliceLenEvidence::Absent) {
                return typed;
            }
            // `Index::index` takes `&self`, so RangeFull on a slice often
            // reaches us through `_receiver = &_slice_ref`. The receiver's
            // type (`&&[T]`) has no numeric length, but its whole-local source
            // does; preserve that provenance rather than dropping to a stale
            // global metadata table.
            return match slice_carrier_evidence_from_ty(place_ty) {
                SliceCarrierEvidence::Carrier => {
                    self.slice_len_evidence_for_local(place.local, visiting, steps)
                }
                SliceCarrierEvidence::NotCarrier => SliceLenEvidence::Absent,
                SliceCarrierEvidence::Conflict => SliceLenEvidence::Conflict,
            };
        }

        if place.projection.len() == 1 && matches!(place.projection[0], ProjectionElem::Deref) {
            return self.slice_len_evidence_for_local(place.local, visiting, steps);
        }

        let mut subslice = None;
        for projection in &place.projection {
            match projection {
                ProjectionElem::Deref => {}
                ProjectionElem::Subslice { from, to, from_end } if subslice.is_none() => {
                    subslice = Some((*from, *to, *from_end));
                }
                _ => return SliceLenEvidence::Conflict,
            }
        }
        let Some((from, to, from_end)) = subslice else {
            return SliceLenEvidence::Conflict;
        };
        match self.slice_len_evidence_for_local(place.local, visiting, steps) {
            SliceLenEvidence::Exact(source_length) => {
                exact_subslice_len(source_length, from, to, from_end)
            }
            SliceLenEvidence::Absent => SliceLenEvidence::Absent,
            SliceLenEvidence::Conflict => SliceLenEvidence::Conflict,
        }
    }

    /// Recover subslice length from call-registered side table.
    ///
    /// When `codegen_call_slice_range` processes `&slice[start..end]`, it registers
    /// `subslice_len[dest_local] = end - start` in `ref_resolution.subslice_len`.
    /// When MIR has `Len(*_x)` and `_x` has a registered subslice_len, return it.
    /// Also follows ref_targets and Move/Copy chains.
    fn try_resolve_len_from_call_subslice(&self, place: &Place) -> Result<Option<Expr>, ()> {
        // Only handle Len(*_x) — one Deref projection.
        if place.projection.len() != 1 || !matches!(place.projection[0], ProjectionElem::Deref) {
            return Ok(None);
        }
        let local = place.local;

        let mut candidate: Option<Expr> = None;

        // Direct lookup.
        if let Some(len) = self.ref_resolution.subslice_len.get(&local) {
            merge_unanimous_len_expr(&mut candidate, len)?;
        }

        // Follow ref_targets: if `_y = &(*_x)`, look up _x's subslice_len.
        if let Some(referent) = self.ref_resolution.ref_targets.get(&local) {
            if referent.projections.is_empty() {
                if let Some(len) = self.ref_resolution.subslice_len.get(&referent.local) {
                    if self.local_has_multiple_whole_definitions(referent.local) {
                        return Err(());
                    }
                    merge_unanimous_len_expr(&mut candidate, len)?;
                }
            }
        }

        // Follow Move/Copy chain: if `_local = Move/Copy(_src)`, check _src.
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(
                    rustc_public::mir::Operand::Copy(src) | rustc_public::mir::Operand::Move(src),
                ) = rhs
                {
                    if src.projection.is_empty() {
                        if let Some(len) = self.ref_resolution.subslice_len.get(&src.local) {
                            if self.local_has_multiple_whole_definitions(src.local) {
                                return Err(());
                            }
                            merge_unanimous_len_expr(&mut candidate, len)?;
                        }
                    }
                }
            }
        }
        // A global side table is path-insensitive. More than one MIR producer
        // for a local with a candidate means its final HashMap value could be
        // whichever block happened to be visited last. With no candidate this
        // is merely a disjoint lane, not a conflict.
        if candidate.is_some() && self.local_has_multiple_whole_definitions(local) {
            return Err(());
        }
        Ok(candidate)
    }

    pub(in crate::codegen_ay::chc) fn local_has_multiple_whole_definitions(
        &self,
        local: usize,
    ) -> bool {
        let stmt_definition_count = self
            .body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(lhs, _)
                        if lhs.local == local && lhs.projection.is_empty()
                )
            })
            .take(2)
            .count();
        let call_definition_count = self
            .body
            .blocks
            .iter()
            .filter(|block| {
                matches!(
                    &block.terminator.kind,
                    TerminatorKind::Call { destination, .. }
                        if destination.local == local && destination.projection.is_empty()
                )
            })
            .take(2)
            .count();
        stmt_definition_count + call_definition_count > 1
    }

    /// Path-insensitive metadata may cross a local-to-local identity edge only
    /// when both endpoints have a single whole-local producer. Otherwise a
    /// `HashMap<Local, Expr>` can retain one CFG predecessor and revive it under
    /// a destination that merely looks unique.
    pub(in crate::codegen_ay::chc) fn path_insensitive_metadata_copy_is_unique(
        &self,
        source_local: usize,
        dest_local: usize,
    ) -> bool {
        !self.local_has_multiple_whole_definitions(source_local)
            && !self.local_has_multiple_whole_definitions(dest_local)
    }

    /// Extract `fld_len` from a Vec/Slice Datatype state variable for `Rvalue::Len`.
    ///
    /// Part of #3084: eliminates false fallback for `.len()` on Vec/Slice locals.
    ///
    /// Handles three patterns:
    /// 1. `Len(_x)` where `_x` is a direct Vec/Slice local
    /// 2. `Len(*_x)` where `_x` has a ref_target pointing to a Vec/Slice local
    /// 3. `Len(*_x)` where `_x` has a ref_target with field projections navigating
    ///    through a struct to reach a Vec/Slice field (e.g., `struct.items: Vec<T>`)
    fn try_resolve_len_from_datatype(
        &self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::CtorFieldExt;

        // Resolve the target local and any field projections from ref_targets.
        let (target_local, ref_projections) = if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
        {
            let ref_target = self.ref_resolution.ref_targets.get(&place.local)?;
            (ref_target.local, ref_target.projections.as_slice())
        } else if place.projection.is_empty() {
            (place.local, [].as_slice())
        } else {
            return None;
        };

        if self.flatten.flattened_tuple_locals.contains(&target_local) {
            return None;
        }

        let vec_idx = self.try_state_idx_for_local(target_local)?;
        let expr = if modified_locals.contains(&target_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&target_local) {
                env_expr.clone()
            } else {
                let (name, sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
                Expr::var(&**name, sort.clone())
            }
        } else {
            let (name, sort) = self.state_var_mgr.state_vars.get(vec_idx)?;
            Expr::var(&**name, sort.clone())
        };

        // Part of #3084: If ref_target had field projections (e.g., struct.field → Vec),
        // navigate through the struct Datatype to reach the Vec/Slice field.
        let field_expr = if !ref_projections.is_empty() {
            let field_projs =
                collect_field_projections(ref_projections, UnknownProjectionPolicy::Skip);
            if field_projs.is_empty() {
                return None;
            }
            Self::apply_field_selections(expr, &field_projs)?
        } else {
            expr
        };

        let sort = field_expr.sort();
        let dt_name = sort.datatype_name()?.to_owned();
        let dt = sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        if ctor.has_field("fld_len") {
            debug!(
                target_local,
                %dt_name,
                ref_proj_count = ref_projections.len(),
                "CHC: Rvalue::Len resolved fld_len from Datatype state variable"
            );
            Some(field_expr.field_select(&dt_name, "fld_len", ptr_sort()))
        } else {
            None
        }
    }
}

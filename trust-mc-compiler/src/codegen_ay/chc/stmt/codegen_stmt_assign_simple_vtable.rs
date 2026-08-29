// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VTable tracking for simple (non-projection) assignments.
//! Extracted from codegen_stmt_assign_simple.rs per #3952.
//!
//! Handles vtable discriminant capture, propagation through identity-like
//! rvalues, unsize coercion vtable recovery, and wrapper-deref vtable recovery.

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Operand, ProjectionElem, Rvalue, UnOp};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::stmt_accumulator::StmtAccumulator;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Apply vtable tracking for a simple assignment destination.
    ///
    /// Captures vtable discriminants from unsize coercions, identity-like
    /// rvalues, wrapper deref loads, and raw fat-pointer aggregates.
    ///
    /// Returns `true` when the destination's `__vtable_sv_N__out` was bound
    /// here. Every branch below binds that ONE variable, so a caller that
    /// binds it again in the same statement would emit a second equality on
    /// it — and if the two disagree the block constraints become UNSAT, which
    /// silently makes the whole harness unreachable rather than failing. See
    /// [`Self::apply_late_vtable_propagation`], which must honour this.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn apply_vtable_tracking(
        &mut self,
        rhs: &Rvalue,
        rhs_expr: &Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let constraints_before = acc.constraints.len();
        // Recover wrapper-dyn unsize vtables before generic capture.
        if let Some(vtable_constraint) = self.try_capture_unsize_coercion_vtable(rhs, local_idx) {
            acc.constraints.push(vtable_constraint);
        } else if let Some(vtable_constraint) =
            self.capture_vtable_discriminant(local_idx, rhs_expr)
        {
            acc.constraints.push(vtable_constraint);
        } else if let Some(src_local) = extract_vtable_source_local(rhs) {
            if let Some(vtable_constraint) =
                self.propagate_vtable_discriminant(src_local, local_idx)
            {
                acc.constraints.push(vtable_constraint);
            } else if let Some(vtable_constraint) =
                self.try_capture_wrapper_deref_vtable(rhs, local_idx)
            {
                acc.constraints.push(vtable_constraint);
            }
        }

        // Part of #3712 (dyn_ptr): a `std::ptr::metadata(trait_object)` UnOp
        // extracts DynMetadata — register the DESTINATION as carrying the
        // source trait-object's vtable identity, so the RawPtr-aggregate
        // propagate below (NonNull::from_raw_parts reconstruction) finds it
        // instead of dropping the vtable component.
        if let Rvalue::UnaryOp(UnOp::PtrMetadata, op) = rhs
            && let Operand::Copy(p) | Operand::Move(p) = op
            && let Some(vc) = self.propagate_vtable_discriminant(p.local, local_idx)
        {
            acc.constraints.push(vc);
        }

        // Part of #3712: Preserve dyn-vtable metadata for raw fat-pointer aggregates.
        if let Rvalue::Aggregate(AggregateKind::RawPtr(_, _), ops) = rhs
            && ops.len() > 1
            && let Ok(meta_ty) = ops[1].ty(self.body.locals())
            && !matches!(meta_ty.kind(), TyKind::RigidTy(RigidTy::Tuple(ref t)) if t.is_empty())
        {
            let propagated = match &ops[1] {
                Operand::Copy(p) | Operand::Move(p) => {
                    self.propagate_vtable_discriminant(p.local, local_idx)
                }
                _ => None,
            };
            if let Some(vc) = propagated {
                acc.constraints.push(vc);
            } else if let Some(id) =
                self.resolve_unique_wrapped_dyn_vtable_id(self.body.locals()[local_idx].ty)
            {
                if let Some(vc) = self.capture_known_vtable_discriminant(
                    local_idx,
                    Expr::bitvec_const(id as u128, POINTER_WIDTH),
                ) {
                    acc.constraints.push(vc);
                }
            }
        }

        acc.constraints.len() > constraints_before
    }

    /// Apply late vtable propagation through identity-like rvalues.
    ///
    /// Called after the main assignment constraint is emitted, to propagate
    /// vtable discriminants through Copy/Move/Ref/Cast chains. This is a
    /// FALLBACK for rvalues [`Self::apply_vtable_tracking`] could not resolve,
    /// so it is skipped outright when that pass already bound the
    /// destination's vtable state variable.
    ///
    /// Running it anyway is what a dyn->dyn coercion used to do: `_d = _s as
    /// &dyn Any` where `_s: &(dyn Any + Send)` captured the TARGET trait's
    /// vtable id from the concrete source type, then propagated `_s`'s
    /// SOURCE-trait id onto the same `__out` variable. The two ids differ, so
    /// the block asserted `1 == 0` and every path through the harness became
    /// infeasible — a vacuous "proof" that verified nothing. A source that
    /// carries no vtable state var (the common `&T -> &dyn T` unsize) never
    /// hit it, which is why only the dyn->dyn shape was affected.
    pub(in crate::codegen_ay::chc) fn apply_late_vtable_propagation(
        &mut self,
        rhs: &Rvalue,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
        already_bound: bool,
    ) {
        if already_bound {
            return;
        }
        if let Some(src_local) = extract_vtable_source_local(rhs) {
            if let Some(vtable_constraint) =
                self.propagate_vtable_discriminant(src_local, local_idx)
            {
                acc.constraints.push(vtable_constraint);
            }
        }
    }

    pub(in crate::codegen_ay::chc) fn try_capture_wrapper_deref_vtable(
        &mut self,
        rhs: &Rvalue,
        dst_local: usize,
    ) -> Option<Expr> {
        let deref_load = match rhs {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
                place.projection.first() == Some(&ProjectionElem::Deref)
            }
            Rvalue::CopyForDeref(place) => place.projection.first() == Some(&ProjectionElem::Deref),
            _ => false,
        };
        if !deref_load {
            return None;
        }

        let local_ty = self.body.locals()[dst_local].ty;
        let vtable_id = self.resolve_unique_wrapped_dyn_vtable_id(local_ty)?;
        self.capture_known_vtable_discriminant(
            dst_local,
            Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH),
        )
    }
}

/// Part of #3159: Extract source local from identity-like rvalues (Copy/Move,
/// Ref, CopyForDeref, AddressOf, Cast) for vtable discriminant propagation.
/// Handles projected places (e.g., `_123.0.0` → base local 123).
pub(in crate::codegen_ay::chc) fn extract_vtable_source_local(rvalue: &Rvalue) -> Option<usize> {
    match rvalue {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p.local),
        Rvalue::Ref(_, _, place) | Rvalue::CopyForDeref(place) => Some(place.local),
        Rvalue::AddressOf(_, place) => Some(place.local),
        Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => Some(p.local),
        _ => None,
    }
}

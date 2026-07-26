// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Collection shadow state propagation for simple (non-projection) assignments.
//! Extracted from codegen_stmt_assign_simple.rs per #3952.
//!
//! Handles propagation of collection ghost state (present, len, cap) through
//! Move/Copy assignments, struct field projections, ADT aggregates, and
//! Ref/AddressOf rvalues.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue};

use super::ChcCtx;
use super::stmt_accumulator::StmtAccumulator;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Propagate collection shadow state through a simple assignment.
    ///
    /// Covers Move/Copy (direct and projected), ADT Aggregate operands,
    /// and Ref/AddressOf collection references.
    pub(in crate::codegen_ay::chc) fn apply_collection_propagation(
        &mut self,
        rhs: &Rvalue,
        rhs_expr: &Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        // Part of #3057: Propagate collection shadow state (present, len, cap)
        // for Move/Copy assignments.
        if let Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place)) = rhs {
            if src_place.projection.is_empty() {
                let src_local: usize = src_place.local;
                self.propagate_collection_shadow_state(src_local, local_idx, acc.constraints);
            } else {
                // Part of #3284: Propagate collection ghost state through
                // struct field projections.
                let has_deref =
                    src_place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
                let (resolved_src_local, resolved_field_idx) = if has_deref {
                    if let Some(rt) = self.ref_resolution.ref_targets.get(&local_idx).cloned() {
                        let field_idx = rt.projections.iter().find_map(|p| {
                            if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                        });
                        (rt.local, field_idx)
                    } else {
                        let resolved_local = self
                            .ref_resolution
                            .ref_targets
                            .get(&src_place.local)
                            .map_or(src_place.local, |rt| rt.local);
                        let field_idx = src_place.projection.iter().find_map(|p| {
                            if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                        });
                        (resolved_local, field_idx)
                    }
                } else {
                    let field_idx = src_place.projection.iter().find_map(|p| {
                        if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                    });
                    (src_place.local, field_idx)
                };

                if let Some(field_idx) = resolved_field_idx {
                    self.propagate_collection_ghost_through_projection(
                        local_idx,
                        rhs_expr,
                        resolved_src_local,
                        field_idx,
                        acc.modified,
                        acc.constraints,
                    );
                }
            }
        }

        // Part of #3348: Propagate collection presence/len/cap aliases from
        // ADT Aggregate operands.
        if let Rvalue::Aggregate(rustc_public::mir::AggregateKind::Adt(_, _, _, _, _), operands) =
            rhs
        {
            self.propagate_collection_presence_from_aggregate(local_idx, operands);
        }

        // Part of #3284: For Ref/AddressOf producing a &Vec (or similar
        // collection reference) from a field inside a flattened struct,
        // propagate ghost vars using ref_targets resolution.
        if matches!(rhs, Rvalue::Ref(..) | Rvalue::AddressOf(..)) {
            if self.collections.len_state.get_len_var(local_idx).is_some() {
                if let Some(rt) = self.ref_resolution.ref_targets.get(&local_idx).cloned() {
                    let field_idx = rt.projections.iter().find_map(|p| {
                        if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                    });
                    if let Some(field_idx) = field_idx {
                        self.propagate_collection_ghost_through_projection(
                            local_idx,
                            rhs_expr,
                            rt.local,
                            field_idx,
                            acc.modified,
                            acc.constraints,
                        );
                    }
                }
            }
        }
    }
}

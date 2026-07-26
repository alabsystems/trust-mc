// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tuple usage analysis for determining flattening eligibility.
//!
//! This module analyzes MIR to classify tuple-typed locals as either:
//! - **Field-only**: Only accessed via field projections, tuple copies, or tuple aggregates.
//!   These can be safely flattened to per-field SSA variables.
//! - **Whole-use**: Require full tuple values (passed to functions, compared as whole, etc.).
//!   These need datatype encoding or reification.
//!
//! # Usage
//! ```text
//! let analysis = TupleUsageAnalysis::run(&body);
//! if analysis.is_field_only(local) {
//!     // Safe to flatten this tuple
//! }
//! ```
//!
//! # Implementation Notes
//! The analysis is conservative: if in doubt, a tuple is marked as whole-use.
//! This ensures soundness - flattening a whole-use tuple would break semantics.
//!
//! Related: #414

use rustc_public::mir::{
    AggregateKind, Body, Local, MirVisitor, Operand, Place, ProjectionElem, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, visit::Location,
};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

/// Result of tuple usage analysis for a function body.
#[derive(Debug, Default)]
pub(crate) struct TupleUsageAnalysis {
    /// Tuple-typed locals that require whole-tuple access.
    /// These need datatype encoding - they can't be flattened.
    ///
    /// Note: We previously tracked `field_only_tuples` separately, but #1582 changed
    /// the semantics to be permissive for inlined closure locals. Now we only track
    /// tuples that MUST NOT be flattened (whole-use), and allow flattening for all others.
    whole_use_tuples: HashSet<Local>,
}

impl TupleUsageAnalysis {
    /// Run tuple usage analysis on a function body.
    ///
    /// Returns an analysis result that can be queried for each local.
    pub(crate) fn run(body: &Body) -> Self {
        let mut visitor = TupleUsageVisitor::new(body);
        visitor.visit_body(body);
        visitor.into_result()
    }

    /// Check if a local is a tuple that can be flattened (field-only access).
    ///
    /// #1582: For locals not in the analysis (e.g., from inlined closures), default to
    /// allowing flattening. We only reject if we have evidence the tuple is used as a whole.
    /// This enables tuple argument destructuring for inlined closures.
    pub(crate) fn is_field_only(&self, local: Local) -> bool {
        // If we KNOW it's used as a whole tuple, don't flatten
        if self.whole_use_tuples.contains(&local) {
            return false;
        }
        // Unknown locals (not in whole_use set) are allowed to be flattened.
        // This includes inlined closure locals not in the original analysis.
        true
    }
}

/// MIR visitor that collects tuple usage information.
struct TupleUsageVisitor<'a> {
    /// Locals that are tuple-typed.
    tuple_locals: HashSet<Local>,
    /// Locals that have been used in a "whole-tuple" manner.
    whole_use: HashSet<Local>,
    /// Body for operand type inspection (needed for closure call detection).
    body: &'a Body,
}

impl<'a> TupleUsageVisitor<'a> {
    fn new(body: &'a Body) -> Self {
        // Pre-populate tuple_locals by scanning local declarations.
        let tuple_locals: HashSet<Local> = body
            .locals()
            .iter()
            .enumerate()
            .filter_map(|(idx, local_decl)| {
                let ty = local_decl.ty;
                if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_))) {
                    Some(Local::from(idx))
                } else {
                    None
                }
            })
            .collect();

        Self { tuple_locals, whole_use: HashSet::new(), body }
    }

    fn into_result(self) -> TupleUsageAnalysis {
        // #1582: We only track whole-use tuples now. Any local not in this set
        // can be flattened (including inlined closure locals not in the analysis).
        TupleUsageAnalysis { whole_use_tuples: self.whole_use }
    }

    /// Mark a local as having whole-tuple usage.
    fn mark_whole_use(&mut self, local: Local) {
        if self.tuple_locals.contains(&local) {
            self.whole_use.insert(local);
        }
    }

    /// Analyze a place to determine if it's a field-only or whole-use access.
    fn analyze_place(&mut self, place: &Place) {
        let local = place.local;
        if !self.tuple_locals.contains(&local) {
            return;
        }

        // Check projections: if first projection is Field, it's a field access (safe to flatten).
        // If empty projections or first is Deref/Index, it's a whole-tuple use.
        if place.projection.is_empty() {
            // Bare tuple reference - could be whole-use depending on context.
            // Caller should determine based on operation type.
        } else if matches!(place.projection.first(), Some(ProjectionElem::Field(..))) {
            // Field access - safe for flattening, no action needed
        } else {
            // Non-field first projection (e.g., Deref) on a tuple = whole use
            self.mark_whole_use(local);
        }
    }

    /// Check if an operand uses a tuple as a whole value.
    fn check_operand_whole_use(&mut self, operand: &Operand) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let local = place.local;
                if self.tuple_locals.contains(&local) {
                    // If the place has no projection or non-field first projection,
                    // this is using the whole tuple.
                    if place.projection.is_empty() {
                        // Bare Copy/Move of tuple - check if used as whole or in tuple copy
                        // For now, be conservative and mark as whole-use.
                        // The tuple copy pattern is handled specially in codegen.
                        self.mark_whole_use(local);
                    } else if !matches!(place.projection.first(), Some(ProjectionElem::Field(..))) {
                        self.mark_whole_use(local);
                    }
                }
            }
            Operand::Constant(_) => {}
        }
    }

    fn operand_ty(&self, operand: &Operand) -> Option<rustc_public::ty::Ty> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => place.ty(self.body.locals()).ok(),
            Operand::Constant(c) => Some(c.const_.ty()),
        }
    }

    fn is_closure_operand(&self, operand: &Operand) -> bool {
        let Some(ty) = self.operand_ty(operand) else {
            return false;
        };
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
                matches!(inner.kind(), TyKind::RigidTy(RigidTy::Closure(..)))
            }
            _ => false, // external enum: TyKind
        }
    }

    fn is_tuple_operand(&self, operand: &Operand) -> bool {
        let Some(ty) = self.operand_ty(operand) else {
            return false;
        };
        matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_)))
    }
}

impl MirVisitor for TupleUsageVisitor<'_> {
    fn visit_statement(&mut self, statement: &Statement, location: Location) {
        match &statement.kind {
            StatementKind::Assign(place, rvalue) => {
                // Check LHS
                self.analyze_place(place);

                // Check RHS
                match rvalue {
                    Rvalue::Use(operand) => {
                        // Copy/Move of a place - this is the tuple copy pattern.
                        // Don't mark as whole-use if it's a tuple-to-tuple copy, even when the
                        // destination is behind a deref (rust-call argument shims).
                        if let Operand::Copy(src) | Operand::Move(src) = operand {
                            let lhs_is_tuple =
                                place.ty(self.body.locals()).ok().is_some_and(|ty| {
                                    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_)))
                                });
                            let rhs_is_tuple = src.ty(self.body.locals()).ok().is_some_and(|ty| {
                                matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_)))
                            });

                            if lhs_is_tuple && rhs_is_tuple && src.projection.is_empty() {
                                // Tuple-to-tuple copy: treat as field-only usage.
                                // No action needed - we only track whole-use tuples.
                                return;
                            }
                        }
                        self.check_operand_whole_use(operand);
                    }
                    Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                        // Tuple aggregate construction - treat assignment as field-only access.
                        // Also inspect operands to catch whole-tuple uses as elements.
                        // No action needed for place.local - we only track whole-use tuples.
                        for operand in operands {
                            self.check_operand_whole_use(operand);
                        }
                    }
                    Rvalue::Aggregate(_, _) => {
                        self.super_statement(statement, location);
                    }
                    Rvalue::Ref(_, _, referenced_place)
                    | Rvalue::AddressOf(_, referenced_place) => {
                        // Taking reference/pointer to a tuple - if bare, it's whole-use
                        let local = referenced_place.local;
                        if self.tuple_locals.contains(&local)
                            && referenced_place.projection.is_empty()
                        {
                            self.mark_whole_use(local);
                        }
                    }
                    _ => {
                        // external enum: Rvalue
                        // Other rvalues: check operands
                        self.super_statement(statement, location);
                    }
                }
            }
            _ => {
                // external enum: StatementKind
                self.super_statement(statement, location);
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator, location: Location) {
        if let TerminatorKind::Call { args, .. } = &terminator.kind {
            // Function arguments: tuples passed as whole are whole-use.
            // Exception: rust-call closure ABI passes (closure, args_tuple). The args tuple
            // should be treated as field-only to enable tuple flattening for inlined closures.
            let is_closure_call = args.len() >= 2
                && self.is_closure_operand(&args[0])
                && self.is_tuple_operand(&args[1]);
            for (idx, arg) in args.iter().enumerate() {
                if is_closure_call && idx == 1 {
                    continue;
                }
                self.check_operand_whole_use(arg);
            }
        }
        self.super_terminator(terminator, location);
    }
}

#[cfg(test)]
mod tests {
    use super::TupleUsageAnalysis;
    use rustc_public::mir::Local;
    use std::collections::HashSet;

    /// Helper: build a `TupleUsageAnalysis` with specific whole-use locals.
    fn analysis_with_whole_use(locals: &[usize]) -> TupleUsageAnalysis {
        let whole_use_tuples: HashSet<Local> = locals.iter().map(|&i| Local::from(i)).collect();
        TupleUsageAnalysis { whole_use_tuples }
    }

    #[test]
    fn test_default_analysis_allows_all_flattening() {
        let analysis = TupleUsageAnalysis::default();
        // Unknown locals default to allowing flattening (per #1582 semantics)
        assert!(analysis.is_field_only(Local::from(0usize)));
        assert!(analysis.is_field_only(Local::from(5usize)));
        assert!(analysis.is_field_only(Local::from(100usize)));
    }

    #[test]
    fn test_whole_use_prevents_flattening() {
        let analysis = analysis_with_whole_use(&[2, 5]);
        assert!(!analysis.is_field_only(Local::from(2usize)));
        assert!(!analysis.is_field_only(Local::from(5usize)));
    }

    #[test]
    fn test_non_whole_use_locals_still_flattenable() {
        let analysis = analysis_with_whole_use(&[3]);
        // Local 3 is whole-use, but 0 and 7 are not
        assert!(analysis.is_field_only(Local::from(0usize)));
        assert!(!analysis.is_field_only(Local::from(3usize)));
        assert!(analysis.is_field_only(Local::from(7usize)));
    }

    #[test]
    fn test_empty_whole_use_set() {
        let analysis = analysis_with_whole_use(&[]);
        assert!(analysis.is_field_only(Local::from(0usize)));
        assert!(analysis.is_field_only(Local::from(1usize)));
    }
}

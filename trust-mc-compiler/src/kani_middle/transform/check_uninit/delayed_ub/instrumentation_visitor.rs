// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Visitor that collects all instructions relevant to uninitialized memory access caused by delayed
//! UB. In practice, that means collecting all instructions where the place is featured.

use crate::kani_middle::{
    points_to::{MemLoc, PointsToGraph},
    transform::{
        body::{InsertPosition, MutableBody, SourceInstruction},
        check_uninit::{
            TargetFinder,
            relevant_instruction::{InitRelevantInstruction, MemoryInitOp},
        },
    },
};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{
    MirVisitor, Operand, Place, Rvalue, Statement, Terminator,
    mono::Instance,
    visit::{Location, PlaceContext},
};
use std::collections::HashSet;

pub(crate) struct InstrumentationVisitor<'a, 'tcx> {
    /// All target instructions in the body.
    targets: Vec<InitRelevantInstruction>,
    /// Current analysis target, eventually needs to be added to a list of all targets.
    current_target: InitRelevantInstruction,
    /// Aliasing analysis data.
    points_to: &'a PointsToGraph<'tcx>,
    /// The list of places we should be looking for, ignoring others
    analysis_targets: &'a HashSet<MemLoc<'tcx>>,
    /// Cached transitive ancestor closure of analysis_targets (#1062)
    /// Pre-computed once at visitor creation to avoid O(depth²) per-place checks.
    target_ancestor_closure: HashSet<MemLoc<'tcx>>,
    current_instance: Instance,
    tcx: TyCtxt<'tcx>,
}

impl TargetFinder for InstrumentationVisitor<'_, '_> {
    fn find_all(mut self, body: &MutableBody) -> Vec<InitRelevantInstruction> {
        for (bb_idx, bb) in body.blocks().iter().enumerate() {
            self.current_target = InitRelevantInstruction {
                source: SourceInstruction::Statement { idx: 0, bb: bb_idx },
                before_instruction: vec![],
                after_instruction: vec![],
            };
            self.visit_basic_block(bb);
        }
        self.targets
    }
}

impl<'a, 'tcx> InstrumentationVisitor<'a, 'tcx> {
    pub(crate) fn new(
        points_to: &'a PointsToGraph<'tcx>,
        analysis_targets: &'a HashSet<MemLoc<'tcx>>,
        current_instance: Instance,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        // Pre-compute transitive ancestor closure for analysis_targets (#1062)
        // This avoids O(depth²) per-place checks by computing once upfront.
        let target_ancestor_closure = Self::compute_ancestor_closure(points_to, analysis_targets);

        Self {
            targets: vec![],
            current_target: InitRelevantInstruction {
                source: SourceInstruction::Statement { idx: 0, bb: 0 },
                before_instruction: vec![],
                after_instruction: vec![],
            },
            points_to,
            analysis_targets,
            target_ancestor_closure,
            current_instance,
            tcx,
        }
    }

    /// Compute the transitive closure of ancestors for a set of nodes.
    /// Returns all nodes that are direct or indirect ancestors of the input set.
    fn compute_ancestor_closure(
        points_to: &PointsToGraph<'tcx>,
        initial: &HashSet<MemLoc<'tcx>>,
    ) -> HashSet<MemLoc<'tcx>> {
        let mut closure = initial.clone();
        let mut frontier = initial.clone();

        while !frontier.is_empty() {
            let ancestors = points_to.ancestors(&frontier);
            // Only keep ancestors not already in closure (avoids infinite loops)
            frontier = ancestors.difference(&closure).copied().collect();
            closure.extend(&frontier);
        }

        closure
    }

    /// Check if any node in `nodes` or their ancestors is in `target_closure`.
    /// This is O(depth) instead of O(depth²) since we only expand one side.
    fn has_common_ancestor_with_closure(
        points_to: &PointsToGraph<'tcx>,
        nodes: &HashSet<MemLoc<'tcx>>,
        target_closure: &HashSet<MemLoc<'tcx>>,
    ) -> bool {
        // First check if any node directly intersects
        if nodes.intersection(target_closure).next().is_some() {
            return true;
        }

        // Then check ancestors level by level
        let mut frontier = nodes.clone();
        let mut visited = nodes.clone();

        while !frontier.is_empty() {
            let ancestors = points_to.ancestors(&frontier);
            // Check for intersection with target closure
            if ancestors.intersection(target_closure).next().is_some() {
                return true;
            }
            // Only expand to unvisited ancestors
            frontier = ancestors.difference(&visited).copied().collect();
            visited.extend(&frontier);
        }

        false
    }

    fn push_target(&mut self, source_op: MemoryInitOp) {
        self.current_target.push_operation(source_op);
    }
}

impl MirVisitor for InstrumentationVisitor<'_, '_> {
    fn visit_statement(&mut self, stmt: &Statement, location: Location) {
        self.super_statement(stmt, location);
        // Switch to the next statement.
        if let SourceInstruction::Statement { idx, bb } = self.current_target.source {
            self.targets.push(self.current_target.clone());
            self.current_target = InitRelevantInstruction {
                source: SourceInstruction::Statement { idx: idx + 1, bb },
                after_instruction: vec![],
                before_instruction: vec![],
            };
        } else {
            unreachable!(
                "current_target.source must be SourceInstruction::Statement during visit_statement"
            )
        }
    }

    fn visit_terminator(&mut self, term: &Terminator, location: Location) {
        if let SourceInstruction::Statement { bb, .. } = self.current_target.source {
            // We don't have to push the previous target, since it already happened in the statement
            // handling code.
            self.current_target = InitRelevantInstruction {
                source: SourceInstruction::Terminator { bb },
                after_instruction: vec![],
                before_instruction: vec![],
            };
        } else {
            unreachable!(
                "current_target.source must be SourceInstruction::Statement at start of visit_terminator"
            )
        }
        self.super_terminator(term, location);
        // Push the current target from the terminator onto the list.
        self.targets.push(self.current_target.clone());
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue, location: Location) {
        match rvalue {
            Rvalue::AddressOf(..) | Rvalue::Ref(..) => {
                // These operations are always legitimate for us.
            }
            _ => self.super_rvalue(rvalue, location), // external enum: Rvalue
        }
    }

    fn visit_place(&mut self, place: &Place, ptx: PlaceContext, location: Location) {
        // In order to check whether we should get-instrument the place, see if it resolves to the
        // analysis target.
        let needs_get = {
            self.points_to
                .resolve_place_stable(place.clone(), self.current_instance, self.tcx)
                .intersection(self.analysis_targets)
                .next()
                .is_some()
        };

        // In order to check whether we should set-instrument the place, we need to figure out if
        // the place has a common ancestor of the same level with the target.
        //
        // This is needed because instrumenting the place only if it resolves to the target could give
        // false positives in presence of some aliasing relations.
        //
        // Here is a simple example:
        // ```
        // fn foo(val_1: u32, val_2: u32, flag: bool) {
        //   let reference = if flag {
        //     &val_1
        //   } else {
        //     &val_2
        //   };
        //   let _ = *reference;
        // }
        // ```
        // It yields the following aliasing graph:
        //
        // `val_1 <-- reference --> val_2`
        //
        // If `val_1` is a legitimate instrumentation target, we would get-instrument an instruction
        // that reads from `*reference`, but that could mean that `val_2` is checked, too. Hence,
        // if we don't set-instrument `val_2` we will get a false-positive.
        //
        // See `tests/expected/uninit/delayed-ub-overapprox.rs` for a more specific example.
        //
        // Optimization (#1062): Use pre-computed target_ancestor_closure instead of
        // expanding both sides in parallel. This reduces O(depth²) to O(depth) per place.
        let needs_set = {
            let place_nodes =
                self.points_to.resolve_place_stable(place.clone(), self.current_instance, self.tcx);

            // Check if any node in place's ancestor closure intersects with target's closure
            Self::has_common_ancestor_with_closure(
                self.points_to,
                &place_nodes,
                &self.target_ancestor_closure,
            )
        };

        // If we are mutating the place, initialize it.
        if ptx.is_mutating() && needs_set {
            self.push_target(MemoryInitOp::SetRef {
                operand: Operand::Copy(place.clone()),
                value: true,
                position: InsertPosition::After,
            });
        } else if !ptx.is_mutating() && needs_get {
            // Otherwise, check its initialization.
            self.push_target(MemoryInitOp::CheckRef { operand: Operand::Copy(place.clone()) });
        }
        self.super_place(place, ptx, location);
    }
}

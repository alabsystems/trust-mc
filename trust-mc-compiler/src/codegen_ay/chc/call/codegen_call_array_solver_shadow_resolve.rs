// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Receiver resolution for `ArraySolver` shadow dispatch.
//!
//! Resolves the receiver local from method call arguments by following
//! reference chains through the MIR. Split from the main shadow dispatch
//! file for size compliance.

use rustc_public::mir::Operand;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve the receiver local for an ArraySolver method call.
    pub(in crate::codegen_ay::chc::call) fn resolve_array_solver_receiver(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<usize> {
        let arg0 = dcx.args.first()?;
        let local = match arg0 {
            Operand::Copy(p) | Operand::Move(p) => p.local,
            _ => return None,
        };
        // The arg may be a reference — check if the local itself is an ArraySolver.
        if self.collections.array_solver_aux.contains_key(&local) {
            return Some(local);
        }
        // Follow ref resolution to find the underlying local.
        if let Some(target) = self.ref_resolution.ref_targets.get(&local) {
            if self.collections.array_solver_aux.contains_key(&target.local) {
                return Some(target.local);
            }
        }
        // Walk ref chains through the MIR.
        self.resolve_ref_chain_for_array_solver(local)
            .filter(|l| self.collections.array_solver_aux.contains_key(l))
    }

    /// Resolve the flattened ArraySolver local for visible-state constraints.
    ///
    /// Multiple MIR locals may have `ArraySolver` type (original call dest,
    /// move targets, copies), all aliased to the same shadow aux state.
    /// But only ONE of them is in `flattened_tuple_locals` and has its
    /// struct fields expanded into individual state variables. Visible-state
    /// identity constraints must target that local; using a non-flattened
    /// alias produces only 1-2 identity constraints instead of 25.
    /// Part of #4050.
    pub(in crate::codegen_ay::chc) fn resolve_flattened_array_solver_local(
        &self,
        receiver_local: usize,
    ) -> usize {
        if self.flatten.flattened_tuple_locals.contains(&receiver_local) {
            return receiver_local;
        }
        // Prefer the receiver's own alias chain before scanning the whole aux map.
        // The dispatcher aliases ArraySolver shadow state across move/copy locals,
        // but only the original owner local reliably carries the visible flattened
        // field slots. Picking an arbitrary flattened aux entry can bind visible
        // updates to the wrong ArraySolver instance.
        if let Some(source_local) = self.resolve_ref_chain_for_array_solver(receiver_local)
            && self.flatten.flattened_tuple_locals.contains(&source_local)
        {
            return source_local;
        }
        if let Some(target) = self.ref_resolution.ref_targets.get(&receiver_local)
            && self.flatten.flattened_tuple_locals.contains(&target.local)
        {
            return target.local;
        }
        // Find the ArraySolver local that IS flattened.
        for &local in self.collections.array_solver_aux.keys() {
            if self.flatten.flattened_tuple_locals.contains(&local) {
                return local;
            }
        }
        // Fallback: return the receiver as-is.
        receiver_local
    }

    /// Walk Copy/Move/Ref chains to find the ultimate source local.
    pub(in crate::codegen_ay::chc) fn resolve_ref_chain_for_array_solver(
        &self,
        start: usize,
    ) -> Option<usize> {
        let mut current = start;
        for _ in 0..5 {
            let mut found = false;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let rustc_public::mir::StatementKind::Assign(place, rvalue) = &stmt.kind else {
                        continue;
                    };
                    if place.local != current || !place.projection.is_empty() {
                        continue;
                    }
                    match rvalue {
                        rustc_public::mir::Rvalue::Ref(_, _, target) => {
                            current = target.local;
                            found = true;
                        }
                        rustc_public::mir::Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if p.projection.is_empty() =>
                        {
                            current = p.local;
                            found = true;
                        }
                        _ => {}
                    }
                    if found {
                        break;
                    }
                }
                if found {
                    break;
                }
            }
            if !found {
                break;
            }
        }
        if current != start { Some(current) } else { None }
    }
}

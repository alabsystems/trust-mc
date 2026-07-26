// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Block statement encoding for CHC.
//!
//! Split per #2036, #2147, #2226. Sibling modules handle sub-concerns:
//! - codegen_stmt_copy: CopyNonOverlapping intrinsic + sort coercion helpers
//! - codegen_stmt_flatten: flattened tuple/enum local assignment helpers (#2226)
//! - codegen_stmt_rvalue: rvalue dispatch, pointer offset, ref/addressof
//! - codegen_stmt_store: Deref/Index/ref_target store helpers
//! - codegen_stmt_assign_projection: projection assignment dispatch (#600, #1100, #1739, #1957, #2214)
//! - codegen_stmt_assign_simple: simple (non-projection) assignment (#3269)
//! - codegen_stmt_projection: field projection helpers
//! - codegen_stmt_aggregate: aggregate construction
//! - codegen_stmt_arithmetic: arithmetic, cast, comparison ops
//! - codegen_stmt_mirror: memory mirroring + collection propagation helpers (#3199)
//!
//! Part of #2306: include!() to proper module migration.

use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::mir::StatementKind;
use tracing::{debug, warn};

use super::codegen_ctx::diagnostics::CellCounter;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, chc_debug_enabled};

// Sub-module for SetDiscriminant encoding (Part of #3743).
mod codegen_stmt_set_discriminant;

// Sub-module for arithmetic safety check conditions (shift distance, div-by-zero,
// signed div overflow), extracted to stay under 500-line limit. Part of #3363.
// Visibility widened to `chc` so the SIMD div/rem lane checks can reuse the
// same predicates as the scalar path.
pub(in crate::codegen_ay::chc) mod codegen_stmt_safety_checks;

// Sub-module for ref metadata propagation and flattened-local encoding. Part of #4206.
mod codegen_stmt_assign_helpers;

// Sub-module for failed rvalue handling, safety checks, alloc-id propagation,
// promoted-const seeding. Part of #4206.
mod codegen_stmt_fallback;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // ============================================================
    // Statement Encoding (Part of #648)
    // ============================================================

    /// Encodes statements in a basic block to constraints.
    ///
    /// Returns (constraints, output_args, modified_locals, safety_checks) where:
    /// - constraints: list of equality constraints from assignments
    /// - output_args: state arguments for successor relations
    /// - modified_locals: set of local indices modified in this block (#656)
    /// - safety_checks: memory safety checks that must hold (emit error on violation)
    pub(in crate::codegen_ay::chc) fn encode_block_statements(
        &mut self,
        bb_idx: usize,
    ) -> (Vec<Expr>, Vec<Expr>, HashSet<usize>, Vec<Expr>) {
        let mut constraints = Vec::new();
        let mut modified: HashSet<usize> = HashSet::new();
        let mut safety_checks = Vec::new();

        // Fix #2055: Track the constraint index for each local's most recent assignment.
        // When a local is assigned multiple times within a single block, previous constraints
        // on its __out variable must be replaced with `true` to avoid contradictory conjuncts
        // (e.g., `_1__out == 0 AND _1__out == 1` is UNSAT, making the block unreachable).
        let mut last_constraint_for_local: HashMap<usize, usize> =
            HashMap::with_capacity(self.body.locals().len());

        // Part of #3436: Track current block for per-block read tracking.
        self.current_encode_bb = bb_idx;

        // Reset memory array modification tracking for new block (#905)
        self.heap_state.reset_modified_arrays();
        self.heap_state.reset_pending_checks();
        // Initialize dead-locals set from block-entry dataflow state.
        // Done before clear_block so the dead set can guide env retention (#3474).
        self.liveness.dead_locals =
            self.liveness.dead_locals_at_entry.get(bb_idx).cloned().unwrap_or_default();
        // Reset per-block encoding state (signedness, expr env, field env, modified indices).
        // Part of #3474: pass dead set so flattened_field_env retains entries for dead locals.
        self.encode.clear_block(&self.liveness.dead_locals);
        // Reset collection length modification tracking for the block (#1949).
        self.collections.len_state.clear_modified();
        if chc_debug_enabled() && !self.liveness.dead_locals.is_empty() {
            debug!("bb{} dead_locals_in={:?}", bb_idx, self.liveness.dead_locals);
        }

        self.seed_promoted_const_store_chains_for_bb0(bb_idx);

        let bb_data = if let Some(bb) = self.body.blocks.get(bb_idx) {
            bb
        } else {
            // No block found, return input state unchanged
            let output_args: Vec<Expr> = self
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(&**name, sort.clone()))
                .collect();
            return (constraints, output_args, HashSet::new(), Vec::new());
        };
        let aggregate_field_sources = self.collect_aggregate_field_sources();
        for stmt in &bb_data.statements {
            // Track locals entering/leaving scope for dead-object detection.
            if let StatementKind::StorageLive(local) = &stmt.kind {
                let local_idx: usize = *local;
                self.liveness.dead_locals.remove(&local_idx);
                debug!(
                    "bb{} StorageLive(_{}) dead_locals={:?}",
                    bb_idx, local_idx, self.liveness.dead_locals
                );
                debug!(local_idx, bb_idx, "CHC: StorageLive — marked local as alive");
                continue;
            }

            if let StatementKind::StorageDead(local) = &stmt.kind {
                let local_idx: usize = *local;
                self.liveness.dead_locals.insert(local_idx);
                debug!(
                    "bb{} StorageDead(_{}) dead_locals={:?}",
                    bb_idx, local_idx, self.liveness.dead_locals
                );
                debug!(local_idx, bb_idx, "CHC: StorageDead — marked local as dead (#762)");
                continue;
            }
            if let StatementKind::Intrinsic(intrinsic) = &stmt.kind {
                match intrinsic {
                    rustc_public::mir::NonDivergingIntrinsic::Assume(op) => {
                        // Preserve intrinsic assume semantics for MIR that still uses
                        // StatementKind::Intrinsic(Assume) instead of kani::assume call.
                        // Part of #2759: track dropped assumes via counter.
                        let cond = self.translate_operand_with_modified(op, &modified);
                        let bool_cond = cond.and_then(|c| self.to_bool_expr(c, bb_idx));
                        if let Some(bc) = bool_cond {
                            constraints.push(bc);
                        } else {
                            // Part of #3099: dropping assume(P) is a sound over-approximation.
                            let dropped = self.diagnostics.assume_dropped_transition.inc_get();
                            warn!(
                                bb_idx,
                                dropped_assume_semantics = dropped,
                                "Intrinsic::Assume guard dropped — sound over-approximation"
                            );
                            self.record_sound_fallback_reason("assume_guard_dropped");
                        }
                    }
                    rustc_public::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                        // Part of #2759: track unresolved CopyNonOverlapping via record_fallback.
                        let handled = {
                            let mut acc = StmtAccumulator::new(
                                &mut modified,
                                &mut constraints,
                                &mut last_constraint_for_local,
                            );
                            self.try_encode_copy_nonoverlapping_intrinsic(
                                copy, bb_idx, &mut acc, false,
                            )
                        };
                        if !handled {
                            // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                            // CopyNonOverlapping has memory array side effects;
                            // dropping it leaves destination memory at identity
                            // (old values intact), not nondeterministic.
                            warn!(
                                bb_idx,
                                "CopyNonOverlapping destination unresolved — statement dropped (DEMOTED)"
                            );
                            self.record_fallback();
                        }
                    }
                }
                continue;
            }
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind {
                let local_idx: usize = lhs.local;
                // Part of #3938: Invalidate cross-block constant when local is reassigned.
                self.encode.invalidate_local_cache(local_idx);
                // FC-29: check register-level stores inside loop-assigns frames
                // against the declared `#[kani::loop_modifies]` coverage.
                self.loop_modifies_store_check(lhs, &modified);
                // D1: Propagate ref metadata (ref_targets, const_ref_values, subslice,
                // ptr offset) through Copy/Move/Cast/Offset. Part of #4130.
                self.propagate_ref_metadata_for_assign(
                    lhs,
                    rhs,
                    local_idx,
                    bb_idx,
                    &modified,
                    &aggregate_field_sources,
                );

                // D2: Flattened local assignment (vtable capture, memory mirroring).
                // Part of #4130.
                if lhs.projection.is_empty()
                    && self.flatten.flattened_tuple_locals.contains(&local_idx)
                {
                    self.try_encode_flattened_assignment(
                        lhs,
                        rhs,
                        local_idx,
                        bb_idx,
                        &mut modified,
                        &mut constraints,
                        &mut last_constraint_for_local,
                    );
                    continue;
                }

                // Get the rhs expression, using OUTPUT vars for previously-modified locals (#657)
                let rhs_opt = self.translate_rvalue_with_modified(rhs, &modified, Some(local_idx));
                let Some(rhs_expr) = rhs_opt else {
                    // D3: Handle failed rvalue translation (self-loop, deref-load,
                    // vtable recovery, collection ghost propagation). Part of #4130.
                    self.handle_failed_rvalue_translation(
                        lhs,
                        rhs,
                        local_idx,
                        bb_idx,
                        &mut modified,
                        &mut constraints,
                        &mut last_constraint_for_local,
                    );
                    continue;
                };

                // D4: Emit UB safety checks (overflow, shift, div-by-zero, negation,
                // pointer offset, float NaN generation). Part of #4130.
                self.emit_assignment_safety_checks(
                    rhs,
                    &rhs_expr,
                    bb_idx,
                    &modified,
                    &mut safety_checks,
                );

                // D5: Propagate known_alloc_ids through pointer-identity operations
                // (deref loads, ShallowInitBox, casts, aggregates, refs). Part of #4130.
                self.propagate_alloc_ids_for_assign(lhs, rhs, local_idx, &rhs_expr);

                {
                    let mut acc = StmtAccumulator::new(
                        &mut modified,
                        &mut constraints,
                        &mut last_constraint_for_local,
                    );
                    if lhs.projection.is_empty() {
                        // Delegates to codegen_stmt_assign_simple.rs for sort coercion,
                        // constraint emission, collection propagation, and Mem mirroring.
                        self.encode_simple_assignment(
                            lhs, rhs, rhs_expr, local_idx, bb_idx, &mut acc,
                        );
                    } else {
                        // Projection assignment: _N.field = rhs (#600)
                        // Delegates to codegen_stmt_assign_projection.rs for deref stores,
                        // array stores, flattened tuple fields, and datatype updates.
                        self.encode_projection_assignment(
                            lhs, rhs_expr, local_idx, bb_idx, &mut acc,
                        );
                    }
                }
                continue;
            }
            // Part of #3743: Handle SetDiscriminant — previously silently dropped.
            if let StatementKind::SetDiscriminant { place, variant_index } = &stmt.kind {
                let mut acc = StmtAccumulator::new(
                    &mut modified,
                    &mut constraints,
                    &mut last_constraint_for_local,
                );
                self.encode_set_discriminant(place, variant_index, bb_idx, &mut acc);
                continue;
            }
            // Part of #3743: Explicit no-ops matching BMC backend (D4).
            if matches!(
                &stmt.kind,
                StatementKind::FakeRead(..)
                    | StatementKind::PlaceMention(..)
                    | StatementKind::AscribeUserType { .. }
                    | StatementKind::Coverage(..)
                    | StatementKind::Nop
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Retag(..)
            ) {
                continue;
            }
            // Part of #3743: Catch-all for unhandled statement kinds.
            // Record a sound fallback so the verdict is correctly demoted.
            warn!(
                bb_idx,
                kind = ?stmt.kind,
                "CHC: unhandled StatementKind — recording sound fallback"
            );
            self.record_sound_fallback_reason("unhandled_statement_kind");
        }

        // Phase 4 (#893): Drain pending memory updates (e.g., heap allocation validity constraints)
        constraints.append(&mut self.heap_state.pending_updates);

        // #1447: Emit accumulated store chain constraints at block end.
        // This produces single constraint per array: arr_out = store(store(arr_in, ...), ...)
        constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));

        // Drain pending memory safety checks collected during deref loads/stores.
        if self.memory_safety_checks {
            safety_checks.append(&mut self.heap_state.pending_checks);
        } else {
            self.heap_state.pending_checks.clear();
        }

        // Part of #3038, #3526: enforce constraint-or-unchanged invariant.
        // Removes unconstrained locals from `modified` so output uses INPUT vars.
        {
            let mut acc = super::stmt_accumulator::StmtAccumulator::new(
                &mut modified,
                &mut constraints,
                &mut last_constraint_for_local,
            );
            let fixups = super::codegen_stmt_vtable_tracking::enforce_modified_constraint_invariant(
                bb_idx, &mut acc,
            );
            // Part of #3447: record sound fallback for each repaired local so CTREX
            // classification reports OverApproximation instead of Genuine.
            if fixups > 0 {
                self.record_sound_fallback_reason("constraint_invariant_fixup");
            }
        }

        // Build output args: for modified locals use output vars, for unmodified use input.
        // Also handles modified memory arrays (#905) and flattened locals (#2214).
        // Per-field granularity (#3348): pass last_constraint_for_local so flattened
        // locals use OUTPUT vars only for constrained fields (INPUT for others).
        let output_args = self.build_block_output_args(&modified, Some(&last_constraint_for_local));

        (constraints, output_args, modified, safety_checks)
    }

    // ============================================================
    // encode_block_statements helper methods (Part of #4130)
    // ============================================================
}

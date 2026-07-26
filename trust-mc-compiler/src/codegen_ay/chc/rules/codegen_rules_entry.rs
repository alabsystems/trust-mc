// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC rule generation: entry rule + stack allocation.
//!
//! Contains:
//! - `declare_error_relation`: nullary error relation declaration
//! - `emit_entry_rule`: bb0 entry rule with Bool defaults + stack allocation
//! - `collect_assigned_locals`: scan for locals with assignments
//! - `allocate_stack_locals`: Phase 4 stack local address allocation
//!
//! Pointer check suppression moved to `codegen_rules_pointer_check.rs` (Part of #3094).
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, Place, StatementKind, TerminatorKind};
use std::collections::{HashMap, HashSet};
use tracing::{debug, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::chc::call::codegen_call_misc::CallMisc;
use crate::codegen_ay::chc::call::codegen_call_vec::ChcVecFields;
use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;
use super::codegen_expr_heap::{obj_size_in, obj_valid_in};
use super::codegen_rules_entry_static::CodegenRulesEntryStatic;
use super::codegen_types::CodegenTypes;
use trust_mc_core::chc::{RelationApp, RelationDecl, Rule};

/// Extension trait for entry rule generation on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenRulesEntry<'tcx, 'body> {
    fn declare_error_relation(&mut self);
    fn emit_entry_rule(&mut self);
    fn collect_assigned_locals(&self) -> HashSet<usize>;
    fn allocate_stack_locals(&mut self) -> Vec<Expr>;
}

impl<'tcx, 'body> CodegenRulesEntry<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    /// Declares the error relation (nullary).
    fn declare_error_relation(&mut self) {
        self.vc.add_relation(RelationDecl::nullary("error"));
    }

    /// Emits the entry rule for bb0 (seeds reachability).
    ///
    /// Without this rule, all relations are empty and error is unreachable
    /// by construction. The entry rule has the form:
    /// `allocation_constraints => bb0(state_vars...)`.
    ///
    /// At Ptr+ track level, includes stack allocation constraints from Phase 4 (#893).
    fn emit_entry_rule(&mut self) {
        // Get bb0 relation name
        let bb0_rel = if let Some(name) = self.block_relations.get(&0) {
            name.clone()
        } else {
            // No blocks in function - nothing to do
            debug!("no bb0 found, skipping entry rule");
            return;
        };

        // Phase 4 (#893): Allocate stack locals at Ptr+ level
        let mut entry_constraints = if self.track_level >= ChcTrackLevel::Ptr {
            self.encode
                .stack_alloc_constraints
                .take()
                .unwrap_or_else(|| self.allocate_stack_locals())
        } else {
            Vec::new()
        };

        self.collect_entry_heap_and_static_constraints(&mut entry_constraints);

        // Part of #4050: Initialize ArraySolver shadow state at function entry.
        // Only emitted when shadow aux vars were declared (body_needs_array_solver_shadow
        // gate prevents adding Array-sorted vars to harnesses that don't need them).
        if !self.collections.array_solver_aux.is_empty() {
            self.collect_array_solver_entry_constraints(&mut entry_constraints);
        }

        // Part of #2214: Use projected state args matching bb0's live set.
        let state_args = self.project_state_args(0);
        let bb0_app = RelationApp::new(bb0_rel, state_args);

        // Build entry rule body: combine all constraints
        let body = if entry_constraints.is_empty() {
            Expr::bool_const(true)
        } else {
            // Conjoin all allocation constraints
            entry_constraints
                .into_iter()
                .reduce(ay_bindings::Expr::and)
                .unwrap_or_else(|| Expr::bool_const(true))
        };

        // Emit init rule: constraints => bb0(state_vars...)
        let init_rule = Rule::init(body, bb0_app);
        self.vc.add_rule(init_rule);

        debug!("emitted entry rule for bb0");
    }

    /// Scans all basic blocks to collect the set of locals that have at least
    /// one assignment targeting them (directly, no projection).
    ///
    /// Tracks both `StatementKind::Assign` and `TerminatorKind::Call` destinations,
    /// since MIR represents function call return values as Call terminators, not
    /// Assign statements. Without this, a Bool local assigned solely via a call
    /// return (e.g., `_3 = some_fn()`) would be incorrectly defaulted to `false`.
    fn collect_assigned_locals(&self) -> HashSet<usize> {
        let mut assigned = HashSet::new();
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, _) = &stmt.kind
                    && lhs.projection.is_empty()
                {
                    assigned.insert(lhs.local);
                }
            }
            // Call terminators assign their return value to `destination`.
            if let TerminatorKind::Call { destination, .. } = &bb_data.terminator.kind
                && destination.projection.is_empty()
            {
                assigned.insert(destination.local);
            }
        }
        assigned
    }

    /// Allocates symbolic addresses for stack locals at function entry (Phase 4 #893).
    ///
    /// For each local variable that needs a stack address:
    /// 1. Allocates a fresh object ID
    /// 2. Creates symbolic address mapping
    /// 3. Returns constraints: obj_size[obj_id] = sizeof(type)
    ///
    /// This ensures stack locals have valid, bounded memory regions from function entry.
    fn allocate_stack_locals(&mut self) -> Vec<Expr> {
        let mut constraints = Vec::new();

        // obj_valid is NOT needed here — obj_valid = const_array(true)
        // makes all entries valid. Only obj_size needs per-local constraints.
        let obj_size = obj_size_in();

        // Skip return place (local 0) and function arguments (locals 1..arg_count+1)
        // They are handled separately by the calling convention
        let arg_count = self.body.arg_locals().len();
        let locals = self.body.locals();

        for (local_idx, local_decl) in locals.iter().enumerate() {
            // Skip return place and arguments
            if local_idx == 0 || local_idx <= arg_count {
                continue;
            }

            // Skip locals whose type size is unknown or zero (ZST).
            // Unknown size: skip allocation tracking entirely (#2456).
            // The local won't appear in local_addresses, so heap access
            // checks through it remain unconstrained (sound over-approximation).
            let type_size = match self.get_type_size(local_decl.ty) {
                Some(0) => continue, // ZST — no allocation needed
                Some(s) => s,
                None => {
                    // Size unknown — only record fallback if translate_ty also
                    // fails (no AY representation). Part of #2915.
                    if Self::translate_ty(local_decl.ty).is_none() {
                        warn!(?local_decl.ty, local_idx, "CHC: stack alloc unknown+untranslatable");
                        self.record_sound_fallback_reason("heap_untranslatable_type");
                    }
                    continue;
                }
            };

            // Allocate object ID for this local
            let obj_id = if let Some(id) = self.heap_state.next_alloc_id() {
                id
            } else {
                warn!(local_idx, "CHC: allocation ID overflow, skipping stack local");
                self.record_sound_fallback_reason("heap_alloc_id_overflow");
                continue;
            };

            // Create address mapping: local_idx -> (obj_id, addr_name)
            // Part of #2267: combined allocation avoids intermediate state_var_name String.
            let addr_name = crate::codegen_ay::names::state_var_addr_name(&self.fn_name, local_idx);
            // Part of #2267: move addr_name instead of cloning (last use).
            self.heap_state.insert_local_address(local_idx, obj_id, addr_name);

            // Build constraints:
            // Note: obj_valid[obj_id] = true is NOT emitted here — it is subsumed
            // by `obj_valid = const_array(true)` in collect_entry_heap_and_static_constraints.
            let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);

            // obj_size[obj_id] = sizeof(local) (allocation has correct size)
            let size_expr = Expr::bitvec_const(type_size as i128, 32);
            if let Ok(size) = u32::try_from(type_size) {
                self.heap_state.record_heap_alloc_size(obj_id, size);
            }
            let size_constraint = obj_size.clone().select(obj_id_expr).eq(size_expr);
            constraints.push(size_constraint);

            // Note: No addr_var constraint needed - get_or_create_local_address() returns
            // concrete values directly using the stored obj_id, not symbolic variables.

            debug!(local_idx, obj_id, type_size, "CHC Phase 4: allocated stack local");
        }

        if !constraints.is_empty() {
            debug!(
                num_allocations = constraints.len(),
                "CHC Phase 4: emitted stack allocation constraints"
            );
        }

        constraints
    }
}

// Private helper methods for entry rule constraint collection.
// These are not part of the public trait — they're implementation details.
// Pointer check helpers moved to codegen_rules_pointer_check.rs (Part of #3094).
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Constrains unassigned Bool locals to false (#1979).
    ///
    /// When the Rust compiler optimizes away assignments (e.g., removing a
    /// known-false is_null() check), the CHC state variable for the destination
    /// local is left unconstrained. Defaulting to false matches zero-init.
    fn collect_bool_default_constraints(&self, constraints: &mut Vec<Expr>) {
        let assigned_locals = self.collect_assigned_locals();
        let arg_count = self.body.arg_locals().len();
        let state_idx_to_local: HashMap<usize, usize> = self
            .state_var_mgr
            .local_to_state_idx
            .iter()
            .map(|(&local, &vec_idx)| (vec_idx, local))
            .collect();
        for (vec_idx, (name, sort)) in self.state_var_mgr.state_vars.iter().enumerate() {
            // Part of #2865: Skip ALL non-MIR state vars (heap metadata, collection
            // lengths, memory/region arrays, statics, pointee vars). Only MIR locals
            // that map through local_to_state_idx should be Bool-defaulted.
            let Some(mir_local) = state_idx_to_local.get(&vec_idx).copied() else {
                continue;
            };
            if mir_local == 0 || mir_local <= arg_count {
                continue;
            }
            if sort.is_bool() && !assigned_locals.contains(&mir_local) {
                debug!(
                    "entry_rule defaulting unassigned Bool _{} (vec_idx={}) to false",
                    mir_local, vec_idx
                );
                let var = Expr::var(&**name, sort.clone());
                constraints.push(var.eq(Expr::bool_const(false)));
            }
        }
    }

    /// Appends entry constraints for static initial values (#428).
    fn collect_static_initial_constraints(&self, constraints: &mut Vec<Expr>) {
        for (vec_idx, init_expr) in &self.ref_resolution.static_initial_values {
            if let Some((name, sort)) = self.state_var_mgr.state_vars.get(*vec_idx) {
                let var = Expr::var(&**name, sort.clone());
                debug!(
                    vec_idx,
                    name = %name,
                    "entry_rule constraining static to initial value (#428)"
                );
                constraints.push(var.eq(init_expr.clone()));
            }
        }
        // P2-S1: contract CHECK harness — interior-mut immutable statics are
        // pinned ONLY on their Freeze fields (built by
        // `collect_contract_partial_static_pins`); the UnsafeCell-covered
        // parts stay unconstrained (havoc). Mutable statics get no pin at all
        // in contract mode (their vec_idx is absent from both collections).
        for pin in &self.ref_resolution.contract_static_partial_pins {
            debug!("entry_rule partial Freeze-field pin for interior-mut static (P2-S1)");
            constraints.push(pin.clone());
        }
    }

    /// Tie Vec auxiliary len/cap state vars to the Vec local's entry-state fields.
    ///
    /// Part of #4044: Vec locals carry both an aggregate state var (with
    /// `fld_len`/`fld_cap`) and auxiliary `vec_len_*`/`vec_cap_*` vars. Without
    /// entry-rule equalities, callers can observe different symbolic lengths on
    /// the same parameter, which breaks `any_where(|o| *o <= v.len())` style
    /// proofs when one path reads `fld_len` and another reads `vec_len_*`.
    fn collect_vec_aux_initial_constraints(&mut self, constraints: &mut Vec<Expr>) {
        let tracked_locals: Vec<_> =
            self.collections.len_state.len_var_names.keys().copied().collect();
        let modified_locals = HashSet::new();

        for local_idx in tracked_locals {
            let Some(vec_expr) = self.resolve_vec_entry_expr(local_idx, &modified_locals) else {
                continue;
            };
            let Some((_, len_expr, cap_expr, _)) = ChcVecFields::extract_without_name(vec_expr)
            else {
                continue;
            };

            if let Some(len_name) = self.collections.len_state.get_len_var(local_idx).cloned() {
                constraints.push(Expr::var(&*len_name, ptr_sort()).eq(len_expr));
            }
            if let Some(cap_name) = self.collections.len_state.get_cap_var(local_idx).cloned() {
                constraints.push(Expr::var(&*cap_name, ptr_sort()).eq(cap_expr));
            }

            debug!(local_idx, "entry_rule: bridged Vec aux len/cap to aggregate fields (#4044)");
        }
    }

    fn resolve_vec_entry_expr(
        &mut self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let place = Place { local: local_idx, projection: Vec::new() };
        let operand = Operand::Copy(place.clone());
        self.resolve_ref_or_const_referent(&operand, modified_locals)
            .or_else(|| self.translate_place_with_modified(&place, modified_locals))
            .or_else(|| self.try_resolve_local_expr(local_idx, modified_locals))
    }

    // Part of #3496 Bug B: collect_static_address_distinctness was removed because
    // static address distinctness is now structural — each static gets a unique
    // obj_id in its concrete BV64 address (see codegen_decl_static.rs).

    // collect_const_ref_memory_constraints moved to codegen_rules_entry_static.rs
    // via CodegenRulesEntryStatic trait (Part of #4196 file-size compliance).

    /// Adds BV-range bounding constraints for Int-lifted state variables.
    ///
    /// Part of #112 Direction 2 step 2: When BV sorts are lifted to Int for
    /// invariant synthesis, the Int domain is unbounded. Without bounds,
    /// PDR can find spurious counterexamples using out-of-BV-range values.
    ///
    /// Part of #3169: Signed types use `-2^(w-1) <= x < 2^(w-1)`, unsigned
    /// types use `0 <= x < 2^w`. Previously all types used unsigned bounds,
    /// which excluded negative values for signed types — an unsound
    /// under-approximation of the input space.
    fn collect_int_lift_bounding_constraints(&self, constraints: &mut Vec<Expr>) {
        if self.int_lifted_vars.is_empty() {
            return;
        }
        for (&vec_idx, &(orig_width, is_signed)) in &self.int_lifted_vars {
            let Some((name, sort)) = self.state_var_mgr.state_vars.get(vec_idx) else {
                continue;
            };
            if !sort.is_int() {
                continue;
            }
            let var = Expr::var(&**name, sort.clone());
            if is_signed {
                // Signed: -2^(w-1) <= x < 2^(w-1)
                if orig_width <= 64 {
                    let lower = Expr::int_const(-(1i128 << (orig_width - 1)));
                    let upper = Expr::int_const(1i128 << (orig_width - 1));
                    constraints.push(var.clone().int_ge(lower));
                    constraints.push(var.int_lt(upper));
                }
            } else {
                // Unsigned: 0 <= x < 2^w
                constraints.push(var.clone().int_ge(Expr::int_const(0)));
                if orig_width <= 64 {
                    let upper = Expr::int_const(1i128 << orig_width);
                    constraints.push(var.int_lt(upper));
                }
            }
            debug!(
                vec_idx,
                name = %name,
                orig_width,
                is_signed,
                "entry_rule: Int-lift bounding constraint (#112/#3169)"
            );
        }
    }
}

/// Heap metadata + static memory constraint collection, extracted from
/// `emit_entry_rule` for function-size compliance.
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn collect_entry_heap_and_static_constraints(&mut self, constraints: &mut Vec<Expr>) {
        // Part of #3159: obj_valid = const_array(true).
        if !self.int_lift {
            let obj_valid = obj_valid_in();
            let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));
            constraints.push(obj_valid.eq(all_valid));
            debug!("entry_rule: obj_valid = const_array(true) (#3159)");
        }
        // Fix #1979, Part of #428: Bool defaults + static initial values.
        self.collect_bool_default_constraints(constraints);
        self.collect_static_initial_constraints(constraints);
        self.collect_vec_aux_initial_constraints(constraints);
        // Part of #2958: Promoted constant memory.
        self.collect_const_ref_memory_constraints(constraints);
        // Part of #4023: Pre-register type arrays for static memory inits.
        self.ensure_static_memory_type_arrays();
        // Part of #3496 Phase 5: Static memory constraints.
        self.collect_static_memory_constraints(constraints);
        // Part of #3793: Static alloc obj_size.
        self.collect_static_alloc_size_constraints(constraints);
        // Part of #4067: Null object obj_size[0] = 0.
        self.collect_null_obj_size_constraint(constraints);
        // Part of #112 D2: BV-range bounds for Int-lifted vars.
        self.collect_int_lift_bounding_constraints(constraints);
    }
}

// Static memory constraint methods (collect_static_alloc_size_constraints,
// ensure_static_memory_type_arrays, collect_static_memory_constraints)
// moved to `codegen_rules_entry_static.rs` via CodegenRulesEntryStatic trait.

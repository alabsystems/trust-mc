// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC block relation declaration and state variable setup.
//!
//! State variable collection extracted to codegen_decl_state_vars.rs per #2246.
//! Deref type array collection extracted to codegen_decl_deref.rs per #2246.
//! Reference analysis extracted to codegen_decl_ref_analysis.rs per #2175.
//! Vtable state variable predeclaration extracted to codegen_decl_vtable.rs per #3159.
//! Liveness analysis extracted to codegen_decl_liveness.rs per #4119.
//! Heap region predeclaration extracted to codegen_decl_heap.rs per #4119.
//! Cleanup chain analysis extracted to codegen_decl_cleanup_seed.rs per #4119.
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

use ay_bindings::Sort;
use rustc_public::mir::TerminatorKind;
use tracing::debug;
use trust_mc_core::chc::{RelationDecl, VarDecl};

use crate::args::{ChcStepMode, ChcTrackLevel};

use super::ChcCtx;
use super::codegen_rules_helpers::CodegenRulesHelpers;
use super::fragment::CutPointKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Register an N-field flattened local: replaces a single Datatype state
    /// variable with N consecutive scalar state variables (`_fld0` .. `_fldN-1`).
    ///
    /// For enum types (Option, Result), pass `enum_discr` with the
    /// `(true_variant, false_variant)` discriminant mapping.
    pub(in crate::codegen_ay::chc) fn flatten_local_nfield(
        &mut self,
        local_idx: usize,
        in_name: &str,
        field_sorts: &[Sort],
        enum_discr: Option<(u64, u64)>,
    ) {
        for (i, sort) in field_sorts.iter().enumerate() {
            use std::fmt::Write;
            let mut fld_in = String::with_capacity(in_name.len() + 6);
            fld_in.push_str(in_name);
            fld_in.push_str("_fld");
            let _ = write!(fld_in, "{i}");
            let fld_out = crate::codegen_ay::names::out_name(&fld_in);
            self.push_state_var_pair(&fld_in, &fld_out, sort.clone());
        }
        self.flatten.flattened_tuple_locals.insert(local_idx);
        self.flatten.flattened_local_field_count.insert(local_idx, field_sorts.len());
        if let Some((true_variant, false_variant)) = enum_discr {
            self.flatten.flattened_enum_discr.insert(local_idx, (true_variant, false_variant));
        }
    }

    /// Register a 2-field flattened local (convenience wrapper).
    pub(in crate::codegen_ay::chc) fn flatten_local_2field(
        &mut self,
        local_idx: usize,
        in_name: &str,
        fld0_sort: Sort,
        fld1_sort: Sort,
        enum_discr: Option<(u64, u64)>,
    ) {
        self.flatten_local_nfield(local_idx, in_name, &[fld0_sort, fld1_sort], enum_discr);
    }

    // Cleanup chain analysis extracted to codegen_decl_cleanup_seed.rs per #4119.

    /// Declares a relation for each basic block in the MIR body.
    pub(in crate::codegen_ay::chc) fn declare_block_relations(&mut self) {
        // First, collect state variable sorts from locals
        self.collect_state_vars();

        // Phase 1.4: Collect state variables for `static mut` references (#428).
        // Must run after collect_state_vars (locals defined) and before
        // collect_numeric_ref_targets (which populates ref_targets).
        self.collect_static_state_vars();
        // Part of #4014: Pre-scan callee bodies for static references not in the
        // harness body. The inline walker discovers these during transition rule
        // generation, but by then the entry rule has already been emitted without
        // the memory init constraints. Scanning upfront ensures the entry rule
        // constrains all reachable static memory arrays.
        self.prescan_callee_statics();

        // Phase 1.5: Collect BigInt/BigRational reference targets for stub resolution (#734, #911)
        self.collect_numeric_ref_targets();

        // Phase 3 (#892, #905): Pre-declare type-indexed arrays for Deref operations.
        // Full memory arrays (deref, local, pointer wrapper) only at Mem level.
        if self.track_level >= ChcTrackLevel::Mem {
            self.collect_deref_type_arrays();
            self.collect_local_type_arrays(); // #2258: pre-declare for local assignments
            self.predeclare_pointer_wrapper_alias_arrays(); // #2967: alias arrays for NonNull/Unique
        }
        // Part of #3841 / #3994: const-ref memory arrays must be pre-declared at
        // every track level because the entry rule emits const_ref_memory_inits
        // regardless of track level. Ptr+ still needs the extra stub/internal and
        // static-memory arrays for size/alloc checks, but promoted-const array
        // registration can no longer wait for Ptr or Mem.
        self.predeclare_const_ref_type_arrays(); // #3222, #3994: promoted constant memory arrays
        if self.track_level >= ChcTrackLevel::Ptr {
            self.predeclare_stub_internal_type_arrays(); // #2982: stub-internal types (Option<usize>, Layout)
            self.predeclare_static_memory_type_arrays(); // #3854: static memory mirror arrays
        }

        // Predeclare heap region arrays so relation signatures include them. (#1448)
        self.predeclare_heap_region_arrays();
        // Part of #4193: Predeclare region arrays for allocations inside callee bodies
        // (e.g., Rc::new → Box::new → __rust_alloc). Without this, the __rust_alloc
        // inside callee bodies creates late state vars that widen CHC relation arity.
        self.predeclare_callee_heap_region_arrays();

        // Declare datatype sorts used by ALL state variables, including type-indexed
        // memory arrays added by collect_deref/local_type_arrays and heap region arrays.
        // Must run after all pre-declarations so Datatype sorts in array elements
        // (e.g., Array(BV64, Datatype(MyStruct))) are properly declared. (Part of #647, #2244)
        self.declare_datatype_sorts();

        // Part of #2970: Declare Datatype sorts for flattened locals.
        // Flattened locals (Vec, Option, structs) have their Datatype sort eliminated
        // from state_vars during collect_state_vars(). When translate_place reconstructs
        // a Datatype from flattened fields, the constructor (e.g. Vec_bv32_mk) must be
        // declared. declare_datatype_sorts() misses these because it only walks state
        // variable sorts. This pass covers the gap.
        self.declare_flattened_datatype_sorts();

        // Part of #3768: flattened/local declaration passes above can discover
        // additional promoted-const memory inits (for example macro-introduced
        // `assert_eq!` temporaries like `&0usize` and `&None::<&T>`). Re-run the
        // const-ref predeclaration once the late passes have finished so entry-rule
        // memory seeds do not hit `const_ref_array_unregistered`.
        self.predeclare_const_ref_type_arrays();

        // Part of #3930: Promoted const refs can still carry datatype expressions
        // (for example `&RangeInclusive<u32>`) even when no state variable uses
        // that datatype sort. Predeclare those constructor sorts before rules use
        // const_ref_values in deref lowering.
        self.declare_const_ref_value_datatype_sorts();

        // Part of #3159: Pre-declare vtable state variables for dyn Trait locals.
        // Must run after collect_state_vars() (so local_to_state_idx is populated)
        // and before compute_live_state_indices() (so vtable vars appear in
        // relation signatures and can propagate values between blocks).
        self.predeclare_vtable_state_vars();

        // Part of #3436: Compute return-reachability for dead block elimination.
        // Error-only blocks (cannot reach Return) are usually excluded from
        // relation declaration and backward liveness propagation, reducing both
        // the number of CHC relations and the per-relation arity.
        let return_reachable = {
            use super::codegen_decl_panic_filter::compute_return_reachable_blocks;
            let rr = compute_return_reachable_blocks(self.body);
            let error_only = rr.iter().filter(|&&r| !r).count();
            if error_only > 0 {
                debug!(
                    total = self.body.blocks.len(),
                    return_reachable = self.body.blocks.len() - error_only,
                    error_only,
                    "CHC dead block elimination: skipping error-only blocks (#3436)"
                );
            }
            rr
        };
        let retained_blocks = {
            use super::codegen_decl_panic_filter::compute_cleanup_relevant_blocks_with_filter;
            let cleanup_relevant =
                compute_cleanup_relevant_blocks_with_filter(self.body, |bb_idx, term| {
                    self.should_retain_cleanup_seed(bb_idx, term)
                });
            let retained: Vec<bool> = return_reachable
                .iter()
                .zip(cleanup_relevant.iter())
                .map(|(ret, cleanup)| *ret || *cleanup)
                .collect();
            let cleanup_only = retained
                .iter()
                .zip(return_reachable.iter())
                .filter(|(keep, ret)| **keep && !**ret)
                .count();
            if cleanup_only > 0 {
                debug!(
                    cleanup_only,
                    "CHC panic-unwind: retaining cleanup-chain blocks alongside return-reachable blocks (#3886)"
                );
            }
            retained
        };

        // Part of #2214: Compute per-block live state indices BEFORE building
        // relation signatures. This enables per-block projected signatures that
        // exclude Datatype sorts from blocks where those locals are dead.
        self.compute_live_state_indices(&retained_blocks);
        self.prune_spawn_scheduler_task_slot_array_liveness();

        // Part of #112: In Large mode, run fragment analysis and rewrite
        // cut point live sets to fragment-level unions.
        if self.step_mode == ChcStepMode::Large {
            self.apply_large_step_fragment_analysis();
        }

        // Part of #112 Direction 2: Identify loop headers for Int-lifting.
        // When int_lift is enabled, ALL block predicates use Int sorts instead of
        // BitVec, letting PDR synthesize invariants in LIA. We must lift ALL
        // blocks (not just loop headers) because Z3's CHC `declare-var` requires
        // globally consistent sorts — if any relation uses Int for a variable,
        // all relations must use Int for that variable.
        if self.int_lift {
            // When Large mode is active, fragment analysis has already identified
            // loop headers as LoopHeader cut points — reuse them to avoid
            // rebuilding the CFG and running dominator analysis a second time.
            if let Some(ref fa) = self.fragment_analysis {
                for cp in &fa.cut_points {
                    if cp.kind == CutPointKind::LoopHeader {
                        self.loop_headers.insert(cp.bb_idx);
                    }
                }
            } else {
                use crate::codegen_ay::loop_unroll::{Cfg, find_loop_headers};
                let cfg = Cfg::from_body(self.body);
                if let Ok(headers) = find_loop_headers(&cfg) {
                    for &header_bb in headers.keys() {
                        self.loop_headers.insert(header_bb);
                    }
                }
            }
            if !self.loop_headers.is_empty() {
                debug!(
                    loop_headers = ?self.loop_headers,
                    count = self.loop_headers.len(),
                    "CHC int-lift: identified loop headers"
                );
            }
        }

        // Determine which blocks get relations: all blocks (Small) or cut points only (Large).
        // Part of #3436: In Small mode, exclude irrelevant error-only blocks.
        // Part of #3886: retain panic-unwind cleanup chains even when they cannot
        // reach Return, because their Drop/assert semantics are part of the proof.
        // Part of #3595: bb0 (entry block) is ALWAYS included regardless of
        // return-reachability. For always-panicking functions (no Return terminator),
        // all blocks are error-only, but we must still emit init → bb0 and
        // bb0 → error() rules to preserve soundness. Without bb0, the CHC
        // encoding becomes vacuously true (false PROOF).
        let declare_block: HashSet<usize> = if self.step_mode == ChcStepMode::Large {
            self.fragment_analysis.as_ref().map(|fa| fa.cut_point_set.clone()).unwrap_or_default()
        } else {
            let mut blocks: HashSet<usize> = (0..self.body.blocks.len())
                .filter(|&bb| retained_blocks.get(bb).copied().unwrap_or(true))
                .collect();
            // Always include bb0 (entry point) for soundness.
            if !self.body.blocks.is_empty() {
                blocks.insert(0);
            }
            blocks
        };

        for (bb_idx, _bb_data) in self.body.blocks.iter().enumerate() {
            if !declare_block.contains(&bb_idx) {
                continue;
            }
            let rel_name: Arc<str> = Arc::from(self.block_relation_name(bb_idx));

            // Part of #2214: Per-block projected relation signatures.
            // Only include state variables that are live at this block's entry.
            // In Large mode, cut point live sets have been widened to fragment-level unions.
            //
            // Part of #112 Direction 2: Relation parameter sorts come directly from
            // state_vars, which already have Int sort for int-lifted locals
            // (lifted during collect_state_vars). Range fields are excluded from
            // lifting (#2876) and retain BV sorts — matching their BV-domain
            // constraints in rule bodies.
            let arg_sorts: Vec<Sort> = self.state_var_mgr.live_state_indices[bb_idx]
                .iter()
                .map(|&idx| self.state_var_mgr.state_vars[idx].1.clone())
                .collect();
            debug!(
                ?bb_idx,
                full_arity = self.state_var_mgr.state_vars.len(),
                projected_arity = arg_sorts.len(),
                step_mode = ?self.step_mode,
                "declared CHC relation for block (live-scoped)"
            );
            let relation = RelationDecl::new(rel_name.as_ref(), arg_sorts);
            self.vc.add_relation(relation);
            self.block_relations.insert(bb_idx, Arc::clone(&rel_name));
            self.rel_name_to_bb.insert(rel_name, bb_idx);
        }

        // Declare input variables for rules. Part of #2214, amended Part of #3348.
        //
        // Emit declare-var for ALL state variables, not just those in `all_live`.
        // Post-codegen pruning (prune_vc_unused_type_arrays) removes dead type
        // arrays from relation signatures but NOT from rule constraints (store
        // chain outputs like `mem_bool__out = store(mem_bool, ...)`). Without
        // declare-var for these pruned vars, Z3 reports "unknown constant" errors.
        // Performance comes from relation arity reduction, not fewer declare-vars
        // (see prune_arrays.rs comment at Phase C).
        for idx in 0..self.state_var_mgr.state_vars.len() {
            let (name, sort) = &self.state_var_mgr.state_vars[idx];
            // Part of #112 Direction 2: declare-var sorts come directly from
            // state_vars, which already have Int for int-lifted locals.
            // Range fields retain BV sorts (#2876), matching their BV-domain
            // rule body expressions. Z3 CHC declare-var sorts are global — they
            // must match relation parameter sorts exactly.
            self.vc.add_var(VarDecl::new(name.clone(), sort.clone()));
            let (out_name, _out_sort) = &self.state_var_mgr.output_state_vars[idx];
            self.vc.add_var(VarDecl::new(out_name.clone(), sort.clone()));
        }
    }

    /// Apply fragment analysis for large-step encoding (#112).
    ///
    /// 1. Run `analyze_fragments()` to identify cut points and partition the CFG.
    /// 2. Compute fragment-level live sets (union of all block live sets in each fragment).
    /// 3. Pre-rewrite `live_state_indices` for cut point blocks with the union,
    ///    so existing `project_state_args()` / `project_full_output_to_block()` work unchanged.
    fn apply_large_step_fragment_analysis(&mut self) {
        let analysis = self.analyze_fragments();

        // Part of #3101: Log composition classification per fragment to diagnose
        // why large-step may not reduce predicate count for loop harnesses.
        let mut composable_count = 0usize;
        let mut fallback_count = 0usize;
        let mut single_count = 0usize;
        for fragment in &analysis.fragments {
            if fragment.blocks.len() == 1 {
                single_count += 1;
            } else {
                // Check composability using the same criteria as fragment_gen.rs.
                let has_call = fragment.blocks.iter().any(|&bb| {
                    bb < self.body.blocks.len()
                        && matches!(
                            self.body.blocks[bb].terminator.kind,
                            TerminatorKind::Call { .. }
                        )
                });
                if has_call {
                    fallback_count += 1;
                    debug!(
                        entry_bb = fragment.entry_bb,
                        block_count = fragment.blocks.len(),
                        "CHC large-step: fragment has Call terminator — will fall back to per-block rules (#3101)"
                    );
                } else {
                    composable_count += 1;
                }
            }
        }
        debug!(
            fn_name = %self.fn_name,
            cut_points = analysis.cut_points.len(),
            fragments = analysis.fragments.len(),
            composable_count,
            fallback_count,
            single_count,
            "CHC large-step: fragment analysis complete"
        );

        // For each fragment, compute the union of all constituent block live sets
        // and rewrite the entry cut point's live_state_indices with this union.
        for fragment in &analysis.fragments {
            let fragment_live: BTreeSet<usize> = fragment
                .blocks
                .iter()
                .flat_map(|&bb| self.state_var_mgr.live_state_indices[bb].iter().copied())
                .collect();
            let fragment_live_vec: Vec<usize> = fragment_live.into_iter().collect();

            let old_arity = self.state_var_mgr.live_state_indices[fragment.entry_bb].len();
            debug!(
                entry_bb = fragment.entry_bb,
                block_count = fragment.blocks.len(),
                old_arity,
                new_arity = fragment_live_vec.len(),
                "CHC large-step: widened cut point live set to fragment union"
            );
            self.state_var_mgr.live_state_indices[fragment.entry_bb] = fragment_live_vec;
        }

        self.fragment_analysis = Some(analysis);
    }

    // Liveness analysis extracted to codegen_decl_liveness.rs per #4119.
    // Heap region predeclaration extracted to codegen_decl_heap.rs per #4119.
    // Vtable state variable predeclaration extracted to codegen_decl_vtable.rs per #3159.
    // Datatype sort declarations extracted to codegen_decl_datatypes.rs
}

#[cfg(test)]
mod tests {
    use super::super::codegen_decl_panic_filter::compute_return_reachable_blocks;
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    const ALWAYS_PANIC_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_always_panics() -> ! {
            panic!("always fails");
        }
    "#;

    #[test]
    fn test_declare_block_relations_keeps_bb0_for_always_panicking_body() {
        with_test_ay_ctx_for_source(ALWAYS_PANIC_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_always_panics");
            let body = instance.body().expect("function body");

            assert!(
                body.blocks
                    .iter()
                    .all(|block| !matches!(block.terminator.kind, TerminatorKind::Return)),
                "probe_always_panics MIR unexpectedly contains a Return terminator"
            );

            let return_reachable = compute_return_reachable_blocks(&body);

            assert!(
                return_reachable.iter().all(|&reachable| !reachable),
                "probe_always_panics should have no Return-reachable blocks: {return_reachable:?}"
            );

            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_always_panics", ChcConfig::default());
            chc_ctx.declare_block_relations();

            assert!(
                chc_ctx.block_relations.contains_key(&0),
                "bb0 must remain declared even when every block is error-only"
            );
            assert_eq!(
                chc_ctx.block_relations.len(),
                1,
                "always-panicking bodies should retain only the bb0 relation after pruning"
            );

            let vc = crate::codegen_ay::chc::mir_to_chc(
                ctx.tcx,
                &body,
                "probe_always_panics",
                ChcConfig::default(),
            );
            assert!(
                vc.relations.iter().any(|relation| relation.name.contains("__bb0")),
                "translated VC must keep the bb0 entry relation"
            );
            assert!(
                vc.rules.iter().any(|rule| rule.head.name == "error"),
                "always-panicking body must still emit an error-headed rule"
            );
        });
    }
}

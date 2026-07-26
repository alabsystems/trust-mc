// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Late state-variable management helpers for `ChcCtx`.
//!
//! Extracted from `codegen_ctx/mod.rs` per #3254 packet 3.

use std::sync::Arc;

use ay_bindings::{Expr, Sort};
use trust_mc_core::chc::RelationApp;

use super::{ChcCtx, push_pending_var_decl};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Register a late-created type array as both a state variable pair and VarDecl.
    ///
    /// Part of #2970: During codegen, `get_or_create_type_array` may create arrays
    /// not predicted by the static MIR scan. This method:
    /// 1. Registers the pair in `StateVarManager` (for expression building)
    /// 2. Pushes `(declare-var)` entries via `PENDING_FRESH_VAR_DECLS` (for Z3)
    ///
    /// Without the VarDecl entries, Z3 reports "unknown constant" errors.
    /// Part of #2267: out_name accepts `&str` to avoid unnecessary String allocations.
    fn extend_block_relations_for_late_state_var(&mut self, in_name: &Arc<str>) {
        let new_idx = self.state_var_mgr.state_vars.len() - 1;
        let new_sort = self.state_var_mgr.state_vars[new_idx].1.clone();
        for live in &mut self.state_var_mgr.live_state_indices {
            live.push(new_idx);
        }
        // Only extend block relations. `error` is nullary and must not grow.
        let block_rel_names: std::collections::HashSet<&str> =
            self.block_relations.values().map(|s| s.as_ref()).collect();
        for rel in &mut self.vc.relations {
            if block_rel_names.contains(rel.name.as_str()) {
                rel.arg_sorts.push(new_sort.clone());
            }
        }
        // Use pass-through semantics for rules already emitted before the new
        // state var existed so earlier blocks keep the pre-existing value.
        let pass_through = Expr::var(in_name.as_ref(), new_sort);
        for rule in &mut self.vc.rules {
            if block_rel_names.contains(rule.head.name.as_str()) {
                let mut args = (*rule.head.args).clone();
                args.push(pass_through.clone());
                rule.head = RelationApp::new(rule.head.name.as_str(), args);
            }
            if let Some(ref mut body_rel) = rule.body.relation
                && block_rel_names.contains(body_rel.name.as_str())
            {
                let mut args = (*body_rel.args).clone();
                args.push(pass_through.clone());
                *body_rel = RelationApp::new(body_rel.name.as_str(), args);
            }
        }
    }

    /// Append any late-created live state vars missing from a block relation app.
    ///
    /// Call-terminator handlers can create late state vars after the caller
    /// constructed `from_app` for the source block. If rule emission reuses the
    /// stale app unchanged, translate-time arity fixup pads the missing slots
    /// with anonymous `__pad_*` vars instead of the real input state vars,
    /// disconnecting same-block stores from later loads.
    pub(in crate::codegen_ay::chc) fn refresh_block_relation_app(
        &self,
        app: &RelationApp,
    ) -> RelationApp {
        let Some(&bb_idx) = self.rel_name_to_bb.get(app.name.as_str()) else {
            return app.clone();
        };

        let live = &self.state_var_mgr.live_state_indices[bb_idx];
        if app.args.len() >= live.len() {
            return app.clone();
        }

        let mut refreshed = Vec::with_capacity(live.len());
        refreshed.extend(app.args.iter().cloned());
        for &idx in &live[app.args.len()..] {
            let (name, sort) = &self.state_var_mgr.state_vars[idx];
            refreshed.push(Expr::var(&**name, sort.clone()));
        }
        RelationApp::new(app.name.as_str(), refreshed)
    }

    pub(in crate::codegen_ay::chc) fn push_late_state_var_pair(
        &mut self,
        in_name: Arc<str>,
        out_name: &str,
        sort: Sort,
    ) {
        let late_out_name = if let Some(bb_idx) = self.fragment_mid_output_bb {
            let mut mid_name = String::with_capacity(in_name.len() + 12);
            mid_name.push_str(in_name.as_ref());
            mid_name.push_str("__mid_bb");
            let _ = std::fmt::Write::write_fmt(&mut mid_name, format_args!("{bb_idx}"));
            mid_name
        } else {
            out_name.to_owned()
        };
        // #2982 diagnostic: late array creation means a prediction gap exists.
        // If this fires, add the type key to predeclare_stub_internal_type_arrays().
        tracing::warn!(
            in_name = %in_name,
            "late-created type array — prediction gap (#2982). \
             Add this type to predeclare_stub_internal_type_arrays()."
        );
        push_pending_var_decl(in_name.clone(), sort.clone());
        push_pending_var_decl(&*late_out_name, sort.clone());
        let len_before = self.state_var_mgr.state_vars.len();
        self.state_var_mgr.push_state_var_pair_arc(in_name, &late_out_name, sort);
        // Part of #3685: propagate new late arrays to live sets and relation
        // declarations so stores in one block carry over to loads in the next.
        // Without this, late arrays are unconstrained across CHC blocks.
        if self.state_var_mgr.state_vars.len() > len_before {
            let new_idx = self.state_var_mgr.state_vars.len() - 1;
            let late_in_name = Arc::clone(&self.state_var_mgr.state_vars[new_idx].0);
            self.extend_block_relations_for_late_state_var(&late_in_name);
        }
    }

    /// Resolve the CURRENT state-variable names for a (possibly late-created)
    /// array registered under its ORIGINAL input name.
    ///
    /// During large-step fragment composition (`generate_composed_rules`) the
    /// state variable names are temporarily swapped to `__mid_bbN` forms, but
    /// the heap-state type/region array registries keep the ORIGINAL names.
    /// Store/load paths must resolve through the state var manager so a store
    /// chain emitted in a non-last fragment block binds that block's output
    /// variable (`X__mid_bbN`) instead of the final `X__out`. Binding `X__out`
    /// from two blocks of one composed rule produces contradictory equalities
    /// on the same variable; after const-folding these become constant-false
    /// rule bodies that silently cut reachability (vacuous proofs — FC-29
    /// root cause on loop-contract harnesses).
    ///
    /// Returns `(current_input_name, current_output_name, state_idx)`;
    /// falls back to the registry names when the array has no state slot.
    pub(in crate::codegen_ay::chc) fn current_array_state_names(
        &self,
        arr_name: &Arc<str>,
        arr_out_name: &str,
    ) -> (Arc<str>, Arc<str>, Option<usize>) {
        if let Some(idx) = self.state_var_mgr.state_var_index_by_name(arr_name)
            && let (Some((in_n, _)), Some((out_n, _))) = (
                self.state_var_mgr.state_vars.get(idx),
                self.state_var_mgr.output_state_vars.get(idx),
            )
        {
            return (Arc::clone(in_n), Arc::clone(out_n), Some(idx));
        }
        (Arc::clone(arr_name), Arc::from(arr_out_name), None)
    }

    /// Late-declare a collection auxiliary state variable (present/len) and add
    /// it to all blocks' live sets so it propagates between basic blocks.
    ///
    /// Part of #3348: Collection present/len vars for struct-embedded maps are
    /// discovered during codegen (constructor bridge), after
    /// `compute_live_state_indices()` has already run. Without adding the new
    /// index to live sets, the variable is excluded from relation signatures and
    /// becomes a free variable in each rule — preventing inter-block propagation.
    pub(in crate::codegen_ay::chc) fn push_late_collection_aux_var(
        &mut self,
        in_name: Arc<str>,
        out_name: &str,
        sort: Sort,
    ) {
        if self.state_var_mgr.state_var_index_by_name(&in_name).is_some() {
            return; // Already declared — no-op.
        }
        push_pending_var_decl(in_name.clone(), sort.clone());
        push_pending_var_decl(out_name, sort.clone());
        self.state_var_mgr.push_state_var_pair_arc(in_name, out_name, sort);
        // Match late type arrays: collection aux vars must also thread through
        // already-emitted block relations, otherwise pre-creation blocks leave
        // them unconstrained across edges.
        let late_in_name =
            Arc::clone(&self.state_var_mgr.state_vars.last().expect("late collection aux").0);
        self.extend_block_relations_for_late_state_var(&late_in_name);
    }

    /// Ensure a MIR local's state variable(s) are live at ALL blocks.
    ///
    /// Part of #4112: Stub-intercepted calls (e.g. FlattenNext for BV64 iterators)
    /// produce iter_update constraints, but the static liveness analysis may not
    /// include the iterator local in every block's live set (the MIR call goes
    /// through a reference, not a direct local use). Without this, the iterator
    /// position counter is silently dropped during `project_full_output_to_block`,
    /// making the constraint invisible to the solver.
    ///
    /// Uses the same APPEND pattern as `extend_block_relations_for_late_state_var`:
    /// push the index at the end of each live set and append to relation arg_sorts.
    /// This is compatible with `refresh_block_relation_app` which handles appended vars.
    pub(in crate::codegen_ay::chc) fn ensure_local_live_at_block(
        &mut self,
        local_idx: usize,
        _bb_idx: usize,
    ) {
        let Some(base_vec_idx) = self.try_state_idx_for_local(local_idx) else {
            return;
        };

        let n = if self.flatten.flattened_tuple_locals.contains(&local_idx) {
            self.flattened_field_count(local_idx)
        } else {
            1
        };

        for offset in 0..n {
            let idx = base_vec_idx + offset;
            if idx >= self.state_var_mgr.state_vars.len() {
                break;
            }

            let already_live_everywhere =
                self.state_var_mgr.live_state_indices.iter().all(|live| live.contains(&idx));
            if already_live_everywhere {
                continue;
            }

            // APPEND the index to every block's live set (same pattern as
            // extend_block_relations_for_late_state_var).
            let (in_name, sort) = &self.state_var_mgr.state_vars[idx];
            let pass_through = Expr::var(&**in_name, sort.clone());
            let sort = sort.clone();

            for live in &mut self.state_var_mgr.live_state_indices {
                if !live.contains(&idx) {
                    live.push(idx);
                }
            }

            // Extend block relation declarations' arg_sorts.
            let block_rel_names: std::collections::HashSet<&str> =
                self.block_relations.values().map(|s| s.as_ref()).collect();
            for rel in &mut self.vc.relations {
                if block_rel_names.contains(rel.name.as_str()) {
                    rel.arg_sorts.push(sort.clone());
                }
            }

            // Patch existing rules with pass-through.
            for rule in &mut self.vc.rules {
                if block_rel_names.contains(rule.head.name.as_str()) {
                    let mut args = (*rule.head.args).clone();
                    args.push(pass_through.clone());
                    rule.head = RelationApp::new(rule.head.name.as_str(), args);
                }
                if let Some(ref mut body_rel) = rule.body.relation {
                    if block_rel_names.contains(body_rel.name.as_str()) {
                        let mut args = (*body_rel.args).clone();
                        args.push(pass_through.clone());
                        *body_rel = RelationApp::new(body_rel.name.as_str(), args);
                    }
                }
            }
        }
    }
}

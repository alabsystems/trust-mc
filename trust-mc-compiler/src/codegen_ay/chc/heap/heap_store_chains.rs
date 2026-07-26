// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Store chain accumulation and draining for SSA-style memory modeling.
//!
//! Extracted from heap_state.rs per design D2 (file-decomposition-500loc-compliance).

use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue, Sort};
use tracing::warn;

use super::codegen_ctx::diagnostics::{CellCounter, ChcDiagnostics};
use super::heap_state::ChcHeapState;
use super::types::ptr_sort;

/// Extract the LHS variable name from an equality constraint `Var(name) = rhs`.
///
/// Returns `Some(name)` for constraints of the form `name = expr` where `name`
/// ends with `__out` (store chain constraints). Returns `None` otherwise.
fn extract_store_chain_out_name(expr: &Expr) -> Option<&str> {
    if let ExprValue::Eq(lhs, _) = expr.value() {
        if let ExprValue::Var { name } = lhs.value() {
            if name.ends_with("__out") {
                return Some(name.as_str());
            }
        }
    }
    None
}

/// Filter `stmt_constraints` to remove store chain constraints superseded by
/// `bridge_constraints`. Part of #3528.
///
/// When a call handler's Mem-level bridge calls `build_memory_store` and drains
/// store chains, the resulting constraints may target the same `__out` variables
/// as constraints already in `stmt_constraints` (from `encode_block_statements`'s
/// drain). The bridge constraints are correctly chained (via seeds) and supersede
/// the original constraints.
///
/// Returns `Some(filtered)` if any constraints were removed, `None` if no
/// conflicts detected (caller should use original `stmt_constraints`).
pub(in crate::codegen_ay::chc) fn filter_superseded_store_chains(
    stmt_constraints: &[Expr],
    bridge_constraints: &[Expr],
) -> Option<Vec<Expr>> {
    let overridden: HashSet<&str> =
        bridge_constraints.iter().filter_map(extract_store_chain_out_name).collect();

    if overridden.is_empty() {
        return None;
    }

    // Check if any stmt_constraints actually match before cloning.
    let has_conflict = stmt_constraints
        .iter()
        .any(|c| extract_store_chain_out_name(c).is_some_and(|n| overridden.contains(n)));

    if !has_conflict {
        return None;
    }

    Some(
        stmt_constraints
            .iter()
            .filter(|c| {
                extract_store_chain_out_name(c).map_or(true, |name| !overridden.contains(name))
            })
            .cloned()
            .collect(),
    )
}

impl ChcHeapState {
    /// Accumulates a store expression for an array (#1447).
    /// Instead of emitting a constraint immediately, we build a nested store chain:
    /// `store(store(arr_in, addr1, val1), addr2, val2)`
    ///
    /// The caller (build_memory_store) already uses get_store_chain() to determine
    /// the base expression, so the store_expr is already properly nested.
    pub(in crate::codegen_ay::chc) fn accumulate_store(
        &mut self,
        type_key: &str,
        arr_out_name: impl Into<Arc<str>>,
        store_expr: Expr,
    ) {
        let arr_out_name: Arc<str> = arr_out_name.into();
        // Insert/update the accumulated store expression.
        // First store: store(arr_in, addr1, val1)
        // Second store: store(store(arr_in, addr1, val1), addr2, val2) [pre-nested by caller]
        if let Some(existing) = self.store_chains.get_mut(type_key) {
            *existing = (arr_out_name, store_expr);
        } else {
            self.store_chains.insert(type_key.into(), (arr_out_name, store_expr));
        }
    }

    /// Gets the current accumulated store expression for reads after stores in same block.
    /// Returns the nested store expression that represents the current array state.
    ///
    /// Falls back to `drained_store_chain_seeds` when the chain was already drained
    /// (Part of #3528): call handler Mem-level bridges run after `encode_block_statements`
    /// drains the statement-phase chains. Without seeds, `build_memory_store` would
    /// start from the input array, producing a conflicting constraint for the same
    /// `__out` variable.
    pub(in crate::codegen_ay::chc) fn get_store_chain(&self, type_key: &str) -> Option<&Expr> {
        self.store_chains
            .get(type_key)
            .map(|(_, expr)| expr)
            .or_else(|| self.drained_store_chain_seeds.get(type_key))
    }

    /// Gets only the live (pre-drain) store chain, ignoring drained seeds.
    ///
    /// Use this when callers need to distinguish between a live chain and a
    /// drained seed (Part of #3552). `get_store_chain()` merges both, which
    /// prevents callers like `codegen_call_vec_into` from routing to the
    /// correct post-drain code path (e.g., mirror_addr resolution).
    #[allow(dead_code)] // W4 consumer pending (#3552)
    pub(in crate::codegen_ay::chc) fn get_live_store_chain(&self, type_key: &str) -> Option<&Expr> {
        self.store_chains.get(type_key).map(|(_, expr)| expr)
    }

    /// Resolve the declared output array sort for a store-chain output name.
    ///
    /// We track expected sorts from `type_arrays` and `region_arrays` so
    /// `drain_store_chains` can avoid constructing mismatched equalities.
    #[must_use]
    fn expected_store_chain_output_sort(&self, arr_out_name: &str) -> Option<Sort> {
        // Part of #2793: O(1) reverse-index lookup replacing O(T+R) linear scan.
        let arr_in_name = arr_out_name.strip_suffix("__out")?;
        self.array_name_to_elem_sort
            .get(arr_in_name)
            .map(|elem_sort| Sort::array(ptr_sort(), elem_sort.clone()))
    }

    /// Drains accumulated store chains into constraints (#1447).
    /// Called at block end to emit single constraint per modified array:
    /// `arr_out = store(store(arr_in, addr1, val1), addr2, val2)`
    pub(in crate::codegen_ay::chc) fn drain_store_chains(
        &mut self,
        diagnostics: &ChcDiagnostics,
    ) -> Vec<Expr> {
        // Part of #3528: Save seeds before draining so that subsequent
        // build_memory_store calls (in call handler Mem-level bridges) can
        // chain on top of the drained expressions via get_store_chain().
        self.drained_store_chain_seeds.clear();
        for (type_key, (_, expr)) in &self.store_chains {
            self.drained_store_chain_seeds.insert(type_key.clone(), expr.clone());
        }

        // Sort by type_key for deterministic constraint ordering (#1974).
        let mut entries: Vec<_> = self.store_chains.drain().collect();
        entries.sort_by(|(a, _), (b, _)| a.cmp(b));
        let mut constraints = Vec::new();
        for (_type_key, (arr_out_name, store_expr)) in entries {
            let store_sort = store_expr.sort().clone();
            let out_sort = self
                .expected_store_chain_output_sort(&arr_out_name)
                .unwrap_or_else(|| store_sort.clone());
            if out_sort != store_sort {
                warn!(
                    arr_out_name = %arr_out_name,
                    expected_sort = ?out_sort,
                    store_sort = ?store_sort,
                    "CHC: store-chain sort mismatch — arr_out left unconstrained (universally quantified, Part of #3138)"
                );
                diagnostics.store_dropped_transition.inc();
                // Part of #3138: Remove self-loop (arr_out = arr_in) that was added by #2977.
                // The arr_out variable is already in modified_state_indices from the
                // accumulate_store call. Without a constraint, arr_out is universally
                // quantified — sound over-approximation. The #2977 self-loop produced
                // identity copies (under-approximation, potentially unsound).
                continue;
            }
            let arr_out = Expr::var(&*arr_out_name, out_sort);
            constraints.push(arr_out.eq(store_expr));
        }
        constraints
    }
}

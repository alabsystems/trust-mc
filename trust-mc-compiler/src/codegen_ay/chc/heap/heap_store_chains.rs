// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Store chain accumulation and draining for SSA-style memory modeling.
//!
//! Extracted from heap_state.rs per design D2 (file-decomposition-500loc-compliance).

use std::collections::{HashMap, HashSet};
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

/// The heap metadata arrays, as their input-variable names.
const HEAP_METADATA_LANES: [&str; 2] = ["obj_valid", "obj_size"];

/// `expr` with every variable named in `substitution` replaced by its value.
fn substitute_vars(expr: &Expr, substitution: &HashMap<String, Expr>) -> Expr {
    if let ExprValue::Var { name } = expr.value() {
        return substitution.get(name).cloned().unwrap_or_else(|| expr.clone());
    }
    let children: Vec<&Expr> = expr.children().collect();
    if children.is_empty() {
        return expr.clone();
    }
    let rewritten: Vec<Expr> = children.iter().map(|c| substitute_vars(c, substitution)).collect();
    if rewritten.iter().zip(children.iter()).all(|(new, old)| new == *old) {
        return expr.clone();
    }
    ay_bindings::rebuild_with_children(expr, rewritten)
}

/// `rhs` when `constraint` is `out = rhs` and `rhs` does not mention `out`.
fn proper_definition_rhs(constraint: &Expr, out: &str) -> Option<Expr> {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else { return None };
    let ExprValue::Var { name } = lhs.value() else { return None };
    if name != out {
        return None;
    }
    let mut stack = vec![rhs.clone()];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value()
            && name == out
        {
            return None;
        }
        stack.extend(node.children().cloned());
    }
    Some(rhs.clone())
}

/// Compose the bridge's definitions of a heap metadata output
/// (`obj_valid__out`, `obj_size__out`) onto the block's.
///
/// A metadata write builds its new array on the block's INPUT
/// (`obj_valid__out = store(obj_valid, id, true)`, the allocator stubs) or on
/// `current_obj_valid_array()` (`store(obj_valid__out, id, false)`), so unlike a
/// memory store chain it is not chained on an earlier write of the block, and
/// [`filter_superseded_store_chains`] then drops that earlier write. A
/// statement's integer-to-pointer invalidation followed by an allocating call
/// in the same block lost the invalidation: `let p = a as *const u8; let v =
/// vec![1, 2, 3];` read `*p` at the slot `a` named as valid, SUCCESSFUL where
/// Kani reports an invalid integer address, on main and on fix/chc-lost-writes
/// alike (lostwrite track round 2, finding 5). Each bridge definition is
/// rewritten onto the one before it (the block's last proper definition, then
/// the bridge's earlier ones), with both the input and the output name taken
/// as that previous array, and only the last one is kept.
fn compose_heap_metadata_definitions(stmt_constraints: &[Expr], bridge: &mut Vec<Expr>) {
    for lane in HEAP_METADATA_LANES {
        let out = format!("{lane}__out");
        let positions: Vec<usize> = bridge
            .iter()
            .enumerate()
            .filter(|(_, c)| extract_store_chain_out_name(c) == Some(out.as_str()))
            .map(|(i, _)| i)
            .collect();
        let mut previous =
            stmt_constraints.iter().rev().find_map(|c| proper_definition_rhs(c, &out));
        if positions.is_empty() || (previous.is_none() && positions.len() == 1) {
            continue;
        }
        let mut composed_last = None;
        for &i in &positions {
            let ExprValue::Eq(lhs, rhs) = bridge[i].value() else { continue };
            let composed = match &previous {
                Some(prev) => {
                    let substitution = HashMap::from([
                        (lane.to_string(), prev.clone()),
                        (out.clone(), prev.clone()),
                    ]);
                    substitute_vars(rhs, &substitution)
                }
                None => rhs.clone(),
            };
            previous = Some(composed.clone());
            composed_last = Some((i, lhs.clone().eq(composed)));
        }
        let Some((keep, definition)) = composed_last else { continue };
        bridge[keep] = definition;
        let mut index = 0;
        bridge.retain(|_| {
            let drop = index != keep && positions.contains(&index);
            index += 1;
            !drop
        });
    }
}

/// Filter `stmt_constraints` to remove store chain constraints superseded by
/// `bridge_constraints`. Part of #3528.
///
/// When a call handler's Mem-level bridge calls `build_memory_store` and drains
/// store chains, the resulting constraints may target the same `__out` variables
/// as constraints already in `stmt_constraints` (from `encode_block_statements`'s
/// drain). The bridge constraints are correctly chained (via seeds) and supersede
/// the original constraints. Heap metadata definitions are not chained that
/// way, so the bridge's are first composed onto the block's
/// ([`compose_heap_metadata_definitions`]), which rewrites `bridge_constraints`.
///
/// Returns `Some(filtered)` if any constraints were removed, `None` if no
/// conflicts detected (caller should use original `stmt_constraints`).
pub(in crate::codegen_ay::chc) fn filter_superseded_store_chains(
    stmt_constraints: &[Expr],
    bridge_constraints: &mut Vec<Expr>,
) -> Option<Vec<Expr>> {
    compose_heap_metadata_definitions(stmt_constraints, bridge_constraints);
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
        self.note_write();
        self.note_memory_effect();
        // Insert/update the accumulated store expression.
        // First store: store(arr_in, addr1, val1)
        // Second store: store(store(arr_in, addr1, val1), addr2, val2) [pre-nested by caller]
        if let Some(existing) = self.store_chains.get_mut(type_key) {
            *existing = (arr_out_name, store_expr);
        } else {
            self.store_chains.insert(type_key.into(), (arr_out_name, store_expr));
        }
    }

    /// Rewrite every pending term of the block through `rewrite`: the live
    /// store chains, the drained chain seeds a call handler chains on, the
    /// pending updates and checks, and the store-to-load forwarding values.
    ///
    /// A call handler that rebinds a local's output slots (the Cell store
    /// lane's register sync or havoc) calls this BEFORE it adds any term of
    /// its own, with the rewrite onto the slots' pre-call values: every term
    /// built earlier in the block meant the pre-call value, and a term built
    /// afterwards means the post-call one, so the two must never be rewritten
    /// together.
    pub(in crate::codegen_ay::chc) fn rewrite_pending_terms(
        &mut self,
        rewrite: impl Fn(&Expr) -> Expr,
    ) {
        for (_, expr) in self.store_chains.values_mut() {
            *expr = rewrite(expr);
        }
        for expr in self.drained_store_chain_seeds.values_mut() {
            *expr = rewrite(expr);
        }
        for expr in &mut self.pending_updates {
            *expr = rewrite(expr);
        }
        for expr in &mut self.pending_checks {
            *expr = rewrite(expr);
        }
        for (_, expr, _) in self.store_forward_map.values_mut() {
            *expr = rewrite(expr);
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

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phi node computation for block entry environment merging.
//!
//! Part of #2408: extracted from env.rs.

use super::{Env, Expr, IncomingEdge, StatementCodegen, VariantFact};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Initialize the environment at block entry by merging incoming edges.
    ///
    /// For the entry block (bb_idx=0), starts with empty environment.
    /// For single-predecessor blocks, inherits predecessor's environment.
    /// For merge points, computes phi nodes for each variable defined on any path.
    ///
    /// REQUIRES: bb_idx is a valid block index in self.body
    /// ENSURES: Sets current_env to merged entry environment
    /// ENSURES: Sets current_path_condition from block_path_conditions
    pub(in crate::codegen_ay) fn initialize_block_entry_env(&mut self, bb_idx: usize) {
        // Which block we are on. Recorded FIRST so the bb0 early-return below
        // does not skip it. Read only by the unwinding-assertion sentinel lookup
        // in the `Unreachable` terminator arm.
        self.current_bb = bb_idx;

        // SwitchInt→variant bridge (#3017): a `Discriminant(P)` read and the `SwitchInt`
        // that consumes it live in the SAME basic block, so the discriminant-scrutinee
        // table is block-local. Clearing it at every block entry prevents a discriminant
        // temp recorded in one block from being read by an unrelated switch in another
        // (which would emit an unsound fact) — fail-closed on that pathological CFG.
        self.discr_of_local.clear();

        if bb_idx == 0 {
            self.current_path_condition = None;
            self.current_env = Env::new();
            // A fresh function/inline body starts with no live variant facts.
            self.current_variant_facts.clear();
            debug!("init_block_entry_env bb{}: entry env (empty)", bb_idx);
            return;
        }

        self.set_block_path_condition(bb_idx);

        // Take ownership of incoming edges — each bb's edges are consumed exactly once
        let Some(incoming) = self.incoming_edges.remove(&bb_idx) else {
            self.current_env = Env::new();
            self.current_variant_facts.clear();
            debug!("init_block_entry_env bb{}: no incoming edges", bb_idx);
            return;
        };

        if incoming.len() == 1 {
            // Move the single predecessor's env directly into current_env
            let mut incoming_iter = incoming.into_iter();
            let Some(single_edge) = incoming_iter.next() else {
                self.current_env = Env::new();
                self.current_variant_facts.clear();
                debug!("init_block_entry_env bb{}: incoming edge list unexpectedly empty", bb_idx);
                return;
            };
            // Single predecessor inherits its facts directly (#3017).
            let IncomingEdge { env, variant_facts, .. } = single_edge;
            self.current_env = env;
            self.current_variant_facts = variant_facts;
            debug!(
                "init_block_entry_env bb{}: single incoming edge, {} vars",
                bb_idx,
                self.current_env.len()
            );
            return;
        }

        // Merge point: keep a variant fact only if present with an identical
        // (place_key, ctor_idx, dt_name) on EVERY incoming edge (#3017). A kill on
        // one predecessor path therefore cannot be masked by a sibling that kept it.
        self.current_variant_facts = Self::intersect_variant_facts(&incoming);

        debug!("init_block_entry_env bb{}: {} incoming edges", bb_idx, incoming.len());
        for (idx, edge) in incoming.iter().enumerate() {
            debug!("  incoming[{}]: pred={:?}, {} vars", idx, edge.edge_predicate, edge.env.len());
        }

        let mut var_names: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
        for edge in &incoming {
            var_names.extend(edge.env.keys().map(|k| &**k));
        }

        let mut entry_env = Env::new();
        for var_name in var_names {
            if let Some(expr) = self.compute_phi_for_var(var_name, &incoming) {
                entry_env.insert(std::sync::Arc::from(var_name), expr);
            }
        }

        self.current_env = entry_env;
        debug!("init_block_entry_env bb{}: merged {} vars", bb_idx, self.current_env.len());
    }

    /// Intersect variant facts across incoming edges (#3017 bridge).
    ///
    /// Keeps a fact from the first edge only when every other edge carries a fact
    /// with an identical `(place_key, ctor_idx, dt_name)`. The first edge's `guard`
    /// is retained — using a possibly-narrower guard only makes the downstream
    /// `guard => is_constructor` assertion fire on FEWER models, never more, so it
    /// stays sound (may lose precision at merges, never adds an unsound constraint).
    fn intersect_variant_facts(incoming: &[IncomingEdge]) -> Vec<VariantFact> {
        let Some((first, rest)) = incoming.split_first() else {
            return Vec::new();
        };
        first
            .variant_facts
            .iter()
            .filter(|f| {
                rest.iter().all(|edge| {
                    edge.variant_facts.iter().any(|g| {
                        g.place_key == f.place_key
                            && g.ctor_idx == f.ctor_idx
                            && g.dt_name == f.dt_name
                    })
                })
            })
            .cloned()
            .collect()
    }

    /// Compute SSA phi node for a variable with multiple incoming definitions.
    ///
    /// REQUIRES: incoming is non-empty
    /// ENSURES: Returns Some if at least one incoming edge has a value for var_name
    /// ENSURES: Result sort matches the first incoming value's sort
    /// ENSURES: If all incoming values are identical, returns that value directly
    /// ENSURES: Otherwise, creates ITE chain selecting based on edge predicates
    fn compute_phi_for_var(&mut self, var_name: &str, incoming: &[IncomingEdge]) -> Option<Expr> {
        debug!("compute_phi_for_var {}: {} incoming edges", var_name, incoming.len());
        let mut incoming_vals: Vec<(Option<Expr>, Expr)> = Vec::with_capacity(incoming.len());
        let mut missing_incoming = false;
        for edge in incoming {
            if let Some(val) = edge.env.get(var_name) {
                incoming_vals.push((edge.edge_predicate.clone(), val.clone()));
            } else {
                missing_incoming = true;
            }
        }

        {
            let first_val = &incoming_vals.first()?.1;
            if !missing_incoming && incoming_vals.iter().all(|(_, v)| v == first_val) {
                debug!("compute_phi_for_var {}: all incoming values identical", var_name);
                return Some(first_val.clone());
            }
        }

        let signed = self.signedness_from_base_name(var_name);

        // #749: Harmonize sorts before creating ITE chain.
        // Different codegen paths can produce different sorts for the same variable:
        // - BigInt operations return Int (via get_bigint_value/sort_inference)
        // - Some fallback paths may return BitVec(32)
        // Convert all to a common sort (Int) to avoid ITE sort mismatch panic.
        let (target_sort, incoming_vals) = Self::harmonize_incoming_sorts(incoming_vals, signed);
        for (_, value) in &incoming_vals {
            self.declare_fresh_fallback_var_if_needed(value);
        }
        // Verify we have at least one incoming value after harmonization
        let _ = incoming_vals.first()?;

        let phi_name = self.ssa_name_from_base(var_name, true);
        let phi_var = self.ctx.declare_var(&phi_name, target_sort);

        // Compute value_guard before consuming incoming_vals via into_iter.
        // Use references to avoid cloning each edge predicate.
        let value_guard = if missing_incoming {
            Self::or_edge_predicates_ref(incoming_vals.iter().map(|(cond, _)| cond.as_ref()))
        } else {
            self.current_path_condition.clone()
        };

        // Consume incoming_vals via into_iter().rev() to avoid cloning each (cond, val) pair
        let mut iter = incoming_vals.into_iter().rev();
        let Some((_, mut ite_expr)) = iter.next() else { return Some(phi_var) };
        for (cond, val) in iter {
            let pred = cond.unwrap_or_else(|| Expr::bool_const(true));
            ite_expr = Expr::ite(pred, val, ite_expr);
        }

        // SMT-LIB requires same-width operands for equality, so coerce widths.
        // Use signedness-aware coercion to preserve Rust cast semantics (#265).
        let (phi_coerced, ite_coerced) = match signed {
            Some(signed) => Self::coerce_to_match_widths_typed(phi_var.clone(), ite_expr, signed),
            None => {
                match self.coerce_to_match_widths_untyped(phi_var.clone(), ite_expr, var_name) {
                    Some(pair) => pair,
                    None => return Some(phi_var),
                }
            }
        };
        match value_guard {
            None => self.ctx.assert(phi_coerced.eq(ite_coerced)),
            Some(guard) => {
                // Keep phi definitions total under guarded reachability:
                // when the block guard is false, preserve a stable symbolic pre-state value.
                let else_expr = self.get_or_declare_ssa_init_symbol(var_name, ite_coerced.sort());
                self.ctx.assert(phi_coerced.eq(Expr::ite(guard, ite_coerced, else_expr)));
            }
        }

        Some(phi_var)
    }

    /// OR-combine optional edge predicates. Returns `None` if any predicate
    /// is unconditional (`None`). Accepts references to avoid cloning each
    /// predicate from the caller's collection.
    fn or_edge_predicates_ref<'e>(
        conds: impl IntoIterator<Item = Option<&'e Expr>>,
    ) -> Option<Expr> {
        let mut combined = Some(Expr::bool_const(false));
        for cond in conds {
            match (combined, cond) {
                (None, _) | (_, None) => return None,
                (Some(a), Some(b)) => combined = Some(a.or(b.clone())),
            }
        }
        combined
    }
}

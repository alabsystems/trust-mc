// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dead-argument elimination for CHC verification conditions.
//!
//! MIR-level encoding creates state variables for all local types and metadata
//! arrays, many of which are never read. This pass strips arguments from
//! relation declarations that appear only in identity copies (passthrough),
//! reducing predicate arity and helping PDR converge on loop invariants.
//!
//! ## Algorithm
//!
//! Uses a three-phase analysis:
//!
//! 1. **Classify constraints + BFS reachability**: Separate "anchored" variables
//!    (those appearing in non-transfer constraints like arithmetic, comparisons,
//!    equality with constants) from "transfer edges" (variable-to-variable
//!    equalities that propagate values between state variables). Then BFS from
//!    anchored variables through transfer edges to find all reachable variables.
//!
//! 2. **Position-based liveness with cross-relation propagation**: For each
//!    relation argument position, collect all variable names that appear at
//!    that position across all rules. A position is initially live if ANY of
//!    those names is in the reachable set. Then, liveness propagates
//!    transitively across relations via transfer edges: when a rule connects
//!    position P of the body relation to position Q of the head relation via
//!    a transfer edge, liveness at either position propagates to the other.
//!    This prevents over-stripping when a variable is relayed through an
//!    intermediate block without being used in real constraints (fix: #3151).
//!
//! 3. **Position-based stripping**: Positions that are dead after propagation
//!    are removed from relation declarations and all rule references.
//!
//! ## Why no dead-end pruning
//!
//! An earlier version (W1:3371) included a dead-end pruning phase that removed
//! transfer-chain variables touching only one anchored neighbor. This caused
//! false CTREX in 9 struct harnesses (ay_watched, ay_literal) because it didn't
//! account for cross-block value propagation: a variable like `_5_fld0__out` in
//! bb0 and `_5_fld0` in bb_K share a relation position but have no explicit
//! transfer edge between them. Dead-end pruning removed both chains
//! independently, losing the struct field value across the block boundary.
//! Fix: Part of #3148.
//!
//! Part of #112: CHC encoding step granularity.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};

use crate::chc::{ChcVc, RelationApp};

#[path = "chc_optimize_collect.rs"]
mod collect;
use collect::collect_var_names;

#[path = "chc_optimize_dead_scalars.rs"]
mod dead_scalars;

#[path = "chc_optimize_dead_vars.rs"]
mod dead_vars;

#[path = "chc_normalize_free_arrays.rs"]
mod normalize_free_arrays;

/// Strips dead arguments from all relations in a CHC VC.
///
/// Returns the total number of argument positions stripped across all relations.
pub fn strip_dead_args(vc: &mut ChcVc) -> usize {
    // Step 1: Collect variable names used in real constraints, with BFS
    // expansion through transfer edges.
    let constrained = collect_constrained_vars(vc);

    // Step 2: For each relation, identify which argument positions are dead
    // using position-based liveness (checks all var names at each position).
    let dead_positions = identify_dead_positions(vc, &constrained);

    // Step 3: Apply stripping to declarations and all rule references.
    apply_stripping(vc, &dead_positions)
}

/// Collects variable names that are "constrained" — either anchored directly
/// by non-transfer constraints or reachable through transfer edges from
/// anchored variables.
///
/// Phase 1: Classify each constraint as either anchoring its variables (real
/// computation) or as a transfer edge (variable-to-variable equality).
///
/// Phase 2: BFS from anchored variables through transfer edges. All reachable
/// variables are considered constrained (see module docs "Why no dead-end
/// pruning").
fn collect_constrained_vars(vc: &ChcVc) -> HashSet<String> {
    // Phase 1: Classify constraints.
    let mut anchored = HashSet::new();
    let mut transfers: Vec<(String, String)> = Vec::new();
    for rule in &vc.rules {
        for expr in &rule.body.constraints {
            classify_constraint(expr, &mut anchored, &mut transfers);
        }
    }

    // Phase 2: BFS from anchored variables through transfer edges.
    let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for (a, b) in &transfers {
        adj.entry(a.as_str()).or_default().push(b.as_str());
        adj.entry(b.as_str()).or_default().push(a.as_str());
    }

    let mut queue: VecDeque<String> = anchored.iter().cloned().collect();
    let mut reachable = anchored;
    while let Some(var) = queue.pop_front() {
        if let Some(neighbors) = adj.get(var.as_str()) {
            for &neighbor in neighbors {
                if !reachable.contains(neighbor) {
                    let owned = neighbor.to_string();
                    reachable.insert(owned.clone());
                    queue.push_back(owned);
                }
            }
        }
    }

    reachable
}

/// Classifies a constraint expression as either anchoring its variables or
/// recording a transfer edge.
///
/// Variable-to-variable equalities `(= Var1 Var2)` are transfer edges —
/// they propagate values between state variables rather than performing
/// real computation. All other expressions anchor their variables.
fn classify_constraint(
    expr: &Expr,
    anchored: &mut HashSet<String>,
    transfers: &mut Vec<(String, String)>,
) {
    if let ExprValue::Eq(lhs, rhs) = expr.value() {
        if let (ExprValue::Var { name: lhs_name }, ExprValue::Var { name: rhs_name }) =
            (lhs.value(), rhs.value())
        {
            transfers.push((lhs_name.clone(), rhs_name.clone()));
            return;
        }
    }
    collect_var_names(expr, anchored);
}

/// Identifies dead argument positions for each relation using position-based
/// liveness analysis with cross-relation propagation.
///
/// For each relation and argument position, collects ALL variable names that
/// appear at that position across all rules (heads and bodies). A position is
/// initially live if ANY of those names is in the reachable set.
///
/// Then, liveness is propagated transitively across relations: when a rule
/// has a transfer edge `(= var_a var_b)` connecting position P of the body
/// relation to position Q of the head relation, liveness at either position
/// propagates to the other. This prevents over-stripping when a variable is
/// only "passed through" an intermediate block via transfer edges but is
/// anchored in upstream/downstream blocks.
///
/// Returns a map from relation name to a boolean mask where `true` means dead.
fn identify_dead_positions(
    vc: &ChcVc,
    constrained: &HashSet<String>,
) -> HashMap<String, Vec<bool>> {
    // Collect all variable names at each position for each relation.
    let position_names = collect_position_names(vc);

    // Step 1: Compute initial per-relation liveness.
    let mut live_map: HashMap<String, Vec<bool>> = HashMap::new();
    for rel in &vc.relations {
        let names_at_positions = match position_names.get(&*rel.name) {
            Some(names) => names,
            None => continue,
        };
        if names_at_positions.len() != rel.arg_sorts.len() {
            continue;
        }

        let live: Vec<bool> = names_at_positions
            .iter()
            .map(|names| names.iter().any(|n| constrained.contains(n)))
            .collect();
        live_map.insert(rel.name.clone(), live);
    }

    // Step 2: Build cross-relation position links via transfer edges.
    // For each rule, map variable names to their positions in body/head
    // relation apps, then record links between positions connected by
    // transfer edges. This enables liveness propagation across blocks.
    let links = build_cross_relation_links(vc);

    // Step 3: Propagate liveness through links (BFS from live positions).
    if !links.is_empty() {
        propagate_liveness(&mut live_map, &links);
    }

    // Convert live_map to dead_map.
    let mut dead_map = HashMap::new();
    for (name, live) in &live_map {
        let dead: Vec<bool> = live.iter().map(|&l| !l).collect();
        if dead.iter().any(|&d| d) {
            dead_map.insert(name.clone(), dead);
        }
    }

    dead_map
}

/// A position in a relation: (relation_name, argument_index).
type RelPos = (String, usize);

/// Builds cross-relation position links from transfer edges in rules.
///
/// For each rule with body relation R_body and head relation R_head, examines
/// transfer edges `(= var_a var_b)`. If var_a is at position i of one relation
/// and var_b is at position j of another, records a link between the two
/// positions.
fn build_cross_relation_links(vc: &ChcVc) -> Vec<(RelPos, RelPos)> {
    let mut links: Vec<(RelPos, RelPos)> = Vec::new();

    for rule in &vc.rules {
        // Collect transfer edges from this rule.
        let mut transfers: Vec<(String, String)> = Vec::new();
        for expr in &rule.body.constraints {
            if let ExprValue::Eq(lhs, rhs) = expr.value() {
                if let (ExprValue::Var { name: a }, ExprValue::Var { name: b }) =
                    (lhs.value(), rhs.value())
                {
                    transfers.push((a.clone(), b.clone()));
                }
            }
        }
        if transfers.is_empty() {
            continue;
        }

        // Build var_name → [(relation_name, position)] for this rule.
        let mut var_positions: HashMap<&str, Vec<(String, usize)>> = HashMap::new();
        if let Some(ref body_rel) = rule.body.relation {
            for (i, arg) in body_rel.args.iter().enumerate() {
                if let ExprValue::Var { name } = arg.value() {
                    var_positions
                        .entry(name.as_str())
                        .or_default()
                        .push((body_rel.name.to_string(), i));
                }
            }
        }
        for (i, arg) in rule.head.args.iter().enumerate() {
            if let ExprValue::Var { name } = arg.value() {
                var_positions
                    .entry(name.as_str())
                    .or_default()
                    .push((rule.head.name.to_string(), i));
            }
        }

        // Connect positions via transfer edges.
        for (a, b) in &transfers {
            let a_positions = var_positions.get(a.as_str());
            let b_positions = var_positions.get(b.as_str());
            if let (Some(a_pos), Some(b_pos)) = (a_positions, b_positions) {
                for ap in a_pos {
                    for bp in b_pos {
                        if ap != bp {
                            links.push((ap.clone(), bp.clone()));
                        }
                    }
                }
            }
        }
    }

    links
}

/// Propagates liveness through cross-relation links using BFS.
///
/// Starting from all initially-live positions, follows links bidirectionally
/// to mark connected positions as live. This ensures that a variable "passed
/// through" an intermediate block (only in transfer edges) is kept alive if
/// it's anchored in any upstream or downstream block.
fn propagate_liveness(live_map: &mut HashMap<String, Vec<bool>>, links: &[(RelPos, RelPos)]) {
    // Build adjacency list for BFS.
    let mut adj: HashMap<(String, usize), Vec<(String, usize)>> = HashMap::new();
    for (a, b) in links {
        adj.entry(a.clone()).or_default().push(b.clone());
        adj.entry(b.clone()).or_default().push(a.clone());
    }

    // Seed BFS with all initially-live positions.
    let mut queue: VecDeque<(String, usize)> = VecDeque::new();
    let mut visited: HashSet<(String, usize)> = HashSet::new();
    for (rel_name, live_vec) in live_map.iter() {
        for (pos, &is_live) in live_vec.iter().enumerate() {
            if is_live {
                let key = (rel_name.clone(), pos);
                if visited.insert(key.clone()) {
                    queue.push_back(key);
                }
            }
        }
    }

    // BFS propagation.
    while let Some(current) = queue.pop_front() {
        if let Some(neighbors) = adj.get(&current) {
            for neighbor in neighbors {
                if visited.insert(neighbor.clone()) {
                    // Mark this position as live.
                    if let Some(live_vec) = live_map.get_mut(&neighbor.0) {
                        if let Some(pos) = live_vec.get_mut(neighbor.1) {
                            *pos = true;
                        }
                    }
                    queue.push_back(neighbor.clone());
                }
            }
        }
    }
}

/// Collects all variable names that appear at each argument position for each
/// relation, across all rules (both heads and bodies).
fn collect_position_names(vc: &ChcVc) -> HashMap<String, Vec<HashSet<String>>> {
    let mut result: HashMap<String, Vec<HashSet<String>>> = HashMap::new();

    for rule in &vc.rules {
        update_position_names(&mut result, &rule.head);
        if let Some(ref rel) = rule.body.relation {
            update_position_names(&mut result, rel);
        }
    }
    result
}

/// Updates the position-name map with variable names from a relation application.
fn update_position_names(map: &mut HashMap<String, Vec<HashSet<String>>>, app: &RelationApp) {
    let entry =
        map.entry(app.name.to_string()).or_insert_with(|| vec![HashSet::new(); app.args.len()]);
    // Ensure the entry has enough positions (in case different rules have
    // different apparent arities due to encoding quirks).
    while entry.len() < app.args.len() {
        entry.push(HashSet::new());
    }
    for (i, arg) in app.args.iter().enumerate() {
        if let ExprValue::Var { name } = arg.value() {
            entry[i].insert(name.clone());
        }
    }
}

/// Applies dead-position stripping to declarations and all rule references.
///
/// Returns the total number of argument positions removed.
fn apply_stripping(vc: &mut ChcVc, dead_positions: &HashMap<String, Vec<bool>>) -> usize {
    let mut total_stripped = 0;

    // Strip relation declarations.
    for rel in &mut vc.relations {
        if let Some(dead) = dead_positions.get(&rel.name) {
            let count_before = rel.arg_sorts.len();
            let mut i = 0;
            rel.arg_sorts.retain(|_| {
                let keep = !dead[i];
                i += 1;
                keep
            });
            total_stripped += count_before - rel.arg_sorts.len();
        }
    }

    // Strip rule heads and bodies.
    for rule in &mut vc.rules {
        strip_relation_app(&mut rule.head, dead_positions);
        if let Some(ref mut rel) = rule.body.relation {
            strip_relation_app(rel, dead_positions);
        }
    }

    total_stripped
}

/// Strips dead argument positions from a single `RelationApp`.
fn strip_relation_app(app: &mut RelationApp, dead_positions: &HashMap<String, Vec<bool>>) {
    let name_str: &str = &app.name;
    if let Some(dead) = dead_positions.get(name_str) {
        let old_args = Arc::unwrap_or_clone(Arc::clone(&app.args));
        let new_args: Vec<Expr> = old_args
            .into_iter()
            .zip(dead.iter())
            .filter(|(_, is_dead)| !*is_dead)
            .map(|(expr, _)| expr)
            .collect();
        app.args = Arc::new(new_args);
    }
}

impl ChcVc {
    /// Strips dead arguments from all relations in this VC.
    ///
    /// Delegates to [`strip_dead_args`] — see module docs for details.
    pub fn strip_dead_args(&mut self) -> usize {
        strip_dead_args(self)
    }

    /// Prunes dead identity-passthrough scalar state variables.
    ///
    /// Safe to call multiple times (e.g., after constant propagation
    /// eliminates rules, making previously-live scalars dead).
    pub fn prune_dead_identity_scalars(&mut self) -> usize {
        dead_scalars::prune_dead_identity_scalars(self)
    }

    /// Prunes dead constraints and stale declare-var entries.
    ///
    /// Correctness-preserving: error/query-headed rules (including BSEM-18
    /// per-property `error_p{N}` heads) are protected rule-locally, and only
    /// definitional variable equalities fully disconnected from the
    /// transitive liveness closure are removed, then declare-var entries for
    /// unreferenced vars are pruned.
    pub fn prune_dead_vars_and_constraints(&mut self) -> usize {
        dead_vars::prune_dead_vars_and_constraints(self)
    }

    /// Normalizes free-variable array bases in store chains to `const_array`.
    ///
    /// Enables the scalarizer to handle store chains whose base is a
    /// universally-quantified free variable (e.g., `__chc_array_N`).
    /// Should run in the emit pipeline before the second-pass scalarizer.
    pub fn normalize_free_array_bases(&mut self) -> usize {
        normalize_free_arrays::normalize_free_array_bases(self)
    }
}

#[cfg(test)]
#[path = "chc_optimize_tests.rs"]
mod tests;

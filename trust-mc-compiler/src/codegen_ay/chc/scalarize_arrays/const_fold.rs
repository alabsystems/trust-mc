// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Invariant array constant folding for read-only arrays.
//!
//! Arrays that are never stored to in transition rules and have all
//! constant-index selects with known values from the entry rule can be
//! eliminated entirely by inlining the constant values and removing the
//! array from relation signatures.
//!
//! Part of #4050: PDR array-param bottleneck optimization.

use std::collections::{BTreeMap, HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort};
use trust_mc_core::chc::ChcVc;

use super::{ArrayUse, classify_constraint_for_array, try_extract_const_idx};

/// Information about a read-only array that can be constant-folded.
///
/// These arrays are constrained only in the entry rule (no body relation),
/// never stored to in transition rules, and have all constant indices.
/// They can be eliminated entirely from relation signatures by inlining
/// the constant values directly.
pub(super) struct ConstFoldInfo {
    /// The input variable name (e.g., `obj_size`).
    pub(super) input_name: String,
    /// The output variable name (e.g., `obj_size__out`).
    pub(super) output_name: String,
    /// The constant map: index → constant value expression.
    pub(super) const_map: BTreeMap<super::ConstIdx, Expr>,
    /// When set, the array is initialized to `const_array(K, uniform_default)`
    /// in every assignment (entry or transition) and is never stored to.
    /// Any `select(arr, idx)` — constant or symbolic — folds to `uniform_default`.
    /// Part of #4097 (hashmap_contains): rescues arrays that have only symbolic
    /// selects after a const-array init, where the per-index `const_map` is empty.
    pub(super) uniform_default: Option<Expr>,
}

/// Identify read-only arrays eligible for constant folding or elimination.
///
/// An array is eligible if:
/// 1. All Select/Store operations use constant indices (or no selects at all)
/// 2. The output var appears ONLY in identity constraints (`out = in`)
///    or not at all in transition rules (rules with a body relation)
///
/// Three sub-cases:
/// - **Constant folding**: entry rule has pointwise or bulk const_array constraints
///   → inline constant values at select sites and remove from relations
/// - **Dead elimination**: array is never selected and never stored
///   → just remove from relations (zero-index read-only arrays)
///
/// Both cases use the same `apply_const_folding` infrastructure.
pub(super) fn identify_const_foldable_arrays(vc: &ChcVc) -> Vec<ConstFoldInfo> {
    let mut input_vars: HashMap<String, Sort> = HashMap::new();
    for v in vc.vars() {
        if v.sort.is_array() && !v.name.ends_with("__out") {
            input_vars.insert(v.name.to_string(), v.sort.clone());
        }
    }

    // Pre-extract entry-rule default values for const_array-initialized arrays.
    // Used to detect identity stores: store(arr, idx, default_val) == arr.
    let entry_defaults = extract_entry_defaults(vc, &input_vars);
    // Part of #4097: also collect const_array defaults assigned in transition rules
    // (e.g., HashMap::new sets `present__out = const_array(K, false)` in the rule
    // for the block that contains it). Used for the uniform-default fold path that
    // allows folding away arrays whose only reads are symbolic-index selects.
    let uniform_defaults = extract_uniform_defaults(vc, &input_vars);
    let select_usage = collect_select_usage(vc);
    let constraint_var_sets = collect_constraint_var_sets(vc);

    let mut result = Vec::new();
    for (input_name, _sort) in &input_vars {
        let output_name = format!("{input_name}__out");

        if whole_input_escapes_to_live_output_copy(vc, input_name, &output_name) {
            continue;
        }

        // Check: all selects must be constant-indexed (or absent).
        // Part of #4097: relaxed when a uniform default is known across all
        // const-array initializations — symbolic selects then fold to the default.
        let all_const_select = !select_usage.invalid_select_vars.contains(input_name.as_str());
        let has_uniform_default = uniform_defaults.contains_key(input_name.as_str());
        if !all_const_select && !has_uniform_default {
            continue;
        }
        let mut has_non_identity_store = false;

        for (rule_idx, rule) in vc.rules.iter().enumerate() {
            let is_transition = rule.body.relation.is_some();

            for (constraint_idx, constraint) in rule.body.constraints.iter().enumerate() {
                let vars = &constraint_var_sets[rule_idx][constraint_idx];

                // For transition rules, check if output is used non-trivially
                if is_transition && vars.contains(output_name.as_str()) {
                    let classification = classify_constraint_for_array(
                        constraint,
                        input_name,
                        &output_name,
                        &input_vars,
                    );
                    match classification {
                        ArrayUse::StoreChain { stores, .. } => {
                            // If the array is initialized as const_array(V) and
                            // every store writes V, the store is identity:
                            // store(const_array(V), idx, V) == const_array(V).
                            let baseline_default = entry_defaults
                                .get(input_name.as_str())
                                .or_else(|| uniform_defaults.get(input_name.as_str()));
                            if let Some(default_val) = baseline_default {
                                let all_stores_are_default =
                                    stores.iter().all(|(_, val)| val == default_val);
                                if !all_stores_are_default {
                                    has_non_identity_store = true;
                                }
                            } else {
                                has_non_identity_store = true;
                            }
                        }
                        ArrayUse::ConstArrayInit => {
                            // Part of #4097: a const_array init in a transition rule
                            // is permitted when it matches the uniform default — the
                            // array remains semantically read-only with that default.
                            if !matches_uniform_default(
                                constraint,
                                input_name,
                                &output_name,
                                &uniform_defaults,
                            ) {
                                has_non_identity_store = true;
                            }
                        }
                        ArrayUse::ExplicitIdentity { base } if base == *input_name => {}
                        ArrayUse::ExplicitIdentity { .. } => {
                            has_non_identity_store = true;
                        }
                        ArrayUse::NotRelated => {}
                        ArrayUse::Unrecognized => {
                            has_non_identity_store = true;
                        }
                    }
                }
            }

            if has_non_identity_store {
                break;
            }
        }

        // Write-only arrays: stores but zero selects. Values are written
        // but never read — safe to eliminate entirely. Must check for ANY
        // select (including symbolic-index) — collect_all_select_indices
        // only finds constant-index selects.
        if has_non_identity_store {
            if !select_usage.has_any_select_vars.contains(input_name.as_str()) {
                result.push(ConstFoldInfo {
                    input_name: input_name.clone(),
                    output_name,
                    const_map: BTreeMap::new(),
                    uniform_default: None,
                });
            }
            continue;
        }

        let uniform_default = uniform_defaults.get(input_name.as_str()).cloned();

        // Extract constant map from entry rule(s).
        let select_indices = select_usage
            .const_indices_by_var
            .get(input_name.as_str())
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let const_map = extract_entry_const_map(vc, input_name, select_indices);
        if const_map.is_empty() && uniform_default.is_none() {
            if !select_indices.is_empty() {
                continue;
            }
            // Truly dead: no selects, no stores, only identity passthrough.
        }

        result.push(ConstFoldInfo {
            input_name: input_name.clone(),
            output_name,
            const_map,
            uniform_default,
        });
    }
    result
}

fn collect_constraint_var_sets(vc: &ChcVc) -> Vec<Vec<HashSet<String>>> {
    vc.rules
        .iter()
        .map(|rule| rule.body.constraints.iter().map(collect_expr_vars).collect())
        .collect()
}

fn collect_expr_vars(expr: &Expr) -> HashSet<String> {
    let mut vars = HashSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } => {
                vars.insert(name.clone());
            }
            _ => stack.extend(node.children()),
        }
    }
    vars
}

fn whole_input_escapes_to_live_output_copy(vc: &ChcVc, input: &str, output: &str) -> bool {
    let live_outputs = live_output_array_args(vc);
    vc.rules
        .iter()
        .filter(|rule| rule.body.relation.is_some())
        .flat_map(|rule| rule.body.constraints.iter())
        .any(|constraint| {
            let mut stack = vec![constraint];
            while let Some(expr) = stack.pop() {
                match expr.value() {
                    ExprValue::And(conjuncts) => stack.extend(conjuncts.iter()),
                    ExprValue::Eq(lhs, rhs) => {
                        if is_live_cross_array_copy(lhs, rhs, input, output, &live_outputs)
                            || is_live_cross_array_copy(rhs, lhs, input, output, &live_outputs)
                        {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
            false
        })
}

fn live_output_array_args(vc: &ChcVc) -> HashSet<String> {
    vc.rules
        .iter()
        .flat_map(|rule| rule.head.args.iter())
        .filter_map(|arg| match arg.value() {
            ExprValue::Var { name } if arg.sort().is_array() && name.ends_with("__out") => {
                Some(name.clone())
            }
            _ => None,
        })
        .collect()
}

fn is_live_cross_array_copy(
    maybe_output: &Expr,
    maybe_input: &Expr,
    input: &str,
    output: &str,
    live_outputs: &HashSet<String>,
) -> bool {
    let ExprValue::Var { name: copied_input } = maybe_input.value() else {
        return false;
    };
    let ExprValue::Var { name: copied_output } = maybe_output.value() else {
        return false;
    };
    copied_input == input && copied_output != output && live_outputs.contains(copied_output)
}

/// Extract the constant map from entry rule constraints.
///
/// Entry rules have no body relation. Handles two patterns:
///
/// 1. **Pointwise**: `(= (select input_var #xN) #xM)` — one entry per constraint
/// 2. **Bulk**: `(= input_var const_array(val))` or `(= input_var store(...const_array(val)...))`
///    — provides a default value for ALL indices, with optional per-index overrides
///
/// For bulk patterns, the const_map is populated by collecting all Select
/// indices used across the entire VC and mapping them to the default value
/// (or store-chain override).
///
/// Entry rules store constraints as a single `And(And(...))` tree,
/// so this function flattens the conjunction before scanning.
fn extract_entry_const_map(
    vc: &ChcVc,
    input_name: &str,
    select_indices: &[super::ConstIdx],
) -> BTreeMap<super::ConstIdx, Expr> {
    let mut const_map = BTreeMap::new();
    let mut default_value: Option<Expr> = None;
    let mut store_overrides: Vec<(super::ConstIdx, Expr)> = Vec::new();

    for rule in &vc.rules {
        // Only entry rules (no body relation)
        if rule.body.relation.is_some() {
            continue;
        }

        for constraint in rule.body.constraints.iter() {
            // Flatten nested And trees and scan each conjunct.
            let mut stack = vec![constraint];
            while let Some(node) = stack.pop() {
                match node.value() {
                    ExprValue::And(conjuncts) => {
                        stack.extend(conjuncts.iter());
                    }
                    _ => {
                        // Try pointwise: (= (select arr idx) val)
                        if let Some((idx, value)) = extract_select_eq_const(node, input_name) {
                            const_map.insert(idx, value);
                            continue;
                        }
                        // Try bulk: (= arr const_array(val)) or (= arr store_chain_on_const_array)
                        if let Some((def_val, overrides)) =
                            extract_const_array_init(node, input_name)
                        {
                            default_value = Some(def_val);
                            store_overrides = overrides;
                        }
                    }
                }
            }
        }
    }

    // If pointwise extraction found entries, use those.
    if !const_map.is_empty() {
        return const_map;
    }

    // If bulk const_array init was found, build const_map from select indices.
    if let Some(default_val) = default_value {
        if select_indices.is_empty() {
            // Array is declared but never selected — can still be folded
            // (removal from relations is the benefit).
            return const_map;
        }

        // Build override map for quick lookup.
        let mut override_map: BTreeMap<super::ConstIdx, Expr> = BTreeMap::new();
        for (idx, val) in store_overrides {
            override_map.insert(idx, val);
        }

        // Populate const_map: each select index → override value or default.
        for idx in select_indices {
            let value = override_map.get(idx).cloned().unwrap_or_else(|| default_val.clone());
            const_map.insert(idx.clone(), value);
        }
    }

    const_map
}

/// Try to extract `(= var const_array(val))` or `(= var store_chain_on_const_array)`
/// from an equality constraint in an entry rule.
///
/// Returns `Some((default_value, store_overrides))` if the pattern matches.
fn extract_const_array_init(
    expr: &Expr,
    target_var: &str,
) -> Option<(Expr, Vec<(super::ConstIdx, Expr)>)> {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return None;
    };

    if let Some(result) = try_const_array_init_pair(lhs, rhs, target_var) {
        return Some(result);
    }
    try_const_array_init_pair(rhs, lhs, target_var)
}

fn try_const_array_init_pair(
    var_side: &Expr,
    val_side: &Expr,
    target_var: &str,
) -> Option<(Expr, Vec<(super::ConstIdx, Expr)>)> {
    let ExprValue::Var { name } = var_side.value() else {
        return None;
    };
    if name != target_var {
        return None;
    }

    match val_side.value() {
        ExprValue::ConstArray { value, .. } => Some((value.clone(), Vec::new())),
        ExprValue::Store { .. } => {
            let (base, stores) = super::decompose_store_chain(val_side)?;
            if base != "__const_array__" {
                return None;
            }
            // Walk to the const_array base to extract the default value.
            let default_val = extract_const_array_default(val_side)?;
            Some((default_val, stores))
        }
        _ => None,
    }
}

/// Extract the default value for arrays initialized as `const_array(V)` in
/// entry rules. Used to detect identity stores: `store(arr, idx, V)` where
/// `V` equals the const_array default produces an array indistinguishable
/// from the input.
fn extract_entry_defaults<'a>(
    vc: &ChcVc,
    input_vars: &'a HashMap<String, Sort>,
) -> HashMap<&'a str, Expr> {
    let mut defaults = HashMap::new();
    for rule in &vc.rules {
        if rule.body.relation.is_some() {
            continue; // only entry rules
        }
        for constraint in rule.body.constraints.iter() {
            let mut stack = vec![constraint];
            while let Some(node) = stack.pop() {
                match node.value() {
                    ExprValue::And(conjuncts) => {
                        stack.extend(conjuncts.iter());
                    }
                    _ => {
                        for input_name in input_vars.keys() {
                            if defaults.contains_key(input_name.as_str()) {
                                continue;
                            }
                            if let Some((def_val, _)) = extract_const_array_init(node, input_name) {
                                defaults.insert(input_name.as_str(), def_val);
                            }
                        }
                    }
                }
            }
        }
    }
    defaults
}

/// Walk a store chain to the const_array base and extract its default value.
fn extract_const_array_default(expr: &Expr) -> Option<Expr> {
    match expr.value() {
        ExprValue::ConstArray { value, .. } => Some(value.clone()),
        ExprValue::Store { array, .. } => extract_const_array_default(array),
        _ => None,
    }
}

/// Part of #4097: Collect a "uniform default" for arrays that are initialized to
/// the same `const_array(K, V)` value across every assignment in the VC.
///
/// Scans both entry rules (`var = const_array(...)`) and transition rules
/// (`var__out = const_array(...)`). Returns a map only when ALL such
/// initialization sites for a given array share an identical default value.
/// If different defaults are observed for the same array, that array is
/// excluded — there is no single value that all reads collapse to.
fn extract_uniform_defaults<'a>(
    vc: &ChcVc,
    input_vars: &'a HashMap<String, Sort>,
) -> HashMap<&'a str, Expr> {
    let mut candidates: HashMap<&'a str, Option<Expr>> = HashMap::new();
    for input_name in input_vars.keys() {
        candidates.insert(input_name.as_str(), None);
    }
    let mut rejected: HashSet<&'a str> = HashSet::new();

    for rule in &vc.rules {
        for constraint in rule.body.constraints.iter() {
            let mut stack = vec![constraint];
            while let Some(node) = stack.pop() {
                if let ExprValue::And(conjuncts) = node.value() {
                    stack.extend(conjuncts.iter());
                    continue;
                }
                let Some((target, def_val)) = extract_any_const_array_init(node, input_vars) else {
                    continue;
                };
                if rejected.contains(target) {
                    continue;
                }
                let slot = candidates.get_mut(target).expect("target was inserted above");
                match slot {
                    None => *slot = Some(def_val),
                    Some(existing) if *existing == def_val => {}
                    Some(_) => {
                        rejected.insert(target);
                        *slot = None;
                    }
                }
            }
        }
    }

    candidates.into_iter().filter_map(|(k, v)| v.map(|val| (k, val))).collect()
}

/// Return the array variable name and const_array default for either
/// `(= var const_array(V))` or `(= var__out const_array(V))` (or a store chain
/// rooted at `const_array(V)`), where `var` (with or without the `__out`
/// suffix) is one of the tracked input arrays.
fn extract_any_const_array_init<'a>(
    expr: &Expr,
    input_vars: &'a HashMap<String, Sort>,
) -> Option<(&'a str, Expr)> {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return None;
    };
    if let Some(pair) = try_any_const_array_init_pair(lhs, rhs, input_vars) {
        return Some(pair);
    }
    try_any_const_array_init_pair(rhs, lhs, input_vars)
}

fn try_any_const_array_init_pair<'a>(
    var_side: &Expr,
    val_side: &Expr,
    input_vars: &'a HashMap<String, Sort>,
) -> Option<(&'a str, Expr)> {
    let ExprValue::Var { name } = var_side.value() else {
        return None;
    };
    let target = if let Some(input_key) = input_vars.get_key_value(name.as_str()) {
        input_key.0.as_str()
    } else {
        let stripped = name.strip_suffix("__out")?;
        input_vars.get_key_value(stripped)?.0.as_str()
    };
    let default = match val_side.value() {
        ExprValue::ConstArray { value, .. } => value.clone(),
        ExprValue::Store { .. } => extract_const_array_default(val_side)?,
        _ => return None,
    };
    Some((target, default))
}

/// Part of #4097: True when `constraint` is `(= out_var const_array(V))` (or a
/// store chain rooted at `const_array(V)`) and `V` equals the recorded uniform
/// default for the array.
fn matches_uniform_default(
    constraint: &Expr,
    input_name: &str,
    output_name: &str,
    uniform_defaults: &HashMap<&str, Expr>,
) -> bool {
    let Some(expected) = uniform_defaults.get(input_name) else {
        return false;
    };
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    matches_const_array_init_with_default(lhs, rhs, output_name, expected)
        || matches_const_array_init_with_default(rhs, lhs, output_name, expected)
}

fn matches_const_array_init_with_default(
    var_side: &Expr,
    val_side: &Expr,
    target_name: &str,
    expected: &Expr,
) -> bool {
    let ExprValue::Var { name } = var_side.value() else {
        return false;
    };
    if name != target_name {
        return false;
    }
    let observed = match val_side.value() {
        ExprValue::ConstArray { value, .. } => value.clone(),
        ExprValue::Store { .. } => match extract_const_array_default(val_side) {
            Some(v) => v,
            None => return false,
        },
        _ => return false,
    };
    observed == *expected
}

struct SelectUsageSummary {
    const_indices_by_var: HashMap<String, Vec<super::ConstIdx>>,
    invalid_select_vars: HashSet<String>,
    has_any_select_vars: HashSet<String>,
}

/// Collect Select usage for all variables in one VC walk.
///
/// A select is invalid for constant folding if its index is symbolic or if it
/// selects from a non-variable array expression that mentions the variable.
/// This preserves `collect_selects_on_var`'s conservative behavior without
/// scanning the whole VC once per array variable.
fn collect_select_usage(vc: &ChcVc) -> SelectUsageSummary {
    let mut indices_by_var: HashMap<String, HashSet<super::ConstIdx>> = HashMap::new();
    let mut invalid_select_vars = HashSet::new();
    let mut has_any_select_vars = HashSet::new();
    for rule in &vc.rules {
        for constraint in rule.body.constraints.iter() {
            let mut stack = vec![constraint];
            while let Some(node) = stack.pop() {
                match node.value() {
                    ExprValue::Select { array, index } => {
                        match array.value() {
                            ExprValue::Var { name } => {
                                has_any_select_vars.insert(name.clone());
                                if let Some(idx) = try_extract_const_idx(index) {
                                    indices_by_var.entry(name.clone()).or_default().insert(idx);
                                } else {
                                    invalid_select_vars.insert(name.clone());
                                }
                            }
                            _ => {
                                mark_vars_in_non_simple_select_array(
                                    array,
                                    &mut has_any_select_vars,
                                    &mut invalid_select_vars,
                                );
                            }
                        }
                        stack.push(index);
                    }
                    _ => {
                        stack.extend(node.children());
                    }
                }
            }
        }
    }

    let const_indices_by_var = indices_by_var
        .into_iter()
        .map(|(name, indices)| {
            let mut sorted: Vec<super::ConstIdx> = indices.into_iter().collect();
            sorted.sort();
            (name, sorted)
        })
        .collect();

    SelectUsageSummary { const_indices_by_var, invalid_select_vars, has_any_select_vars }
}

fn mark_vars_in_non_simple_select_array(
    expr: &Expr,
    has_any_select_vars: &mut HashSet<String>,
    invalid_select_vars: &mut HashSet<String>,
) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } => {
                has_any_select_vars.insert(name.clone());
                invalid_select_vars.insert(name.clone());
            }
            _ => stack.extend(node.children()),
        }
    }
}

/// Try to extract `(= (select var idx_const) value_const)` from an expression.
fn extract_select_eq_const(expr: &Expr, target_var: &str) -> Option<(super::ConstIdx, Expr)> {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return None;
    };

    // Try lhs = (select var idx), rhs = value
    if let Some((idx, val)) = try_select_const_pair(lhs, rhs, target_var) {
        return Some((idx, val));
    }
    // Try rhs = (select var idx), lhs = value
    try_select_const_pair(rhs, lhs, target_var)
}

fn try_select_const_pair(
    select_side: &Expr,
    value_side: &Expr,
    target_var: &str,
) -> Option<(super::ConstIdx, Expr)> {
    let ExprValue::Select { array, index } = select_side.value() else {
        return None;
    };
    let ExprValue::Var { name } = array.value() else {
        return None;
    };
    if name != target_var {
        return None;
    }
    let idx = try_extract_const_idx(index)?;
    Some((idx, value_side.clone()))
}

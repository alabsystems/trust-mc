// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Application phase of invariant array constant folding.
//!
//! Given [`ConstFoldInfo`] entries from the identification phase, rewrites
//! the VC to inline constants, drop defining constraints, and remove
//! folded arrays from relation signatures.
//!
//! Part of #4050: PDR array-param bottleneck optimization.

use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort, rebuild_with_children};
use tracing::debug;
use trust_mc_core::chc::{ChcVc, RelationApp};
use trust_mc_core::constraints::Constraints;

use super::const_fold::ConstFoldInfo;
use super::try_extract_const_idx;

/// Stack red-zone / segment sizes for `stacker::maybe_grow`, mirroring
/// ay-bindings `fold_expr` (#8414). Deep dyn-trait Store chains (Box/Rc<dyn>
/// heap+vtable encoding) overflow the native stack in this hand-written
/// recursive rewriter; growing onto a heap-backed segment is verdict-identical.
const FOLD_STACK_RED_ZONE: usize = 32 * 1024;
const FOLD_STACK_SIZE: usize = 1024 * 1024;

/// Apply constant folding for read-only invariant arrays.
///
/// For arrays that are never stored to in transition rules and have all
/// constant-index selects with known values from the entry rule, this pass:
/// 1. Replaces `(select arr idx)` with the constant value inline
/// 2. Removes the array from relation signatures
/// 3. Drops entry-rule constraints that defined the constant map
/// 4. Drops identity constraints `(= arr_out arr)` from transitions
///
/// Every candidate is re-validated by [`fold_preconditions_hold`] before any
/// rewriting: identification has blind spots (selects on the `__out` name,
/// selects at indices missing from `const_map`, store-chain overrides hiding
/// behind a `const_array` root), and folding such an array would either inline
/// a wrong value (false PROOF) or leave a residual read of an array whose
/// defining constraints were dropped (false CTREX). Candidates that fail the
/// check are skipped entirely — failing to fold is always sound.
pub(super) fn apply_const_folding(vc: &mut ChcVc, fold_infos: &[ConstFoldInfo]) {
    let fold_infos: Vec<&ConstFoldInfo> = fold_infos
        .iter()
        .filter(|info| {
            let ok = fold_preconditions_hold(vc, info);
            if !ok {
                debug!(
                    array = %info.input_name,
                    "CHC: fail closed — apply-time invariant check rejected const-folding \
                     (found a select or write that identification did not vet)"
                );
            }
            ok
        })
        .collect();
    if fold_infos.is_empty() {
        return;
    }

    let folded_inputs: HashMap<&str, usize> =
        fold_infos.iter().enumerate().map(|(i, info)| (info.input_name.as_str(), i)).collect();
    let folded_outputs: HashMap<&str, usize> =
        fold_infos.iter().enumerate().map(|(i, info)| (info.output_name.as_str(), i)).collect();
    // For read-only arrays `arr__out == arr` in every reachable state (vetted
    // above), so selects fold identically through either name. Folding the
    // `__out` name too prevents residual reads of an array that this pass
    // removes from relation signatures.
    let folded_select_arrays: HashMap<&str, usize> = folded_inputs
        .iter()
        .chain(folded_outputs.iter())
        .map(|(&name, &idx)| (name, idx))
        .collect();

    debug!(
        folded_arrays = fold_infos.len(),
        arrays = %fold_infos.iter().map(|i| format!("{}({}vals)", i.input_name, i.const_map.len())).collect::<Vec<_>>().join(", "),
        "CHC: constant-folding read-only arrays"
    );

    // Rewrite all rules.
    for rule in &mut vc.rules {
        let is_entry_rule = rule.body.relation.is_none();
        // Rewrite constraints: inline constants, drop array-defining constraints.
        // Entry rules use a single And(...) expression, so we flatten first.
        let old_constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        let mut flat_constraints = Vec::new();
        for c in &old_constraints {
            flatten_and_tree(c, &mut flat_constraints);
        }
        let mut new_constraints = Vec::new();
        for constraint in &flat_constraints {
            if should_drop_folded_constraint(
                constraint,
                &folded_inputs,
                &folded_outputs,
                is_entry_rule,
            ) {
                continue;
            }
            new_constraints.push(fold_selects_in_expr(
                constraint,
                &fold_infos,
                &folded_select_arrays,
            ));
        }
        rule.body.constraints = Constraints::Owned(new_constraints);

        // Remove folded arrays from relation applications.
        rule.head = remove_folded_args(&rule.head, &folded_inputs, &folded_outputs);
        if let Some(ref body_rel) = rule.body.relation {
            let new_body = remove_folded_args(body_rel, &folded_inputs, &folded_outputs);
            rule.body.relation = Some(new_body);
        }
    }

    // Rewrite relation declarations.
    let mut relation_sorts: HashMap<String, Vec<Sort>> = HashMap::new();
    for rule in &vc.rules {
        let name = rule.head.name.to_string();
        relation_sorts.entry(name).or_insert_with(|| {
            let sorts: Vec<Sort> = rule.head.args.iter().map(|a| a.sort().clone()).collect();
            sorts
        });
    }
    for rel in &mut vc.relations {
        if let Some(new_sorts) = relation_sorts.get(&rel.name) {
            rel.arg_sorts = new_sorts.clone();
        }
    }

    debug!(folded_arrays = fold_infos.len(), "CHC: invariant array constant folding complete");
}

/// Flatten nested `And(...)` expressions into a list of conjuncts.
fn flatten_and_tree(expr: &Expr, out: &mut Vec<Expr>) {
    match expr.value() {
        ExprValue::And(conjuncts) => {
            for c in conjuncts {
                flatten_and_tree(c, out);
            }
        }
        _ => out.push(expr.clone()),
    }
}

/// Check if a constraint should be dropped during constant folding.
///
/// Drops:
/// - `(= (select input #xN) val)` — entry rule pointwise constant definitions
/// - `(= input const_array(val))` — entry rule bulk constant initialization
/// - `(= input store(...const_array(val)...))` — entry rule bulk init with overrides
/// - `(= output input)` — identity passthroughs in transitions
fn should_drop_folded_constraint(
    constraint: &Expr,
    folded_inputs: &HashMap<&str, usize>,
    folded_outputs: &HashMap<&str, usize>,
    is_entry_rule: bool,
) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };

    // Drop `(= (select arr #xN) val)` — entry rule constant definitions.
    // ENTRY RULES ONLY (fail closed): the identical shape in a transition rule
    // is a READ, `(= x (select arr #xN))`, whose binding of `x` must be
    // preserved by folding the select to its constant — deleting the whole
    // conjunct would leave `x` unconstrained and let the solver fabricate
    // counterexample witnesses.
    if is_entry_rule
        && (is_folded_select(lhs, folded_inputs) || is_folded_select(rhs, folded_inputs))
    {
        return true;
    }

    // Drop `(= arr const_array(val))` or `(= arr store_chain_on_const_array)`
    // — entry rule bulk initialization constraints
    if is_folded_array_init(lhs, rhs, folded_inputs)
        || is_folded_array_init(rhs, lhs, folded_inputs)
    {
        return true;
    }

    // Part of #4097: drop transition-rule output initializations too:
    // `(= arr__out const_array(val))` — once the array is removed from the
    // relation signature, this assignment has no surviving lhs to constrain.
    if is_folded_array_init(lhs, rhs, folded_outputs)
        || is_folded_array_init(rhs, lhs, folded_outputs)
    {
        return true;
    }

    // Drop `(= arr_out arr_in)` — identity passthroughs
    if let (ExprValue::Var { name: n1 }, ExprValue::Var { name: n2 }) = (lhs.value(), rhs.value()) {
        if (folded_outputs.contains_key(n1.as_str()) && folded_inputs.contains_key(n2.as_str()))
            || (folded_outputs.contains_key(n2.as_str()) && folded_inputs.contains_key(n1.as_str()))
        {
            return true;
        }
    }

    false
}

/// Check if `(= var_side val_side)` is a folded array's const_array init.
fn is_folded_array_init(
    var_side: &Expr,
    val_side: &Expr,
    folded_inputs: &HashMap<&str, usize>,
) -> bool {
    let ExprValue::Var { name } = var_side.value() else {
        return false;
    };
    if !folded_inputs.contains_key(name.as_str()) {
        return false;
    }
    matches!(val_side.value(), ExprValue::ConstArray { .. } | ExprValue::Store { .. })
}

/// Detect `(select arr #xN)` for a folded array at a constant index — the
/// entry-rule pointwise constant-definition pattern that `apply_const_folding`
/// captures into `const_map`. Symbolic-index selects must NOT be reported here:
/// they are real loads that the caller-side `fold_selects_in_expr` will rewrite
/// to either the per-index constant or the `uniform_default` (#4097). Dropping
/// such a constraint would silently delete the binding for the LHS variable.
fn is_folded_select(expr: &Expr, folded_inputs: &HashMap<&str, usize>) -> bool {
    if let ExprValue::Select { array, index } = expr.value() {
        if let ExprValue::Var { name } = array.value() {
            if folded_inputs.contains_key(name.as_str())
                && super::try_extract_const_idx(index).is_some()
            {
                return true;
            }
        }
    }
    false
}

/// Replace `(select folded_arr idx)` with the constant from the map.
///
/// `folded_select_arrays` maps BOTH the input and `__out` names to the fold
/// info; read-only-ness (vetted by [`fold_preconditions_hold`]) makes the two
/// interchangeable for reads.
fn fold_selects_in_expr(
    expr: &Expr,
    fold_infos: &[&ConstFoldInfo],
    folded_select_arrays: &HashMap<&str, usize>,
) -> Expr {
    stacker::maybe_grow(FOLD_STACK_RED_ZONE, FOLD_STACK_SIZE, || match expr.value() {
        ExprValue::Select { array, index } => {
            if let ExprValue::Var { name } = array.value() {
                if let Some(&info_idx) = folded_select_arrays.get(name.as_str()) {
                    let info = fold_infos[info_idx];
                    if let Some(const_idx) = try_extract_const_idx(index) {
                        if let Some(value) = info.const_map.get(&const_idx) {
                            return value.clone();
                        }
                    }
                    // Part of #4097: a `const_map` miss (symbolic index, or a
                    // constant index identification never recorded) folds to
                    // the uniform default. `fold_preconditions_hold` has
                    // verified that the array provably holds the default at
                    // every index of every state this select can observe, so
                    // this is exact — not a guess.
                    if let Some(value) = &info.uniform_default {
                        return value.clone();
                    }
                    // Unreachable when preconditions hold: every select either
                    // hits `const_map` or the array has a verified uniform
                    // default. Keep the select intact (and loud in debug
                    // builds) rather than inventing a value.
                    debug_assert!(
                        false,
                        "const-fold select miss without uniform default on {name} — \
                         fold_preconditions_hold should have rejected this array"
                    );
                }
            }
            // Recurse into children
            let new_arr = fold_selects_in_expr(array, fold_infos, folded_select_arrays);
            let new_idx = fold_selects_in_expr(index, fold_infos, folded_select_arrays);
            new_arr.select(new_idx)
        }
        ExprValue::Eq(lhs, rhs) => {
            let new_lhs = fold_selects_in_expr(lhs, fold_infos, folded_select_arrays);
            let new_rhs = fold_selects_in_expr(rhs, fold_infos, folded_select_arrays);
            new_lhs.eq(new_rhs)
        }
        _ => {
            let children: Vec<&Expr> = expr.children().collect();
            if children.is_empty() {
                return expr.clone();
            }
            let rewritten: Vec<Expr> = children
                .iter()
                .map(|c| fold_selects_in_expr(c, fold_infos, folded_select_arrays))
                .collect();
            let any_changed = rewritten.iter().zip(children.iter()).any(|(new, old)| new != *old);
            if !any_changed {
                return expr.clone();
            }
            rebuild_with_children(expr, rewritten)
        }
    })
}

// ---------------------------------------------------------------------------
// Apply-time invariant validation (fail closed)
// ---------------------------------------------------------------------------

/// A select on a folded array that must fold through `uniform_default`.
struct UniformSelectSite {
    rule_idx: usize,
    /// The select reads the `__out` (post-state) name.
    on_output: bool,
}

/// Per-rule facts about how a rule constrains the folded array, collected
/// while checking that every whole-array constraint preserves uniformity.
#[derive(Default, Clone)]
struct UniformRuleFacts {
    /// `(= arr const_array(default))` (or a store chain of default values
    /// rooted at one) — pins the PRE-state / initial value.
    inits_input: bool,
    /// Same shape on `arr__out` — pins the POST-state.
    inits_output: bool,
    /// `(= arr__out arr)` (or `store(arr, i, default)` chains) — threads the
    /// pre-state value through to the post-state.
    has_identity: bool,
}

/// Recheck `identify_const_foldable_arrays`' preconditions directly against
/// the VC for one fold candidate, exactly mirroring what `apply_const_folding`
/// will do:
///
/// 1. Every conjunct mentioning the array either gets DROPPED by
///    `should_drop_folded_constraint` without losing information, or survives
///    with every mention being a `(select <var> idx)` that
///    [`fold_selects_in_expr`] rewrites. Any other residual mention (datatype
///    constructor capture, copy to a non-folded array, raw array equality,
///    composite select base, ...) would reference an array whose defining
///    constraints were dropped and which was removed from relation state —
///    i.e. a FREE array the solver can fill in at will (false CTREX).
/// 2. Selects that miss `const_map` fold to `uniform_default`, so the default
///    must actually be invariant: every whole-array constraint anywhere in
///    the VC must establish or preserve it (no store-chain overrides hiding
///    behind a `const_array` root), all `const_map` values must equal it, and
///    the uniform state must provably REACH each such select (a
///    `const_array(V)` init observed only in some transition rule says
///    nothing about reads of the entry havoc state).
///
/// Identification establishes a weaker, name-sensitive approximation of this
/// and never re-examines selects that miss `const_map` (#4097's unchecked
/// precondition). Any use this function cannot prove sound rejects the array
/// from folding — failing to fold is always sound.
fn fold_preconditions_hold(vc: &ChcVc, info: &ConstFoldInfo) -> bool {
    // Inlined `const_map` values must not themselves resurrect the array.
    if info.const_map.values().any(|value| expr_mentions_folded_array(value, info)) {
        return false;
    }

    // Pass 1: per-conjunct residual analysis.
    let mut uniform_sites: Vec<UniformSelectSite> = Vec::new();
    let mut output_const_sites: Vec<usize> = Vec::new();
    for (rule_idx, rule) in vc.rules.iter().enumerate() {
        let is_entry_rule = rule.body.relation.is_none();
        for constraint in rule.body.constraints.iter() {
            let mut conjuncts = Vec::new();
            flatten_and_tree(constraint, &mut conjuncts);
            for conjunct in &conjuncts {
                if !conjunct_folds_away(
                    conjunct,
                    info,
                    rule_idx,
                    is_entry_rule,
                    &mut uniform_sites,
                    &mut output_const_sites,
                ) {
                    return false;
                }
            }
        }
    }

    // `const_map`-hit reads of the POST-state name are only justified when the
    // rule ties the post-state to the (read-only) pre-state via an identity.
    if !output_const_sites.iter().all(|&rule_idx| rule_has_identity_pair(&vc.rules[rule_idx], info))
    {
        return false;
    }

    if uniform_sites.is_empty() {
        // All selects (if any) fold through `const_map`, whose entries are
        // backed by actual entry-rule constraints; read-only-ness for that
        // mode was vetted at identification on this same (unmutated) VC.
        return true;
    }

    let Some(default) = info.uniform_default.as_ref() else {
        return false;
    };
    // A const-hit select folding to W while a uniform-miss select folds to
    // V != W on the same array would be contradictory.
    if !info.const_map.values().all(|value| value == default) {
        return false;
    }
    uniform_default_reaches_all_sites(vc, info, default, &uniform_sites)
}

/// How `apply_const_folding` treats one flattened conjunct for this array.
enum DropKind {
    /// Dropped by `should_drop_folded_constraint` without losing information
    /// about anything the fold keeps alive.
    Dropped,
    /// Dropped by `should_drop_folded_constraint`, but the drop would lose
    /// information (e.g. an entry pointwise def whose value disagrees with
    /// what reads of that lane will fold to). Reject the array.
    InconsistentDrop,
    /// Survives into the folded VC.
    Kept,
}

fn conjunct_drop_kind(conjunct: &Expr, info: &ConstFoldInfo, is_entry_rule: bool) -> DropKind {
    let ExprValue::Eq(lhs, rhs) = conjunct.value() else {
        return DropKind::Kept;
    };

    // Entry pointwise defs: `(= (select arr #xN) val)`.
    if is_entry_rule {
        for (select_side, value_side) in [(lhs, rhs), (rhs, lhs)] {
            let Some(idx) = folded_input_const_select(select_side, info) else {
                continue;
            };
            // Dropping the def is information-preserving only when every read
            // of the lane folds back to exactly this value.
            let preserved = match info.const_map.get(&idx) {
                Some(mapped) => mapped == value_side,
                None => info.uniform_default.as_ref().is_some_and(|default| default == value_side),
            };
            return if preserved && !expr_mentions_folded_array(value_side, info) {
                DropKind::Dropped
            } else {
                DropKind::InconsistentDrop
            };
        }
    }

    // Bulk init / write definitions: `(= arr|arr__out const_array|store_chain)`.
    for (var_side, val_side) in [(lhs, rhs), (rhs, lhs)] {
        let Some(is_output) = folded_array_var(var_side, info) else {
            continue;
        };
        if matches!(val_side.value(), ExprValue::ConstArray { .. } | ExprValue::Store { .. }) {
            // A PRE-state definition in a transition rule constrains the state
            // arriving from the body relation; dropping it would erase a real
            // constraint instead of an initialization. Fail closed.
            return if is_output || is_entry_rule {
                DropKind::Dropped
            } else {
                DropKind::InconsistentDrop
            };
        }
    }

    // Identity passthrough `(= arr__out arr)`.
    if folded_array_var(lhs, info).is_some() && folded_array_var(rhs, info).is_some() {
        return DropKind::Dropped;
    }
    DropKind::Kept
}

/// `(select info.input_name #xN)` with a constant index.
fn folded_input_const_select(expr: &Expr, info: &ConstFoldInfo) -> Option<super::ConstIdx> {
    let ExprValue::Select { array, index } = expr.value() else {
        return None;
    };
    if !matches!(array.value(), ExprValue::Var { name } if *name == info.input_name) {
        return None;
    }
    try_extract_const_idx(index)
}

/// True when, after folding, this conjunct retains no reference to the array.
fn conjunct_folds_away(
    conjunct: &Expr,
    info: &ConstFoldInfo,
    rule_idx: usize,
    is_entry_rule: bool,
    uniform_sites: &mut Vec<UniformSelectSite>,
    output_const_sites: &mut Vec<usize>,
) -> bool {
    match conjunct_drop_kind(conjunct, info, is_entry_rule) {
        DropKind::Dropped => return true,
        DropKind::InconsistentDrop => return false,
        DropKind::Kept => {}
    }

    // Surviving conjunct: every mention of the array must be the base of a
    // `(select <var> idx)` the fold rewrites.
    let mut stack = vec![conjunct];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Select { array, index }
                if matches!(
                    array.value(),
                    ExprValue::Var { name }
                        if *name == info.input_name || *name == info.output_name
                ) =>
            {
                let on_output =
                    matches!(array.value(), ExprValue::Var { name } if *name == info.output_name);
                let const_map_hit = try_extract_const_idx(index)
                    .is_some_and(|idx| info.const_map.contains_key(&idx));
                if const_map_hit {
                    if on_output {
                        output_const_sites.push(rule_idx);
                    }
                } else {
                    if info.uniform_default.is_none() {
                        return false;
                    }
                    uniform_sites.push(UniformSelectSite { rule_idx, on_output });
                }
                stack.push(index);
            }
            ExprValue::Var { name } if *name == info.input_name || *name == info.output_name => {
                // Raw whole-array mention that would survive folding.
                return false;
            }
            _ => stack.extend(node.children()),
        }
    }
    true
}

/// `(= arr__out arr)`-shaped conjunct anywhere in the rule.
fn rule_has_identity_pair(rule: &trust_mc_core::chc::Rule, info: &ConstFoldInfo) -> bool {
    rule.body.constraints.iter().any(|constraint| {
        let mut conjuncts = Vec::new();
        flatten_and_tree(constraint, &mut conjuncts);
        conjuncts.iter().any(|conjunct| {
            let ExprValue::Eq(lhs, rhs) = conjunct.value() else {
                return false;
            };
            folded_array_var(lhs, info).is_some() && folded_array_var(rhs, info).is_some()
        })
    })
}

fn expr_mentions_folded_array(expr: &Expr, info: &ConstFoldInfo) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } if *name == info.input_name || *name == info.output_name => {
                return true;
            }
            _ => stack.extend(node.children()),
        }
    }
    false
}

/// Mentions of the folded array other than as the base of a `(select var idx)`
/// (those are vetted by `collect_select_fold_sites`).
fn expr_mentions_array_outside_select_base(expr: &Expr, info: &ConstFoldInfo) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Select { array, index }
                if matches!(
                    array.value(),
                    ExprValue::Var { name }
                        if *name == info.input_name || *name == info.output_name
                ) =>
            {
                stack.push(index);
            }
            ExprValue::Var { name } if *name == info.input_name || *name == info.output_name => {
                return true;
            }
            _ => stack.extend(node.children()),
        }
    }
    false
}

enum UniformUse {
    /// Constraint cannot be proven to preserve the uniform default.
    Violation,
    /// `(= arr__out arr)` or a default-valued store chain rooted at the array.
    Identity,
    /// `(= arr const_array(default))`-shaped init of the input name.
    InitInput,
    /// Same on the `__out` name.
    InitOutput,
    /// Does not constrain the whole array.
    Benign,
}

fn folded_array_var(expr: &Expr, info: &ConstFoldInfo) -> Option<bool> {
    match expr.value() {
        ExprValue::Var { name } if *name == info.input_name => Some(false),
        ExprValue::Var { name } if *name == info.output_name => Some(true),
        _ => None,
    }
}

fn classify_uniform_conjunct(conjunct: &Expr, info: &ConstFoldInfo, default: &Expr) -> UniformUse {
    if let ExprValue::Eq(lhs, rhs) = conjunct.value() {
        match (folded_array_var(lhs, info), folded_array_var(rhs, info)) {
            (Some(_), Some(_)) => return UniformUse::Identity,
            (Some(is_output), None) => {
                return classify_uniform_value(rhs, info, default, is_output);
            }
            (None, Some(is_output)) => {
                return classify_uniform_value(lhs, info, default, is_output);
            }
            (None, None) => {}
        }
    }
    if expr_mentions_array_outside_select_base(conjunct, info) {
        UniformUse::Violation
    } else {
        UniformUse::Benign
    }
}

fn classify_uniform_value(
    val_side: &Expr,
    info: &ConstFoldInfo,
    default: &Expr,
    is_output: bool,
) -> UniformUse {
    let mut node = val_side;
    loop {
        match node.value() {
            ExprValue::Store { array, index, value } => {
                // Every stored value must BE the default, and the index must
                // not smuggle a whole-array reference.
                if value != default || expr_mentions_array_outside_select_base(index, info) {
                    return UniformUse::Violation;
                }
                node = array;
            }
            ExprValue::ConstArray { value, .. } => {
                if value != default {
                    return UniformUse::Violation;
                }
                return if is_output { UniformUse::InitOutput } else { UniformUse::InitInput };
            }
            // `arr__out = store(arr, i, default)` — preserves uniformity.
            ExprValue::Var { .. } if folded_array_var(node, info).is_some() => {
                return UniformUse::Identity;
            }
            // Copy from a foreign array, datatype forwarding, ITE of arrays,
            // ... — contents unprovable.
            _ => return UniformUse::Violation,
        }
    }
}

/// Verify that the uniform default is established before every recorded
/// select site, via a greatest-fixpoint over the relation graph.
fn uniform_default_reaches_all_sites(
    vc: &ChcVc,
    info: &ConstFoldInfo,
    default: &Expr,
    sites: &[UniformSelectSite],
) -> bool {
    // (a) Every whole-array constraint must establish or preserve the default;
    //     collect per-rule facts along the way.
    let mut facts: Vec<UniformRuleFacts> = vec![UniformRuleFacts::default(); vc.rules.len()];
    for (rule_idx, rule) in vc.rules.iter().enumerate() {
        for constraint in rule.body.constraints.iter() {
            let mut conjuncts = Vec::new();
            flatten_and_tree(constraint, &mut conjuncts);
            for conjunct in &conjuncts {
                match classify_uniform_conjunct(conjunct, info, default) {
                    UniformUse::Violation => return false,
                    UniformUse::Identity => facts[rule_idx].has_identity = true,
                    UniformUse::InitInput => facts[rule_idx].inits_input = true,
                    UniformUse::InitOutput => facts[rule_idx].inits_output = true,
                    UniformUse::Benign => {}
                }
            }
        }
    }

    // (b) Greatest fixpoint: a relation carries the uniform array iff EVERY
    //     rule producing it delivers a uniform array through its head args.
    //     Relations with no producing rules are unreachable, hence vacuously
    //     uniform.
    let mut producers: HashMap<&str, Vec<usize>> = HashMap::new();
    for (rule_idx, rule) in vc.rules.iter().enumerate() {
        producers.entry(rule.head.name.as_str()).or_default().push(rule_idx);
    }
    let relation_uniform = |uniform: &HashSet<&str>, name: &str| -> bool {
        !producers.contains_key(name) || uniform.contains(name)
    };
    let pre_state_uniform = |uniform: &HashSet<&str>, rule_idx: usize| -> bool {
        let rule = &vc.rules[rule_idx];
        match &rule.body.relation {
            // Entry rule: the "pre-state" is the initial value the rule pins.
            None => facts[rule_idx].inits_input,
            Some(body_rel) => {
                facts[rule_idx].inits_input || relation_uniform(uniform, body_rel.name.as_str())
            }
        }
    };
    let rule_delivers = |uniform: &HashSet<&str>, rule_idx: usize| -> bool {
        let rule = &vc.rules[rule_idx];
        let head_carries = rule.head.args.iter().find_map(|arg| folded_array_var(arg, info));
        match head_carries {
            // The head does not carry the array: any read of it under this
            // relation would be an unbound rule variable. Fail closed.
            None => false,
            // Head threads the pre-state name directly.
            Some(false) => pre_state_uniform(uniform, rule_idx),
            // Head carries the post-state: it must be re-established or tied
            // to a uniform pre-state by an identity.
            Some(true) => {
                facts[rule_idx].inits_output
                    || (facts[rule_idx].has_identity && pre_state_uniform(uniform, rule_idx))
            }
        }
    };

    let mut uniform: HashSet<&str> = producers.keys().copied().collect();
    loop {
        let stale: Vec<&str> = uniform
            .iter()
            .copied()
            .filter(|rel| producers[rel].iter().any(|&rule_idx| !rule_delivers(&uniform, rule_idx)))
            .collect();
        if stale.is_empty() {
            break;
        }
        for rel in stale {
            uniform.remove(rel);
        }
    }

    // (c) Each uniform-default select must observe a state where the default
    //     provably holds.
    sites.iter().all(|site| {
        let pre_uniform = pre_state_uniform(&uniform, site.rule_idx);
        if site.on_output {
            facts[site.rule_idx].inits_output || (facts[site.rule_idx].has_identity && pre_uniform)
        } else {
            pre_uniform
        }
    })
}

/// Remove folded array args from a relation application.
fn remove_folded_args(
    app: &RelationApp,
    folded_inputs: &HashMap<&str, usize>,
    folded_outputs: &HashMap<&str, usize>,
) -> RelationApp {
    let new_args: Vec<Expr> = app
        .args
        .iter()
        .filter(|arg| {
            if let ExprValue::Var { name } = arg.value() {
                !folded_inputs.contains_key(name.as_str())
                    && !folded_outputs.contains_key(name.as_str())
            } else {
                true
            }
        })
        .cloned()
        .collect();
    RelationApp::new(app.name.as_str(), new_args)
}

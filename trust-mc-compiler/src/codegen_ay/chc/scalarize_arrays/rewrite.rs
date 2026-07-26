// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VC rewriting for constant-index array scalarization (Phase 2-4).
//!
//! Separated from `scalarize_arrays.rs` per 500-LOC compliance.
//! Contains: expression rewriting, constraint rewriting, relation
//! expansion, and the top-level `scalarize_vc` orchestrator.
//!
//! Part of #4050: PDR array-param bottleneck optimization.

use std::collections::{BTreeSet, HashMap};

use ay_bindings::{Expr, ExprValue, Sort, rebuild_with_children};
use tracing::debug;
use trust_mc_core::chc::{ChcVc, RelationApp, VarDecl};
use trust_mc_core::constraints::Constraints;

use super::output_copies::{
    build_scalar_copy_constraints, build_scalar_store_constraints_from_base,
    scalar_info_for_array_var,
};
use super::{
    ConstIdx, RewriteContext, ScalarInfo, const_array_default_for_store_chain,
    decompose_store_chain, identify_scalarizable_arrays, rewrite_expr,
    transparent_forwarded_array_base, try_extract_const_idx,
};

/// Build lookup maps from the ScalarInfo list for efficient rewriting.
pub(super) struct RewriteMaps {
    /// input_name → ScalarInfo index in the infos vec.
    pub(super) by_input: HashMap<String, usize>,
    /// output_name → ScalarInfo index in the infos vec.
    pub(super) by_output: HashMap<String, usize>,
}

impl RewriteMaps {
    pub(super) fn new(infos: &[ScalarInfo]) -> Self {
        let mut by_input = HashMap::new();
        let mut by_output = HashMap::new();
        for (i, info) in infos.iter().enumerate() {
            by_input.insert(info.input_name.clone(), i);
            by_output.insert(info.output_name.clone(), i);
        }
        Self { by_input, by_output }
    }
}

/// Recursively rewrite expression children using `ay_bindings::rebuild_with_children`.
///
/// This is the fallback for expression types that don't need special handling.
pub(super) fn rewrite_expr_children(
    expr: &Expr,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
    ctx: &mut RewriteContext,
) -> Expr {
    let children: Vec<&Expr> = expr.children().collect();
    if children.is_empty() {
        return expr.clone();
    }

    let rewritten: Vec<Expr> = children.iter().map(|c| rewrite_expr(c, infos, maps, ctx)).collect();

    // Check if any child actually changed.
    let any_changed = rewritten.iter().zip(children.iter()).any(|(new, old)| new != *old);
    if !any_changed {
        return expr.clone();
    }

    rebuild_with_children(expr, rewritten)
}

/// Simplify local store/select chains before array folding/scalarization.
///
/// This removes array-theory terms like `select(store(mem, #x10, v), #x10)`
/// and `select(store(mem, #x10, v), #x20)` when the indices are equal or
/// provably distinct constants. The latter rewrites to `select(mem, #x20)`,
/// exposing the base array to the scalarizer instead of leaving a nested array
/// expression that relation-argument rewriting cannot eliminate.
fn simplify_store_select_chains_in_vc(vc: &mut ChcVc) {
    let mut simplified = 0usize;
    for rule in &mut vc.rules {
        let old_constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        let mut new_constraints = Vec::with_capacity(old_constraints.len());
        for constraint in old_constraints {
            let (new_constraint, count) = simplify_store_select_chains(&constraint);
            simplified += count;
            new_constraints.push(new_constraint);
        }
        rule.body.constraints = Constraints::Owned(new_constraints);
    }

    if simplified > 0 {
        debug!(
            simplified,
            "CHC: simplified constant array store/select chains before scalarization"
        );
    }
}

fn simplify_store_select_chains(expr: &Expr) -> (Expr, usize) {
    match expr.value() {
        ExprValue::Select { array, index } => {
            let (new_array, array_count) = simplify_store_select_chains(array);
            let (new_index, index_count) = simplify_store_select_chains(index);
            let count = array_count + index_count;
            if let Some(resolved) = simplify_select_from_array(&new_array, &new_index) {
                let (resolved, resolved_count) = simplify_store_select_chains(&resolved);
                return (resolved, count + resolved_count + 1);
            }
            if new_array == *array && new_index == *index {
                return (expr.clone(), count);
            }
            (new_array.select(new_index), count)
        }
        ExprValue::Store { array, index, value } => {
            let (new_array, array_count) = simplify_store_select_chains(array);
            let (new_index, index_count) = simplify_store_select_chains(index);
            let (new_value, value_count) = simplify_store_select_chains(value);
            let count = array_count + index_count + value_count;

            if let ExprValue::ConstArray { value: default, .. } = new_array.value() {
                if *default == new_value {
                    return (new_array, count + 1);
                }
            }
            if let ExprValue::Select { array: selected_array, index: selected_index } =
                new_value.value()
            {
                if *selected_array == new_array && *selected_index == new_index {
                    return (new_array, count + 1);
                }
            }

            if new_array == *array && new_index == *index && new_value == *value {
                return (expr.clone(), count);
            }
            (new_array.store(new_index, new_value), count)
        }
        _ => {
            let children: Vec<&Expr> = expr.children().collect();
            if children.is_empty() {
                return (expr.clone(), 0);
            }

            let mut changed = false;
            let mut total = 0usize;
            let mut rewritten = Vec::with_capacity(children.len());
            for child in &children {
                let (new_child, child_count) = simplify_store_select_chains(child);
                changed |= new_child != **child;
                total += child_count;
                rewritten.push(new_child);
            }
            if !changed {
                return (expr.clone(), total);
            }
            (rebuild_with_children(expr, rewritten), total)
        }
    }
}

fn simplify_select_from_array(array: &Expr, select_index: &Expr) -> Option<Expr> {
    match array.value() {
        ExprValue::ConstArray { value, .. } => Some(value.clone()),
        ExprValue::Store { array: inner, index: store_index, value } => {
            if select_index == store_index {
                return Some(value.clone());
            }

            let store_const = try_extract_const_idx(store_index)?;
            if let Some(select_const) = try_extract_const_idx(select_index) {
                if select_const == store_const {
                    return Some(value.clone());
                }
                return Some(
                    simplify_select_from_array(inner, select_index)
                        .unwrap_or_else(|| inner.clone().select(select_index.clone())),
                );
            }

            let fallback = simplify_select_from_array(inner, select_index)
                .unwrap_or_else(|| inner.clone().select(select_index.clone()));
            Some(Expr::ite(select_index.clone().eq(store_index.clone()), value.clone(), fallback))
        }
        _ => None,
    }
}

/// Rewrite a single constraint, potentially splitting it into multiple constraints.
///
/// Returns the replacement constraints. For non-array constraints, returns
/// the single rewritten constraint. For store-chain constraints, returns
/// per-index scalar equalities.
pub(super) fn rewrite_constraint(
    constraint: &Expr,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
    ctx: &mut RewriteContext,
) -> Vec<Expr> {
    // Check if this is an `(= arr_var store_chain)` or `(= arr_var const_array)`.
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        // Not an equality — just rewrite Selects in sub-expressions.
        return vec![rewrite_expr(constraint, infos, maps, ctx)];
    };

    // Determine which side (if any) is a scalarizable output var.
    if let Some(result) = try_rewrite_output_constraint(lhs, rhs, infos, maps, ctx) {
        return result;
    }
    if let Some(result) = try_rewrite_output_constraint(rhs, lhs, infos, maps, ctx) {
        return result;
    }

    // Also handle input-var initialization in entry rules:
    // `(= input_var const_array(val))` → per-scalar `(= scalar_in val)`.
    if let Some(result) = try_rewrite_input_init(lhs, rhs, infos, maps, ctx) {
        return result;
    }
    if let Some(result) = try_rewrite_input_init(rhs, lhs, infos, maps, ctx) {
        return result;
    }

    vec![rewrite_expr(constraint, infos, maps, ctx)]
}

/// Try to rewrite `(= output_var val_expr)` for scalarizable arrays.
fn try_rewrite_output_constraint(
    var_side: &Expr,
    val_side: &Expr,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
    ctx: &mut RewriteContext,
) -> Option<Vec<Expr>> {
    let ExprValue::Var { name } = var_side.value() else {
        return None;
    };
    let &info_idx = maps.by_output.get(name)?;
    let info = &infos[info_idx];

    Some(match val_side.value() {
        ExprValue::Store { .. } => {
            if let Some((base, stores)) = decompose_store_chain(val_side) {
                if base == info.input_name {
                    return Some(build_scalar_store_constraints(info, &stores, None));
                }
                if base == "__const_array__" {
                    return Some(build_scalar_store_constraints(
                        info,
                        &stores,
                        const_array_default_for_store_chain(val_side),
                    ));
                }
                if scalar_info_for_array_var(&base, maps).is_some() {
                    return Some(build_scalar_store_constraints_from_base(
                        info, &base, &stores, infos, maps,
                    ));
                }
            }
            vec![rewrite_expr_for_eq(var_side, val_side, infos, maps, ctx)]
        }
        ExprValue::ConstArray { value, .. } => {
            let mut constraints = Vec::new();
            for idx in info.index_to_scalar.keys() {
                let scalar_out = Expr::var(info.scalar_output_name(idx), info.elem_sort.clone());
                let rewritten_val = rewrite_expr(value, infos, maps, ctx);
                constraints.push(scalar_out.eq(rewritten_val.clone()));
            }
            constraints
        }
        ExprValue::Var { name: vname } if *vname == info.input_name => {
            let mut constraints = Vec::new();
            for idx in info.index_to_scalar.keys() {
                let scalar_out = Expr::var(info.scalar_output_name(idx), info.elem_sort.clone());
                let scalar_in = Expr::var(info.scalar_input_name(idx), info.elem_sort.clone());
                constraints.push(scalar_out.eq(scalar_in));
            }
            constraints
        }
        ExprValue::Var { name: vname } if scalar_info_for_array_var(vname, maps).is_some() => {
            build_scalar_copy_constraints(info, vname, infos, maps)
        }
        _ => {
            if let Some(base) = transparent_forwarded_array_base(val_side, &|candidate| {
                maps.by_input.contains_key(candidate) || maps.by_output.contains_key(candidate)
            }) {
                if base == info.input_name {
                    return Some(build_scalar_copy_constraints(info, &base, infos, maps));
                }
                if scalar_info_for_array_var(&base, maps).is_some() {
                    return Some(build_scalar_copy_constraints(info, &base, infos, maps));
                }
            }
            vec![rewrite_expr_for_eq(var_side, val_side, infos, maps, ctx)]
        }
    })
}

/// Try to rewrite `(= input_var const_array(val))` for scalarizable arrays.
///
/// Entry rules initialize arrays via `(= arr const_array(val))`. After
/// scalarization replaces the array in relation args with scalar vars,
/// this constraint must be converted to per-scalar initializations.
fn try_rewrite_input_init(
    var_side: &Expr,
    val_side: &Expr,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
    ctx: &mut RewriteContext,
) -> Option<Vec<Expr>> {
    let ExprValue::Var { name } = var_side.value() else {
        return None;
    };
    let &info_idx = maps.by_input.get(name)?;
    let info = &infos[info_idx];

    match val_side.value() {
        ExprValue::ConstArray { value, .. } => {
            let mut constraints = Vec::new();
            for idx in info.index_to_scalar.keys() {
                let scalar_in = Expr::var(info.scalar_input_name(idx), info.elem_sort.clone());
                let rewritten_val = rewrite_expr(value, infos, maps, ctx);
                constraints.push(scalar_in.eq(rewritten_val.clone()));
            }
            Some(constraints)
        }
        ExprValue::Store { .. } => {
            if let Some((base, stores)) = decompose_store_chain(val_side) {
                if base == "__const_array__" {
                    return Some(build_scalar_input_store_constraints(
                        info,
                        &stores,
                        const_array_default_for_store_chain(val_side),
                    ));
                }
            }
            None
        }
        _ => None,
    }
}

/// Helper: reconstruct `(= lhs rhs)` with rewritten children.
fn rewrite_expr_for_eq(
    lhs: &Expr,
    rhs: &Expr,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
    ctx: &mut RewriteContext,
) -> Expr {
    let new_lhs = rewrite_expr(lhs, infos, maps, ctx);
    let new_rhs = rewrite_expr(rhs, infos, maps, ctx);
    new_lhs.eq(new_rhs)
}

/// Build per-index scalar input constraints from a store chain on const_array.
fn build_scalar_input_store_constraints(
    info: &ScalarInfo,
    stores: &[(ConstIdx, Expr)],
    default_value: Option<&Expr>,
) -> Vec<Expr> {
    let mut stored_values: HashMap<&ConstIdx, &Expr> = HashMap::new();
    for (idx, val) in stores {
        stored_values.insert(idx, val);
    }

    let mut constraints = Vec::new();
    for idx in info.index_to_scalar.keys() {
        let scalar_in = Expr::var(info.scalar_input_name(idx), info.elem_sort.clone());
        if let Some(val) = stored_values.get(idx) {
            constraints.push(scalar_in.eq((*val).clone()));
        } else if let Some(default) = default_value {
            constraints.push(scalar_in.eq(default.clone()));
        }
    }
    constraints
}

/// Build per-index scalar equality constraints from a store chain decomposition.
fn build_scalar_store_constraints(
    info: &ScalarInfo,
    stores: &[(ConstIdx, Expr)],
    default_value: Option<&Expr>,
) -> Vec<Expr> {
    let mut stored_values: HashMap<&ConstIdx, &Expr> = HashMap::new();
    for (idx, val) in stores {
        stored_values.insert(idx, val);
    }

    let mut constraints = Vec::new();
    for idx in info.index_to_scalar.keys() {
        let scalar_out = Expr::var(info.scalar_output_name(idx), info.elem_sort.clone());
        if let Some(val) = stored_values.get(idx) {
            constraints.push(scalar_out.eq((*val).clone()));
        } else if let Some(default) = default_value {
            constraints.push(scalar_out.eq(default.clone()));
        } else {
            let scalar_in = Expr::var(info.scalar_input_name(idx), info.elem_sort.clone());
            constraints.push(scalar_out.eq(scalar_in));
        }
    }
    constraints
}

/// Expand a relation application's args: replace Array-sorted Var expressions
/// with scalar Var expressions.
pub(super) fn expand_relation_app(
    app: &RelationApp,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
) -> RelationApp {
    let mut new_args = Vec::new();
    for arg in app.args.iter() {
        if let ExprValue::Var { name } = arg.value() {
            if let Some(&info_idx) = maps.by_input.get(name) {
                let info = &infos[info_idx];
                for idx in info.index_to_scalar.keys() {
                    new_args.push(Expr::var(info.scalar_input_name(idx), info.elem_sort.clone()));
                }
                continue;
            }
            if let Some(&info_idx) = maps.by_output.get(name) {
                let info = &infos[info_idx];
                for idx in info.index_to_scalar.keys() {
                    new_args.push(Expr::var(info.scalar_output_name(idx), info.elem_sort.clone()));
                }
                continue;
            }
        }
        new_args.push(arg.clone());
    }
    RelationApp::new(app.name.as_str(), new_args)
}

/// One rule's staged (not yet committed) scalarization rewrite.
struct StagedRule {
    constraints: Vec<Expr>,
    head: RelationApp,
    body_relation: Option<RelationApp>,
}

/// Rewrite every rule WITHOUT mutating the VC, so the result can be discarded
/// if the rewrite turns out to need a fail-closed unwind.
fn stage_rule_rewrites(
    vc: &ChcVc,
    infos: &[super::ScalarInfo],
    maps: &RewriteMaps,
    rewrite_ctx: &mut RewriteContext,
) -> Vec<StagedRule> {
    vc.rules
        .iter()
        .map(|rule| {
            let old_constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
            let mut new_constraints = Vec::new();
            for constraint in &old_constraints {
                new_constraints.extend(rewrite_constraint(constraint, infos, maps, rewrite_ctx));
            }
            // Second pass: rewrite Selects in the newly generated constraints.
            let final_constraints: Vec<Expr> =
                new_constraints.iter().map(|c| rewrite_expr(c, infos, maps, rewrite_ctx)).collect();
            StagedRule {
                constraints: final_constraints,
                head: expand_relation_app(&rule.head, infos, maps),
                body_relation: rule
                    .body
                    .relation
                    .as_ref()
                    .map(|body_rel| expand_relation_app(body_rel, infos, maps)),
            }
        })
        .collect()
}

/// Scan a staged rewrite for surviving whole-array mentions of scalarized
/// arrays (input or output name) in constraints or relation-app args.
///
/// A scalarized array is removed from relation state, so any residual mention
/// (an unrewritten datatype-constructor capture, an `(= other arr)` copy whose
/// counterpart is not scalarized, a symbolic select left in place by the
/// fail-closed path in `rewrite_expr`, ...) would reference a rule-local FREE
/// array: the solver could then pick its contents at will and fabricate
/// counterexample witnesses. Returns the input names of all such arrays so the
/// caller can unwind their scalarization (fail closed).
fn residual_scalarized_array_mentions(
    staged: &[StagedRule],
    infos: &[super::ScalarInfo],
    maps: &RewriteMaps,
) -> BTreeSet<String> {
    let mut rejected = BTreeSet::new();
    let mut note_mentions = |expr: &Expr| {
        let mut stack = vec![expr];
        while let Some(node) = stack.pop() {
            if let ExprValue::Var { name } = node.value() {
                if let Some(&info_idx) =
                    maps.by_input.get(name).or_else(|| maps.by_output.get(name))
                {
                    rejected.insert(infos[info_idx].input_name.clone());
                }
            }
            stack.extend(node.children());
        }
    };
    for rule in staged {
        for constraint in &rule.constraints {
            note_mentions(constraint);
        }
        for arg in rule.head.args.iter() {
            note_mentions(arg);
        }
        if let Some(body_rel) = &rule.body_relation {
            for arg in body_rel.args.iter() {
                note_mentions(arg);
            }
        }
    }
    rejected
}

/// Core scalarization function operating on the finished VC.
pub(in crate::codegen_ay) fn scalarize_vc(vc: &mut ChcVc) {
    // Phase -2 (Part of #40): collapse fragment-composition `__mid_bbN` array
    // aliases so identification and the residual fail-closed check see the
    // canonical `X`/`X__out` names instead of banning arrays over pure
    // rule-local frame-chain copies.
    super::collapse_mid_aliases::collapse_mid_aliases(vc);

    // Phase -1: expose constant store/select chains to const-folding and scalarization.
    simplify_store_select_chains_in_vc(vc);

    // Phase 0: Constant-fold and eliminate read-only arrays.
    let fold_infos = super::const_fold::identify_const_foldable_arrays(vc);
    if !fold_infos.is_empty() {
        super::const_fold_apply::apply_const_folding(vc, &fold_infos);
    }

    // Phase 1+2: Identify scalarizable arrays and STAGE the rewrite. The
    // staging is only committed when no array's rewrite hit a fail-closed
    // condition (a rewrite-time symbolic select recorded by `RewriteContext`,
    // or a residual whole-array mention that would survive as an unconstrained
    // free array). On any hit, the staged rewrite is discarded, the offending
    // arrays are banned, and identification re-runs so dependent arrays unwind
    // through the regular lane-dependency rejection paths. Failing to
    // scalarize is sound; completing a rewrite with free fallback vars is not.
    let mut banned: BTreeSet<String> = BTreeSet::new();
    let staged = loop {
        let infos = identify_scalarizable_arrays(vc, &banned);
        if infos.is_empty() {
            break None;
        }
        let maps = RewriteMaps::new(&infos);
        let mut rewrite_ctx = RewriteContext::new();
        let staged_rules = stage_rule_rewrites(vc, &infos, &maps, &mut rewrite_ctx);

        let mut rejected = residual_scalarized_array_mentions(&staged_rules, &infos, &maps);
        rejected.extend(rewrite_ctx.rejected_arrays().iter().cloned());
        if rejected.is_empty() {
            break Some((infos, staged_rules, rewrite_ctx));
        }

        debug!(
            arrays = %rejected.iter().cloned().collect::<Vec<_>>().join(", "),
            "CHC: fail closed — unwinding scalarization of arrays whose rewrite left \
             unconstrained reads (rewrite-time symbolic select or residual array mention)"
        );
        // Each retry strictly grows `banned` with names drawn from the current
        // candidate set, so the loop terminates within #array-vars iterations.
        banned.extend(rejected);
    };

    let Some((infos, staged_rules, rewrite_ctx)) = staged else {
        // No arrays to scalarize, but still prune dead scalars.
        let carried = super::protect_lanes::carry_rhs_scalarized_lanes(vc);
        if carried > 0 {
            debug!(carried, "CHC: carried scalarized lane vars before scalar pruning");
        }
        super::prune_dead_scalars::prune_dead_scalars(vc);
        return;
    };

    let total_scalars: usize = infos.iter().map(|i| i.index_to_scalar.len()).sum();
    debug!(
        scalarizable_arrays = infos.len(),
        total_scalars,
        arrays = %infos.iter().map(|i| format!("{}({}idx)", i.input_name, i.index_to_scalar.len())).collect::<Vec<_>>().join(", "),
        "CHC: scalarizing constant-index arrays"
    );

    // Commit the staged rewrite.
    for (rule, staged_rule) in vc.rules.iter_mut().zip(staged_rules) {
        rule.body.constraints = Constraints::Owned(staged_rule.constraints);
        rule.head = staged_rule.head;
        rule.body.relation = staged_rule.body_relation;
    }

    // Phase 3: Rewrite relation declarations.
    let mut relation_sorts: HashMap<String, Vec<Sort>> = HashMap::new();
    for rule in &vc.rules {
        record_relation_sorts(&mut relation_sorts, &rule.head);
        if let Some(body_rel) = &rule.body.relation {
            record_relation_sorts(&mut relation_sorts, body_rel);
        }
    }
    for rel in &mut vc.relations {
        if let Some(new_sorts) = relation_sorts.get(&rel.name) {
            let old_arity = rel.arg_sorts.len();
            rel.arg_sorts = new_sorts.clone();
            if rel.arg_sorts.len() != old_arity {
                debug!(
                    relation = %rel.name,
                    old_arity,
                    new_arity = rel.arg_sorts.len(),
                    "CHC: scalarized relation arity"
                );
            }
        }
    }

    // Phase 4: Add scalar var declarations.
    for info in &infos {
        for idx in info.index_to_scalar.keys() {
            vc.add_var(VarDecl::new(info.scalar_input_name(idx), info.elem_sort.clone()));
            vc.add_var(VarDecl::new(info.scalar_output_name(idx), info.elem_sort.clone()));
        }
    }
    for var in rewrite_ctx.take_extra_vars() {
        vc.add_var(var);
    }

    debug!(
        arrays_scalarized = infos.len(),
        total_scalar_vars = total_scalars * 2,
        "CHC: array scalarization complete"
    );

    // Phase 5: Protect scalarized lanes read after relation boundaries, then
    // prune dead identity-passthrough scalars.
    let carried = super::protect_lanes::carry_rhs_scalarized_lanes(vc);
    if carried > 0 {
        debug!(carried, "CHC: carried scalarized lane vars before scalar pruning");
    }
    super::prune_dead_scalars::prune_dead_scalars(vc);
}

fn record_relation_sorts(relation_sorts: &mut HashMap<String, Vec<Sort>>, app: &RelationApp) {
    let name = app.name.to_string();
    relation_sorts
        .entry(name)
        .or_insert_with(|| app.args.iter().map(|a| a.sort().clone()).collect());
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Late relation-argument pruning for post-scalarization dead lanes.
//!
//! This intentionally does not enable the broad `strip_dead_args` optimizer. It
//! removes only relation positions whose relation apps carry closed values or
//! the exact generated padding variable for that position. For Array-sorted
//! positions it also accepts compound producer expressions, matching the
//! deallocation shape left by const-index scalarization. Bare non-pad variables
//! are preserved because they may be real state carried between relations.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprFold, ExprValue, fold_expr, rebuild_with_children};
use trust_mc_core::chc::{ChcVc, RelationApp};
use trust_mc_core::constraints::Constraints;

#[derive(Debug, Clone, Copy)]
struct ClosedArgCandidate {
    array_sort: bool,
    seen: bool,
    rejected: bool,
}

/// Prune relation args that are closed producer/pad-only after scalarization.
///
/// Returns the number of relation argument positions removed.
pub(in crate::codegen_ay) fn prune_dead_array_relation_args(vc: &mut ChcVc) -> usize {
    let relation_names: HashSet<String> = vc.relations.iter().map(|rel| rel.name.clone()).collect();
    let constraint_vars = collect_non_relation_constraint_vars(vc, &relation_names);
    let candidates = collect_candidate_states(vc, &relation_names, &constraint_vars);
    let masks = dead_array_arg_masks(candidates);
    let pruned = masks.values().map(|mask| mask.iter().filter(|&&dead| dead).count()).sum();
    if pruned == 0 {
        return 0;
    }

    strip_relation_decls(vc, &masks);
    strip_rule_relation_apps(vc, &masks);
    remove_stripped_pad_vars(vc, &masks);

    tracing::debug!(pruned, "CHC: pruned dead relation args after scalarization (#4329/#4330)");
    pruned
}

fn collect_candidate_states(
    vc: &ChcVc,
    relation_names: &HashSet<String>,
    constraint_vars: &HashSet<String>,
) -> HashMap<String, Vec<ClosedArgCandidate>> {
    let mut candidates: HashMap<String, Vec<ClosedArgCandidate>> = vc
        .relations
        .iter()
        .map(|rel| {
            let states = rel
                .arg_sorts
                .iter()
                .map(|sort| ClosedArgCandidate {
                    array_sort: sort.is_array(),
                    seen: false,
                    rejected: false,
                })
                .collect();
            (rel.name.clone(), states)
        })
        .collect();

    for rule in &vc.rules {
        record_relation_app_arg_shapes(&rule.head, &mut candidates, constraint_vars);
        if let Some(body_rel) = &rule.body.relation {
            record_relation_app_arg_shapes(body_rel, &mut candidates, constraint_vars);
        }
        for constraint in rule.body.constraints.iter() {
            record_embedded_relation_app_arg_shapes(
                constraint,
                relation_names,
                &mut candidates,
                constraint_vars,
            );
        }
    }

    candidates
}

fn dead_array_arg_masks(
    candidates: HashMap<String, Vec<ClosedArgCandidate>>,
) -> HashMap<String, Vec<bool>> {
    candidates
        .into_iter()
        .filter_map(|(name, states)| {
            let mask =
                states.into_iter().map(|state| state.seen && !state.rejected).collect::<Vec<_>>();
            mask.iter().any(|&dead| dead).then_some((name, mask))
        })
        .collect()
}

fn collect_non_relation_constraint_vars(
    vc: &ChcVc,
    relation_names: &HashSet<String>,
) -> HashSet<String> {
    let mut vars = HashSet::new();
    for rule in &vc.rules {
        for constraint in rule.body.constraints.iter() {
            collect_expr_vars_excluding_relation_apps(constraint, relation_names, &mut vars);
        }
    }
    vars
}

fn collect_expr_vars_excluding_relation_apps(
    expr: &Expr,
    relation_names: &HashSet<String>,
    vars: &mut HashSet<String>,
) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            // Pure array state forwarding constraints such as `arr__out = arr`
            // do not make the array observable. If the array is otherwise absent
            // from non-relation constraints, the corresponding relation slot can
            // be pruned; the forwarding equality then becomes irrelevant.
            ExprValue::Eq(lhs, rhs) if is_pure_array_state_copy(lhs, rhs) => {}
            ExprValue::Var { name } => {
                vars.insert(name.clone());
            }
            ExprValue::FuncApp { name, .. } if relation_names.contains(name.as_str()) => {}
            _ => stack.extend(node.children()),
        }
    }
}

fn is_pure_array_state_copy(lhs: &Expr, rhs: &Expr) -> bool {
    let (ExprValue::Var { name: lhs_name }, ExprValue::Var { name: rhs_name }) =
        (lhs.value(), rhs.value())
    else {
        return false;
    };
    lhs.sort().is_array()
        && rhs.sort().is_array()
        && (lhs_name.ends_with("__out") || rhs_name.ends_with("__out"))
}

fn record_embedded_relation_app_arg_shapes(
    expr: &Expr,
    relation_names: &HashSet<String>,
    candidates: &mut HashMap<String, Vec<ClosedArgCandidate>>,
    constraint_vars: &HashSet<String>,
) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::FuncApp { name, args } = node.value()
            && relation_names.contains(name.as_str())
        {
            record_relation_args(name, args, candidates, constraint_vars);
        }
        stack.extend(node.children());
    }
}

fn record_relation_app_arg_shapes(
    app: &RelationApp,
    candidates: &mut HashMap<String, Vec<ClosedArgCandidate>>,
    constraint_vars: &HashSet<String>,
) {
    record_relation_args(app.name.as_str(), app.args.as_ref(), candidates, constraint_vars);
}

fn record_relation_args(
    rel_name: &str,
    args: &[Expr],
    candidates: &mut HashMap<String, Vec<ClosedArgCandidate>>,
    constraint_vars: &HashSet<String>,
) {
    let Some(states) = candidates.get_mut(rel_name) else {
        return;
    };
    if args.len() != states.len() {
        for state in states.iter_mut() {
            state.rejected = true;
        }
        return;
    }

    for (idx, state) in states.iter_mut().enumerate() {
        if state.rejected {
            continue;
        }
        state.seen = true;
        if let Err(reason) = classify_prunable_relation_arg(
            rel_name,
            idx,
            state.array_sort,
            &args[idx],
            constraint_vars,
        ) {
            tracing::debug!(
                relation = rel_name,
                idx,
                reason = %reason,
                "CHC: dead relation arg candidate rejected (#4329/#4330)"
            );
            state.rejected = true;
        }
    }
}

fn classify_prunable_relation_arg(
    rel_name: &str,
    idx: usize,
    array_sort: bool,
    arg: &Expr,
    constraint_vars: &HashSet<String>,
) -> Result<(), String> {
    let mut vars = HashSet::new();
    collect_expr_vars(arg, &mut vars);
    if vars.is_empty() {
        return Ok(());
    }

    let pad_name = generated_pad_name(rel_name, idx);
    if let ExprValue::Var { name } = arg.value() {
        if name == &pad_name && !constraint_vars.contains(name) {
            return Ok(());
        }
        if array_sort && !constraint_vars.contains(name) {
            return Ok(());
        }
        return Err(format!("bare_var:{name}"));
    }

    if let Some(pad) = vars.iter().find(|name| name.starts_with("__pad_")) {
        return Err(format!("compound_mentions_pad:{pad}"));
    }

    if array_sort { Ok(()) } else { Err("compound_scalar_mentions_non_pad_var".to_string()) }
}

fn collect_expr_vars(expr: &Expr, vars: &mut HashSet<String>) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } => {
                vars.insert(name.clone());
            }
            _ => stack.extend(node.children()),
        }
    }
}

fn strip_relation_decls(vc: &mut ChcVc, masks: &HashMap<String, Vec<bool>>) {
    for rel in &mut vc.relations {
        let Some(mask) = masks.get(rel.name.as_str()) else {
            continue;
        };
        rel.arg_sorts = rel
            .arg_sorts
            .iter()
            .enumerate()
            .filter(|(idx, _)| !mask[*idx])
            .map(|(_, sort)| sort.clone())
            .collect();
    }
}

fn strip_rule_relation_apps(vc: &mut ChcVc, masks: &HashMap<String, Vec<bool>>) {
    for rule in &mut vc.rules {
        strip_relation_app_args(&mut rule.head, masks);
        if let Some(body_rel) = &mut rule.body.relation {
            strip_relation_app_args(body_rel, masks);
        }

        let mut folder = StripDeadArrayRelationExprs { masks, any_stripped: false };
        let rewritten_constraints: Vec<Expr> =
            rule.body.constraints.iter().map(|expr| fold_expr(&mut folder, expr)).collect();
        if folder.any_stripped {
            rule.body.constraints = Constraints::Owned(rewritten_constraints);
        }
    }
}

fn strip_relation_app_args(app: &mut RelationApp, masks: &HashMap<String, Vec<bool>>) -> bool {
    let Some(mask) = masks.get(app.name.as_str()) else {
        return false;
    };
    if app.args.len() != mask.len() || !mask.iter().any(|&dead| dead) {
        return false;
    }

    app.args = Arc::new(strip_args_by_mask(app.args.iter().cloned(), mask));
    true
}

fn strip_args_by_mask(args: impl IntoIterator<Item = Expr>, mask: &[bool]) -> Vec<Expr> {
    args.into_iter().enumerate().filter(|(idx, _)| !mask[*idx]).map(|(_, arg)| arg).collect()
}

fn remove_stripped_pad_vars(vc: &mut ChcVc, masks: &HashMap<String, Vec<bool>>) {
    let stripped_pad_names: HashSet<String> = masks
        .iter()
        .flat_map(|(rel_name, mask)| {
            mask.iter()
                .enumerate()
                .filter(|(_, dead)| **dead)
                .map(|(idx, _)| generated_pad_name(rel_name, idx))
        })
        .collect();
    if stripped_pad_names.is_empty() {
        return;
    }

    let keep = vc
        .vars()
        .iter()
        .filter(|var| !stripped_pad_names.contains(var.name.as_ref()))
        .map(|var| var.name.to_string())
        .collect();
    vc.retain_vars(&keep);
}

fn generated_pad_name(rel_name: &str, idx: usize) -> String {
    format!("__pad_{rel_name}_{idx}")
}

struct StripDeadArrayRelationExprs<'a> {
    masks: &'a HashMap<String, Vec<bool>>,
    any_stripped: bool,
}

impl ExprFold for StripDeadArrayRelationExprs<'_> {
    fn fold_post(&mut self, original: &Expr, children: Vec<Expr>) -> Expr {
        if let ExprValue::FuncApp { name, .. } = original.value()
            && let Some(mask) = self.masks.get(name.as_str())
            && children.len() == mask.len()
            && mask.iter().any(|&dead| dead)
        {
            self.any_stripped = true;
            return Expr::func_app_with_sort(
                name.clone(),
                strip_args_by_mask(children, mask),
                original.sort().clone(),
            );
        }
        rebuild_with_children(original, children)
    }
}

#[cfg(test)]
mod tests;

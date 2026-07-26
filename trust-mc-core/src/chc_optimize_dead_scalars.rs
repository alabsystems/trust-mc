// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dead identity-passthrough state variable elimination for CHC VCs.
//!
//! Removes state variables (both scalar and Array-sorted) that are pure
//! identity passthroughs: never constrained beyond `out = in` in any
//! rule. Reduces relation arity without losing verification information.
//!
//! Array-sorted vars are included because after constant propagation
//! eliminates error rules (e.g., trivially-true obj_valid checks),
//! arrays like `obj_valid`/`obj_size` may become pure identity
//! passthroughs. Pruning them drops the Array param count below the
//! PDR ≥2-Array bottleneck threshold.
//!
//! Safe to run multiple times — after constant propagation eliminates
//! dead rules, previously-live variables may become dead.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue, Sort};

use crate::chc::{ChcVc, RelationApp};
use crate::constraints::Constraints;

/// Prune dead identity-passthrough state variables from the VC.
///
/// A state variable is "dead" if in every rule it only appears in
/// identity constraints `(= out in)` or not at all. Returns count pruned.
/// Handles both scalar and Array-sorted vars — Array vars become dead
/// after const-prop eliminates error rules that referenced them.
pub(super) fn prune_dead_identity_scalars(vc: &mut ChcVc) -> usize {
    let mut scalar_pairs: Vec<(String, String)> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    for v in vc.vars() {
        if !v.name.ends_with("__out") {
            let output = format!("{}__out", v.name);
            if seen.insert(v.name.to_string()) {
                scalar_pairs.push((v.name.to_string(), output));
            }
        }
    }

    if scalar_pairs.is_empty() {
        return 0;
    }

    let constraint_infos: Vec<Vec<ConstraintInfo<'_>>> = vc
        .rules
        .iter()
        .map(|rule| {
            rule.body
                .constraints
                .iter()
                .map(|constraint| ConstraintInfo {
                    expr: constraint,
                    mentions: expr_var_mentions(constraint),
                    is_init_rule: rule.body.relation.is_none(),
                })
                .collect()
        })
        .collect();

    let mut dead_inputs: HashSet<String> = HashSet::new();
    let mut dead_outputs: HashSet<String> = HashSet::new();

    for (input, output) in &scalar_pairs {
        if is_dead_scalar(&constraint_infos, input, output) {
            dead_inputs.insert(input.clone());
            dead_outputs.insert(output.clone());
        }
    }

    if dead_inputs.is_empty() {
        return 0;
    }

    let count = dead_inputs.len();

    // Rewrite rules: drop identity constraints, remove dead vars.
    for rule in &mut vc.rules {
        let is_init_rule = rule.body.relation.is_none();
        let old: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        let new: Vec<Expr> = old
            .into_iter()
            .filter(|c| !is_dead_identity(c, &dead_inputs, &dead_outputs, is_init_rule))
            .collect();
        rule.body.constraints = Constraints::Owned(new);

        rule.head = remove_dead_args(&rule.head, &dead_inputs, &dead_outputs);
        if let Some(ref body_rel) = rule.body.relation {
            rule.body.relation = Some(remove_dead_args(body_rel, &dead_inputs, &dead_outputs));
        }
    }

    // Rewrite relation declarations to match new arities.
    let mut relation_sorts: HashMap<String, Vec<Sort>> = HashMap::new();
    for rule in &vc.rules {
        let name = rule.head.name.to_string();
        relation_sorts
            .entry(name)
            .or_insert_with(|| rule.head.args.iter().map(|a| a.sort().clone()).collect());
    }
    for rel in &mut vc.relations {
        if let Some(new_sorts) = relation_sorts.get(&rel.name) {
            rel.arg_sorts = new_sorts.clone();
        }
    }

    count
}

struct ConstraintInfo<'a> {
    expr: &'a Expr,
    mentions: HashSet<String>,
    is_init_rule: bool,
}

/// Check if a state variable is dead: pure identity passthrough or
/// constant-only initialization in all rules — never read.
fn is_dead_scalar(rules: &[Vec<ConstraintInfo<'_>>], input: &str, output: &str) -> bool {
    for rule in rules {
        for constraint in rule {
            if is_identity(constraint.expr, input, output) {
                continue;
            }
            // Allow constant-init of output in entry rules:
            // `(= output (const_array V))` or `(= output literal)`.
            // The output is set but never read — safe to prune.
            if is_const_init_of_output(constraint.expr, output) {
                continue;
            }
            if constraint.is_init_rule && is_const_select_of_input(constraint.expr, input) {
                continue;
            }
            if is_store_update_of_output(constraint.expr, input, output) {
                continue;
            }
            if constraint.mentions.contains(output) || constraint.mentions.contains(input) {
                return false;
            }
        }
    }
    true
}

/// Check if constraint is `(= input output)` or `(= output input)`.
fn is_identity(constraint: &Expr, input: &str, output: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    match (lhs.value(), rhs.value()) {
        (ExprValue::Var { name: a }, ExprValue::Var { name: b }) => {
            (a == input && b == output) || (a == output && b == input)
        }
        _ => false,
    }
}

/// Check if constraint is `(= output <constant>)` or `(= <constant> output)`.
///
/// Matches entry-rule initializations like `(= obj_valid__out (const_array false))`
/// or `(= obj_size__out (const_array #x00000000))`. These set the output to a
/// known constant but don't read the input — safe to prune when the variable
/// is otherwise dead (never read in any constraint).
fn is_const_init_of_output(constraint: &Expr, output: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    let val_side = if matches!(lhs.value(), ExprValue::Var { name } if name == output) {
        rhs
    } else if matches!(rhs.value(), ExprValue::Var { name } if name == output) {
        lhs
    } else {
        return false;
    };
    // The value side must be a constant (no variable references).
    !expr_mentions_any_var(val_side)
}

/// Check if constraint is `(= (select input const) const)` or the reverse.
fn is_const_select_of_input(constraint: &Expr, input: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    (is_select_of_var(lhs, input) && !expr_mentions_any_var(rhs))
        || (is_select_of_var(rhs, input) && !expr_mentions_any_var(lhs))
}

fn is_select_of_var(expr: &Expr, input: &str) -> bool {
    let ExprValue::Select { array, index } = expr.value() else {
        return false;
    };
    matches!(array.value(), ExprValue::Var { name } if name == input)
        && !expr_mentions_any_var(index)
}

/// Check if constraint is `(= output (store input const const))` or the reverse.
fn is_store_update_of_output(constraint: &Expr, input: &str, output: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    (is_output_var(lhs, output) && is_store_from_input(rhs, input))
        || (is_output_var(rhs, output) && is_store_from_input(lhs, input))
}

fn is_output_var(expr: &Expr, output: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name } if name == output)
}

fn is_store_from_input(expr: &Expr, input: &str) -> bool {
    let ExprValue::Store { array, index, value } = expr.value() else {
        return false;
    };
    matches!(array.value(), ExprValue::Var { name } if name == input)
        && !expr_mentions_any_var(index)
        && !expr_mentions_any_var(value)
}

/// Collect all variable names mentioned by an expression tree once.
fn expr_var_mentions(expr: &Expr) -> HashSet<String> {
    let mut mentions = HashSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value() {
            mentions.insert(name.to_string());
        }
        stack.extend(node.children());
    }
    mentions
}

/// Check if an expression mentions ANY variable.
fn expr_mentions_any_var(expr: &Expr) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if matches!(node.value(), ExprValue::Var { .. }) {
            return true;
        }
        stack.extend(node.children());
    }
    false
}

/// Check if constraint is a dead identity or dead const-init.
fn is_dead_identity(
    constraint: &Expr,
    dead_inputs: &HashSet<String>,
    dead_outputs: &HashSet<String>,
    is_init_rule: bool,
) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    match (lhs.value(), rhs.value()) {
        (ExprValue::Var { name: a }, ExprValue::Var { name: b }) => {
            (dead_outputs.contains(a.as_str()) && dead_inputs.contains(b.as_str()))
                || (dead_outputs.contains(b.as_str()) && dead_inputs.contains(a.as_str()))
        }
        // Const-init: (= dead_output <constant>)
        (ExprValue::Var { name }, _) if dead_outputs.contains(name.as_str()) => {
            !expr_mentions_any_var(rhs)
                || dead_inputs.iter().any(|input| is_store_from_input(rhs, input))
        }
        (_, ExprValue::Var { name }) if dead_outputs.contains(name.as_str()) => {
            !expr_mentions_any_var(lhs)
                || dead_inputs.iter().any(|input| is_store_from_input(lhs, input))
        }
        _ if is_init_rule => {
            dead_inputs.iter().any(|input| is_const_select_of_input(constraint, input))
        }
        _ => false,
    }
}

/// Remove dead vars from a relation application.
fn remove_dead_args(
    app: &RelationApp,
    dead_inputs: &HashSet<String>,
    dead_outputs: &HashSet<String>,
) -> RelationApp {
    let old_args = Arc::unwrap_or_clone(Arc::clone(&app.args));
    let new_args: Vec<Expr> = old_args
        .into_iter()
        .filter(|arg| {
            if let ExprValue::Var { name } = arg.value() {
                !dead_inputs.contains(name.as_str()) && !dead_outputs.contains(name.as_str())
            } else {
                true
            }
        })
        .collect();
    RelationApp::new(app.name.as_str(), new_args)
}

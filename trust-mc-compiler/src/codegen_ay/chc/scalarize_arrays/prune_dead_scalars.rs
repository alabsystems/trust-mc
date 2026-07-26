// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dead scalar state variable elimination.
//!
//! Removes scalar (non-Array) state variables that are pure identity
//! passthroughs: never constrained beyond `out = in` in any transition
//! rule, and never read in any non-identity constraint. These variables
//! inflate relation arity without carrying information.
//!
//! Common source: allocator MIR locals inlined into harness functions
//! that are on return-reachable paths but carry no verification-relevant
//! state for the harness.
//!
//! Part of #4050: PDR array-param bottleneck optimization.

use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort};
use tracing::debug;
use trust_mc_core::chc::{ChcVc, RelationApp, Rule};
use trust_mc_core::constraints::Constraints;

/// Prune dead scalar state variables from the VC.
///
/// A scalar state variable is "dead" if:
/// 1. It is not Array-sorted (arrays are handled by const_fold/scalarize)
/// 2. In every transition rule, it only appears in identity constraints
///    (`out = in`) or not at all
/// 3. It is never read in any non-identity constraint in any rule
///
/// Dead variables are removed from relation applications and declarations,
/// and their identity constraints are dropped.
pub(super) fn prune_dead_scalars(vc: &mut ChcVc) {
    prune_dead_single_use_local_assignments(vc);

    // Collect scalar (non-Array) state var pairs.
    let mut scalar_pairs: Vec<(String, String)> = Vec::new();
    let mut seen_inputs: HashSet<String> = HashSet::new();
    for v in vc.vars() {
        if !v.sort.is_array() && !v.name.ends_with("__out") {
            let output = format!("{}__out", v.name);
            if !seen_inputs.contains(v.name.as_ref()) {
                seen_inputs.insert(v.name.to_string());
                scalar_pairs.push((v.name.to_string(), output));
            }
        }
    }

    if scalar_pairs.is_empty() {
        prune_dead_single_use_local_assignments(vc);
        return;
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
                })
                .collect()
        })
        .collect();

    // Identify dead scalars: for each pair, check all rules.
    let mut dead_inputs: HashSet<String> = HashSet::new();
    let mut dead_outputs: HashSet<String> = HashSet::new();

    for (input_name, output_name) in &scalar_pairs {
        if is_dead_scalar(&constraint_infos, input_name, output_name) {
            dead_inputs.insert(input_name.clone());
            dead_outputs.insert(output_name.clone());
        }
    }

    if dead_inputs.is_empty() {
        prune_dead_single_use_local_assignments(vc);
        return;
    }

    debug!(
        total_scalar_pairs = scalar_pairs.len(),
        dead_scalars = dead_inputs.len(),
        live_scalars = scalar_pairs.len() - dead_inputs.len(),
        "CHC: pruning dead identity-passthrough scalars"
    );

    // Rewrite all rules: drop identity constraints, remove dead vars from relations.
    for rule in &mut vc.rules {
        let old_constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        let new_constraints: Vec<Expr> = old_constraints
            .into_iter()
            .filter(|c| !is_dead_identity_constraint(c, &dead_inputs, &dead_outputs))
            .collect();
        rule.body.constraints = Constraints::Owned(new_constraints);

        rule.head = remove_dead_args(&rule.head, &dead_inputs, &dead_outputs);
        if let Some(ref body_rel) = rule.body.relation {
            rule.body.relation = Some(remove_dead_args(body_rel, &dead_inputs, &dead_outputs));
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

    debug!(pruned = dead_inputs.len(), "CHC: dead scalar pruning complete");

    prune_dead_single_use_local_assignments(vc);
}

struct ConstraintInfo<'a> {
    expr: &'a Expr,
    mentions: HashSet<String>,
}

/// Check if a scalar state variable is dead (pure identity passthrough).
fn is_dead_scalar(rules: &[Vec<ConstraintInfo<'_>>], input_name: &str, output_name: &str) -> bool {
    for rule in rules {
        for constraint in rule {
            if is_identity_constraint(constraint.expr, input_name, output_name) {
                continue;
            }
            if constraint.mentions.contains(output_name) || constraint.mentions.contains(input_name)
            {
                return false;
            }
        }
    }
    true
}

/// Check if a constraint is `(= var1 var2)` where one is input and other is output.
fn is_identity_constraint(constraint: &Expr, input_name: &str, output_name: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    match (lhs.value(), rhs.value()) {
        (ExprValue::Var { name: n1 }, ExprValue::Var { name: n2 }) => {
            (n1 == input_name && n2 == output_name) || (n1 == output_name && n2 == input_name)
        }
        _ => false,
    }
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

/// Check if a constraint is a dead identity passthrough.
fn is_dead_identity_constraint(
    constraint: &Expr,
    dead_inputs: &HashSet<String>,
    dead_outputs: &HashSet<String>,
) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    if let (ExprValue::Var { name: n1 }, ExprValue::Var { name: n2 }) = (lhs.value(), rhs.value()) {
        // Drop (= dead_out dead_in) or (= dead_in dead_out)
        if (dead_outputs.contains(n1.as_str()) && dead_inputs.contains(n2.as_str()))
            || (dead_outputs.contains(n2.as_str()) && dead_inputs.contains(n1.as_str()))
        {
            return true;
        }
    }
    false
}

/// Remove dead vars from a relation application.
fn remove_dead_args(
    app: &RelationApp,
    dead_inputs: &HashSet<String>,
    dead_outputs: &HashSet<String>,
) -> RelationApp {
    let new_args: Vec<Expr> = app
        .args
        .iter()
        .filter(|arg| {
            if let ExprValue::Var { name } = arg.value() {
                !dead_inputs.contains(name.as_str()) && !dead_outputs.contains(name.as_str())
            } else {
                true
            }
        })
        .cloned()
        .collect();
    RelationApp::new(app.name.as_str(), new_args)
}

/// Drop constraints like `(= tmp expr)` when `tmp` is a rule-local
/// single-use temporary. Such equalities only bind an otherwise-unused
/// universally-quantified rule variable, so they are structurally redundant.
fn prune_dead_single_use_local_assignments(vc: &mut ChcVc) {
    let mut pruned = 0usize;
    for rule in &mut vc.rules {
        let protected_vars = relation_arg_vars(rule);
        loop {
            let old_constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
            let var_counts = constraint_var_counts(&old_constraints);
            let old_len = old_constraints.len();
            let new_constraints: Vec<Expr> = old_constraints
                .into_iter()
                .filter(|constraint| {
                    !is_dead_single_use_local_assignment(constraint, &var_counts, &protected_vars)
                })
                .collect();

            let newly_pruned = old_len - new_constraints.len();
            if newly_pruned == 0 {
                break;
            }

            pruned += newly_pruned;
            rule.body.constraints = Constraints::Owned(new_constraints);
        }
    }

    if pruned > 0 {
        debug!(pruned, "CHC: pruned dead single-use rule-local scalar assignments");
    }
}

fn relation_arg_vars(rule: &Rule) -> HashSet<String> {
    let mut vars = HashSet::new();
    collect_relation_arg_vars(&rule.head, &mut vars);
    if let Some(body_rel) = &rule.body.relation {
        collect_relation_arg_vars(body_rel, &mut vars);
    }
    vars
}

fn collect_relation_arg_vars(app: &RelationApp, vars: &mut HashSet<String>) {
    for arg in app.args.iter() {
        vars.extend(expr_var_mentions(arg));
    }
}

fn constraint_var_counts(constraints: &[Expr]) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    for constraint in constraints {
        add_expr_var_counts(constraint, &mut counts);
    }
    counts
}

fn add_expr_var_counts(expr: &Expr, counts: &mut HashMap<String, usize>) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value() {
            *counts.entry(name.to_string()).or_insert(0) += 1;
        }
        stack.extend(node.children());
    }
}

fn is_dead_single_use_local_assignment(
    constraint: &Expr,
    var_counts: &HashMap<String, usize>,
    protected_vars: &HashSet<String>,
) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    is_dead_single_use_assignment_side(lhs, rhs, var_counts, protected_vars)
}

fn is_dead_single_use_assignment_side(
    var_side: &Expr,
    value_side: &Expr,
    var_counts: &HashMap<String, usize>,
    protected_vars: &HashSet<String>,
) -> bool {
    let ExprValue::Var { name } = var_side.value() else {
        return false;
    };
    if protected_vars.contains(name.as_str()) {
        return false;
    }
    if var_counts.get(name.as_str()).copied() != Some(1) {
        return false;
    }
    !expr_var_mentions(value_side).contains(name.as_str())
}

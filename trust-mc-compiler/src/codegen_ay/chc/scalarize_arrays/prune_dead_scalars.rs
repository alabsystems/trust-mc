// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dead scalar state variable elimination.
//!
//! Removes scalar (non-Array) state SLOTS that are pure identity
//! passthroughs: never constrained beyond a frame copy between two names of
//! that same slot (`out = in`, `mid = in`, …) in any transition rule, and never
//! read in any other constraint. These slots inflate relation arity without
//! carrying information.
//!
//! Removal is positional and per relation: a column goes only when EVERY
//! application of that relation carries a dead slot there, so the declaration
//! and every application stay in lockstep. See `prune_dead_scalars` for what
//! by-name removal cost.
//!
//! Common source: allocator MIR locals inlined into harness functions
//! that are on return-reachable paths but carry no verification-relevant
//! state for the harness.
//!
//! Part of #4050: PDR array-param bottleneck optimization.

use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue};
use tracing::debug;
use trust_mc_core::chc::{ChcVc, RelationApp, Rule};
use trust_mc_core::constraints::Constraints;

/// Canonical slot identity of a state-variable name.
///
/// The encoder gives ONE relation column several names: the input var `X`, its
/// output `X__out`, and — inside a composed large-step fragment — the mid-frame
/// aliases `X__mid_bbN` / `X__mid_bbN__out` (`fragment_compose::set_names_to_mid`).
/// All of them denote the same slot, so any decision about that COLUMN has to be
/// taken on the canonical base, never on the surface name.
///
/// Mirrors `translate::canonical_slot_name`, minus the pad special case: a
/// `__pad_*` filler is its own (unpaired) identity here.
fn slot_base(name: &str) -> &str {
    let mut base = name;
    if let Some(pos) = base.find("__mid_bb") {
        base = &base[..pos];
    }
    if let Some(stripped) = base.strip_suffix("__out") {
        base = stripped;
    }
    base
}

/// `(= u v)` where `u` and `v` are two names of the SAME slot — the frame-copy
/// shape (`X__out = X`, `X__mid_bb7 = X`, …). Returns that slot's canonical base.
fn alias_identity_base(constraint: &Expr) -> Option<&str> {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return None;
    };
    let (ExprValue::Var { name: n1 }, ExprValue::Var { name: n2 }) = (lhs.value(), rhs.value())
    else {
        return None;
    };
    let b1 = slot_base(n1);
    if b1 == slot_base(n2) { Some(b1) } else { None }
}

/// Prune dead scalar state slots from the VC.
///
/// A scalar state slot is "dead" if:
/// 1. It is not Array-sorted (arrays are handled by const_fold/scalarize)
/// 2. Every constraint that mentions ANY name of the slot is a frame copy
///    between two names of that same slot (`out = in`, `mid = in`, …)
///
/// Removal is POSITIONAL, per relation, and only for a relation all of whose
/// applications currently conform to the declared arity. A column is dropped
/// only when *every* application of that relation carries a dead slot there.
///
/// Why not by name (the shape this replaced): a relation column is a property of
/// the RELATION, but the name at that column varies per rule — a fragment-composed
/// application carries `X__mid_bbN` where the per-block applications carry `X`, and
/// a padded application carries `__pad_*` where its peers carry a real slot. Filtering
/// arguments by name therefore removed the column from SOME applications of a relation
/// and not others. The declaration was then rebuilt from the first rule head only, and
/// the sort-only `fixup_relation_app_arities` padded the short applications back to
/// arity at the TAIL — shifting every column past the removal point. Two applications
/// of one loop-head relation ended up disagreeing about which state variable owns a
/// column, which is not cosmetic: it re-binds the loop counter's `Range { start, end }`
/// to the wrong slots, `Range::next` computes `start < end` on swapped operands, the
/// loop body becomes PROVABLY unreachable and every value it computes is frozen at its
/// pre-loop value. Live on `kani/Intrinsics/Count/{ctlz,cttz}.rs`, where it refuted a
/// true assertion; the mirror image of the same corruption fabricates PROOFS
/// (`block_relation_slot_names_consistent`, `dual_slot_misalign_option_predicate`).
///
/// Part of #4050: PDR array-param bottleneck optimization.
pub(super) fn prune_dead_scalars(vc: &mut ChcVc) {
    prune_dead_single_use_local_assignments(vc);

    // Candidate slots: canonical bases of every declared non-Array var.
    let mut dead: HashSet<String> = HashSet::new();
    for v in vc.vars() {
        if v.sort.is_array() {
            continue;
        }
        dead.insert(slot_base(v.name.as_ref()).to_string());
    }
    let total_slots = dead.len();
    if dead.is_empty() {
        prune_dead_single_use_local_assignments(vc);
        return;
    }

    // Disqualify every slot a non-frame-copy constraint reads or writes, under
    // ANY of its names.
    for rule in &vc.rules {
        for constraint in rule.body.constraints.iter() {
            if alias_identity_base(constraint).is_some() {
                continue;
            }
            for name in expr_var_mentions(constraint) {
                dead.remove(slot_base(&name));
            }
        }
    }

    if dead.is_empty() {
        prune_dead_single_use_local_assignments(vc);
        return;
    }

    // Per-relation dead-column mask. `None` = do not touch this relation's
    // columns: some application does not conform to the declared arity, or two
    // applications disagree about which slot owns a column, so positions are not
    // comparable across its applications.
    //
    // A column is droppable only when EVERY application either names the same
    // dead slot there or passes a variable-free constant (whose value nothing
    // can read, the slot being dead), and at least one application names it — a
    // column no application names cannot be shown dead.
    let decl_arity: HashMap<String, usize> =
        vc.relations.iter().map(|r| (r.name.clone(), r.arg_sorts.len())).collect();
    // relation -> per position: (droppable-so-far, slot named here, saw a name)
    let mut acc: HashMap<String, Option<Vec<(bool, Option<String>, bool)>>> = HashMap::new();
    for rule in &vc.rules {
        let mut observe = |app: &RelationApp| {
            let Some(&arity) = decl_arity.get(app.name.as_str()) else {
                acc.insert(app.name.to_string(), None);
                return;
            };
            let entry = acc
                .entry(app.name.to_string())
                .or_insert_with(|| Some(vec![(true, None, false); arity]));
            let Some(columns) = entry.as_mut() else { return };
            if app.args.len() != arity {
                *entry = None;
                return;
            }
            for (k, arg) in app.args.iter().enumerate() {
                match arg.value() {
                    ExprValue::Var { name } => {
                        let base = slot_base(name).to_string();
                        match &columns[k].1 {
                            // Two applications name different slots at one
                            // column: the frame is already corrupt, so refuse
                            // to edit this relation at all.
                            Some(seen) if *seen != base => {
                                *entry = None;
                                return;
                            }
                            Some(_) => {}
                            None => columns[k].1 = Some(base.clone()),
                        }
                        columns[k].2 = true;
                        if !dead.contains(base.as_str()) {
                            columns[k].0 = false;
                        }
                    }
                    _ if !expr_mentions_any_var(arg) => {}
                    _ => columns[k].0 = false,
                }
            }
        };
        observe(&rule.head);
        if let Some(ref body_rel) = rule.body.relation {
            observe(body_rel);
        }
    }
    let masks: HashMap<String, Option<Vec<bool>>> = acc
        .into_iter()
        .map(|(name, columns)| {
            let mask = columns.map(|cols| {
                cols.into_iter().map(|(droppable, _, named)| droppable && named).collect()
            });
            (name, mask)
        })
        .collect();

    let pruned_columns: usize = masks
        .values()
        .flatten()
        .map(|mask| mask.iter().filter(|dead_col| **dead_col).count())
        .sum();
    if pruned_columns == 0 {
        prune_dead_single_use_local_assignments(vc);
        return;
    }

    debug!(
        total_slots,
        dead_slots = dead.len(),
        pruned_columns,
        "CHC: pruning dead identity-passthrough scalars"
    );

    // Rewrite all rules: drop the dead columns, then the now-inert frame copies.
    for rule in &mut vc.rules {
        rule.head = remove_dead_columns(&rule.head, &masks);
        if let Some(ref body_rel) = rule.body.relation {
            rule.body.relation = Some(remove_dead_columns(body_rel, &masks));
        }

        // A frame copy is only inert once BOTH its names have left this rule's
        // relation atoms. A slot can be dead yet still occupy a column of a
        // relation this pass declined to touch; dropping its copy there would
        // turn the surviving column into an unconstrained free variable.
        let still_framed = relation_arg_vars(rule);
        let new_constraints: Vec<Expr> = rule
            .body
            .constraints
            .iter()
            .filter(|c| !is_inert_dead_frame_copy(c, &dead, &still_framed))
            .cloned()
            .collect();
        rule.body.constraints = Constraints::Owned(new_constraints);
    }

    // Rewrite relation declarations with the same mask that rewrote the apps.
    for rel in &mut vc.relations {
        let Some(Some(mask)) = masks.get(&rel.name) else { continue };
        if mask.len() != rel.arg_sorts.len() {
            continue;
        }
        let mut position = 0usize;
        rel.arg_sorts.retain(|_| {
            let keep = !mask[position];
            position += 1;
            keep
        });
    }

    debug!(pruned = pruned_columns, "CHC: dead scalar pruning complete");

    prune_dead_single_use_local_assignments(vc);
}

/// Is this constraint a frame copy of a dead slot whose names have all left the
/// rule's relation atoms?
fn is_inert_dead_frame_copy(
    constraint: &Expr,
    dead: &HashSet<String>,
    still_framed: &HashSet<String>,
) -> bool {
    let Some(base) = alias_identity_base(constraint) else {
        return false;
    };
    if !dead.contains(base) {
        return false;
    }
    expr_var_mentions(constraint).iter().all(|name| !still_framed.contains(name))
}

/// Drop the dead columns of a relation application, by POSITION.
fn remove_dead_columns(
    app: &RelationApp,
    masks: &HashMap<String, Option<Vec<bool>>>,
) -> RelationApp {
    let Some(Some(mask)) = masks.get(app.name.as_str()) else {
        return app.clone();
    };
    if mask.len() != app.args.len() {
        return app.clone();
    }
    let new_args: Vec<Expr> = app
        .args
        .iter()
        .zip(mask.iter())
        .filter(|(_, dead_col)| !**dead_col)
        .map(|(arg, _)| arg.clone())
        .collect();
    RelationApp::new(app.name.as_str(), new_args)
}

/// Does this expression mention any variable at all?
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

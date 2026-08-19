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

use ay_bindings::{Expr, ExprValue};

use crate::chc::{ChcVc, RelationApp};
use crate::constraints::Constraints;

/// Canonical slot identity of a state-variable name.
///
/// One relation COLUMN is named several ways by the encoder: the input var `X`,
/// its output `X__out`, and — inside a composed large-step fragment — the
/// mid-frame aliases `X__mid_bbN` / `X__mid_bbN__out`. Any decision about the
/// column has to be taken on this canonical base, never on the surface name.
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
/// shape. Returns that slot's canonical base.
fn alias_identity_base(constraint: &Expr) -> Option<&str> {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return None;
    };
    let (ExprValue::Var { name: a }, ExprValue::Var { name: b }) = (lhs.value(), rhs.value())
    else {
        return None;
    };
    let base = slot_base(a);
    if base == slot_base(b) { Some(base) } else { None }
}

/// Per-position removal plan for one relation.
///
/// `None` means "leave this relation's columns alone": some application does not
/// conform to the declared arity, or two applications disagree about which slot
/// owns a column, so positions are not comparable across its applications.
type ColumnMask = Option<Vec<bool>>;

/// Which columns of each relation may be dropped?
///
/// A column is droppable only when EVERY application of that relation either
/// carries a named argument for the same dead slot there, or carries a
/// variable-free constant (whose value nothing can read, the slot being dead).
/// At least one application must name the slot — a column no application names
/// cannot be shown dead, so it stays.
fn dead_column_masks(vc: &ChcVc, dead: &HashSet<String>) -> HashMap<String, ColumnMask> {
    let decl_arity: HashMap<&str, usize> =
        vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.len())).collect();
    // relation -> per position: (droppable-so-far, slot named here, saw a name)
    let mut acc: HashMap<String, Option<Vec<(bool, Option<String>, bool)>>> = HashMap::new();
    let observe = |app: &RelationApp,
                   acc: &mut HashMap<String, Option<Vec<(bool, Option<String>, bool)>>>| {
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
                        // Two applications name different slots at one column:
                        // the frame is already corrupt. Refuse to edit it.
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
                // A variable-free constant is safe to drop along with the
                // column: the slot is dead, so no constraint reads the value.
                _ if !expr_mentions_any_var(arg) => {}
                _ => columns[k].0 = false,
            }
        }
    };
    for rule in &vc.rules {
        observe(&rule.head, &mut acc);
        if let Some(ref body_rel) = rule.body.relation {
            observe(body_rel, &mut acc);
        }
    }
    acc.into_iter()
        .map(|(name, columns)| {
            let mask = columns.map(|cols| {
                cols.into_iter().map(|(droppable, _, named)| droppable && named).collect()
            });
            (name, mask)
        })
        .collect()
}

/// Drop the masked columns of a relation application, by POSITION.
fn remove_dead_columns(app: &RelationApp, masks: &HashMap<String, ColumnMask>) -> RelationApp {
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
        .filter(|(_, dropped)| !**dropped)
        .map(|(arg, _)| arg.clone())
        .collect();
    RelationApp::new(app.name.as_str(), new_args)
}

/// Prune dead identity-passthrough state variables from the VC.
///
/// A state variable is "dead" if in every rule it only appears in
/// identity constraints `(= out in)`, constant initializations, or not at all.
/// Returns the number of relation columns removed. Handles both scalar and
/// Array-sorted vars — Array vars become dead after const-prop eliminates error
/// rules that referenced them.
///
/// Removal is POSITIONAL and per relation (see [`dead_column_masks`]), because a
/// relation's column set is a property of the RELATION while the NAME at a given
/// column varies per rule: a fragment-composed application carries `X__mid_bbN`
/// where the per-block applications carry `X`, and after constant propagation it
/// may carry a literal instead. Filtering arguments by name therefore removed a
/// column from some applications of a relation and not others. The declaration
/// was then rebuilt from the first rule head alone, and the sort-only
/// `fixup_relation_app_arities` padded the short applications back to arity at
/// the TAIL, shifting every column past the removal point. Downstream,
/// `canonicalize_block_relation_apps` re-places constant-valued arguments
/// POSITIONALLY, so a `Range { start: 0, end: 8 }` initialization arrived as
/// `start = 8, end = 0`: `Range::next` computed `8 < 0`, the `for` body became
/// unreachable and every value it computes stayed frozen at its pre-loop value.
/// That refuted a true assertion in `kani/Intrinsics/Count/{ctlz,cttz}.rs`; the
/// mirror image of the same corruption fabricates PROOFS (see
/// `block_relation_slot_names_consistent`).
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

    let mut dead: HashSet<String> = HashSet::new();

    for (input, output) in &scalar_pairs {
        if slot_base(input) != input.as_str() {
            // Not a base name (a mid-frame alias): it is covered by its base.
            continue;
        }
        if is_dead_scalar(&constraint_infos, input, output) {
            dead.insert(input.clone());
        }
    }

    if dead.is_empty() {
        return 0;
    }

    let masks = dead_column_masks(vc, &dead);
    let pruned: usize = masks
        .values()
        .flatten()
        .map(|mask| mask.iter().filter(|dropped| **dropped).count())
        .sum();
    if pruned == 0 {
        return 0;
    }

    // Rewrite rules: drop the dead columns, then the frame copies they leave inert.
    for rule in &mut vc.rules {
        rule.head = remove_dead_columns(&rule.head, &masks);
        if let Some(ref body_rel) = rule.body.relation {
            rule.body.relation = Some(remove_dead_columns(body_rel, &masks));
        }

        // A dead slot's own equalities are only inert once every name of that
        // slot has left this rule's relation atoms. A slot can be dead yet still
        // occupy a column of a relation this pass declined to touch; dropping
        // its constraint there would turn the surviving column into an
        // unconstrained free variable — an over-approximation, not a
        // simplification.
        let mut framed: HashSet<String> = HashSet::new();
        for arg in rule.head.args.iter() {
            framed.extend(expr_var_mentions(arg));
        }
        if let Some(ref body_rel) = rule.body.relation {
            for arg in body_rel.args.iter() {
                framed.extend(expr_var_mentions(arg));
            }
        }
        let old: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        let new: Vec<Expr> =
            old.into_iter().filter(|c| !is_inert_dead_constraint(c, &dead, &framed)).collect();
        rule.body.constraints = Constraints::Owned(new);
    }

    // Rewrite relation declarations with the SAME mask that rewrote the apps.
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

    pruned
}

/// Is this constraint entirely about dead slots whose names have all left the
/// rule's relation atoms?
///
/// Every constraint that mentions a dead slot mentions ONLY that slot (that is
/// what [`is_dead_scalar`] establishes), so once the slot is out of the frame the
/// constraint binds nothing.
fn is_inert_dead_constraint(
    constraint: &Expr,
    dead: &HashSet<String>,
    framed: &HashSet<String>,
) -> bool {
    let mentions = expr_var_mentions(constraint);
    if mentions.is_empty() {
        return false;
    }
    mentions.iter().all(|name| dead.contains(slot_base(name)) && !framed.contains(name))
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
            // A mid-frame alias of this slot (`X__mid_bbN`) is the same COLUMN
            // under another name. Anything but a frame copy between two of the
            // slot's own names is a real read/write of the slot, so it keeps
            // the slot alive just as `X`/`X__out` would.
            if alias_identity_base(constraint.expr) == Some(input) {
                continue;
            }
            if constraint
                .mentions
                .iter()
                .any(|name| slot_base(name) == input && name != input && name != output)
            {
                return false;
            }
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

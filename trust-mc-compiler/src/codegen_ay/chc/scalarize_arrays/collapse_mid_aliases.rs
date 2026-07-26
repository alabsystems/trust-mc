// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule-local collapse of `__mid_bbN` array alias chains (Part of #40).
//!
//! Fragment composition emits identity frame constraints for unmodified state
//! variables, e.g. `(= mem__mid_bb1 mem)`, and threads the `__mid` name into
//! the successor relation application. The scalarizer's vocabulary is only
//! `X` / `X__out` (`canonical_input_name`), so a surviving `__mid` mention
//! trips the fail-closed residual check and unwinds the scalarization of the
//! whole array — dragging `mem (Array BV64 BV8)` and `obj_size` into every
//! loop predicate and stalling PDR (the ArrayParamLimit class).
//!
//! This pre-pass eliminates the aliases before identification: within each
//! rule, a conjunct `(= A B)` where both sides are Array-sorted variables and
//! at least one is a `__mid_bb` name defines a pure rule-local alias. Rule
//! variables are universally quantified over the clause, so substituting the
//! alias by its root everywhere in the rule (constraints, head args, body
//! relation args) and dropping the then-tautological identity is
//! verdict-identical equality elimination.
//!
//! Fail-closed guard: if any `__mid_bb` array variable in the rule also has a
//! *non-identity* defining equality (`(= mid <store/ite/...>)`), the entire
//! rule is left untouched — the existing residual-mention ban loop in
//! `scalarize_vc` then keeps the affected arrays un-scalarized, which is the
//! sound (if imprecise) baseline behavior.

use ay_bindings::{Expr, ExprValue, rebuild_with_children};
use tracing::debug;
use trust_mc_core::chc::{ChcVc, RelationApp};
use trust_mc_core::constraints::Constraints;

/// Whether this name is a fragment-composition intermediate.
fn is_mid_name(name: &str) -> bool {
    name.contains("__mid_bb")
}

/// `Some((name, sort_is_array))` when the expression is a plain variable.
fn as_var_name(expr: &Expr) -> Option<&str> {
    match expr.value() {
        ExprValue::Var { name } => Some(name),
        _ => None,
    }
}

/// A conjunct `(= A B)` with both sides Array-sorted plain variables, at
/// least one of them a `__mid_bb` intermediate.
fn as_mid_identity(expr: &Expr) -> Option<(String, String)> {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return None;
    };
    let a = as_var_name(lhs)?;
    let b = as_var_name(rhs)?;
    if !lhs.sort().is_array() || !rhs.sort().is_array() {
        return None;
    }
    if !is_mid_name(a) && !is_mid_name(b) {
        return None;
    }
    Some((a.to_string(), b.to_string()))
}

/// Substitute every occurrence of variable `from` with `to` in an expression.
fn substitute_var(expr: &Expr, from: &str, to: &Expr) -> Expr {
    if let ExprValue::Var { name } = expr.value() {
        if name == from {
            return to.clone();
        }
        return expr.clone();
    }
    let children: Vec<&Expr> = expr.children().collect();
    if children.is_empty() {
        return expr.clone();
    }
    let rewritten: Vec<Expr> = children.iter().map(|c| substitute_var(c, from, to)).collect();
    let changed = rewritten.iter().zip(children.iter()).any(|(new, old)| new != *old);
    if !changed {
        return expr.clone();
    }
    rebuild_with_children(expr, rewritten)
}

fn substitute_in_app(app: &RelationApp, from: &str, to: &Expr) -> RelationApp {
    let new_args: Vec<Expr> = app.args.iter().map(|arg| substitute_var(arg, from, to)).collect();
    RelationApp::new(app.name.as_str(), new_args)
}

/// A tautological equality `(= X X)` after substitution.
fn is_tautological_eq(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::Eq(lhs, rhs) if lhs == rhs)
}

/// Fail-closed guard: does any `__mid_bb` array variable in this rule have a
/// non-identity defining equality (one side the mid var, the other side not a
/// plain variable — a store/ITE/const-array definition)?
fn rule_has_non_identity_mid_definition(constraints: &[Expr]) -> bool {
    for constraint in constraints {
        let ExprValue::Eq(lhs, rhs) = constraint.value() else {
            continue;
        };
        let lhs_mid_array = as_var_name(lhs).is_some_and(is_mid_name) && lhs.sort().is_array();
        let rhs_mid_array = as_var_name(rhs).is_some_and(is_mid_name) && rhs.sort().is_array();
        if (lhs_mid_array && as_var_name(rhs).is_none())
            || (rhs_mid_array && as_var_name(lhs).is_none())
        {
            return true;
        }
    }
    false
}

/// Collapse `__mid_bbN` array aliases in every rule of the VC.
///
/// Runs before array identification in `scalarize_vc` so the canonical
/// `X`/`X__out` vocabulary sees through fragment-composition frame chains.
pub(super) fn collapse_mid_aliases(vc: &mut ChcVc) {
    let mut collapsed = 0usize;
    let mut skipped_rules = 0usize;

    for rule in &mut vc.rules {
        let mut constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();

        // Fast path: nothing to do for rules without mid-array identities.
        if !constraints.iter().any(|c| as_mid_identity(c).is_some()) {
            continue;
        }

        // Fail-closed: a mid var with a real (non-identity) definition means
        // the frame-chain assumption does not hold for this rule — leave it
        // untouched and let the residual ban loop handle the arrays.
        if rule_has_non_identity_mid_definition(&constraints) {
            skipped_rules += 1;
            continue;
        }

        let mut head = rule.head.clone();
        let mut body_relation = rule.body.relation.clone();
        let mut changed = false;

        // Each iteration eliminates one mid name from the rule entirely, so
        // this terminates within the number of distinct mid variables.
        loop {
            let Some((idx, (a, b))) = constraints
                .iter()
                .enumerate()
                .find_map(|(i, c)| as_mid_identity(c).map(|names| (i, names)))
            else {
                break;
            };

            // Substitute the mid name by the other side; when both are mid,
            // either direction eliminates one alias per iteration.
            let (from, to_name) = if is_mid_name(&a) { (a, b) } else { (b, a) };
            let to_expr = {
                // Reuse the sort from the identity conjunct's variable.
                let ExprValue::Eq(lhs, rhs) = constraints[idx].value() else {
                    unreachable!("as_mid_identity only matches Eq conjuncts");
                };
                let sort = if as_var_name(lhs) == Some(from.as_str()) {
                    rhs.sort().clone()
                } else {
                    lhs.sort().clone()
                };
                Expr::var(to_name, sort)
            };

            for constraint in &mut constraints {
                *constraint = substitute_var(constraint, &from, &to_expr);
            }
            head = substitute_in_app(&head, &from, &to_expr);
            if let Some(body_rel) = &body_relation {
                body_relation = Some(substitute_in_app(body_rel, &from, &to_expr));
            }
            constraints.retain(|c| !is_tautological_eq(c));
            collapsed += 1;
            changed = true;
        }

        if changed {
            rule.body.constraints = Constraints::Owned(constraints);
            rule.head = head;
            rule.body.relation = body_relation;
        }
    }

    if collapsed > 0 || skipped_rules > 0 {
        debug!(
            collapsed,
            skipped_rules, "CHC: collapsed __mid_bb array alias chains before scalarization (#40)"
        );
    }
}

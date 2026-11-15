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
//! Fail-closed guard, PER VARIABLE (not per rule): a `__mid_bb` array variable
//! that also carries a *non-identity* defining equality (`(= mid
//! <store/ite/...>)`) in the same rule is NOT eliminated — the residual-mention
//! ban loop in `scalarize_vc` then keeps that array un-scalarized, which is the
//! sound (if imprecise) baseline behavior. Every OTHER mid alias in the same
//! rule is still collapsed.
//!
//! Why per variable. Fragment composition emits, for one rule, a non-identity
//! definition for each state var the block MODIFIES and an identity frame
//! constraint for each var it does not (`fragment_compose/mod.rs`, "Frame
//! constraints for unmodified state vars"). So the ordinary shape of a loop
//! body that writes memory is one impure mid (`mem__mid_bbN = store(mem, ..)`)
//! beside pure ones (`obj_size__mid_bbN = obj_size`, other type arrays). The
//! original per-rule guard abandoned the WHOLE rule on the first impure mid,
//! which left the pure aliases in place, tripped the residual check on them
//! too, and banned those arrays as well — the very outcome this pass exists to
//! prevent. Eliminating an equality between two universally quantified clause
//! variables is verdict-identical whatever the other conjuncts say, so the
//! guard only ever needed to protect the impure variable itself.
//!
//! `prune_arrays.rs` already makes the same judgement per CONSTRAINT rather
//! than per rule (`is_pure_array_identity_copy`).

use std::collections::BTreeSet;

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

/// The `__mid_bb` array variables in this rule that carry a NON-identity
/// defining equality (one side the mid var, the other side not a plain
/// variable — a store / ITE / const-array definition).
///
/// These are the only variables the guard withholds: for them the frame-chain
/// assumption does not hold, so they keep their real definition and the
/// residual-mention ban in `scalarize_vc` keeps their array un-scalarized.
fn impure_mid_array_vars(constraints: &[Expr]) -> BTreeSet<String> {
    let mut impure = BTreeSet::new();
    for constraint in constraints {
        let ExprValue::Eq(lhs, rhs) = constraint.value() else {
            continue;
        };
        for (side, other) in [(lhs, rhs), (rhs, lhs)] {
            if side.sort().is_array()
                && as_var_name(other).is_none()
                && let Some(name) = as_var_name(side).filter(|name| is_mid_name(name))
            {
                impure.insert(name.to_string());
            }
        }
    }
    impure
}

/// Which side of a mid identity may be eliminated: a `__mid_bb` name whose only
/// definitions in this rule are identities. `None` leaves the conjunct in place
/// — the per-variable fail-closed case.
fn eliminable_alias(a: &str, b: &str, impure: &BTreeSet<String>) -> Option<(String, String)> {
    [(a, b), (b, a)].into_iter().find_map(|(from, to)| {
        (is_mid_name(from) && !impure.contains(from)).then(|| (from.to_string(), to.to_string()))
    })
}

/// Collapse `__mid_bbN` array aliases in every rule of the VC.
///
/// Runs before array identification in `scalarize_vc` so the canonical
/// `X`/`X__out` vocabulary sees through fragment-composition frame chains.
pub(super) fn collapse_mid_aliases(vc: &mut ChcVc) {
    let mut collapsed = 0usize;
    let mut withheld_vars = 0usize;

    for rule in &mut vc.rules {
        let mut constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();

        // Fast path: nothing to do for rules without mid-array identities.
        if !constraints.iter().any(|c| as_mid_identity(c).is_some()) {
            continue;
        }

        let mut head = rule.head.clone();
        let mut body_relation = rule.body.relation.clone();
        let mut changed = false;

        // Each iteration eliminates one mid name from the rule entirely — it is
        // substituted in every constraint, head arg and body-relation arg — so
        // this terminates within the number of distinct mid variables.
        //
        // The withheld set is recomputed every round on purpose: substituting
        // `midA := midB` can hand midB a real (non-identity) definition, and
        // midB must then be withheld in its turn.
        loop {
            let impure = impure_mid_array_vars(&constraints);
            let Some((idx, from, to_name)) = constraints.iter().enumerate().find_map(|(i, c)| {
                let (a, b) = as_mid_identity(c)?;
                let (from, to) = eliminable_alias(&a, &b, &impure)?;
                Some((i, from, to))
            }) else {
                // Nothing further is eliminable here: either no mid identities
                // remain, or the ones that do name a withheld variable.
                withheld_vars += impure.len();
                break;
            };
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

    if collapsed > 0 || withheld_vars > 0 {
        debug!(
            collapsed,
            withheld_vars, "CHC: collapsed __mid_bb array alias chains before scalarization (#40)"
        );
    }
}

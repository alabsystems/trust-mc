// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Strategy D: Auxiliary variable linearization for forward accumulator loops.
//!
//! Transforms nonlinear invariants (e.g., `sum <= counter²`) into linear
//! ones by adding a synthetic state variable `sq` that tracks `counter²`
//! via the forward-difference recurrence: `sq' = sq + 2*counter + 1`.
//!
//! This enables Z3 PDR to synthesize the invariant in LIA (Linear Integer
//! Arithmetic) without needing NLA (Nonlinear Arithmetic) support.
//!
//! Applied as a post-processing pass on the generated VC, after
//! `generate_transition_rules()` and `emit_loop_invariant_lemmas()`.
//!
//! Part of #3258: CHC lemma injection for last 2 UNKNOWN harnesses.
//! Part of designs/2026-03-05-unknown-14-recovery-roadmap.md Phase 3 Strategy D.

use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;
use tracing::debug;

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::types::int_sort;
use trust_mc_core::Constraints;
use trust_mc_core::chc::{RelationApp, Rule, RuleBody, VarDecl};

use super::lemma_hint::{IncrSource, LoopModification};
use super::lemma_hint_detect;

/// Apply auxiliary variable linearization to the CHC VC.
///
/// Scans for forward accumulator patterns (`sum += counter; counter += 1`)
/// and adds a synthetic `sq` variable that tracks `counter²` via LIA
/// recurrence, converting the NLA invariant to a LIA one.
///
/// Only active when int-lift is enabled and loop headers are present.
pub(in crate::codegen_ay::chc) fn apply_linearization(ctx: &mut ChcCtx<'_, '_>) {
    if !ctx.int_lift || ctx.loop_headers.is_empty() {
        return;
    }

    let result = lemma_hint_detect::detect_all_modifications(&ctx.vc.rules);

    // Find forward accumulator patterns: sum += counter; counter += 1
    let mut patterns: Vec<(Arc<str>, Arc<str>)> = Vec::new();
    for (accum_name, accum_mod) in &result.modifications {
        if let LoopModification::IncrementBy(IncrSource::Variable(counter_name)) = accum_mod {
            let counter: &str = counter_name;
            let counter_mod = result.modifications.get(counter);
            if matches!(counter_mod, Some(LoopModification::IncrementBy(IncrSource::Constant(1)))) {
                patterns.push((Arc::clone(accum_name), Arc::clone(counter_name)));
            }
        }
    }

    if patterns.is_empty() {
        return;
    }
    debug!(patterns = patterns.len(), "linearization: detected forward accumulator patterns");

    for (accum_name, counter_name) in &patterns {
        linearize_forward_accumulator(ctx, accum_name, counter_name);
    }
}

/// Linearize a single forward accumulator pattern.
///
/// For `sum += counter; counter += 1`, adds:
/// 1. Synthetic `sq` variable to all non-error relations
/// 2. Entry constraint: `sq = 0`
/// 3. Counter-update constraint: `sq' = sq + 2*counter + 1`
/// 4. Frame condition: `sq' = sq` for non-updating rules
/// 5. Removes NLA hints (counter²) emitted by `emit_loop_invariant_lemmas`
/// 6. Direct LIA hints on loop header: `2*sum + counter ≠ sq → error`
/// 7. Non-negativity hints: `sq < 0 → error`, `counter < 0`, `sum < 0` (D.1)
fn linearize_forward_accumulator(ctx: &mut ChcCtx<'_, '_>, accum_name: &str, counter_name: &str) {
    let sq_in_name: Arc<str> = Arc::from(["_aux_sq_", counter_name].concat());
    let sq_out_name: Arc<str> = Arc::from(["_aux_sq_", counter_name, "__out"].concat());
    let counter_out_name = [counter_name, "__out"].concat();

    // Declare universally quantified variables for sq
    ctx.vc.add_var(VarDecl::new(Arc::clone(&sq_in_name), int_sort()));
    ctx.vc.add_var(VarDecl::new(Arc::clone(&sq_out_name), int_sort()));

    let sq_in = Expr::var(&*sq_in_name, int_sort());
    let sq_out = Expr::var(&*sq_out_name, int_sort());

    // Step 1: Add Int sort to all non-error relation declarations
    for rel in &mut ctx.vc.relations {
        if rel.name != "error" {
            rel.arg_sorts.push(int_sort());
        }
    }

    // Step 2: Patch all existing rules to include sq in relation args
    for rule in &mut ctx.vc.rules {
        let is_entry = rule.body.relation.is_none();
        let head_is_error = rule.head.name == "error";

        // Determine if this rule updates the counter by checking for
        // counter__out = non-constant in equality constraints.
        // Initialization rules (counter__out = 0) use the frame condition instead.
        let updates_counter = !is_entry
            && !head_is_error
            && is_counter_update(&rule.body.constraints, &counter_out_name);

        // Append sq_in to body relation args (if body has a non-error relation)
        if let Some(ref mut body_rel) = rule.body.relation {
            if body_rel.name != "error" {
                let mut args = (*body_rel.args).clone();
                args.push(sq_in.clone());
                body_rel.args = Arc::new(args);
            }
        }

        // Append to head relation args (unless error)
        if !head_is_error {
            let mut args = (*rule.head.args).clone();
            if is_entry {
                // Entry: sq starts at 0
                args.push(Expr::int_const(BigInt::from(0)));
            } else if updates_counter {
                // Counter update: use sq_out (linked by constraint below)
                args.push(sq_out.clone());
            } else {
                // Frame condition: sq passes through unchanged
                args.push(sq_in.clone());
            }
            rule.head.args = Arc::new(args);
        }

        // Add linearization constraint for counter-update rules:
        // sq_out = sq + 2*counter + 1
        if updates_counter {
            let two = Expr::int_const(BigInt::from(2));
            let one = Expr::int_const(BigInt::from(1));
            let counter_var = Expr::var(counter_name, int_sort());
            let sq_next = sq_in.clone().int_add(two.int_mul(counter_var).int_add(one));
            let constraint = sq_out.clone().eq(sq_next);
            push_constraint(&mut rule.body.constraints, constraint);
        }
    }

    // Step 2.5: Remove NLA hint rules from emit_loop_invariant_lemmas.
    // Those hints contain counter * counter (nonlinear multiplication) which
    // PDR cannot handle via Farkas' lemma. The LIA equivalents using sq
    // are emitted in Step 3 below.
    remove_nla_counter_squared_hints(&mut ctx.vc.rules, counter_name);

    // Step 3: Emit LIA invariant hints directly on the loop header relation.
    // These replace the NLA hints (2*sum + counter = counter²) with LIA equivalents
    // using the synthetic sq variable (2*sum + counter = sq).
    // Direct hints on the full-state header are more effective than routing through
    // a summary projection, because PDR can incorporate them into the header
    // invariant without needing to reason about an extra relation.
    let headers: Vec<usize> = ctx.loop_headers.iter().copied().collect();
    for &header_bb in &headers {
        let Some(header_rel) = ctx.block_relations.get(&header_bb).map(|s| &**s) else {
            continue;
        };

        let mut header_args = ctx.project_state_args(header_bb);
        header_args.push(sq_in.clone());
        let sum_var = Expr::var(accum_name, int_sort());
        let counter_var = Expr::var(counter_name, int_sort());
        let two = Expr::int_const(BigInt::from(2));
        let zero = Expr::int_const(BigInt::from(0));

        // LIA hint: 2*sum + counter ≠ sq → error (replaces NLA: 2*sum + counter ≠ counter²)
        {
            let header_app = RelationApp::new(header_rel, header_args.clone());
            let two_sum_plus_ctr =
                two.clone().int_mul(sum_var.clone()).int_add(counter_var.clone());
            let neq_sq = two_sum_plus_ctr.eq(sq_in.clone()).not();
            ctx.vc.add_rule(Rule::new(
                RuleBody::new(Some(header_app), vec![neq_sq]),
                RelationApp::new("error", Vec::new()),
            ));
        }

        // Non-negativity: sq < 0 → error
        {
            let header_app = RelationApp::new(header_rel, header_args.clone());
            ctx.vc.add_rule(Rule::new(
                RuleBody::new(Some(header_app), vec![sq_in.clone().int_lt(zero.clone())]),
                RelationApp::new("error", Vec::new()),
            ));
        }

        // Non-negativity: counter < 0 → error
        {
            let header_app = RelationApp::new(header_rel, header_args.clone());
            ctx.vc.add_rule(Rule::new(
                RuleBody::new(Some(header_app), vec![counter_var.int_lt(zero.clone())]),
                RelationApp::new("error", Vec::new()),
            ));
        }

        // Non-negativity: sum < 0 → error
        {
            let header_app = RelationApp::new(header_rel, header_args);
            ctx.vc.add_rule(Rule::new(
                RuleBody::new(Some(header_app), vec![sum_var.int_lt(zero)]),
                RelationApp::new("error", Vec::new()),
            ));
        }

        debug!(
            header_bb,
            counter = %counter_name,
            accum = %accum_name,
            "emitted direct LIA hints on loop header (Strategy D + D.1)"
        );
    }

    debug!(
        counter = %counter_name,
        accum = %accum_name,
        "applied forward accumulator linearization (Strategy D + D.1)"
    );
}

/// Remove error rules containing `counter * counter` (NLA) patterns.
///
/// These rules were emitted by `emit_loop_invariant_lemmas` with the NLA
/// invariant `2*sum + counter = counter²`. The linearization pass replaces
/// this with the LIA equivalent `2*sum + counter = sq`, so the NLA rules
/// must be removed to prevent PDR from encountering nonlinear terms.
fn remove_nla_counter_squared_hints(rules: &mut Vec<Rule>, counter_name: &str) {
    let before = rules.len();
    rules.retain(|rule| {
        if rule.head.name != "error" {
            return true;
        }
        !constraints_contain_counter_squared(&rule.body.constraints, counter_name)
    });
    let removed = before - rules.len();
    if removed > 0 {
        debug!(removed, counter = %counter_name, "removed NLA counter² hint rules");
    }
}

/// Check if constraints contain a `counter * counter` multiplication.
fn constraints_contain_counter_squared(constraints: &Constraints, counter_name: &str) -> bool {
    for c in constraints {
        if expr_contains_counter_squared(c, counter_name) {
            return true;
        }
    }
    false
}

/// Recursively check if an expression contains `IntMul(Var(counter), Var(counter))`.
fn expr_contains_counter_squared(expr: &Expr, counter_name: &str) -> bool {
    match expr.value() {
        ExprValue::IntMul(lhs, rhs) => {
            if is_var_named(lhs, counter_name) && is_var_named(rhs, counter_name) {
                return true;
            }
            expr_contains_counter_squared(lhs, counter_name)
                || expr_contains_counter_squared(rhs, counter_name)
        }
        ExprValue::Not(inner) => expr_contains_counter_squared(inner, counter_name),
        ExprValue::Eq(lhs, rhs) | ExprValue::IntAdd(lhs, rhs) | ExprValue::IntSub(lhs, rhs) => {
            expr_contains_counter_squared(lhs, counter_name)
                || expr_contains_counter_squared(rhs, counter_name)
        }
        _ => false,
    }
}

/// Push a constraint expression into a `Constraints` container.
fn push_constraint(constraints: &mut Constraints, expr: Expr) {
    match constraints {
        Constraints::Owned(v) => v.push(expr),
        Constraints::Shared { extra, .. } => extra.push(expr),
    }
}

/// Check if a rule updates the counter (increments it) vs initializes it.
///
/// Scans for `counter__out = rhs` patterns where `rhs` is NOT a constant.
/// Initialization rules set `counter__out = 0` (constant), while back-edge
/// rules set `counter__out = f(...)` where `f` depends on variables.
///
/// This distinction is critical for linearization: the sq recurrence
/// (`sq' = sq + 2*counter + 1`) must only apply to back-edge rules where
/// the counter actually increments, not to initialization rules.
fn is_counter_update(constraints: &Constraints, var_name: &str) -> bool {
    for c in constraints {
        if let ExprValue::Eq(lhs, rhs) = c.value() {
            if is_var_named(lhs, var_name) && !is_constant(rhs) {
                return true;
            }
            if is_var_named(rhs, var_name) && !is_constant(lhs) {
                return true;
            }
        }
    }
    false
}

/// Check if an expression is a `Var` with the given name.
fn is_var_named(expr: &Expr, name: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name: n } if n == name)
}

/// Check if an expression is a constant (contains no variables).
///
/// An expression is constant if it's an IntConst, BitVecConst, BoolConst,
/// or a Bv2Int/Int2Bv wrapping a constant.
fn is_constant(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::IntConst(_) | ExprValue::BoolConst(_) => true,
        ExprValue::BitVecConst { .. } => true,
        ExprValue::Bv2Int(inner) | ExprValue::Int2Bv(inner, _) => is_constant(inner),
        _ => false,
    }
}

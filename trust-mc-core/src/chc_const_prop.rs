// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC constant propagation. Removes relation parameters that always carry the
//! same constant, reducing arity for PDR. Part of #3371.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};

use crate::chc::ChcVc;
use crate::constraints::Constraints;

#[path = "chc_const_prop_heap_liveness.rs"]
mod heap_liveness;
use heap_liveness::heap_liveness_positions;
pub use heap_liveness::{
    has_block_relation_cycle, has_scalarized_obj_size_bounds, has_scalarized_obj_valid_liveness,
    has_signed_overflow_error_edge,
};

#[path = "chc_const_prop_identity.rs"]
mod identity;
use identity::detect_identity_positions;

/// Propagates constants through a CHC verification condition.
///
/// Returns the total number of constant positions removed across all
/// iterations.
pub fn propagate_constants(vc: &mut ChcVc) -> usize {
    let mut total_propagated = 0;
    loop {
        let constants = identify_constant_positions(vc);
        if constants.is_empty() {
            break;
        }
        let propagated = apply_constant_propagation(vc, &constants);
        total_propagated += propagated;
        if propagated == 0 {
            break;
        }
    }
    // Eliminate rules whose body contains a trivially-false conjunct. This is
    // inert even for `error`/query-target heads: false premises are unreachable.
    eliminate_trivially_false_rules(vc);
    // Strip tautological constraints that are noise for PDR.
    strip_trivially_true_constraints(vc);
    total_propagated
}

/// For each relation, identifies positions where ALL head args resolve to
/// the same constant literal.
///
/// Head args are resolved through body constraints: if a head arg is a
/// variable `_out` with `(= _out #x4)` in the body, it resolves to `#x4`.
/// This handles the common CHC encoding pattern where constants flow
/// through `__out` variables.
///
/// Returns a map from relation name to a vec of `Option<Expr>` — `Some(c)` if
/// position i is always constant `c`, `None` otherwise.
fn identify_constant_positions(vc: &ChcVc) -> HashMap<String, Vec<Option<Expr>>> {
    // Collect: for each (relation, position), all resolved values at that position.
    // Self-referential rules (body relation == head relation) with identity
    // pass-through at a position are excluded — they preserve whatever value
    // the position has and should not prevent constant identification.
    let mut position_values: HashMap<String, Vec<Vec<Expr>>> = HashMap::new();
    let protected_positions = heap_liveness_positions(vc);

    for rule in &vc.rules {
        let resolved_args = resolve_head_args(rule);
        let name = rule.head.name.to_string();

        // Detect self-referential identity pass-through: if body relation
        // name == head relation name, check which positions are identity
        // (head arg at position i maps back to body arg at position i
        // through equality chains in the body constraints).
        let identity_positions = detect_identity_positions(rule);

        let entry =
            position_values.entry(name).or_insert_with(|| vec![Vec::new(); resolved_args.len()]);
        while entry.len() < resolved_args.len() {
            entry.push(Vec::new());
        }
        for (i, arg) in resolved_args.into_iter().enumerate() {
            // Skip identity positions from self-referential rules — they
            // don't contribute new information about what constant the
            // position holds.
            if identity_positions.contains(&i) {
                continue;
            }
            entry[i].push(arg);
        }
    }

    let mut result = HashMap::new();
    for (name, positions) in &position_values {
        let mut constants: Vec<Option<Expr>> = Vec::with_capacity(positions.len());
        let mut has_any = false;
        for values in positions {
            let refs: Vec<&Expr> = values.iter().collect();
            let pos = constants.len();
            if protected_positions
                .get(name.as_str())
                .is_some_and(|positions| positions.contains(&pos))
            {
                constants.push(None);
            } else if let Some(constant) = unique_constant(&refs) {
                constants.push(Some(constant.clone()));
                has_any = true;
            } else {
                constants.push(None);
            }
        }
        if has_any {
            result.insert(name.clone(), constants);
        }
    }
    result
}

/// Resolves head args through body constraints.
///
/// For each head arg, if it's a variable, checks the body constraints for
/// `(= var const)` or `(= const var)` assignments (including transitive
/// equality chains). Returns the resolved values (constants where possible,
/// original args otherwise).
fn resolve_head_args(rule: &crate::chc::Rule) -> Vec<Expr> {
    // First, build a map of variable → constant from body constraints.
    let mut known: HashMap<String, Expr> = HashMap::new();
    propagate_through_equalities(&rule.body.constraints, &mut known);

    // Resolve each head arg.
    rule.head
        .args
        .iter()
        .map(|arg| {
            if let ExprValue::Var { name } = arg.value() {
                if let Some(constant) = known.get(name) {
                    return constant.clone();
                }
            }
            arg.clone()
        })
        .collect()
}

/// Returns the constant value if all expressions are the same constant literal.
fn unique_constant<'a>(values: &[&'a Expr]) -> Option<&'a Expr> {
    if values.is_empty() {
        return None;
    }

    let first = values[0];
    if !is_constant(first) {
        return None;
    }

    for &v in &values[1..] {
        if v != first {
            return None;
        }
    }

    Some(first)
}

/// Constant literal: scalar, const_array, or store with all-constant components.
fn is_constant(expr: &Expr) -> bool {
    is_scalar_constant(expr)
        || matches!(expr.value(), ExprValue::ConstArray { value, .. } if is_constant(value))
        || matches!(expr.value(), ExprValue::Store { array, index, value } if is_constant(array) && is_constant(index) && is_constant(value))
}

/// Scalar constant only (Bool, BitVec, Int, Real). Excludes Store/ConstArray
/// whose derived PartialEq is structural, not semantic (#3479).
pub(crate) fn is_scalar_constant(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::BoolConst(_)
            | ExprValue::BitVecConst { .. }
            | ExprValue::IntConst(_)
            | ExprValue::RealConst(_)
    )
}

/// Applies constant propagation for one iteration.
///
/// For each rule whose body relation has constant positions:
/// 1. Records which body-relation variables map to constants.
/// 2. Propagates through equality chains in constraints.
/// 3. Substitutes known constants into constraint expressions.
/// 4. Replaces known-constant variables in head args.
/// 5. Adds explicit equality constraints for removed variables.
/// 6. Removes constant positions from body args.
///
/// Then strips constant positions from declarations and head args.
///
/// Returns the number of positions removed.
fn apply_constant_propagation(
    vc: &mut ChcVc,
    constants: &HashMap<String, Vec<Option<Expr>>>,
) -> usize {
    // Phase 1: Per-rule propagation.
    for rule in &mut vc.rules {
        let body_rel = match &rule.body.relation {
            Some(rel) => rel,
            None => continue,
        };

        let rel_constants = match constants.get(body_rel.name.as_str()) {
            Some(c) => c,
            None => continue,
        };

        // Build known_constants: var_name → constant_expr from body relation args.
        let mut known: HashMap<String, Expr> = HashMap::new();
        for (i, maybe_const) in rel_constants.iter().enumerate() {
            if let Some(constant) = maybe_const {
                if let Some(arg) = body_rel.args.get(i) {
                    if let ExprValue::Var { name } = arg.value() {
                        known.insert(name.clone(), constant.clone());
                    }
                }
            }
        }

        if known.is_empty() {
            continue;
        }

        // Propagate through equality chains in constraints.
        propagate_through_equalities(&rule.body.constraints, &mut known);

        // Propagate constants to unconstrained `__out` head variables.
        // The codegen creates identity pass-throughs as universally quantified
        // `__out` variables without explicit `(= X__out X)` constraints.
        // This is valid CHC but prevents const prop from cascading. For each
        // head arg `Var(Y)` where Y = X + "__out" and X is known-constant,
        // if Y is not already bound by any constraint, propagate the constant.
        propagate_to_unconstrained_out_vars(&rule.head.args, &rule.body.constraints, &mut known);

        // Substitute known constants into constraint expressions.
        // This transforms `(= _20 #x0)` into `(= #x4 #x0)` when `_20 → #x4`,
        // enabling PDR to evaluate the constraint directly without invariant
        // synthesis through the identity chain.
        let mut substituted: Vec<Expr> =
            rule.body.constraints.iter().map(|c| substitute_vars(c, &known)).collect();

        // Re-add explicit equality constraints for ALL known-constant
        // variables that appear in the body relation args (from_app).
        //
        // This serves two purposes:
        // 1. For globally-constant positions (from `rel_constants`): preserves
        //    the variable binding after the position is stripped from the
        //    relation signature in Phase 2.
        // 2. For per-rule equalities (e.g., SwitchInt guards): after
        //    `propagate_through_equalities` learns `var → const` from a
        //    guard like `(= var const)`, `substitute_vars` folds the guard
        //    to `true`. But the variable remains in `body.relation.args`
        //    (from_app), so without re-adding the constraint the variable
        //    becomes unconstrained — causing unsound over-approximation.
        //    Part of #3426.
        let body_rel_var_names: HashSet<&str> = body_rel
            .args
            .iter()
            .filter_map(|arg| {
                if let ExprValue::Var { name } = arg.value() { Some(name.as_str()) } else { None }
            })
            .collect();
        for (name, constant) in &known {
            if body_rel_var_names.contains(name.as_str()) {
                let var_expr = Expr::var(name.clone(), constant.sort().clone());
                substituted.push(var_expr.eq(constant.clone()));
            }
        }

        rule.body.constraints = Constraints::Owned(substituted);

        // Replace known-constant variables in head args.
        let old_args = Arc::unwrap_or_clone(Arc::clone(&rule.head.args));
        let new_args: Vec<Expr> = old_args
            .into_iter()
            .map(|arg| {
                if let ExprValue::Var { name } = arg.value() {
                    if let Some(constant) = known.get(name) {
                        return constant.clone();
                    }
                }
                arg
            })
            .collect();
        rule.head.args = Arc::new(new_args);

        // Remove constant positions from body relation args.
        if let Some(ref mut rel) = rule.body.relation {
            let rel_name: &str = &rel.name;
            if let Some(rel_consts) = constants.get(rel_name) {
                let old_args = Arc::unwrap_or_clone(Arc::clone(&rel.args));
                let new_args: Vec<Expr> = old_args
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| rel_consts.get(*i).map_or(true, |c| c.is_none()))
                    .map(|(_, arg)| arg)
                    .collect();
                rel.args = Arc::new(new_args);
            }
        }
    }

    // Phase 2: Strip constant positions from head args and declarations.
    let mut total_stripped = 0;

    // Strip head args in rules where the relation has constant positions.
    for rule in &mut vc.rules {
        let rel_name = rule.head.name.to_string();
        if let Some(rel_consts) = constants.get(&rel_name) {
            let old_args = Arc::unwrap_or_clone(Arc::clone(&rule.head.args));
            let new_args: Vec<Expr> = old_args
                .into_iter()
                .enumerate()
                .filter(|(i, _)| rel_consts.get(*i).map_or(true, |c| c.is_none()))
                .map(|(_, arg)| arg)
                .collect();
            rule.head.args = Arc::new(new_args);
        }
    }

    // Strip relation declarations.
    for rel in &mut vc.relations {
        if let Some(rel_consts) = constants.get(&rel.name) {
            let count_before = rel.arg_sorts.len();
            let mut i = 0;
            rel.arg_sorts.retain(|_| {
                let keep = rel_consts.get(i).map_or(true, |c| c.is_none());
                i += 1;
                keep
            });
            total_stripped += count_before - rel.arg_sorts.len();
        }
    }

    total_stripped
}

/// Propagates constants through equality chains in constraints.
///
/// Flattens `And(...)` conjunctions, then iterates until fixed point:
/// - `(= Var Const)` / `(= Const Var)` — direct assignment
/// - `(= Var(a) Var(b))` where one is known — transitive propagation
/// - `(= Var Expr)` where Expr evaluates to constant after substitution
fn propagate_through_equalities(constraints: &Constraints, known: &mut HashMap<String, Expr>) {
    let flat = flatten_conjunctions(constraints);
    let mut changed = true;
    while changed {
        changed = false;
        for expr in &flat {
            if let ExprValue::Eq(lhs, rhs) = expr.value() {
                match (lhs.value(), rhs.value()) {
                    // (= Var Const) or (= Const Var)
                    (ExprValue::Var { name }, _) if is_constant(rhs) => {
                        if !known.contains_key(name) {
                            known.insert(name.clone(), rhs.clone());
                            changed = true;
                        }
                    }
                    (_, ExprValue::Var { name }) if is_constant(lhs) => {
                        if !known.contains_key(name) {
                            known.insert(name.clone(), lhs.clone());
                            changed = true;
                        }
                    }
                    // (= Var(a) Var(b)) where one is known
                    (ExprValue::Var { name: a }, ExprValue::Var { name: b }) => {
                        if let Some(c) = known.get(b).cloned() {
                            if !known.contains_key(a) {
                                known.insert(a.clone(), c);
                                changed = true;
                            }
                        } else if let Some(c) = known.get(a).cloned() {
                            if !known.contains_key(b) {
                                known.insert(b.clone(), c);
                                changed = true;
                            }
                        }
                    }
                    // (= Var Expr) where Expr evaluates to constant after substitution
                    // or folds to constant via try_eval_to_const (e.g., extract(concat(3, 0))).
                    (ExprValue::Var { name }, _) if !known.contains_key(name) => {
                        let evaluated = substitute_vars(rhs, known);
                        if is_constant(&evaluated) {
                            known.insert(name.clone(), evaluated);
                            changed = true;
                        } else if let Some(folded) = eval::try_eval_to_const(&evaluated) {
                            known.insert(name.clone(), folded);
                            changed = true;
                        }
                    }
                    (_, ExprValue::Var { name }) if !known.contains_key(name) => {
                        let evaluated = substitute_vars(lhs, known);
                        if is_constant(&evaluated) {
                            known.insert(name.clone(), evaluated);
                            changed = true;
                        } else if let Some(folded) = eval::try_eval_to_const(&evaluated) {
                            known.insert(name.clone(), folded);
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    // Phases 2-3: Resolve scalar constants flowing through array store/select.
    array::resolve_array_store_selects(&flat, known);
}

#[path = "chc_const_prop_eval.rs"]
pub mod eval;

#[path = "chc_const_prop_subst.rs"]
mod subst;

#[path = "chc_const_prop_array.rs"]
mod array;

use eval::{
    flatten_conjunctions, has_false_conjunct, propagate_to_unconstrained_out_vars,
    strip_trivially_true_constraints,
};
use subst::substitute_vars;

/// Eliminates rules whose body constraints contain `false`.
///
/// Error-headed rules are exempt (task #76): a false-bodied error rule such as
/// `(rule (=> false error))` is a deliberate discharge obligation
/// (straightline `replace_with_unsat_error_obligation`) or a check proven
/// unreachable by const-prop — not an unreachable transition. Deleting it
/// degrades a certified discharge into the naked "no rules at all" shape,
/// which the driver's trivial-safe path cannot distinguish from LOST checks
/// (the emit-time degenerate fail-close exempts `trivially_safe_discharged`
/// VCs precisely because this obligation is expected to survive).
/// Is this rule the canonical certified-discharge shape: NO body relation and
/// a body that is exactly the literal `false` (or a conjunction collapsing to
/// it)? Part of task #76's retention refinement — see the comment at the
/// retention site.
pub(crate) fn rule_body_is_literal_false(rule: &crate::chc::Rule) -> bool {
    use ay_bindings::ExprValue;
    rule.body.relation.is_none()
        && !rule.body.constraints.is_empty()
        && rule.body.constraints.iter().all(|c| matches!(c.value(), ExprValue::BoolConst(false)))
}

fn eliminate_trivially_false_rules(vc: &mut ChcVc) -> usize {
    let before = vc.rules.len();
    vc.rules.retain(|rule| {
        let head: &str = rule.head.name.as_ref();
        if (head == "error" || head.starts_with("error_p")) && rule_body_is_literal_false(rule) {
            // Retain ONLY the certified discharge shape (a LITERAL `false`
            // body, as emitted by `replace_with_unsat_error_obligation`).
            // Complex-bodied error rules that merely EVALUATE to false are
            // genuinely infeasible edges — retaining them sends the solver
            // into re-deriving the infeasibility (offset-bytes-overflow
            // regressed 272ms -> 59.8s at the v41 gate under the blanket
            // exemption).
            return true;
        }
        !has_false_conjunct(&rule.body.constraints)
    });
    before - vc.rules.len()
}

impl ChcVc {
    /// Propagates constants through the CHC verification condition.
    /// Delegates to [`propagate_constants`] — see module docs for details.
    pub fn propagate_constants(&mut self) -> usize {
        propagate_constants(self)
    }

    /// Eliminates unreachable rules whose body constraints contain `false`.
    pub fn eliminate_trivially_false_rules(&mut self) -> usize {
        eliminate_trivially_false_rules(self)
    }
}

#[cfg(test)]
#[path = "chc_const_prop_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "chc_const_prop_heap_liveness_tests.rs"]
mod heap_liveness_tests;

#[cfg(test)]
#[path = "chc_const_prop_overlap_shuffle_tests.rs"]
mod overlap_shuffle_tests;

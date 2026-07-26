// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dead declare-var and dead constraint elimination for CHC VCs.
//!
//! After array pruning and scalarization, typed memory arrays are removed
//! from relation signatures but their `declare-var` entries and store/select
//! constraints remain. These universally quantified array variables force
//! the solver into Array theory even when all relation predicates are
//! scalar-only. This pass strips dead constraints and their variables.

use std::collections::{HashMap, HashSet};

use ay_bindings::ExprValue;

use crate::chc::ChcVc;
use crate::chc_const_prop::rule_body_is_literal_false;
use crate::constraints::Constraints;

/// Prunes dead constraints and stale declare-var entries.
///
/// STAGE 1 (#4278 generalization): rules headed by the query target or by a
/// per-property error relation (`error_p{N}`, BSEM-18) are protected
/// rule-locally — none of their constraints are ever stripped. See
/// [`collect_protected_heads`].
///
/// STAGE 2 (correctness-preserving pruning): liveness is a TRANSITIVE
/// CLOSURE seeded from relation-app vars, protected-rule constraint vars,
/// and cover vars (see [`close_essential_transitively`]); a constraint is
/// stripped only if its variable set is fully disjoint from the closed set
/// AND it is a definitional variable equality `(= x e)` whose bound variable
/// occurs nowhere else in the rule — a provable semantic no-op (see
/// [`is_strippable`]). Deletion iterates rule-locally so chained dead
/// definitions (`a2 = f(a1)`, `a1 = g(a0)`) unwind one hop per round.
///
/// Returns the number of constraints stripped.
pub(super) fn prune_dead_vars_and_constraints(vc: &mut ChcVc) -> usize {
    let mut total_stripped = prune_trivially_false_rules(vc);

    // Collect all variable names in relation apps — these are "essential".
    let mut essential: HashSet<String> = HashSet::new();
    for rule in &vc.rules {
        collect_relation_app_vars(&rule.head, &mut essential);
        if let Some(ref rel) = rule.body.relation {
            collect_relation_app_vars(rel, &mut essential);
        }
    }

    // STAGE 1 (#4278 generalization): error/query-headed rules are protected
    // rule-LOCALLY — the strip loop below skips them entirely (keeps ALL of
    // their constraints), and their variables are deliberately NOT added to
    // the global `essential` fixpoint. See `collect_protected_heads` for the
    // full rationale (BSEM-18 `error_p{N}` heads; the historical global
    // re-seed cascade).
    let protected_heads = collect_protected_heads(vc);

    // STAGE 2: seed the liveness closure with the constraint variables of
    // protected (error/query) rules. Stage 1 already keeps those rules intact
    // rule-locally; seeding their vars here only WIDENS the retention closure
    // computed below (more constraints kept in the transition rules that feed
    // the error guards) — it can never re-enable stripping anywhere.
    for rule in &vc.rules {
        if protected_heads.contains(&*rule.head.name) {
            for constraint in rule.body.constraints.iter() {
                collect_expr_vars(constraint, &mut essential);
            }
        }
    }

    // Cover assertion vars are also essential.
    for (_, cond) in &vc.cover_assertions {
        collect_expr_vars(cond, &mut essential);
    }

    if essential.is_empty() {
        return total_stripped;
    }

    // STAGE 2: transitive liveness closure. See
    // `close_essential_transitively` for why one-hop liveness is not enough
    // (interior `__mid_bb` equality-chain hops emitted by fragment_compose).
    close_essential_transitively(vc, &mut essential);

    // Strip dead constraints. STAGE 2 replaced the historical one-hop
    // criterion ("keep iff ALL vars essential, or an equality with an
    // essential var on one side") with correctness-preserving pruning:
    //
    // A constraint is stripped ONLY if BOTH hold:
    // 1. its variable set is FULLY DISJOINT from the transitively-closed
    //    essential set (it lives in a cluster disconnected from every
    //    relation app, protected rule, and cover assertion), AND
    // 2. it is a definitional variable equality `(= x e)` where `x` is a
    //    plain variable, `e` does not mention `x`, and `x` appears in no
    //    other constraint of the same rule. Then `∃x. x = e` is vacuously
    //    true and dropping the conjunct is an exact semantic no-op.
    //
    // Condition 2 is what makes the pass semantics-preserving: deleting a
    // disconnected but possibly-UNSAT cluster would WEAKEN the rule (its
    // body was unsatisfiable, i.e. the rule was vacuous; after deletion it
    // fires), which can silently delete a real error edge — the task-#57
    // missed-bug surface. Such clusters are kept instead.
    //
    // We iterate because deleting a definitional equality can orphan a
    // variable of an upstream definition (chains like `a2 = f(a1)`,
    // `a1 = g(a0)`: `a1` becomes single-occurrence only after `a2 = f(a1)`
    // is gone). The closed `essential` set is invariant under this loop:
    // only fully-disjoint constraints are removed, so no constraint that
    // contributed a closure edge is ever deleted.
    loop {
        let mut round_stripped = 0;

        for rule in &mut vc.rules {
            // STAGE 1: rule-local protection of error/query-headed rules.
            // Error rules encode `reach(state) ∧ ¬safety_cond → error_p{N}`;
            // stripping ANY of their constraints weakens the guard — in the
            // limit producing a literally unconditional
            // `(rule (=> (main__bb4 ...) error_p0))` — which fabricates
            // "Genuine" counterexamples on safe programs. Rules are
            // individually universally quantified, so keeping a protected
            // rule intact requires nothing from other rules: skip it whole,
            // WITHOUT seeding the global `essential` fixpoint from it.
            if protected_heads.contains(&*rule.head.name) {
                continue;
            }
            let old: Vec<ay_bindings::Expr> = rule.body.constraints.iter().cloned().collect();
            let n = old.len();

            // STAGE 2: per-rule occurrence counts — the number of constraints
            // of THIS rule mentioning each variable. Rules are individually
            // universally quantified, so rule-local occurrence is the right
            // scope for the "appears nowhere else" test. (Occurrences in the
            // rule's relation apps need no counting: relation-app vars are
            // essential, and strippability already requires disjointness.)
            let var_sets: Vec<HashSet<String>> = old
                .iter()
                .map(|c| {
                    let mut vars = HashSet::new();
                    collect_expr_vars(c, &mut vars);
                    vars
                })
                .collect();
            let mut occurs: HashMap<&str, usize> = HashMap::new();
            for vars in &var_sets {
                for v in vars {
                    *occurs.entry(v.as_str()).or_insert(0) += 1;
                }
            }

            let keep: Vec<bool> = old
                .iter()
                .zip(&var_sets)
                .map(|(c, vars)| !is_strippable(c, vars, &essential, &occurs))
                .collect();
            if keep.iter().all(|&k| k) {
                continue;
            }

            let new: Vec<ay_bindings::Expr> =
                old.into_iter().zip(keep).filter_map(|(c, k)| k.then_some(c)).collect();
            round_stripped += n - new.len();
            rule.body.constraints = Constraints::Owned(new);
        }

        total_stripped += round_stripped;
        if round_stripped == 0 {
            break;
        }
        // STAGE 2: no essential-set recalculation here — the closed set is
        // invariant under the restricted deletion (see the loop comment).
        // Iterating re-checks only the rule-local occurrence counts, which
        // unlock chained definitional deletions.
    }

    // Prune declare-var entries for unreferenced variables.
    let mut referenced: HashSet<String> = essential;
    for rule in &vc.rules {
        for c in rule.body.constraints.iter() {
            collect_expr_vars(c, &mut referenced);
        }
    }
    for (_, cond) in &vc.cover_assertions {
        collect_expr_vars(cond, &mut referenced);
    }
    vc.retain_vars(&referenced);

    total_stripped += dedupe_rules(vc);

    total_stripped
}

/// STAGE 1 (#4278 generalization): computes the set of protected rule heads.
///
/// Error rules have the form `reach(state) ∧ ¬safety_cond → error_head` and
/// their guard conditions frequently reference rule-local fresh variables
/// (e.g. `__kani_any_inline_*`, `__mid_bb{N}` fragment snapshots) that appear
/// in no relation signature. Stripping any constraint from such a rule
/// silently converts a conditional error rule into an unconditional one,
/// which fabricates counterexamples on safe programs.
///
/// Historically (#4278) this was handled by globally seeding the essential
/// set from constraints of rules whose head equals the query target. That
/// had two defects:
///
/// 1. It missed the BSEM-18 per-property heads `error_p{N}` (see
///    trust-mc-compiler's `error_property.rs`): every real check is headed
///    by `error_p{N}` and bridged into `error` by a constraint-free rule,
///    so the protection had become a no-op — the root of the
///    Rotate/bitreverse/loop-contract spurious-FP clusters.
/// 2. The GLOBAL (re-)seed let error-rule vars resurrect constraints in
///    unrelated transition rules — a cascade implicated in a
///    contract-postcondition missed bug (task #57).
///
/// Rules are individually universally quantified, so an error rule's
/// semantics depends only on its own body (constraints + body relation app):
/// rule-LOCAL protection (skip the rule in the strip loop; never seed the
/// global fixpoint from it) is both sufficient and cascade-free. The final
/// declare-var retention pass collects variables from ALL surviving
/// constraints, so the protected rules' variable declarations survive too.
///
/// The protected set is computed structurally (no string-prefix matching):
///
/// 1. the aggregate query target (`vc.query.target`, default `"error"`);
/// 2. every per-property error relation registered in `vc.properties`
///    (BSEM-18: one `error_p{id}` per check site);
/// 3. defensively, the body relation of every constraint-free bridge rule
///    `p() → query_target()` with a nullary body relation — the exact
///    BSEM-18 bridge shape — covering VCs whose `properties` metadata is
///    not populated (hand-built or ingested VCs).
fn collect_protected_heads(vc: &ChcVc) -> HashSet<String> {
    let query_target = vc.query.target.clone().unwrap_or_else(|| "error".to_owned());
    let mut protected: HashSet<String> = HashSet::new();
    for property in &vc.properties {
        protected.insert(property.relation.clone());
    }
    for rule in &vc.rules {
        if rule.head.name == query_target.as_str() && rule.body.constraints.is_empty() {
            if let Some(ref rel) = rule.body.relation {
                if rel.args.is_empty() {
                    protected.insert(rel.name.to_string());
                }
            }
        }
    }
    protected.insert(query_target);
    protected
}

/// STAGE 2: transitive liveness closure over shared-variable edges.
///
/// Starting from the seed set (relation-app vars, protected-rule constraint
/// vars, cover vars), repeatedly mark ALL variables of any constraint that
/// shares at least one variable with the essential set, until fixpoint.
///
/// This repairs the multi-hop definition chains that the historical one-hop
/// keep rule cut: `fragment_compose` emits loop frame chains like
/// `mid_bb26 = entry_var; mid_bb21 = mid_bb26; …; head_arg = mid_bb5` whose
/// interior hops mention no relation-app variable at all. Cutting an interior
/// hop left the chain end dangling (havocked loop-entry state), which
/// downstream constant propagation then specialized into a fabricated
/// counterexample (ctlz/cttz cluster).
fn close_essential_transitively(vc: &ChcVc, essential: &mut HashSet<String>) {
    // Cache per-constraint var sets once; drop a constraint from the
    // worklist as soon as all its vars are essential.
    let mut worklist: Vec<HashSet<String>> = Vec::new();
    for rule in &vc.rules {
        for constraint in rule.body.constraints.iter() {
            let mut vars = HashSet::new();
            collect_expr_vars(constraint, &mut vars);
            if !vars.is_empty() {
                worklist.push(vars);
            }
        }
    }
    loop {
        let mut changed = false;
        worklist.retain(|vars| {
            if vars.is_disjoint(essential) {
                return true; // not (yet) connected — keep on the worklist
            }
            for v in vars {
                if essential.insert(v.clone()) {
                    changed = true;
                }
            }
            false // fully essential now — no need to revisit
        });
        if !changed {
            break;
        }
    }
}

/// STAGE 2: decides whether a single constraint may be deleted.
///
/// A constraint is strippable ONLY if its variables are fully disjoint from
/// the transitively-closed essential set AND it is a definitional variable
/// equality `(= x e)` (either orientation) where `x` is a plain variable
/// that does not occur in `e` and occurs in no other constraint of the same
/// rule (`occurs[x] == 1`). Under per-rule universal quantification,
/// dropping such a conjunct rewrites `∃x. B ∧ x = e` into `B ∧ (∃x. x = e)`
/// where `∃x. x = e` is vacuously true — an exact semantic no-op, so the
/// deletion can never weaken (or strengthen) the rule.
fn is_strippable(
    constraint: &ay_bindings::Expr,
    vars: &HashSet<String>,
    essential: &HashSet<String>,
    occurs: &HashMap<&str, usize>,
) -> bool {
    // Pure literals (no vars) are never stripped here; literally-false
    // bodies are handled by `prune_trivially_false_rules`.
    if vars.is_empty() {
        return false;
    }
    // Fully-disjoint requirement: any overlap with the closed essential set
    // means the constraint (transitively) feeds a relation app, a protected
    // error rule, or a cover assertion — keep it.
    if vars.iter().any(|v| essential.contains(v)) {
        return false;
    }
    if let ExprValue::Eq(lhs, rhs) = constraint.value() {
        for (var_side, expr_side) in [(lhs, rhs), (rhs, lhs)] {
            if let ExprValue::Var { name } = var_side.value() {
                let mut expr_vars = HashSet::new();
                collect_expr_vars(expr_side, &mut expr_vars);
                if !expr_vars.contains(name) && occurs.get(name.as_str()).copied() == Some(1) {
                    return true;
                }
            }
        }
    }
    false
}

fn dedupe_rules(vc: &mut ChcVc) -> usize {
    let mut stripped = 0;
    let mut seen = HashSet::new();
    vc.rules.retain(|rule| {
        if seen.insert(rule.clone()) {
            true
        } else {
            stripped += rule.body.constraints.len();
            false
        }
    });
    stripped
}

fn prune_trivially_false_rules(vc: &mut ChcVc) -> usize {
    let mut stripped = 0;
    vc.rules.retain(|rule| {
        // Error-headed false-bodied rules are exempt (task #76): they are
        // deliberate discharge obligations (`(rule (=> false error))` from
        // the straightline `replace_with_unsat_error_obligation`) or checks
        // proven unreachable — deleting them degrades a certified discharge
        // into the naked "no rules at all" shape the driver cannot
        // distinguish from LOST checks.
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
        let has_false = rule.body.constraints.iter().any(constraint_contains_false_conjunct);
        if has_false {
            stripped += rule.body.constraints.len();
            false
        } else {
            true
        }
    });
    stripped
}

fn constraint_contains_false_conjunct(expr: &ay_bindings::Expr) -> bool {
    match expr.value() {
        ExprValue::BoolConst(false) => true,
        ExprValue::And(children) => children.iter().any(constraint_contains_false_conjunct),
        _ => false,
    }
}

/// Collect all variable names from a relation application's args.
fn collect_relation_app_vars(app: &crate::chc::RelationApp, out: &mut HashSet<String>) {
    for arg in app.args.iter() {
        collect_expr_vars(arg, out);
    }
}

/// Recursively collect all variable names from an expression.
fn collect_expr_vars(expr: &ay_bindings::Expr, out: &mut HashSet<String>) {
    match expr.value() {
        ExprValue::Var { name } => {
            out.insert(name.clone());
        }
        _ => {
            for child in expr.value().children() {
                collect_expr_vars(child, out);
            }
        }
    }
}

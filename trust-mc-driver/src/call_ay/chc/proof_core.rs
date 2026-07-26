// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Proof-core distillation for CHC range-loop predicates.
//! Part of #2875 (lane #20).

use std::collections::HashSet;

use crate::args::AYChcProofCoreMode;
use ay::chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, LemmaHint, PredicateId};

use super::auto_invariants::{
    candidate_from_comparison, canonical_state_expr, collect_comparisons,
    detect_incremented_indices, int_body_var_to_state_map,
};
use super::sort_helpers::{is_numeric_sort, make_ge, make_le, make_zero};

mod solve;
use solve::{
    PROOF_CORE_PRIORITY, PROOF_CORE_SOURCE, build_obligations, screen_inductiveness,
    solve_and_intersect,
};

/// Telemetry counters for the proof-core distillation stage.
#[derive(Clone, Debug, Default)]
pub(crate) struct ProofCoreStats {
    /// Total bounded obligations generated.
    pub(crate) obligations_total: usize,
    /// Obligations that returned unsat (proof found).
    pub(crate) unsat: usize,
    /// Formulas extracted from unsat cores.
    pub(crate) core_formulas: usize,
    /// Formulas rejected by inductiveness screening.
    pub(crate) rejected: usize,
    /// Formulas injected as hints into the portfolio config.
    pub(crate) injected: usize,
}

/// A predicate eligible for proof-core distillation.
#[derive(Debug)]
pub(crate) struct EligiblePredicate {
    pub(crate) id: PredicateId,
    pub(crate) arg_sorts: Vec<ChcSort>,
    /// State indices that are incremented by 1 across the transition.
    pub(crate) incremented_indices: HashSet<usize>,
    /// State indices that are preserved (unchanged) across the transition.
    pub(crate) preserved_indices: HashSet<usize>,
    /// Indices into `ChcProblem::clauses()` of fact clauses defining this predicate.
    pub(crate) fact_clause_indices: Vec<usize>,
    /// Indices into `ChcProblem::clauses()` of recursive transition clauses.
    pub(crate) transition_clause_indices: Vec<usize>,
}

/// Kind of bounded obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObligationKind {
    /// Init/base case: candidate must hold at loop entry.
    Base,
    /// Step/inductive case: candidate must be preserved across one iteration.
    Step,
}

/// A single candidate with its activation literal and canonical form.
#[derive(Debug, Clone)]
pub(crate) struct ActivatedCandidate {
    /// Activation literal variable name (e.g., `__pc_act_0`).
    pub(crate) activation_var: String,
    /// Candidate formula substituted into clause-local variables.
    pub(crate) substituted: ChcExpr,
    /// Candidate formula in canonical predicate variables.
    pub(crate) canonical: ChcExpr,
}

/// A bounded obligation for proof-core distillation. PC3 solves these by
/// checking each candidate individually: `background ∧ ¬candidate` — UNSAT
/// means the candidate is implied by the background.
#[derive(Debug)]
pub(crate) struct BoundedObligation {
    pub(crate) kind: ObligationKind,
    pub(crate) predicate: PredicateId,
    pub(crate) clause_index: usize,
    /// Background constraint (always asserted).
    /// - Base: the fact clause's init constraint.
    /// - Step: transition constraint AND all candidate hypotheses (body-var substituted).
    pub(crate) background: ChcExpr,
    /// Candidate conclusions: each checked individually against background.
    pub(crate) candidates: Vec<ActivatedCandidate>,
}

fn log_skip(verbose: bool, pred_id: PredicateId, name: &str, reason: &str) {
    if verbose {
        println!("[AY-chc] proof-core: P{} ({}) — skipped, {}", pred_id.index(), name, reason);
    }
}

/// Find predicates eligible for proof-core distillation.
pub(crate) fn find_eligible_predicates(
    problem: &ChcProblem,
    verbose: bool,
) -> Vec<EligiblePredicate> {
    let mut eligible = Vec::new();

    for predicate in problem.predicates() {
        let pred_id = predicate.id;
        let arg_sorts = &predicate.arg_sorts;

        let mut fact_indices = Vec::new();
        let mut transition_indices = Vec::new();
        let mut combined_incremented: Option<HashSet<usize>> = None;
        let mut combined_preserved = HashSet::new();

        for (ci, clause) in problem.clauses().iter().enumerate() {
            let head_args = match &clause.head {
                ClauseHead::Predicate(id, args) if *id == pred_id => args,
                _ => continue,
            };

            let body_match = clause.body.predicates.iter().find(|(id, _)| *id == pred_id);

            if let Some((_, body_args)) = body_match {
                // Recursive transition clause.
                let body_var_map = int_body_var_to_state_map(body_args, arg_sorts);
                if body_var_map.is_empty() {
                    continue;
                }

                let inc = detect_incremented_indices(head_args, arg_sorts, &body_var_map);
                if inc.is_empty() {
                    continue;
                }

                // Detect preserved indices: non-incremented numeric args where
                // head_arg is the same body variable (unchanged across transition).
                let mut clause_preserved = HashSet::new();
                for (idx, (head_arg, sort)) in head_args.iter().zip(arg_sorts.iter()).enumerate() {
                    if !is_numeric_sort(sort) || inc.contains(&idx) {
                        continue;
                    }
                    if let ChcExpr::Var(var) = head_arg {
                        if body_var_map.get(&var.name).copied() == Some(idx) {
                            clause_preserved.insert(idx);
                        }
                    }
                }

                match &mut combined_incremented {
                    Some(existing) => {
                        // Intersect: only keep indices incremented in ALL transition clauses.
                        existing.retain(|i| inc.contains(i));
                    }
                    None => {
                        combined_incremented = Some(inc);
                    }
                }
                combined_preserved.extend(clause_preserved);
                transition_indices.push(ci);
            } else if clause.body.predicates.is_empty() {
                // Fact clause (no body predicates).
                fact_indices.push(ci);
            }
        }

        let Some(inc) = combined_incremented else {
            log_skip(verbose, pred_id, &predicate.name, "no incremented indices");
            continue;
        };
        if inc.is_empty() {
            log_skip(verbose, pred_id, &predicate.name, "inconsistent incremented indices");
            continue;
        }
        if fact_indices.is_empty() {
            log_skip(verbose, pred_id, &predicate.name, "no fact clauses");
            continue;
        }
        if verbose {
            println!(
                "[AY-chc] proof-core: P{} ({}) — eligible: {} inc, {} preserved, {} facts, {} trans",
                pred_id.index(),
                predicate.name,
                inc.len(),
                combined_preserved.len(),
                fact_indices.len(),
                transition_indices.len(),
            );
        }

        eligible.push(EligiblePredicate {
            id: pred_id,
            arg_sorts: arg_sorts.clone(),
            incremented_indices: inc,
            preserved_indices: combined_preserved,
            fact_clause_indices: fact_indices,
            transition_clause_indices: transition_indices,
        });
    }

    eligible
}

/// Generate candidate invariant formulas for an eligible predicate.
///
/// Returns candidates in canonical predicate variables (`__pN_aM`).
/// Uses the same comparison-analysis patterns as `auto_invariants`.
pub(crate) fn generate_candidates(
    problem: &ChcProblem,
    eligible: &EligiblePredicate,
) -> Vec<ChcExpr> {
    let mut candidates = Vec::new();
    let mut seen: HashSet<ChcExpr> = HashSet::new();

    let pred_id = eligible.id;
    let arg_sorts = &eligible.arg_sorts;

    for &ci in &eligible.transition_clause_indices {
        let clause = &problem.clauses()[ci];
        let head_args = match &clause.head {
            ClauseHead::Predicate(_, args) => args,
            _ => continue,
        };
        let Some((_, body_args)) = clause.body.predicates.iter().find(|(id, _)| *id == pred_id)
        else {
            continue;
        };

        let body_var_map = int_body_var_to_state_map(body_args, arg_sorts);
        if body_var_map.is_empty() {
            continue;
        }

        // 1. Comparison-derived candidates from the transition constraint.
        if let Some(constraint) = &clause.body.constraint {
            let mut comparisons = Vec::new();
            collect_comparisons(constraint, &mut comparisons);

            for (op, lhs, rhs) in &comparisons {
                let candidate = candidate_from_comparison(
                    op,
                    lhs,
                    rhs,
                    pred_id,
                    arg_sorts,
                    &body_var_map,
                    &eligible.incremented_indices,
                );
                if let Some(formula) = candidate {
                    push_candidate_if_new(&mut candidates, &mut seen, formula);
                }
            }
        }

        // 2. idx >= 0 for each incremented index.
        for &idx in &eligible.incremented_indices {
            let sort = &arg_sorts[idx];
            let state_var = canonical_state_expr(pred_id, idx, sort);
            let candidate = make_ge(state_var, make_zero(sort), sort);
            push_candidate_if_new(&mut candidates, &mut seen, candidate);
        }

        // 3. inc_idx <= preserved_idx for each incremented/preserved pair.
        for &inc_idx in &eligible.incremented_indices {
            for &pres_idx in &eligible.preserved_indices {
                let is_preserved_here = match &head_args[pres_idx] {
                    ChcExpr::Var(var) => body_var_map.get(&var.name).copied() == Some(pres_idx),
                    _ => false,
                };
                if !is_preserved_here {
                    continue;
                }
                let inc_var = canonical_state_expr(pred_id, inc_idx, &arg_sorts[inc_idx]);
                let pres_var = canonical_state_expr(pred_id, pres_idx, &arg_sorts[pres_idx]);
                let candidate = make_le(inc_var, pres_var, &arg_sorts[inc_idx]);
                push_candidate_if_new(&mut candidates, &mut seen, candidate);
            }
        }

        // 4. Difference-bound: other >= inc for non-incremented numeric state vars.
        let numeric_state_indices: Vec<usize> = body_var_map
            .values()
            .copied()
            .filter(|idx| arg_sorts.get(*idx).map_or(false, is_numeric_sort))
            .collect();

        for &inc_idx in &eligible.incremented_indices {
            for &other_idx in &numeric_state_indices {
                if other_idx == inc_idx || eligible.incremented_indices.contains(&other_idx) {
                    continue;
                }
                let other_var = canonical_state_expr(pred_id, other_idx, &arg_sorts[other_idx]);
                let inc_var = canonical_state_expr(pred_id, inc_idx, &arg_sorts[inc_idx]);
                let candidate = make_ge(other_var, inc_var, &arg_sorts[other_idx]);
                push_candidate_if_new(&mut candidates, &mut seen, candidate);
            }
        }
    }

    candidates
}

fn push_candidate_if_new(
    candidates: &mut Vec<ChcExpr>,
    seen: &mut HashSet<ChcExpr>,
    candidate: ChcExpr,
) {
    if seen.insert(normalized_candidate_key(&candidate)) {
        candidates.push(candidate);
    }
}

fn normalized_candidate_key(formula: &ChcExpr) -> ChcExpr {
    let ChcExpr::Op(op, args) = formula else {
        return formula.clone();
    };
    let Some(reversed_op) = reversed_comparison_op(op) else {
        return formula.clone();
    };
    if args.len() != 2 {
        return formula.clone();
    }
    ChcExpr::Op(reversed_op, vec![args[1].clone(), args[0].clone()])
}

fn reversed_comparison_op(op: &ChcOp) -> Option<ChcOp> {
    match op {
        ChcOp::Gt => Some(ChcOp::Lt),
        ChcOp::Ge => Some(ChcOp::Le),
        ChcOp::BvUGt => Some(ChcOp::BvULt),
        ChcOp::BvUGe => Some(ChcOp::BvULe),
        ChcOp::BvSGt => Some(ChcOp::BvSLt),
        ChcOp::BvSGe => Some(ChcOp::BvSLe),
        _ => None,
    }
}

/// Run proof-core distillation as a pre-solve stage.
///
/// PC1: gate + telemetry. PC2: eligibility + obligation builder.
/// PC3: core extraction + lifting. PC4: inductiveness screen.
///
/// Returns `(stats, hints)` for the caller to merge into the hint pipeline.
/// The caller is responsible for injecting hints via `set_pdr_user_hints`
/// in the correct merge order (user → proof-core → auto-invariant).
pub(crate) fn run_proof_core_distillation(
    problem: &ay::chc::ChcProblem,
    mode: AYChcProofCoreMode,
    verbose: bool,
) -> (ProofCoreStats, Vec<LemmaHint>) {
    match mode {
        AYChcProofCoreMode::Off => (ProofCoreStats::default(), Vec::new()),
        AYChcProofCoreMode::Range => {
            let eligible = find_eligible_predicates(problem, verbose);
            if eligible.is_empty() {
                if verbose {
                    println!("[AY-chc] proof-core: no eligible predicates found");
                }
                return (ProofCoreStats::default(), Vec::new());
            }

            let mut stats = ProofCoreStats::default();
            let mut all_hints: Vec<LemmaHint> = Vec::new();

            for pred in &eligible {
                let candidates = generate_candidates(problem, pred);
                if verbose {
                    println!(
                        "[AY-chc] proof-core: P{} — {} candidate formulas",
                        pred.id.index(),
                        candidates.len(),
                    );
                }

                let obligations = build_obligations(problem, pred, &candidates, verbose);
                stats.obligations_total += obligations.len();

                // PC3: Solve obligations and intersect cores.
                let validated = solve_and_intersect(&obligations, &mut stats, verbose);

                // PC4: One-step inductiveness screening. Only inject candidates
                // that are individually inductive (without assuming other candidates
                // as hypotheses), preventing circular dependency injection.
                let screened = screen_inductiveness(problem, pred, &validated, &mut stats, verbose);

                for formula in &screened {
                    all_hints.push(LemmaHint::new(
                        pred.id,
                        formula.clone(),
                        PROOF_CORE_PRIORITY,
                        PROOF_CORE_SOURCE,
                    ));
                }
                stats.injected += screened.len();

                if verbose && !screened.is_empty() {
                    println!(
                        "[AY-chc] proof-core: P{} — {} formulas passed inductiveness screen \
                         ({} validated, {} rejected by PC4)",
                        pred.id.index(),
                        screened.len(),
                        validated.len(),
                        validated.len() - screened.len(),
                    );
                }
            }

            if verbose && !all_hints.is_empty() {
                println!("[AY-chc] proof-core: {} total hints ready for merge", all_hints.len(),);
            }

            (stats, all_hints)
        }
    }
}

#[cfg(test)]
mod tests_proof_core;

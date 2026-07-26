// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! PC2+PC3+PC4: obligation builder, per-candidate validity checks,
//! cross-obligation intersection, and one-step inductiveness screening.
//!
//! Extracted from proof_core.rs per 500-line file-size policy.
//! Part of #2875 (lane #20).

use std::collections::HashSet;

use ay::chc::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, PredicateId, SmtContext, SmtResult,
};
use tracing::debug;

use super::{
    ActivatedCandidate, BoundedObligation, EligiblePredicate, ObligationKind, ProofCoreStats,
};

/// Priority for proof-core hints (lower = higher priority).
/// Between user hints (10) and auto-invariants (58).
pub(super) const PROOF_CORE_PRIORITY: u16 = 30;

/// Source tag for proof-core hints.
pub(super) const PROOF_CORE_SOURCE: &str = "trust_mc-proof-core";

/// Build substitution from canonical `__pN_aM` vars to clause-local args.
fn build_substitution(
    pred_id: PredicateId,
    arg_sorts: &[ChcSort],
    target_args: &[ChcExpr],
) -> Vec<(ChcVar, ChcExpr)> {
    arg_sorts
        .iter()
        .enumerate()
        .filter(|(_, sort)| matches!(sort, ChcSort::Int))
        .map(|(i, sort)| {
            let canonical_var = ChcVar::new(format!("__p{}_a{}", pred_id.index(), i), sort.clone());
            (canonical_var, target_args[i].clone())
        })
        .collect()
}

/// Build bounded base (from facts) and step (from transitions) obligations.
pub(super) fn build_obligations(
    problem: &ChcProblem,
    eligible: &EligiblePredicate,
    candidates: &[ChcExpr],
    verbose: bool,
) -> Vec<BoundedObligation> {
    if candidates.is_empty() {
        if verbose {
            debug!(
                "proof-core: P{} — no candidates, skipping obligation build",
                eligible.id.index()
            );
        }
        return Vec::new();
    }

    let mut obligations = Vec::new();
    let pred_id = eligible.id;
    let arg_sorts = &eligible.arg_sorts;

    // Base obligations from fact clauses.
    for &ci in &eligible.fact_clause_indices {
        let clause = &problem.clauses()[ci];
        let head_args = match &clause.head {
            ClauseHead::Predicate(_, args) => args,
            _ => continue,
        };

        let background = clause.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

        let subst = build_substitution(pred_id, arg_sorts, head_args);
        let activated: Vec<ActivatedCandidate> = candidates
            .iter()
            .enumerate()
            .map(|(i, canonical)| {
                let substituted = canonical.substitute(&subst);
                ActivatedCandidate {
                    activation_var: format!("__pc_act_{i}"),
                    substituted,
                    canonical: canonical.clone(),
                }
            })
            .collect();

        obligations.push(BoundedObligation {
            kind: ObligationKind::Base,
            predicate: pred_id,
            clause_index: ci,
            background,
            candidates: activated,
        });
    }

    // Step obligations from transition clauses.
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

        // Hypothesis: all candidates hold in pre-state (body vars).
        let body_subst = build_substitution(pred_id, arg_sorts, body_args);
        let hypotheses: Vec<ChcExpr> =
            candidates.iter().map(|c| c.substitute(&body_subst)).collect();

        // Background: transition constraint AND all hypotheses.
        let trans_constraint = clause.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let mut bg_conjuncts = hypotheses;
        bg_conjuncts.push(trans_constraint);
        let background = ChcExpr::and_all(bg_conjuncts);

        // Conclusion: candidates substituted into head args.
        let head_subst = build_substitution(pred_id, arg_sorts, head_args);
        let activated: Vec<ActivatedCandidate> = candidates
            .iter()
            .enumerate()
            .map(|(i, canonical)| {
                let substituted = canonical.substitute(&head_subst);
                ActivatedCandidate {
                    activation_var: format!("__pc_act_{i}"),
                    substituted,
                    canonical: canonical.clone(),
                }
            })
            .collect();

        obligations.push(BoundedObligation {
            kind: ObligationKind::Step,
            predicate: pred_id,
            clause_index: ci,
            background,
            candidates: activated,
        });
    }

    if verbose {
        let base_count = obligations.iter().filter(|o| o.kind == ObligationKind::Base).count();
        let step_count = obligations.iter().filter(|o| o.kind == ObligationKind::Step).count();
        debug!(
            "proof-core: P{} — {} obligations ({} base, {} step) with {} candidates each",
            pred_id.index(),
            obligations.len(),
            base_count,
            step_count,
            candidates.len(),
        );
    }

    obligations
}

/// Solve a single bounded obligation using per-candidate validity checks.
///
/// For each candidate, checks `background ∧ ¬candidate` — if UNSAT, the
/// background implies the candidate (it is valid). Returns canonical formulas
/// for all valid candidates. Empty if no candidates hold.
///
/// Part of #2875 (lane #20, PC3).
pub(super) fn solve_obligation(obligation: &BoundedObligation, verbose: bool) -> Vec<ChcExpr> {
    if obligation.candidates.is_empty() {
        return Vec::new();
    }

    let mut valid = Vec::new();

    for ac in &obligation.candidates {
        // Check: background ∧ ¬candidate — UNSAT means background ⊨ candidate.
        let query =
            ChcExpr::and(obligation.background.clone(), ChcExpr::not(ac.substituted.clone()));
        let mut ctx = SmtContext::new();
        let result = ctx.check_sat(&query);

        let is_valid = result.is_unsat();
        if is_valid {
            valid.push(ac.canonical.clone());
        }

        if verbose {
            let label = if result.is_unsat() {
                "valid"
            } else if matches!(&result, SmtResult::Sat(_)) {
                "invalid"
            } else {
                "unknown"
            };
            debug!(
                "proof-core: {:?} P{} ci={} candidate '{}' — {}",
                obligation.kind,
                obligation.predicate.index(),
                obligation.clause_index,
                ac.activation_var,
                label,
            );
        }
    }

    if verbose {
        debug!(
            "proof-core: {:?} obligation P{} ci={} — {}/{} candidates valid",
            obligation.kind,
            obligation.predicate.index(),
            obligation.clause_index,
            valid.len(),
            obligation.candidates.len(),
        );
    }

    valid
}

/// Solve all obligations for a predicate and intersect valid sets.
///
/// A candidate is validated only if it is valid in EVERY obligation
/// (both base and step). This ensures the candidate is both initially true (base)
/// and inductively preserved (step).
///
/// Part of #2875 (lane #20, PC3).
pub(super) fn solve_and_intersect(
    obligations: &[BoundedObligation],
    stats: &mut ProofCoreStats,
    verbose: bool,
) -> Vec<ChcExpr> {
    if obligations.is_empty() {
        return Vec::new();
    }

    let mut intersection: Option<HashSet<ChcExpr>> = None;

    for obligation in obligations {
        let core_formulas = solve_obligation(obligation, verbose);

        if core_formulas.is_empty() {
            stats.rejected += obligation.candidates.len();
            if verbose {
                debug!(
                    "proof-core: {:?} P{} ci={} — no valid candidates, clearing intersection",
                    obligation.kind,
                    obligation.predicate.index(),
                    obligation.clause_index,
                );
            }
            return Vec::new();
        }

        stats.unsat += 1;
        stats.core_formulas += core_formulas.len();

        let core_set: HashSet<ChcExpr> = core_formulas.into_iter().collect();
        intersection = Some(match intersection {
            Some(existing) => existing.intersection(&core_set).cloned().collect(),
            None => core_set,
        });

        if matches!(&intersection, Some(existing) if existing.is_empty()) {
            if verbose {
                debug!(
                    "proof-core: {:?} P{} ci={} — empty cross-obligation intersection, \
                     skipping remaining obligations",
                    obligation.kind,
                    obligation.predicate.index(),
                    obligation.clause_index,
                );
            }
            return Vec::new();
        }
    }

    intersection.map_or_else(Vec::new, |s| s.into_iter().collect())
}

/// Per-check timeout for individual inductiveness queries (PC4).
const INDUCTIVENESS_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(1);

/// PC4: One-step inductiveness screening.
///
/// For each validated candidate, checks whether it is individually one-step
/// inductive across every transition clause — without assuming other candidates
/// as hypotheses. This prevents circular dependencies where two non-inductive
/// candidates each pass only because the other is assumed.
///
/// For each transition clause, checks:
///   `transition_constraint(pre, post) ∧ C(pre) ∧ ¬C(post)` — UNSAT means
///   C is preserved by the transition on its own.
///
/// Returns only candidates that pass in ALL transition clauses.
///
/// Part of #2875 (lane #20, PC4).
pub(super) fn screen_inductiveness(
    problem: &ChcProblem,
    eligible: &EligiblePredicate,
    validated: &[ChcExpr],
    stats: &mut ProofCoreStats,
    verbose: bool,
) -> Vec<ChcExpr> {
    if validated.is_empty() {
        return Vec::new();
    }

    let pred_id = eligible.id;
    let arg_sorts = &eligible.arg_sorts;
    let mut screened = Vec::new();

    'candidate: for candidate in validated {
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

            // C(pre): candidate substituted into body (pre-state) variables.
            let body_subst = build_substitution(pred_id, arg_sorts, body_args);
            let c_pre = candidate.substitute(&body_subst);

            // C(post): candidate substituted into head (post-state) variables.
            let head_subst = build_substitution(pred_id, arg_sorts, head_args);
            let c_post = candidate.substitute(&head_subst);

            // transition_constraint ∧ C(pre) ∧ ¬C(post) — UNSAT means inductive.
            let trans_constraint = clause.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and_all([trans_constraint, c_pre, ChcExpr::not(c_post)]);

            let mut ctx = SmtContext::new();
            let result = ctx.check_sat_with_timeout(&query, INDUCTIVENESS_TIMEOUT);

            let inductive = result.is_unsat();

            if verbose {
                let label = if inductive { "inductive" } else { "non-inductive" };
                debug!(
                    "proof-core: PC4 screen P{} ci={} — {} ({})",
                    pred_id.index(),
                    ci,
                    label,
                    if matches!(result, SmtResult::Unknown) {
                        "timeout/unknown"
                    } else {
                        "checked"
                    },
                );
            }

            if !inductive {
                stats.rejected += 1;
                if verbose {
                    debug!(
                        "proof-core: PC4 rejected non-inductive candidate for P{}",
                        pred_id.index(),
                    );
                }
                continue 'candidate;
            }
        }

        // Candidate passed all transition clauses — individually inductive.
        screened.push(candidate.clone());
    }

    if verbose {
        debug!(
            "proof-core: PC4 screen P{} — {}/{} candidates passed individual inductiveness",
            pred_id.index(),
            screened.len(),
            validated.len(),
        );
    }

    screened
}

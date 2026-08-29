// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct-SMT refutation shortcut for acyclic CHC problems, available to the
//! native library typed full-verification path.
//!
//! When ay's PDR/PDR engine returns Unknown on an acyclic problem (as it
//! does today for bit-vector overflow obligations), this composes a concrete
//! derivation path to `error` and SMT-checks the accumulated background-theory
//! constraints. A positive result is a *real* counterexample (sound), so the
//! caller may report `Failed` with the returned witness model instead of an
//! inconclusive Unknown. `None` means no satisfiable acyclic derivation was
//! found.
//!
//! This mirrors the binary-crate `call_ay::chc::native_nullary` shortcut, ported
//! here because the library and binary are separate compilation units. It is
//! sort-generic (handles `BitVec` as well as `Int`/`Bool`), which lets
//! bit-vector overflow obligations refute with a concrete witness rather than
//! stalling at Unknown.

mod relevance_slicing;
mod wide_nonlinear_abstraction;

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_chc::{
    ChcExpr, ChcProblem, ClauseHead, HornClause, PredicateId, SmtContext, SmtResult, SmtValue,
};

use self::wide_nonlinear_abstraction::abstract_wide_nonlinear;

/// Wall-clock bound for any single decidable SMT query in this CEX-search
/// shortcut. A real counterexample is a *satisfiable* (SAT) derivation, which the
/// native theory loop finds quickly; the branches with NO counterexample (UNSAT)
/// over bit-blasted BV divide/remainder are exactly where the native loop
/// restart-thrashes to its deadline, so a generous bound there is pure wasted
/// wall-clock — summed over a fact-saturation's many such branches it dominates
/// the whole verification (a provably-dead `match n % 3 { .., _ => unreachable!() }`
/// spent ~70s here before its PDR/BMC safety proof even started). Keep it tight:
/// SAT counterexamples still return well within 1s, and an undecided branch falls
/// through to the full PDR/BMC solve (which proves it), so tightening only trims
/// waste — it never fabricates a proof or drops a counterexample (gate stays GREEN).
const SMT_QUERY_TIMEOUT: Duration = Duration::from_secs(1);

/// Total wall-clock the relevance-slicing pre-phase may spend before it gives up
/// and lets the caller run the full body query unchanged. Bounds the ADDED cost
/// of slicing on bodies it cannot decide; the phase is a pure optimisation, so
/// abandoning it is always allowed.
fn slice_phase_budget() -> Duration {
    SMT_QUERY_TIMEOUT
}

/// Per-slice budget. Slices are, by construction, much smaller than the body; if
/// one needs more than a fraction of the full-body budget it is not the cheap win
/// this phase exists to harvest, so move on rather than starve the phase.
fn slice_probe_timeout() -> Duration {
    (SMT_QUERY_TIMEOUT / 4).max(Duration::from_millis(20)).min(SMT_QUERY_TIMEOUT)
}

/// Kill switch for the relevance-slicing pre-phase (any non-empty value disables
/// it). Measurement lever only: with slicing off the lane behaves exactly as it
/// did before the phase existed, because the phase can only convert an
/// `Undecided` into a definitively-justified `Unsat`.
fn slicing_disabled() -> bool {
    std::env::var_os("TRUST_SMT_SLICE_DISABLE").is_some_and(|v| !v.is_empty())
}

// These are the exact private limits used by the pinned ay-chc
// `ChcExpr::substitute` implementation. Keep this guard in lockstep with every
// ay-chc revision bump: crossing either limit makes substitution best-effort,
// which is unsuitable for the clause-local alpha-renaming below.
const AY_CHC_SUBSTITUTION_MAX_DEPTH: usize = 500;
const AY_CHC_SUBSTITUTION_MAX_DISTINCT_NODES: usize = 1_000_000;

/// Decision of the acyclic direct-SMT shortcut over a CHC problem: a real
/// counterexample (`Unsafe`), a complete proof of safety (`Safe`), or a deferral
/// to the full CHC/PDR engine (`Inconclusive`). Sound in all three arms.
// Short-lived decision value; the variant size gap is immaterial and this
// enum's arms are pinned to the soundness proof, so it is not restructured.
#[allow(clippy::large_enum_variant)]
pub(crate) enum AcyclicDecision {
    /// Acyclic problem; the exhaustive search composed a satisfiable derivation of
    /// `error` — a real counterexample (sound).
    Unsafe(AcyclicUnsafeWitness),
    /// Acyclic problem; the EXHAUSTIVE (non-truncated) bounded search found no
    /// satisfiable derivation of `error`. Because the dependency graph is acyclic
    /// every derivation has bounded length, so this is a COMPLETE decision: SAFE.
    /// This is what proves trivial non-recursive obligations (e.g. an exhaustive
    /// enum match's `(_d∈tags) ∧ (_d∉tags)` unreachable) that PDR alone returns
    /// Unknown for — PDR synthesizes inductive invariants and has nothing to
    /// induct over here.
    Safe,
    /// Not acyclic, or the bounded search hit a fact/combination cap (incomplete):
    /// the shortcut cannot decide; defer to the full CHC/PDR engine.
    Inconclusive,
}

/// Concrete result of composing one satisfiable acyclic error derivation.
///
/// The clause-index trace is part of the witness rather than a diagnostic: a
/// fresh consumer uses it to select the exact clauses from its independently
/// rebuilt problem, reconstructs the accumulated path formula, binds every
/// variable to the supplied typed model, and asks SMT to check that exact
/// assignment.  A model without this trace cannot identify which of several
/// possible derivations it is supposed to satisfy and is therefore not
/// replayable.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AcyclicUnsafeWitness {
    pub(crate) model: serde_json::Value,
    pub(crate) derivation_clause_indices: Vec<u64>,
}

#[allow(clippy::large_enum_variant)] // short-lived decision value
enum DerivationOutcome {
    Witness(AcyclicUnsafeWitness),
    ExhaustivelyNone,
    Truncated,
}

pub(crate) fn acyclic_direct_smt_decision(problem: &ChcProblem) -> AcyclicDecision {
    // The composer below currently models the linear CHCs emitted by TrustMC's
    // production lowering. A body with multiple predicate facts needs fresh
    // instantiation per fact combination; treating the clause's syntactic
    // variables as one shared namespace can otherwise turn a reachable join
    // into a false UNSAT and hence a false `Safe`. Fail closed until composition
    // performs per-combination instantiation for nonlinear Horn clauses.
    if !is_acyclic_problem(problem)
        || problem.clauses().iter().any(|clause| clause.body.predicates.len() > 1)
    {
        return AcyclicDecision::Inconclusive;
    }
    match acyclic_error_derivation(problem) {
        DerivationOutcome::Witness(model) => AcyclicDecision::Unsafe(model),
        DerivationOutcome::ExhaustivelyNone => AcyclicDecision::Safe,
        DerivationOutcome::Truncated => AcyclicDecision::Inconclusive,
    }
}

/// Check if the CHC problem's predicate dependency graph is acyclic.
///
/// An acyclic dependency graph means every execution path through the CHC
/// system has bounded length, so the bounded derivation search below is
/// complete.
fn is_acyclic_problem(problem: &ChcProblem) -> bool {
    let n = problem.predicates().len();
    if n == 0 {
        return true;
    }
    let edges = problem.dependency_edges();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut incoming = vec![0usize; n];
    for (from, to) in &edges {
        let from_idx = from.index();
        let to_idx = to.index();
        if from_idx >= n || to_idx >= n {
            return false;
        }
        adj[from_idx].push(to_idx);
        let Some(next) = incoming[to_idx].checked_add(1) else {
            return false;
        };
        incoming[to_idx] = next;
    }

    // Kahn's topological walk avoids recursive DFS: a retained-but-large
    // obligation must not be able to overflow the consumer's call stack while
    // it is deciding whether a serialized witness is replayable.
    let mut ready: VecDeque<usize> = incoming
        .iter()
        .enumerate()
        .filter_map(|(index, degree)| (*degree == 0).then_some(index))
        .collect();
    let mut visited = 0usize;
    while let Some(node) = ready.pop_front() {
        visited += 1;
        for &successor in &adj[node] {
            incoming[successor] -= 1;
            if incoming[successor] == 0 {
                ready.push_back(successor);
            }
        }
    }
    visited == n
}

#[derive(Clone)]
struct ReachFact {
    args: Vec<ChcExpr>,
    constraints: Vec<ChcExpr>,
    derivation_clause_indices: Vec<u64>,
}

/// Conservative exact reachability for acyclic CHCs. Returns a JSON rendering of
/// the SMT model that witnesses a derivation to `error`. `None` means no
/// satisfiable acyclic derivation was found.
fn acyclic_error_derivation(problem: &ChcProblem) -> DerivationOutcome {
    const MAX_FACTS_PER_PREDICATE: usize = 128;
    const MAX_COMBINATIONS_PER_CLAUSE: usize = 1024;

    let Some(clauses) = alpha_renamed_clauses(problem) else {
        // Substitution is budgeted in ay-chc. A partial rename would reintroduce
        // cross-clause variable capture, so inability to rename completely must
        // defer rather than license an exhaustive `Safe` result.
        return DerivationOutcome::Truncated;
    };
    let mut smt = problem.make_smt_context();
    let mut facts: HashMap<PredicateId, Vec<ReachFact>> = HashMap::new();
    // Set on any fact/combination cap hit: a truncated search may have MISSED a
    // derivation, so its "no witness" is NOT a sound safety proof — report
    // Truncated and defer to PDR rather than claim SAFE.
    let mut truncated = false;

    for _ in 0..=problem.predicates().len().saturating_add(problem.clauses().len()) {
        let mut changed = false;

        for (clause_index, clause) in clauses.iter().enumerate() {
            let Some(body_fact_options) = body_fact_options(clause, &facts) else {
                continue;
            };

            let mut checked = 0usize;
            for combo in FactCombinationIter::new(body_fact_options) {
                checked += 1;
                if checked > MAX_COMBINATIONS_PER_CLAUSE {
                    truncated = true;
                    break;
                }

                let mut constraints = Vec::new();
                for (body_idx, fact) in combo.iter().enumerate() {
                    constraints.extend(fact.constraints.iter().cloned());
                    let (_, body_args) = &clause.body.predicates[body_idx];
                    constraints.extend(body_args.iter().zip(&fact.args).map(
                        |(body_arg, fact_arg)| ChcExpr::eq(body_arg.clone(), fact_arg.clone()),
                    ));
                }
                if let Some(constraint) = &clause.body.constraint {
                    constraints.push(constraint.clone());
                }

                let model = match solve_constraints(&mut smt, &constraints) {
                    SolveOutcome::Sat(model) => model,
                    // Definitive UNSAT: this body derives nothing — sound to prune.
                    SolveOutcome::Unsat => continue,
                    SolveOutcome::Undecided => {
                        // SMT Unknown/timeout: the body may actually be satisfiable
                        // (a real reachable fact, and downstream a real reachable
                        // panic) that ay could not decide. Pruning it silently would
                        // let the fixpoint claim `ExhaustivelyNone` → SAFE on an
                        // undecided edge — a false proof. Taint exhaustiveness so the
                        // outcome is `Truncated` → `Inconclusive` → defer to PDR.
                        truncated = true;
                        continue;
                    }
                };

                let mut derivation_clause_indices = combo
                    .first()
                    .map_or_else(Vec::new, |fact| fact.derivation_clause_indices.clone());
                let Ok(clause_index) = u64::try_from(clause_index) else {
                    return DerivationOutcome::Truncated;
                };
                derivation_clause_indices.push(clause_index);

                match &clause.head {
                    ClauseHead::False => {
                        return DerivationOutcome::Witness(AcyclicUnsafeWitness {
                            model,
                            derivation_clause_indices,
                        });
                    }
                    ClauseHead::Predicate(pred, args) => {
                        let entry = facts.entry(*pred).or_default();
                        if entry.len() >= MAX_FACTS_PER_PREDICATE {
                            truncated = true;
                            continue;
                        }
                        if entry.iter().any(|fact| {
                            fact.args.as_slice() == args.as_slice()
                                && fact.constraints.as_slice() == constraints.as_slice()
                        }) {
                            continue;
                        }
                        entry.push(ReachFact {
                            args: args.clone(),
                            constraints,
                            derivation_clause_indices,
                        });
                        changed = true;
                    }
                    _ => {}
                }
            }
        }

        if !changed {
            // Fixpoint reached with no derivation of `error`. Exhaustive (and thus
            // a sound SAFE proof) only if no cap was ever hit.
            return if truncated {
                DerivationOutcome::Truncated
            } else {
                DerivationOutcome::ExhaustivelyNone
            };
        }
    }

    // Ran the iteration bound without converging — treat as incomplete.
    DerivationOutcome::Truncated
}

/// Hard replay ceilings.  They are deliberately independent of the producer's
/// saturation caps: a hostile serialized witness must not be able to turn the
/// consumer check into an unbounded allocation or path walk.
const MAX_REPLAY_PATH_CLAUSES: usize = 262_144;
const MAX_REPLAY_MODEL_BINDINGS: usize = 65_536;
const MAX_REPLAY_PROBLEM_PREDICATES: usize = 65_536;
const MAX_REPLAY_PROBLEM_CLAUSES: usize = 262_144;

/// Independently replay an acyclic direct-SMT witness against a freshly built
/// problem.
///
/// This does not trust a producer's `SAT` tag or its model object.  It
/// alpha-renames the fresh clauses exactly as the composer does, reconstructs
/// the clause-local path named by `derivation_clause_indices`, requires a
/// well-formed fact-to-query chain, parses a total and sort-exact assignment for
/// every variable in that path (with no extras), and checks the conjunction
/// with all supplied values fixed.  Any malformed/unsupported value, budget
/// breach, path mismatch, or non-SAT result fails closed.
pub(crate) fn replay_acyclic_direct_smt_witness(
    problem: &ChcProblem,
    witness: &AcyclicUnsafeWitness,
) -> Result<(), String> {
    if problem.predicates().len() > MAX_REPLAY_PROBLEM_PREDICATES
        || problem.clauses().len() > MAX_REPLAY_PROBLEM_CLAUSES
    {
        return Err(format!(
            "fresh replay problem has {} predicates and {} clauses, above the replay budget",
            problem.predicates().len(),
            problem.clauses().len()
        ));
    }
    if !is_acyclic_problem(problem) {
        return Err("fresh replay problem is cyclic".to_string());
    }
    if problem.clauses().iter().any(|clause| clause.body.predicates.len() > 1) {
        return Err("fresh replay problem contains a nonlinear Horn clause".to_string());
    }
    let trace = &witness.derivation_clause_indices;
    if trace.is_empty() {
        return Err("derivation trace is empty".to_string());
    }
    if trace.len() > MAX_REPLAY_PATH_CLAUSES || trace.len() > problem.clauses().len() {
        return Err(format!("derivation trace length {} exceeds the replay budget", trace.len()));
    }

    let clauses = alpha_renamed_clauses(problem)
        .ok_or_else(|| "fresh clauses exceed the exact alpha-renaming budget".to_string())?;
    let mut seen = HashSet::with_capacity(trace.len());
    let mut constraints = Vec::new();
    let mut previous_head: Option<(PredicateId, Vec<ChcExpr>)> = None;

    for (position, raw_index) in trace.iter().copied().enumerate() {
        let index = usize::try_from(raw_index)
            .map_err(|_| format!("derivation clause index {raw_index} is not representable"))?;
        let clause = clauses
            .get(index)
            .ok_or_else(|| format!("derivation clause index {raw_index} is out of range"))?;
        if !seen.insert(index) {
            return Err(format!("derivation clause index {raw_index} is repeated"));
        }

        match (&previous_head, clause.body.predicates.as_slice()) {
            (None, []) => {}
            (None, _) => {
                return Err("derivation does not begin with a fact clause".to_string());
            }
            (Some((head_predicate, head_args)), [(body_predicate, body_args)]) => {
                if head_predicate != body_predicate || head_args.len() != body_args.len() {
                    return Err(format!(
                        "derivation transition at position {position} does not consume the previous head"
                    ));
                }
                constraints.extend(
                    body_args.iter().zip(head_args).map(|(body_arg, head_arg)| {
                        ChcExpr::eq(body_arg.clone(), head_arg.clone())
                    }),
                );
            }
            (Some(_), _) => {
                return Err(format!("derivation transition at position {position} is not linear"));
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            constraints.push(constraint.clone());
        }

        let is_last = position + 1 == trace.len();
        match (&clause.head, is_last) {
            (ClauseHead::Predicate(predicate, args), false) => {
                previous_head = Some((*predicate, args.clone()));
            }
            (ClauseHead::False, true) => {
                previous_head = None;
            }
            (ClauseHead::False, false) => {
                return Err(format!(
                    "non-final derivation clause at position {position} has a false head"
                ));
            }
            (ClauseHead::Predicate(_, _), true) => {
                return Err("derivation does not end in a query clause".to_string());
            }
            _ => return Err("derivation contains an unrecognized clause-head shape".to_string()),
        }
    }

    let formula = ChcExpr::and_all(constraints.iter().cloned());
    let mut variables = BTreeMap::new();
    for variable in formula.vars() {
        if let Some(previous_sort) = variables.insert(variable.name.clone(), variable.sort.clone())
            && previous_sort != variable.sort
        {
            return Err(format!(
                "derivation variable `{}` is used at inconsistent sorts",
                variable.name
            ));
        }
    }
    if variables.len() > MAX_REPLAY_MODEL_BINDINGS {
        return Err(format!(
            "derivation model requires {} bindings, above the replay budget",
            variables.len()
        ));
    }
    let model = witness
        .model
        .as_object()
        .ok_or_else(|| "witness model is not a JSON object".to_string())?;
    if model.len() != variables.len() {
        return Err(format!(
            "witness model has {} bindings but the derivation requires exactly {}",
            model.len(),
            variables.len()
        ));
    }
    if model.keys().any(|name| !variables.contains_key(name)) {
        return Err("witness model contains an unexpected binding".to_string());
    }

    for (name, sort) in variables {
        let encoded =
            model.get(&name).ok_or_else(|| format!("witness model is missing `{name}`"))?;
        let value = parse_model_value(&name, &sort, encoded)?;
        constraints.push(ChcExpr::eq(ChcExpr::var(ay_chc::ChcVar::new(name, sort)), value));
    }

    let mut smt = problem.make_smt_context();
    match solve_constraints(&mut smt, &constraints) {
        SolveOutcome::Sat(_) => Ok(()),
        SolveOutcome::Unsat => {
            Err("witness assignment does not satisfy the reconstructed derivation".to_string())
        }
        SolveOutcome::Undecided => {
            Err("witness replay was undecided within the strict SMT budget".to_string())
        }
    }
}

fn parse_model_value(
    name: &str,
    expected_sort: &ay_chc::ChcSort,
    encoded: &serde_json::Value,
) -> Result<ChcExpr, String> {
    let object = encoded
        .as_object()
        .ok_or_else(|| format!("model binding `{name}` is not a typed object"))?;
    let kind = object
        .get("kind")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| format!("model binding `{name}` has no string kind"))?;
    match (expected_sort, kind) {
        (ay_chc::ChcSort::Bool, "bool") if object.len() == 2 => object
            .get("value")
            .and_then(serde_json::Value::as_bool)
            .map(ChcExpr::bool_const)
            .ok_or_else(|| format!("model binding `{name}` has an invalid Bool value")),
        (ay_chc::ChcSort::Int, "int") if object.len() == 2 => {
            let value = object
                .get("value")
                .and_then(parse_json_i128)
                .ok_or_else(|| format!("model binding `{name}` has an invalid Int value"))?;
            Ok(ChcExpr::int(value))
        }
        (ay_chc::ChcSort::Real, "real") if object.len() == 4 => {
            let numerator = object
                .get("numerator")
                .and_then(serde_json::Value::as_str)
                .and_then(|value| value.parse::<i64>().ok())
                .ok_or_else(|| format!("model binding `{name}` has an invalid Real numerator"))?;
            let denominator = object
                .get("denominator")
                .and_then(serde_json::Value::as_str)
                .and_then(|value| value.parse::<i64>().ok())
                .filter(|value| *value != 0)
                .ok_or_else(|| format!("model binding `{name}` has an invalid Real denominator"))?;
            if object.get("decimal").and_then(serde_json::Value::as_str).is_none() {
                return Err(format!("model binding `{name}` has no Real decimal rendering"));
            }
            Ok(ChcExpr::Real(numerator, denominator))
        }
        (ay_chc::ChcSort::BitVec(expected_width), "bit_vec") if object.len() == 4 => {
            let width = object
                .get("width")
                .and_then(serde_json::Value::as_u64)
                .and_then(|width| u32::try_from(width).ok())
                .ok_or_else(|| format!("model binding `{name}` has an invalid bit-vector width"))?;
            if width != *expected_width || width == 0 || width > 128 {
                return Err(format!(
                    "model binding `{name}` has width {width}, expected {expected_width}"
                ));
            }
            let value = object
                .get("value")
                .and_then(serde_json::Value::as_str)
                .and_then(|value| value.parse::<u128>().ok())
                .ok_or_else(|| format!("model binding `{name}` has an invalid bit-vector value"))?;
            if width < 128 && value >= (1u128 << width) {
                return Err(format!("model binding `{name}` exceeds its bit-vector width"));
            }
            let expected_hex =
                format!("0x{:0width$x}", value, width = (width as usize).div_ceil(4));
            if object.get("hex").and_then(serde_json::Value::as_str) != Some(expected_hex.as_str())
            {
                return Err(format!("model binding `{name}` has a non-canonical hex rendering"));
            }
            Ok(ChcExpr::BitVec(value, width))
        }
        (ay_chc::ChcSort::Array(key_sort, value_sort), "const_array") if object.len() == 2 => {
            let default = object
                .get("default")
                .ok_or_else(|| format!("model binding `{name}` has no array default"))?;
            let default = parse_model_value(name, value_sort, default)?;
            Ok(ChcExpr::ConstArray((**key_sort).clone(), Arc::new(default)))
        }
        _ => Err(format!(
            "model binding `{name}` kind `{kind}` does not exactly encode sort `{expected_sort}`"
        )),
    }
}

fn parse_json_i128(value: &serde_json::Value) -> Option<i128> {
    value
        .as_i64()
        .map(i128::from)
        .or_else(|| value.as_u64().map(i128::from))
        .or_else(|| value.as_str()?.parse::<i128>().ok())
}

/// Give every clause a disjoint variable namespace before composing facts.
///
/// CHC variables are universally quantified *per clause*. Reusing the same
/// textual [`ay_chc::ChcVar`] in two clauses is alpha-equivalent in Horn
/// semantics, but directly conjoining the two clause bodies without renaming
/// accidentally identifies those locals. That can strengthen a reachable path
/// into an UNSAT path and make the exhaustive search return a false `Safe`.
///
/// One deterministic namespace per clause is sufficient for the unary-body,
/// acyclic domain admitted above: a clause cannot occur twice on one derivation
/// path. Nonlinear bodies remain fail-closed because two facts produced by the
/// same clause could require distinct instantiations in one combination.
fn alpha_renamed_clauses(problem: &ChcProblem) -> Option<Vec<HornClause>> {
    // `HornClause::vars` and `ChcExpr::substitute` both have private traversal
    // limits in ay-chc. In particular, a variable below the depth limit can be
    // omitted by `vars`, remain unrenamed by the best-effort substitution, and
    // then also be omitted by a `renamed.vars()` post-check. That would restore
    // cross-clause capture and could turn a reachable path into a false UNSAT.
    // Inspect the public expression shape iteratively first, before calling
    // either budgeted operation. Anything at their boundary defers to PDR.
    if !problem.clauses().iter().all(clause_fits_alpha_substitution_limits) {
        return None;
    }

    let original_names: HashSet<String> =
        problem.clauses().iter().flat_map(HornClause::vars).map(|var| var.name).collect();
    let mut namespace_id = 0usize;
    let namespace = loop {
        let candidate = format!("__trust_mc_direct_smt_alpha_{namespace_id}_");
        if original_names.iter().all(|name| !name.starts_with(&candidate)) {
            break candidate;
        }
        namespace_id = namespace_id.checked_add(1)?;
    };

    problem
        .clauses()
        .iter()
        .enumerate()
        .map(|(clause_index, clause)| {
            let substitutions: Vec<_> = clause
                .vars()
                .into_iter()
                .enumerate()
                .map(|(variable_index, variable)| {
                    let replacement = ChcExpr::var(ay_chc::ChcVar::new(
                        format!("{namespace}c{clause_index}_v{variable_index}"),
                        variable.sort.clone(),
                    ));
                    (variable, replacement)
                })
                .collect();

            let mut renamed = clause.clone();
            for (_, args) in &mut renamed.body.predicates {
                for arg in args {
                    *arg = arg.substitute(&substitutions);
                }
            }
            if let Some(constraint) = &mut renamed.body.constraint {
                *constraint = constraint.substitute(&substitutions);
            }
            match &mut renamed.head {
                ClauseHead::Predicate(_, args) => {
                    for arg in args {
                        *arg = arg.substitute(&substitutions);
                    }
                }
                ClauseHead::False => {}
                _ => return None,
            }

            renamed
                .vars()
                .iter()
                .all(|variable| variable.name.starts_with(&namespace))
                .then_some(renamed)
        })
        .collect()
}

/// Return whether every expression in `clause` is wholly traversable by the
/// pinned ay-chc variable collector and substitution implementation.
fn clause_fits_alpha_substitution_limits(clause: &HornClause) -> bool {
    for (_, args) in &clause.body.predicates {
        if !args.iter().all(expr_fits_alpha_substitution_limits) {
            return false;
        }
    }
    if clause
        .body
        .constraint
        .as_ref()
        .is_some_and(|constraint| !expr_fits_alpha_substitution_limits(constraint))
    {
        return false;
    }
    match &clause.head {
        ClauseHead::Predicate(_, args) => args.iter().all(expr_fits_alpha_substitution_limits),
        ClauseHead::False => true,
        // `ClauseHead` is non-exhaustive. A future expression-bearing shape
        // needs an explicit traversal before it can enter the direct-SMT lane.
        _ => false,
    }
}

/// Iteratively scan one public `ChcExpr` DAG without relying on ay-chc's
/// depth-limited helpers.
///
/// The node count is by distinct `Arc` allocation, matching substitution's
/// pointer memo. We also revisit a shared node reached at a greater depth so a
/// deep alias cannot hide behind an earlier shallow visit. Counting leaves is
/// deliberately conservative: ay-chc spends its node budget on non-variable
/// nodes, so accepting no more total nodes guarantees its budget cannot expire.
fn expr_fits_alpha_substitution_limits(expr: &ChcExpr) -> bool {
    expr_fits_alpha_substitution_limits_with(
        expr,
        AY_CHC_SUBSTITUTION_MAX_DEPTH,
        AY_CHC_SUBSTITUTION_MAX_DISTINCT_NODES,
    )
}

fn expr_fits_alpha_substitution_limits_with(
    expr: &ChcExpr,
    max_depth: usize,
    max_distinct_nodes: usize,
) -> bool {
    if max_depth == 0 || max_distinct_nodes == 0 {
        return false;
    }

    let mut deepest_visit: HashMap<*const ChcExpr, usize> = HashMap::new();
    let mut pending = vec![(expr, 0usize)];
    while let Some((node, depth)) = pending.pop() {
        // ay-chc's collector stops before inspecting a node at this depth, and
        // substitution can leave the corresponding subtree unchanged.
        if depth >= max_depth {
            return false;
        }

        let pointer = std::ptr::from_ref(node);
        match deepest_visit.get_mut(&pointer) {
            Some(previous_depth) if depth <= *previous_depth => continue,
            Some(previous_depth) => *previous_depth = depth,
            None => {
                if deepest_visit.len() >= max_distinct_nodes {
                    return false;
                }
                deepest_visit.insert(pointer, depth);
            }
        }

        let child_depth = depth + 1;
        match node {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                pending.extend(args.iter().map(|child| (child.as_ref(), child_depth)));
            }
            ChcExpr::ConstArray(_, value) => {
                pending.push((value.as_ref(), child_depth));
            }
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
            // `ChcExpr` is non-exhaustive. New expression shapes must opt in
            // with an explicit child traversal before alpha-renaming is safe.
            _ => return false,
        }
    }
    true
}

fn body_fact_options(
    clause: &HornClause,
    facts: &HashMap<PredicateId, Vec<ReachFact>>,
) -> Option<Vec<Vec<ReachFact>>> {
    let mut options = Vec::with_capacity(clause.body.predicates.len());
    for (pred, _) in &clause.body.predicates {
        let pred_facts = facts.get(pred)?;
        if pred_facts.is_empty() {
            return None;
        }
        options.push(pred_facts.clone());
    }
    Some(options)
}

/// Decide whether `constraints` are satisfiable and, if so, return a typed,
/// machine-readable JSON model witnessing the assignment. `None` means the
/// conjunction is unsatisfiable or could not be decided under the wall-clock
/// bound.
///
/// Every conjunction — linear integer arithmetic, bit-vectors, Booleans, arrays,
/// and nonlinear integer multiplication alike — is dispatched to ay's SMT solver
/// under [`SMT_QUERY_TIMEOUT`]. Decidable fragments return a `Sat` model (a real
/// witness) or `Unsat`. Nonlinear integer multiplication is undecidable for ay's
/// QF_LIA core; it returns `Unknown` promptly (it honors the bound).
///
/// CRITICAL: `Unknown` is reported as [`SolveOutcome::Undecided`], NOT folded into
/// "no model". An undecided body may actually be satisfiable; pruning it as if
/// `Unsat` would let the exhaustive search claim SAFE on a reachable-but-undecided
/// panic (a false proof). Only a definitive UNSAT licenses pruning.
///
/// Three-valued outcome of an acyclic clause-body satisfiability query.
///
/// SOUNDNESS (load-bearing): the acyclic search may prune a clause-body edge
/// (treat it as deriving no fact) ONLY when the body is *definitively* `Unsat`.
/// An `Unknown` / timeout result is NOT a proof of unsatisfiability — the body
/// may actually be satisfiable (a real reachable fact, and downstream a real
/// reachable panic) that ay simply could not decide. Folding `Unknown` into
/// "no model" (the previous `_ => None`) let an undecided edge be silently
/// pruned, so the fixpoint reported `ExhaustivelyNone` → `AcyclicDecision::Safe`
/// → a proof-grade `ChcValidity` SAFE certificate on a program that can panic.
/// We therefore keep `Undecided` distinct and taint exhaustiveness on it.
#[allow(clippy::large_enum_variant)] // short-lived, soundness-pinned decision value
enum SolveOutcome {
    /// Body is satisfiable; carries the witness model.
    Sat(serde_json::Value),
    /// Body is definitively unsatisfiable (plain / core / Farkas) — safe to prune.
    Unsat,
    /// Solver could not decide (Unknown / timeout / undecidable fragment). The
    /// edge may be live; the caller MUST taint `truncated` and defer to PDR.
    Undecided,
}

/// The three-valued *tag* (no payload) of an SMT result. This names the single
/// soundness-critical classification of the acyclic search and is the decision
/// proven sound in `clean:proofs/trust-soundness/fix_correctness.lean`
/// (theorem `p0_2_fix_exact`) and pinned to THIS code by the differential oracle
/// `differential_smt_classification_matches_clean_proven_table`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SolveOutcomeTag {
    Sat,
    Unsat,
    Undecided,
}

/// Pure, total classification of an SMT result into its [`SolveOutcomeTag`].
///
/// SOUNDNESS (load-bearing): only a *definitive* UNSAT (plain / core / Farkas)
/// licenses pruning a clause-body edge. `SmtResult::Unknown` — and, fail-closed,
/// ANY future indeterminate variant — must classify as `Undecided`, NEVER
/// `Unsat`. Folding `Unknown` into "no model" / prunable (the reverted
/// `07511178f` `_ => None`) let an undecided edge be pruned, so the fixpoint
/// claimed `ExhaustivelyNone` → `AcyclicDecision::Safe` on a program that can
/// panic — a false proof.
///
/// This function is the machine-checked decision table at the soundness
/// frontier. Two artifacts keep it honest, in opposite directions:
///   * `clean`'s `p0_2_fix_exact` proves this *table* equals the truth (only
///     definitive-UNSAT is prunable);
///   * the differential oracle test proves THIS production code equals that
///     proven table — closing the proof-to-code fidelity gap by construction.
/// Keeping the classification a single named function (rather than inline match
/// arms) is what makes that correspondence testable at all.
fn classify_smt_result(result: &SmtResult) -> SolveOutcomeTag {
    if result.is_sat() {
        SolveOutcomeTag::Sat
    } else if result.is_unsat() {
        // `is_unsat()` is exactly `Unsat | UnsatWithCore(_) | UnsatWithFarkas(_)`.
        SolveOutcomeTag::Unsat
    } else {
        // `Unknown` and any future indeterminate variant fail closed to Undecided.
        SolveOutcomeTag::Undecided
    }
}

/// SOUND relevance-slicing pre-phase: try to prove the body UNSATISFIABLE from a
/// strict SUBSET of its top-level conjuncts. Returns `true` only on a definitive
/// subset-UNSAT.
///
/// # Why this exists
///
/// The TrustIr lowering fuses a whole function's panic-freedom obligation into
/// one clause body. Large bit-vector components can make that fused query
/// undecidable even when a small, variable-disjoint component is contradictory.
/// Slicing exposes those small contradictions without weakening the proof bar.
///
/// # Soundness derivation
///
/// Let flattening split ONLY top-level conjunctions, equivalence-preservingly, so
/// `PHI = C1 ∧ … ∧ Cn`. For any subset `S`, `PHI ⟹ AND(i∈S, Ci)`, hence
/// `UNSAT(AND(i∈S, Ci)) ⟹ UNSAT(PHI)`. The caller may therefore prune the
/// body only when a probed strict subset receives the same definitive-UNSAT tag
/// used by the full query.
///
/// Three details are load-bearing and test-pinned: slices index original
/// conjuncts without rewriting them; only [`SolveOutcomeTag::Unsat`] is consumed;
/// and slice models never enter the refutation lane.
fn slicing_proves_unsat(smt: &mut SmtContext, constraints: &[ChcExpr]) -> bool {
    if slicing_disabled() {
        return false;
    }
    let conjuncts = relevance_slicing::flat_conjuncts(constraints);
    let slices = relevance_slicing::relevance_slices(&conjuncts);
    if slices.is_empty() {
        return false;
    }

    let started = Instant::now();
    let phase_budget = slice_phase_budget();
    let probe_timeout = slice_probe_timeout();
    for slice in slices {
        if started.elapsed() >= phase_budget {
            return false;
        }
        // A genuine SUBSET: each element is a clone of an original conjunct,
        // selected by index. Never a rewrite.
        let subset: Vec<ChcExpr> = slice.iter().map(|&index| conjuncts[index].clone()).collect();
        debug_assert!(subset.len() < conjuncts.len(), "relevance_slices must emit strict subsets");
        let formula = ChcExpr::and_all(subset);
        smt.reset();
        let result = smt.check_sat_with_timeout(&formula, probe_timeout);
        // A SAT or undecided slice says nothing about the full conjunction.
        if classify_smt_result(&result) == SolveOutcomeTag::Unsat {
            return true;
        }
    }
    false
}

fn solve_constraints(smt: &mut SmtContext, constraints: &[ChcExpr]) -> SolveOutcome {
    // Run before the fused query because the target bodies can consume the whole
    // caller budget there. This can only turn a would-be `Undecided` into a
    // subset-justified `Unsat`; it cannot divert a satisfiable body or produce a
    // witness.
    if slicing_proves_unsat(smt, constraints) {
        return SolveOutcome::Unsat;
    }

    let formula = ChcExpr::and_all(constraints.iter().cloned());

    smt.reset();
    let result = smt.check_sat_with_timeout(&formula, SMT_QUERY_TIMEOUT);
    match classify_smt_result(&result) {
        SolveOutcomeTag::Sat => {
            // `Sat` tag ⟺ `result.is_sat()` ⟺ `SmtResult::Sat(_)` carries a model.
            let model = result
                .model()
                .expect("classify_smt_result returned Sat ⟹ SmtResult::Sat carries a model");
            let mut assignments = serde_json::Map::new();
            for (name, value) in model {
                assignments.insert(name.clone(), smt_value_to_json(value));
            }
            SolveOutcome::Sat(serde_json::Value::Object(assignments))
        }
        // Only a *definitive* UNSAT (plain, with core, or with Farkas certificate)
        // proves the body unsatisfiable and licenses pruning it.
        SolveOutcomeTag::Unsat => SolveOutcome::Unsat,
        // `SmtResult::Unknown` — and, fail-closed, any future indeterminate
        // variant — is NOT a proof of unsatisfiability. Before giving up, make ONE
        // last-resort attempt on a sound OVER-approximation of the body: havoc the
        // wide-integer / nonlinear noise (the base-1e9 Horner encoding of `>i128`
        // constants and nonlinear `Mul`/`Div`/`Mod`, which choke the LIA/NIA core)
        // to fresh unconstrained variables, leaving the boolean/comparison skeleton
        // intact. Because `models(concrete) ⊆ models(abstract)`, a DEFINITIVE
        // abstract-UNSAT proves the concrete body unsatisfiable too — the only
        // direction we consume. Anything other than a definitive abstract-UNSAT
        // (including an abstract-SAT, whose model is meaningless for the concrete
        // body) falls through to the original, fail-closed `Undecided`. The
        // abstract model is NEVER read — it can only license, never refute.
        SolveOutcomeTag::Undecided => {
            let abstract_constraints = abstract_wide_nonlinear(constraints);
            let abstract_formula = ChcExpr::and_all(abstract_constraints.iter().cloned());
            smt.reset();
            let abstract_result = smt.check_sat_with_timeout(&abstract_formula, SMT_QUERY_TIMEOUT);
            // Reuse the differential-oracle-pinned classifier: only a definitive
            // UNSAT tag (never `Unknown`, never `Sat`) may promote the verdict.
            match classify_smt_result(&abstract_result) {
                SolveOutcomeTag::Unsat => SolveOutcome::Unsat,
                _ => SolveOutcome::Undecided,
            }
        }
    }
}

/// Render an [`SmtValue`] as a typed, machine-readable JSON object. Each variant
/// carries a `kind` tag plus the fields a downstream consumer needs to interpret
/// the witness without re-parsing a debug string. Bit-vectors expose both the
/// decimal value and a zero-padded hex form so overflow counterexamples are
/// directly readable.
fn smt_value_to_json(value: &SmtValue) -> serde_json::Value {
    match value {
        SmtValue::Bool(b) => serde_json::json!({ "kind": "bool", "value": b }),
        SmtValue::Int(i) => {
            // serde_json's `Number` spans only i64/u64; a wider model integer (an
            // `i128` outside that range — exactly the overflow counterexamples this
            // renderer exists to show) makes `json!` fail "number out of range",
            // and the resulting unwrap ICE'd the whole driver. A verifier must
            // never crash on a witness value: emit a native JSON number when it
            // fits, else a full-precision decimal string.
            let value = i64::try_from(*i)
                .map(serde_json::Value::from)
                .or_else(|_| u64::try_from(*i).map(serde_json::Value::from))
                .unwrap_or_else(|_| serde_json::Value::String(i.to_string()));
            serde_json::json!({ "kind": "int", "value": value })
        }
        SmtValue::Real(r) => serde_json::json!({
            "kind": "real",
            "numerator": r.numer().to_string(),
            "denominator": r.denom().to_string(),
            "decimal": r.to_string(),
        }),
        SmtValue::BitVec(v, width) => {
            let hex_digits = (*width as usize).div_ceil(4).max(1);
            serde_json::json!({
                "kind": "bit_vec",
                "width": width,
                "value": v.to_string(),
                "hex": format!("0x{:0width$x}", v, width = hex_digits),
            })
        }
        SmtValue::Opaque(s) => serde_json::json!({ "kind": "opaque", "symbol": s }),
        SmtValue::ConstArray(default) => serde_json::json!({
            "kind": "const_array",
            "default": smt_value_to_json(default),
        }),
        SmtValue::ArrayMap { default, entries } => serde_json::json!({
            "kind": "array_map",
            "default": smt_value_to_json(default),
            "entries": entries
                .iter()
                .map(|(index, element)| serde_json::json!({
                    "index": smt_value_to_json(index),
                    "value": smt_value_to_json(element),
                }))
                .collect::<Vec<_>>(),
        }),
        SmtValue::Datatype(ctor, fields) => serde_json::json!({
            "kind": "datatype",
            "constructor": ctor,
            "fields": fields.iter().map(smt_value_to_json).collect::<Vec<_>>(),
        }),
        // SmtValue is #[non_exhaustive]; fall back to a typed opaque rendering
        // rather than dropping an unknown variant from the witness.
        other => serde_json::json!({ "kind": "unknown", "debug": format!("{other:?}") }),
    }
}

struct FactCombinationIter {
    options: Vec<Vec<ReachFact>>,
    indices: Vec<usize>,
    done: bool,
}

impl FactCombinationIter {
    fn new(options: Vec<Vec<ReachFact>>) -> Self {
        let len = options.len();
        Self { options, indices: vec![0; len], done: false }
    }
}

impl Iterator for FactCombinationIter {
    type Item = Vec<ReachFact>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let item: Vec<ReachFact> = self
            .options
            .iter()
            .zip(&self.indices)
            .map(|(facts, index)| facts[*index].clone())
            .collect();

        if self.indices.is_empty() {
            self.done = true;
            return Some(item);
        }

        for pos in (0..self.indices.len()).rev() {
            self.indices[pos] += 1;
            if self.indices[pos] < self.options[pos].len() {
                return Some(item);
            }
            self.indices[pos] = 0;
        }
        self.done = true;
        Some(item)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use ay_chc::{ChcOp, ChcSort, ChcVar, ClauseBody};

    /// `error <- (_4∈{0,1,2}) ∧ (_4∉{0,1,2})` — the exact typed-VC an exhaustive
    /// enum match's unreachable default produces. The body is UNSAT so `error` is
    /// unreachable: a COMPLETE acyclic decision must say SAFE. PDR alone returns
    /// Unknown here (no inductive structure to synthesize), which is the bug this
    /// shortcut closes.
    fn exhaustive_unreachable_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let d = ChcVar::new("_4", ChcSort::Int);
        let v = || ChcExpr::var(d.clone());
        let in_cases = ChcExpr::or_vec(vec![
            ChcExpr::eq(v(), ChcExpr::int(0)),
            ChcExpr::eq(v(), ChcExpr::int(1)),
            ChcExpr::eq(v(), ChcExpr::int(2)),
        ]);
        let not_in_cases = ChcExpr::and_vec(vec![
            ChcExpr::not(ChcExpr::eq(v(), ChcExpr::int(0))),
            ChcExpr::not(ChcExpr::eq(v(), ChcExpr::int(1))),
            ChcExpr::not(ChcExpr::eq(v(), ChcExpr::int(2))),
        ]);
        let constraint = ChcExpr::and_vec(vec![in_cases, not_in_cases]);
        problem.add_clause(HornClause::new(ClauseBody::constraint(constraint), ClauseHead::False));
        problem
    }

    #[test]
    fn exhaustive_unreachable_decides_safe() {
        match acyclic_direct_smt_decision(&exhaustive_unreachable_problem()) {
            AcyclicDecision::Safe => {}
            AcyclicDecision::Unsafe(_) => {
                panic!("UNSAT-body unreachable wrongly refuted (unsound)")
            }
            AcyclicDecision::Inconclusive => {
                panic!("complete acyclic search must decide, not defer")
            }
        }
    }

    #[test]
    fn clause_local_variable_names_are_alpha_renamed_before_composition() {
        // Horn variables are scoped per clause. Although all three clauses use
        // the textual name `x`, C1.x and C2.x are independent:
        //
        //   x = 0       -> p(x)
        //   p(y), x = 1 -> q(x)
        //   q(z), z = 1 -> false
        //
        // The real derivation p(0) -> q(1) -> false is reachable. Without
        // clause-local alpha-renaming, the direct composer carried C1's `x = 0`
        // into C2 and conjoined C2's unrelated `x = 1`, pruned the path as
        // UNSAT, and could return a false `Safe`.
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![ChcSort::Int]);
        let q = problem.declare_predicate("q", vec![ChcSort::Int]);

        let c1_x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(c1_x.clone(), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![c1_x]),
        ));

        let c2_x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let c2_y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![c2_y])],
                Some(ChcExpr::eq(c2_x.clone(), ChcExpr::int(1))),
            ),
            ClauseHead::Predicate(q, vec![c2_x]),
        ));

        let c3_z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![c3_z.clone()])],
                Some(ChcExpr::eq(c3_z, ChcExpr::int(1))),
            ),
            ClauseHead::False,
        ));

        let AcyclicDecision::Unsafe(witness) = acyclic_direct_smt_decision(&problem) else {
            panic!("clause-local names must be alpha-renamed; this error derivation is reachable");
        };
        replay_acyclic_direct_smt_witness(&problem, &witness)
            .expect("the producer's exact trace/model must independently replay");

        let mut wrong_values = witness.clone();
        for binding in wrong_values
            .model
            .as_object_mut()
            .expect("producer model is an assignment object")
            .values_mut()
        {
            if binding.get("kind").and_then(serde_json::Value::as_str) == Some("int") {
                binding["value"] = serde_json::json!(42);
            }
        }
        assert!(
            replay_acyclic_direct_smt_witness(&problem, &wrong_values).is_err(),
            "a model that violates the reconstructed equalities must fail replay"
        );

        let mut missing_binding = witness.clone();
        let first_name = missing_binding
            .model
            .as_object()
            .and_then(|model| model.keys().next().cloned())
            .expect("fixture model has at least one binding");
        missing_binding
            .model
            .as_object_mut()
            .expect("producer model is an assignment object")
            .remove(&first_name);
        assert!(
            replay_acyclic_direct_smt_witness(&problem, &missing_binding).is_err(),
            "a partial model must fail the total-assignment gate"
        );

        let mut wrong_transition = witness;
        assert!(wrong_transition.derivation_clause_indices.len() >= 2);
        wrong_transition.derivation_clause_indices[1] =
            wrong_transition.derivation_clause_indices[0];
        assert!(
            replay_acyclic_direct_smt_witness(&problem, &wrong_transition).is_err(),
            "a repeated/wrong transition cannot identify the original derivation"
        );
    }

    #[test]
    fn expression_beyond_ay_substitution_depth_defers_before_alpha_renaming() {
        // ay-chc's variable collector stops at depth 500 and its substitution
        // can leave that subtree unchanged. Before the iterative preflight,
        // both the original-variable collection and the post-rename check
        // missed this leaf, so a partial alpha-rename could be treated as
        // complete. Deep same-block SSA chains can produce this shape.
        let mut constraint = ChcExpr::var(ChcVar::new("deep_local", ChcSort::Bool));
        for _ in 0..=AY_CHC_SUBSTITUTION_MAX_DEPTH {
            constraint = ChcExpr::FuncApp(
                "deep_bool_identity".to_string(),
                ChcSort::Bool,
                vec![Arc::new(constraint)],
            );
        }
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::new(ClauseBody::constraint(constraint), ClauseHead::False));

        assert!(alpha_renamed_clauses(&problem).is_none());
        assert!(matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Inconclusive));
    }

    #[test]
    fn alpha_substitution_shape_scan_enforces_distinct_node_budget() {
        let expression = ChcExpr::Op(
            ChcOp::And,
            vec![Arc::new(ChcExpr::Bool(true)), Arc::new(ChcExpr::Bool(false))],
        );

        assert!(expr_fits_alpha_substitution_limits_with(&expression, 8, 3));
        assert!(!expr_fits_alpha_substitution_limits_with(&expression, 8, 2));
    }

    #[test]
    fn reach_fact_dedup_uses_structure_not_delimiter_based_display_text() {
        // `FuncApp` names are caller-controlled and Display does not escape
        // newlines. These three distinct Boolean atoms therefore satisfy:
        //
        //   display(injected) == display(a) + "\n" + display(b)
        //
        // The old fact signature joined constraints with newlines, so it
        // conflated the two p facts below. It kept only `injected -> p`, for
        // which the error body adds `!injected` and is UNSAT, while suppressing
        // the real `a && b -> p` path (SAT with a=b=true, injected=false). That
        // made this reachable error falsely Safe.
        let a = ChcExpr::FuncApp("a".to_string(), ChcSort::Bool, vec![]);
        let b = ChcExpr::FuncApp("b".to_string(), ChcSort::Bool, vec![]);
        let injected = ChcExpr::FuncApp("a:Bool)\n(b".to_string(), ChcSort::Bool, vec![]);
        assert_eq!(injected.to_string(), format!("{a}\n{b}"));
        assert_ne!(injected, a);
        assert_ne!(injected, b);

        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![]);
        let q = problem.declare_predicate("q", vec![]);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(injected.clone()),
            ClauseHead::Predicate(p, vec![]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(a),
            ClauseHead::Predicate(q, vec![]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(q, vec![])], Some(b)),
            ClauseHead::Predicate(p, vec![]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![])], Some(ChcExpr::not(injected))),
            ClauseHead::False,
        ));

        assert!(
            matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Unsafe(_)),
            "structurally distinct reach facts must not collide and suppress the SAT error path"
        );
    }

    #[test]
    fn nonlinear_horn_body_defers_until_per_combination_freshening_exists() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![]);
        let q = problem.declare_predicate("q", vec![]);
        problem.add_clause(HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(p, vec![])));
        problem.add_clause(HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(q, vec![])));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![]), (q, vec![])]),
            ClauseHead::False,
        ));

        assert!(matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Inconclusive));
    }

    /// REGRESSION (modulo_unreachable capability): `n % 4` lowers to `BinOp::URem`
    /// = `bvurem`, so the `k >= 4 => unreachable` obligation is the QF_BV VC
    /// `error <- (n bvurem 4) >=u 4`, UNSAT because an unsigned remainder is always
    /// `< its divisor`. ay's bvurem UNSAT reasoning restart-thrashes past the tight
    /// `SMT_QUERY_TIMEOUT`, so without help the shortcut returns Inconclusive and
    /// the obligation goes unproved. The fix emits the remainder RANGE LEMMA
    /// `(n bvurem 4) <u 4` (always sound for a nonzero divisor) alongside the
    /// obligation; with it, the contradiction `rem >=u 4 ∧ rem <u 4` is decided on
    /// `rem` alone — no bvurem bit-blasting — so the obligation proves SAFE fast.
    /// PROBE matching modulo_unreachable's REAL CHC (captured): `n % 4` is modeled
    /// with `IntMod` (Int sort), and the translation already conjoins the remainder
    /// lemma `k < 4`. The error body therefore contains `k >= 4 ∧ k < 4` — a pure
    /// LINEAR contradiction, UNSAT regardless of `IntMod` (treat it as an
    /// uninterpreted term). If this is NOT Safe, the bug is that `IntMod`'s presence
    /// blocks an otherwise-sound linear UNSAT (fragment/proof-grade gating too coarse).
    #[test]
    fn modulo_intmod_with_range_lemma_decides_safe() {
        let mut problem = ChcProblem::new();
        let n = ChcExpr::var(ChcVar::new("n", ChcSort::Int));
        let k = ChcExpr::var(ChcVar::new("k", ChcSort::Int));
        let four = ChcExpr::int(4);
        let body = ChcExpr::and_vec(vec![
            ChcExpr::eq(k.clone(), ChcExpr::mod_op(n, four.clone())), // k = n % 4
            ChcExpr::ge(k.clone(), four.clone()),                     // k >= 4 (error cond)
            ChcExpr::lt(k, four),                                     // k < 4  (remainder lemma)
        ]);
        problem.add_clause(HornClause::new(ClauseBody::constraint(body), ClauseHead::False));
        match acyclic_direct_smt_decision(&problem) {
            AcyclicDecision::Safe => {}
            AcyclicDecision::Unsafe(_) => panic!("UNSOUND: k>=4 ∧ k<4 wrongly SAT"),
            AcyclicDecision::Inconclusive => {
                panic!("IntMod presence blocked the sound linear UNSAT (k>=4 ∧ k<4)")
            }
        }
    }

    #[test]
    fn modulo_bvurem_range_lemma_decides_safe() {
        let mut problem = ChcProblem::new();
        let n = ChcExpr::var(ChcVar::new("n", ChcSort::BitVec(32)));
        let four = ChcExpr::BitVec(4, 32);
        let rem = ChcExpr::bv_urem(n, four.clone());
        let rem_ge_4 = ChcExpr::bv_ule(four.clone(), rem.clone()); // 4 <=u rem
        let rem_lt_4 = ChcExpr::not(ChcExpr::bv_ule(four, rem)); // ¬(4 <=u rem) == rem <u 4 (the lemma)
        let body = ChcExpr::and_vec(vec![rem_ge_4, rem_lt_4]);
        problem.add_clause(HornClause::new(ClauseBody::constraint(body), ClauseHead::False));
        match acyclic_direct_smt_decision(&problem) {
            AcyclicDecision::Safe => {}
            AcyclicDecision::Unsafe(_) => {
                panic!("UNSOUND: (n % 4) >=u 4 wrongly refuted — remainder is always < divisor")
            }
            AcyclicDecision::Inconclusive => {
                panic!("the remainder range lemma must let the shortcut decide SAFE without bvurem")
            }
        }
    }

    /// The guarded subtraction-overflow VC that orca-core's `title_has_token`
    /// produces (build #77 ground truth, `proof_obligations[2]`): a dominating
    /// early-return guard `needle <= haystack`, the checked-op bindings
    /// `_6 = haystack, _7 = needle`, and the overflow violation
    /// `(_6 - _7 < 0) ∨ (_6 - _7 > HI)`. The guard makes both disjuncts
    /// unsatisfiable, so this is a trivial acyclic UNSAT the solver must prove
    /// SAFE. (Confirms the overflow gap is routing, not solver capability:
    /// the full pipeline reports this exact VC Unsupported.)
    #[test]
    fn guarded_subtraction_overflow_decides_safe() {
        let mut problem = ChcProblem::new();
        let haystack = ChcExpr::var(ChcVar::new("haystack", ChcSort::Int));
        let needle = ChcExpr::var(ChcVar::new("needle", ChcSort::Int));
        let v6 = ChcExpr::var(ChcVar::new("_6", ChcSort::Int));
        let v7 = ChcExpr::var(ChcVar::new("_7", ChcSort::Int));
        let diff = || ChcExpr::sub(v6.clone(), v7.clone());
        let body = ChcExpr::and_vec(vec![
            ChcExpr::le(needle.clone(), haystack.clone()), // dominating guard
            ChcExpr::ge(needle.clone(), ChcExpr::int(0)),  // usize range
            ChcExpr::le(haystack.clone(), ChcExpr::int(1000)), // bounded upper end
            ChcExpr::eq(v6.clone(), haystack),             // _6 = haystack
            ChcExpr::eq(v7.clone(), needle),               // _7 = needle
            ChcExpr::or_vec(vec![
                ChcExpr::lt(diff(), ChcExpr::int(0)),
                ChcExpr::gt(diff(), ChcExpr::int(1000)),
            ]),
        ]);
        problem.add_clause(HornClause::new(ClauseBody::constraint(body), ClauseHead::False));
        match acyclic_direct_smt_decision(&problem) {
            AcyclicDecision::Safe => {}
            AcyclicDecision::Unsafe(_) => panic!("guarded subtraction wrongly refuted (unsound)"),
            AcyclicDecision::Inconclusive => panic!("guarded subtraction VC must decide SAFE"),
        }
    }

    #[test]
    fn satisfiable_body_decides_unsafe() {
        // `error <- (_4 == 0)` is trivially satisfiable ⇒ a real counterexample.
        let mut problem = ChcProblem::new();
        let d = ChcVar::new("_4", ChcSort::Int);
        let constraint = ChcExpr::eq(ChcExpr::var(d), ChcExpr::int(0));
        problem.add_clause(HornClause::new(ClauseBody::constraint(constraint), ClauseHead::False));
        assert!(matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Unsafe(_)));
    }

    #[test]
    fn undecidable_satisfiable_body_must_not_decide_safe() {
        // P0 SOUNDNESS REGRESSION (commit 07511178f): an acyclic obligation whose
        // `error` clause body is genuinely SATISFIABLE (a reachable panic) but
        // UNDECIDABLE for ay's QF_LIA core — here nonlinear integer multiplication
        // `x * y == 6 ∧ x > 1 ∧ y > 1` (SAT at x=2,y=3) — must NEVER be promoted to
        // a proof-grade SAFE.
        //
        // Before the three-valued `solve_constraints` fix, ay's `Unknown` was folded
        // into "no model" (`_ => None`); the caller pruned the edge WITHOUT setting
        // `truncated`, so the fixpoint reported `ExhaustivelyNone` → `Safe` →
        // `ChcValidity` — a false proof of a program that can panic. The fix maps
        // `Unknown` → `SolveOutcome::Undecided` → `truncated = true` →
        // `DerivationOutcome::Truncated` → `AcyclicDecision::Inconclusive` (defer to
        // PDR). The decision must be anything BUT `Safe`. (If ay ever DOES decide this
        // body it returns `Sat` → `Unsafe`, also ≠ `Safe`; only a `Safe` here is the
        // soundness bug.)
        let mut problem = ChcProblem::new();
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
        let body = ChcExpr::and_vec(vec![
            ChcExpr::eq(ChcExpr::mul(x.clone(), y.clone()), ChcExpr::int(6)),
            ChcExpr::gt(x, ChcExpr::int(1)),
            ChcExpr::gt(y, ChcExpr::int(1)),
        ]);
        problem.add_clause(HornClause::new(ClauseBody::constraint(body), ClauseHead::False));
        assert!(
            !matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Safe),
            "an undecidable-but-satisfiable error clause must NEVER be promoted to SAFE: \
             SMT `Unknown` must taint exhaustiveness and defer to PDR, never prune as `Unsat`"
        );
    }

    /// DIFFERENTIAL ORACLE (proof-to-code fidelity link for P0#2).
    ///
    /// `clean:proofs/trust-soundness/fix_correctness.lean` proves the SMT-result
    /// decision *table* sound: `p0_2_fix_exact` shows the three-valued classifier
    /// equals the truth (Sat→live, definitive-UNSAT→prunable, everything else→
    /// Undecided), and `p0_2_bug_prunes`+`p0_2_truth_keeps` show the reverted
    /// `_ => None` bug was a false PROVE (it pruned an Unknown edge).
    ///
    /// That proof is only as good as its fidelity to the real code. This test
    /// closes that gap: it runs the ACTUAL production classifier
    /// [`classify_smt_result`] — the same function `solve_constraints` dispatches
    /// on — across every constructible `SmtResult` variant and asserts it equals
    /// the clean-proven table. If production ever drifts from the proven decision
    /// (e.g. someone re-folds `Unknown` into the prunable arm), this goes red.
    /// It executes real code, not a transcription of the match, so it cannot be
    /// satisfied by restating the bug.
    #[test]
    fn differential_smt_classification_matches_clean_proven_table() {
        use SolveOutcomeTag::*;

        // The clean-proven decision table (fix_correctness.lean::fixedPrunable),
        // checked against the real production classifier. `UnsatWithCore` /
        // `UnsatWithFarkas` are not re-exported from `ay_chc` so are not
        // constructible here; they route through `is_unsat()` to `Unsat`, and
        // misclassifying them would only cost completeness (defer to PDR), never
        // soundness — the only soundness-critical decision is `Unknown`.
        let table: &[(SmtResult, SolveOutcomeTag)] = &[
            (SmtResult::Sat(Default::default()), Sat),
            (SmtResult::Unsat, Unsat),
            (SmtResult::Unknown, Undecided),
        ];
        for (result, expected) in table {
            assert_eq!(
                classify_smt_result(result),
                *expected,
                "production classify_smt_result drifted from the clean-proven table on {result:?}"
            );
        }

        // The load-bearing soundness invariant, stated as code: an `Unknown` edge
        // is NEVER prunable. This is the exact false-proof `07511178f` introduced
        // and `p0_2_truth_keeps` proves must not happen. Pruning it would let the
        // acyclic fixpoint claim SAFE on a reachable-but-undecided panic.
        assert_ne!(
            classify_smt_result(&SmtResult::Unknown),
            Unsat,
            "FALSE-PROOF REGRESSION: SMT `Unknown` classified as prunable `Unsat` — \
             an undecided edge would be silently pruned, promoting a may-panic body to SAFE"
        );
    }

    // ==================================================================
    // Relevance slicing (`relevance_slicing`, `slicing_proves_unsat`)
    // ==================================================================

    /// A BV term wider than ay's per-term bit-blast budget. Ay refuses to blast
    /// such a query and returns `Unknown` for the whole conjunction, fail-closed.
    fn arbitrary_precision_bv_noise() -> Vec<ChcExpr> {
        let wide = ChcExpr::var(ChcVar::new("bignum", ChcSort::BitVec(20_000)));
        let other = ChcExpr::var(ChcVar::new("bignum_hi", ChcSort::BitVec(20_000)));
        vec![ChcExpr::bv_ule(wide.clone(), other.clone()), ChcExpr::bv_ule(other, wide)]
    }

    /// `shift ≥ 32 ∧ shift < 32` plus surrounding range facts: two conjuncts
    /// contradict and the rest share the same variable, so they stay in one
    /// connected component.
    fn shift_contradiction() -> Vec<ChcExpr> {
        let shift = || ChcExpr::var(ChcVar::new("shift", ChcSort::Int));
        vec![
            ChcExpr::ge(shift(), ChcExpr::int(0)),
            ChcExpr::le(ChcExpr::int(0), shift()),
            ChcExpr::le(shift(), ChcExpr::int(4_294_967_295_i64)),
            ChcExpr::ge(shift(), ChcExpr::int(32)),
            ChcExpr::lt(shift(), ChcExpr::int(32)),
        ]
    }

    /// Satisfiable filler over pairwise-disjoint variables, matching the
    /// discriminant-range facts that dominate real fused bodies.
    fn discriminant_range_filler(count: usize) -> Vec<ChcExpr> {
        (0..count)
            .map(|i| {
                let v = ChcExpr::var(ChcVar::new(format!("__trust_mir__discr__{i}"), ChcSort::Int));
                ChcExpr::or_vec(vec![
                    ChcExpr::eq(ChcExpr::int(0), v.clone()),
                    ChcExpr::eq(ChcExpr::int(1), v),
                ])
            })
            .collect()
    }

    #[test]
    fn bitblast_refused_body_with_disjoint_contradiction_decides_unsat() {
        let mut constraints = arbitrary_precision_bv_noise();
        constraints.extend(discriminant_range_filler(6));
        constraints.extend(shift_contradiction());

        // Precondition: the fused query really is undecidable without slicing.
        let mut smt = SmtContext::new();
        let fused = ChcExpr::and_all(constraints.iter().cloned());
        smt.reset();
        let fused_result = smt.check_sat_with_timeout(&fused, SMT_QUERY_TIMEOUT);
        assert_eq!(
            classify_smt_result(&fused_result),
            SolveOutcomeTag::Undecided,
            "test precondition broke: fused body is no longer undecidable ({fused_result:?})"
        );

        let mut smt = SmtContext::new();
        assert!(
            matches!(solve_constraints(&mut smt, &constraints), SolveOutcome::Unsat),
            "slicing must prove the fused body UNSAT from its disjoint contradiction"
        );
    }

    #[test]
    fn bitblast_refused_unreachable_error_decides_safe() {
        let mut constraints = arbitrary_precision_bv_noise();
        constraints.extend(discriminant_range_filler(6));
        constraints.extend(shift_contradiction());
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and_all(constraints)),
            ClauseHead::False,
        ));
        match acyclic_direct_smt_decision(&problem) {
            AcyclicDecision::Safe => {}
            AcyclicDecision::Unsafe(_) => panic!("UNSOUND: an UNSAT error body was refuted"),
            AcyclicDecision::Inconclusive => {
                panic!("slicing must decide the disjoint contradiction")
            }
        }
    }

    /// Every subset of a satisfiable conjunction is satisfiable. This goes red if
    /// slicing rewrites a conjunct or consumes anything except definitive UNSAT.
    #[test]
    fn slicing_never_prunes_a_satisfiable_body() {
        let mut constraints = discriminant_range_filler(12);
        let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
        let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
        constraints.push(ChcExpr::lt(a.clone(), b.clone()));
        constraints.push(ChcExpr::ge(a.clone(), ChcExpr::int(0)));
        constraints.push(ChcExpr::le(b, ChcExpr::int(100)));
        constraints.push(ChcExpr::le(a, ChcExpr::int(50)));

        let mut smt = SmtContext::new();
        assert!(
            !slicing_proves_unsat(&mut smt, &constraints),
            "FALSE PROOF: slicing claimed UNSAT on a satisfiable body"
        );
        let mut smt = SmtContext::new();
        assert!(
            matches!(solve_constraints(&mut smt, &constraints), SolveOutcome::Sat(_)),
            "the satisfiable body must still produce its SAT model"
        );
    }

    #[test]
    fn slicing_cannot_divert_a_real_counterexample() {
        let mut constraints = discriminant_range_filler(10);
        let d = ChcExpr::var(ChcVar::new("_4", ChcSort::Int));
        constraints.push(ChcExpr::eq(d.clone(), ChcExpr::int(0)));
        constraints.push(ChcExpr::lt(d, ChcExpr::int(7)));
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and_all(constraints)),
            ClauseHead::False,
        ));
        assert!(
            matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Unsafe(_)),
            "a satisfiable error body must still refute with a witness"
        );
    }

    #[test]
    fn non_conjunctive_top_level_is_never_sliced() {
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let mut arms = vec![ChcExpr::and_vec(vec![
            ChcExpr::ge(x.clone(), ChcExpr::int(32)),
            ChcExpr::lt(x, ChcExpr::int(32)),
        ])];
        arms.extend((0..12).map(|i| {
            ChcExpr::ge(ChcExpr::var(ChcVar::new(format!("y{i}"), ChcSort::Int)), ChcExpr::int(0))
        }));
        let constraints = vec![ChcExpr::or_vec(arms)];
        assert!(
            relevance_slicing::relevance_slices(&relevance_slicing::flat_conjuncts(&constraints))
                .is_empty(),
            "an Or-headed body must not be sliced"
        );
        let mut smt = SmtContext::new();
        assert!(
            !slicing_proves_unsat(&mut smt, &constraints),
            "FALSE PROOF: slicing entered a disjunction"
        );
    }

    /// Pin exact top-level conjunction flattening and prove every materialized
    /// slice is a sub-multiset of the independently re-derived body conjuncts.
    #[test]
    fn every_probed_slice_is_a_submultiset_of_the_body_conjuncts() {
        use std::collections::BTreeMap;

        let mut constraints = arbitrary_precision_bv_noise();
        constraints.extend(discriminant_range_filler(20));
        constraints.extend(shift_contradiction());

        let conjuncts = relevance_slicing::flat_conjuncts(&constraints);
        assert_eq!(
            ChcExpr::and_all(conjuncts.iter().cloned()),
            ChcExpr::and_all(constraints.iter().cloned()),
            "flattening must preserve the conjunction exactly"
        );

        let folded = ChcExpr::and_all(constraints.iter().cloned());
        let mut available: BTreeMap<ChcExpr, usize> = BTreeMap::new();
        for conjunct in folded.conjuncts() {
            *available.entry(conjunct.clone()).or_default() += 1;
        }

        let slices = relevance_slicing::relevance_slices(&conjuncts);
        assert!(!slices.is_empty(), "this body must slice, or the test proves nothing");
        for slice in slices {
            let subset: Vec<ChcExpr> =
                slice.iter().map(|&index| conjuncts[index].clone()).collect();
            let mut used: BTreeMap<ChcExpr, usize> = BTreeMap::new();
            for element in &subset {
                *used.entry(element.clone()).or_default() += 1;
            }
            for (element, count) in &used {
                let have = available.get(element).copied().unwrap_or(0);
                assert!(*count <= have, "slice duplicated an unavailable conjunct");
                assert!(available.contains_key(element), "slice rewrote a conjunct: {element:?}");
            }
        }
    }
}

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

mod freed_var_replay;
mod havoc_reads;
mod havoc_taint;
mod relevance_slicing;
mod wide_nonlinear_abstraction;

pub use self::freed_var_replay::replay_error_derivation_free_of;
pub use self::havoc_reads::{HavocCertificate, certify_error_free_of_havoc};

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_chc::{
    CancellationToken, ChcExpr, ChcProblem, ClauseHead, HornClause, PredicateId, SmtContext,
    SmtResult, SmtValue,
};

use self::wide_nonlinear_abstraction::abstract_wide_nonlinear;

/// Budget for any single decidable SMT query in this CEX-search shortcut: one
/// wall-clock slice, re-run when the scheduler rather than the solver spent it
/// ([`check_sat_on_budget`]). A real counterexample is a *satisfiable* (SAT)
/// derivation, which the native theory loop finds quickly; the branches with NO
/// counterexample (UNSAT) over bit-blasted BV divide/remainder are exactly
/// where the native loop restart-thrashes to its deadline, so a generous bound
/// there is pure wasted wall-clock — summed over a fact-saturation's many such
/// branches it dominates the whole verification (a provably-dead
/// `match n % 3 { .., _ => unreachable!() }` spent ~70s here before its PDR/BMC
/// safety proof even started). Keep it tight: SAT counterexamples still return
/// well within 1s, and an undecided branch falls through to the full PDR/BMC
/// solve (which proves it), so tightening only trims waste — it never
/// fabricates a proof or drops a counterexample (gate stays GREEN).
///
/// The owner's ruling of 2026-10-01 (with design step 8e, `docs/DECISION_QUEUE.md`)
/// replaces this wall clock with ONE deterministic solver-effort bound
/// proportional to the query's size. That is not done: the pinned ay's
/// `SmtContext` bounds a check by wall clock only, and on the queries the ruling
/// targets what binds at that pin is ay-chc's fixed size ceilings, not this
/// budget (`docs/ay-asks/2026-10-01-large-query-size-ceilings-and-deterministic-effort`).
/// Metering the budget on the thread's CPU clock ([`check_sat_on_budget`])
/// takes the machine's load out of it; it is not that deterministic bound.
const SMT_QUERY_TIMEOUT: Duration = Duration::from_secs(1);

/// Per-query budget for the acyclic direct-SMT decision. Defaults to
/// [`SMT_QUERY_TIMEOUT`]; the env `TRUST_SMT_QUERY_TIMEOUT_MS` (milliseconds) raises
/// it. DIAGNOSTIC-ONLY lever to confirm a `Truncated`/`Inconclusive` wall is
/// bit-blast-BUDGET-bound (raising it → `Safe`) vs a genuine missing-fact wall
/// (still not `Safe`). SOUND either way: a larger budget only lets the *same*
/// exhaustive acyclic search finish; it never fabricates a proof (the caller still
/// consumes only a definitive UNSAT / `ExhaustivelyNone`). Not the durable lever —
/// raising it in production is load-sensitive and can blow the seal replay watchdog.
fn smt_query_timeout() -> Duration {
    match std::env::var("TRUST_SMT_QUERY_TIMEOUT_MS").ok().and_then(|s| s.parse::<u64>().ok()) {
        Some(ms) => Duration::from_millis(ms),
        None => SMT_QUERY_TIMEOUT,
    }
}

/// Total budget the relevance-slicing pre-phase may spend before it gives up
/// and lets the caller run the full body query unchanged, metered as
/// [`phase_budget_spent`] meters it. Bounds the ADDED cost of slicing on bodies
/// it cannot decide; the phase is a pure optimisation, so abandoning it is
/// always allowed.
fn slice_phase_budget() -> Duration {
    smt_query_timeout()
}

/// Per-slice budget. Slices are, by construction, much smaller than the body; if
/// one needs more than a fraction of the full-body budget it is not the cheap win
/// this phase exists to harvest, so we move on rather than starve the phase.
fn slice_probe_timeout() -> Duration {
    let full = smt_query_timeout();
    (full / 4).max(Duration::from_millis(20)).min(full)
}

/// Kill switch for the relevance-slicing pre-phase (any non-empty value disables
/// it). Measurement lever only: with slicing off the lane behaves exactly as it
/// did before the phase existed, because the phase can only convert an
/// `Undecided` into a definitively-justified `Unsat`.
fn slicing_disabled() -> bool {
    std::env::var_os("TRUST_SMT_SLICE_DISABLE").is_some_and(|v| !v.is_empty())
}

/// Most attempts [`check_sat_on_budget`] makes at one query: the first, and up
/// to two re-runs of an attempt the scheduler robbed of its budget.
const MAX_BUDGET_ATTEMPTS: u32 = 3;

/// How far a re-run's wall slice, or a phase's wall backstop, may stretch past
/// its budget, as a multiple of it: enough wall to deliver the budget's CPU at
/// one eighth of a core.
const MAX_BUDGET_STRETCH: u32 = 8;

/// One budgeted satisfiability check, metered on the work the solver did, not on
/// the wall clock alone.
///
/// WHAT WENT WRONG WITH THE WALL ALONE. Every budget in this module was a
/// wall-clock slice, and a wall-clock slice is also spent by every interval in
/// which the scheduler ran another thread. The queries the composer decides
/// cost tens to hundreds of milliseconds of CPU, well inside [`SMT_QUERY_TIMEOUT`]
/// (measured on the pinned ay at a load of about 85 on an 18-core host: the
/// three-conjunct array query of the TMC-1 `struct_elem#2` program took 235-250
/// ms of CPU in 630-880 ms of wall; the queries of the in-degree-256 wide join,
/// 50-100 ms). At a load of 110-140 a thread gets a sixth of a core or less, and
/// the same query ran its second of wall out undecided, where it had been
/// decided minutes earlier. Whether a function was proved through ChcValidity,
/// or refuted with a replayable witness, then depended on the machine's load,
/// not on the problem: `chc_large_block_verdict_parity`'s
/// `wide_joins_keep_their_verdicts` and the shared-solve differential failed on
/// it, at random.
///
/// THE FIX is ay's own for its prelude probes (`probe_arm`, ay-milp
/// `session.rs`): keep the wall slice per attempt, which is what bounds the
/// solver, and read the thread's CPU clock (`ay_sys::thread_cpu_time`) around
/// it. An undecided attempt that ran its wall slice out having computed for
/// less than HALF the budget did not exhaust the budget; it was robbed of it,
/// and is re-run from scratch in a slice stretched to deliver the budget's CPU
/// at the share of a core the robbed attempt measured
/// ([`robbed_attempt_retry_slice`]). An attempt that decided, that declined
/// before its slice ran out (a structural `Unknown`), or that computed through
/// at least half the budget is final, so on an idle machine this is the single
/// check it always was. A re-run only lets the same search finish: it never
/// fabricates a proof, and the caller still consumes only a definitive `Unsat`
/// or a model it replays.
///
/// BOUNDS. At most [`MAX_BUDGET_ATTEMPTS`] attempts, each at most
/// [`MAX_BUDGET_STRETCH`] times the budget of wall; a re-run is paid for only on
/// a machine that is already starving the solver, and the native lane's
/// watchdog bounds the whole decision regardless. Without a per-thread CPU
/// clock nothing is ever robbed: the single wall-clock check, as before.
fn check_sat_on_budget(smt: &mut SmtContext, formula: &ChcExpr, budget: Duration) -> SmtResult {
    let mut slice = budget;
    let mut attempt = 1;
    loop {
        smt.reset();
        let cpu_started = ay_sys::thread_cpu_time();
        let started = Instant::now();
        let result = smt.check_sat_with_timeout(formula, slice);
        if attempt >= MAX_BUDGET_ATTEMPTS
            || classify_smt_result(&result) != SolveOutcomeTag::Undecided
        {
            return result;
        }
        let cpu =
            cpu_started.zip(ay_sys::thread_cpu_time()).map(|(from, to)| to.saturating_sub(from));
        match robbed_attempt_retry_slice(budget, slice, started.elapsed(), cpu) {
            Some(next) => {
                slice = next;
                attempt += 1;
            }
            None => return result,
        }
    }
}

/// The wall slice to re-run an undecided attempt in, or `None` when the attempt
/// is final ([`check_sat_on_budget`]). The attempt was given `slice` of wall,
/// ran `wall` of it, and computed for `cpu` on its thread (`None` without a
/// per-thread CPU clock). It was robbed when its slice ran out with less than
/// half the `budget` computed; the re-run gets the wall that delivers the whole
/// budget at the robbed attempt's share of a core, between the budget and
/// [`MAX_BUDGET_STRETCH`] times it.
fn robbed_attempt_retry_slice(
    budget: Duration,
    slice: Duration,
    wall: Duration,
    cpu: Option<Duration>,
) -> Option<Duration> {
    let cpu = cpu?;
    if wall < slice || cpu >= budget / 2 {
        return None;
    }
    let ceiling = budget.checked_mul(MAX_BUDGET_STRETCH).unwrap_or(Duration::MAX);
    if cpu.is_zero() {
        return Some(ceiling);
    }
    let stretched =
        Duration::try_from_secs_f64(budget.as_secs_f64() * wall.as_secs_f64() / cpu.as_secs_f64())
            .unwrap_or(ceiling);
    Some(stretched.clamp(budget, ceiling))
}

/// Whether a phase that started at `started` on the wall and at `cpu_started` on
/// its thread's CPU clock has spent `budget`: the CPU it computed for, as
/// [`check_sat_on_budget`] meters a check, with [`MAX_BUDGET_STRETCH`] times the
/// budget of wall as the backstop; the wall alone, as before, without a
/// per-thread CPU clock.
fn phase_budget_spent(budget: Duration, started: Instant, cpu_started: Option<Duration>) -> bool {
    let wall = started.elapsed();
    match cpu_started.zip(ay_sys::thread_cpu_time()) {
        Some((from, to)) => {
            to.saturating_sub(from) >= budget
                || wall >= budget.checked_mul(MAX_BUDGET_STRETCH).unwrap_or(Duration::MAX)
        }
        None => wall >= budget,
    }
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
    acyclic_direct_smt_decision_with_cancellation(problem, &CancellationToken::new())
}

/// [`acyclic_direct_smt_decision`] under a native watchdog's token (decision
/// NATIVE-SOLVE-CANCEL, `native::solve_watchdog`). The search polls `cancel`
/// on entry, before each clause body and before returning a decision. Once it
/// observes cancellation the search stops
/// as `Inconclusive`, the deferral it gives when it hits a cap, never `Safe`.
/// An SMT check already running is not interrupted (ay offers no public
/// interrupt for an `SmtContext`); its own budget bounds it, so a cancelled
/// search does at most one body's checks more.
pub(crate) fn acyclic_direct_smt_decision_with_cancellation(
    problem: &ChcProblem,
    cancel: &CancellationToken,
) -> AcyclicDecision {
    if cancel.is_cancelled() {
        return AcyclicDecision::Inconclusive;
    }
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
    let outcome = acyclic_error_derivation(problem, cancel);
    // A final body may finish after cancellation without another loop poll.
    // Observe the token before publishing any decisive search result.
    if cancel.is_cancelled() {
        return AcyclicDecision::Inconclusive;
    }
    match outcome {
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
/// satisfiable acyclic derivation was found. A cancelled `cancel` ends the
/// search as `Truncated`.
fn acyclic_error_derivation(problem: &ChcProblem, cancel: &CancellationToken) -> DerivationOutcome {
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
    // The clause bodies already decided, each named by its clause and the
    // index of the fact it took for each body predicate (`FactCombinationIter`).
    // A predicate's facts are only ever appended, so the name is stable, and a
    // later round of the fixpoint would ask the solver the same closed question
    // again: a satisfiable body re-derives a fact already recorded (a
    // satisfiable `error` body has already returned its witness), an
    // unsatisfiable one prunes nothing new, and an undecided one has already
    // marked the search truncated. Asking again spent the per-query budget a
    // second time on every undecided body; on a large-block query (design step
    // 8e, one clause for a whole function) the round that only confirms the
    // fixpoint doubled the decision's wall time. A body still counts against
    // the combination cap in every round, so what the search explores, and
    // where it truncates, is unchanged.
    let mut decided: HashSet<(usize, Vec<usize>)> = HashSet::new();

    for _ in 0..=problem.predicates().len().saturating_add(problem.clauses().len()) {
        let mut changed = false;

        for (clause_index, clause) in clauses.iter().enumerate() {
            let Some(body_fact_options) = body_fact_options(clause, &facts) else {
                continue;
            };

            let mut checked = 0usize;
            for (fact_indices, combo) in FactCombinationIter::new(body_fact_options) {
                // The watchdog that owns this search has given up on it: stop
                // before another body's checks. `Truncated` claims nothing.
                if cancel.is_cancelled() {
                    return DerivationOutcome::Truncated;
                }
                checked += 1;
                if checked > MAX_COMBINATIONS_PER_CLAUSE {
                    truncated = true;
                    break;
                }
                if !decided.insert((clause_index, fact_indices)) {
                    continue;
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
                        // The witness tail asks the solver again (the havoc
                        // preference's retries) and replays: a cancelled search
                        // stops here as well, before or between those checks.
                        let Some(model) = prefer_havoc_free_model(
                            problem,
                            &mut smt,
                            &derivation_clause_indices,
                            &constraints,
                            model,
                            cancel,
                        ) else {
                            return DerivationOutcome::Truncated;
                        };
                        if cancel.is_cancelled() {
                            return DerivationOutcome::Truncated;
                        }
                        let model = replayable_model(
                            problem,
                            &derivation_clause_indices,
                            &constraints,
                            model,
                        );
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

/// `model` of the derivation `derivation` (whose renamed constraints are
/// `constraints`), or — when `model` reads a TRANSLATION HAVOC through a choice
/// the solver made and the derivation has a model that reads none — that other
/// model.
///
/// A witness whose derivation reads a havoc is refused by the consumer's
/// replay (`native::bounded_unroll::derivation_reads_translation_havoc`), which
/// does not read a havoc under a top-level `(=> g φ)` whose plain Boolean
/// antecedent the model sets false, nor in the unselected branch of an `ite`
/// whose plain Boolean condition the model fixes. A large-block query (design
/// step 8e) is one clause for the whole function, so its first model may take a
/// path through a block or an in-edge whose terms read a havoc while another
/// path to `error` reads none — where the per-block encoding's fact order
/// happened to find that other path first. Ask once more with the Boolean
/// condition that the consumer's existing structural read rule reads no havoc.
/// Nested choices remain alternatives: disabling an outer reachability guard
/// is not required when changing an inner ITE avoids the read.
///
/// This is ONLY a witness search restriction. UNSAT/undecided on the restricted
/// query returns the original model, never a safety verdict for the original
/// query. The unchanged consumer independently replays and gates the witness
/// against the unrestricted original problem.
///
/// `None` when `cancel` is cancelled before that retry (decision
/// NATIVE-SOLVE-CANCEL): the retry is an SMT check, and a search its watchdog
/// has given up on asks the solver nothing more.
fn prefer_havoc_free_model(
    problem: &ChcProblem,
    smt: &mut SmtContext,
    derivation: &[u64],
    constraints: &[ChcExpr],
    model: serde_json::Value,
    cancel: &CancellationToken,
) -> Option<serde_json::Value> {
    if crate::native::bounded_unroll::derivation_reads_translation_havoc(
        problem, derivation, &model,
    ) == Some(false)
    {
        return Some(model);
    }
    let Some(guard) = havoc_avoiding_guard(problem, derivation) else {
        return Some(model);
    };
    if cancel.is_cancelled() {
        return None;
    }
    let mut retry = constraints.to_vec();
    retry.push(guard);
    match solve_constraints(smt, &retry) {
        SolveOutcome::Sat(next) => Some(next),
        SolveOutcome::Unsat | SolveOutcome::Undecided => Some(model),
    }
}

/// A search-only condition in the same alpha-renamed namespace. Its accepted
/// branch cases exactly match HavocReads; unknown shapes/argument havocs decline.
fn havoc_avoiding_guard(problem: &ChcProblem, derivation: &[u64]) -> Option<ChcExpr> {
    use trust_mc_core::chc::is_translation_havoc_var;
    let names = alpha_renamed_variable_names(problem)?;
    let mut guards = Vec::new();
    for &clause_index in derivation {
        let clause_index = usize::try_from(clause_index).ok()?;
        let clause = problem.clauses().get(clause_index)?;
        let names = names.get(clause_index)?;
        let head = match &clause.head {
            ClauseHead::Predicate(_, arguments) => arguments.as_slice(),
            _ => &[],
        };
        for argument in clause.body.predicates.iter().flat_map(|(_, args)| args).chain(head) {
            // alpha_renamed_variable_names has already checked that every
            // expression fits the pinned collector/substitution limits.
            if argument.vars().iter().any(|var| is_translation_havoc_var(&var.name)) {
                return None;
            }
        }
        let mut memo = HashMap::new();
        let mut pending: Vec<_> = clause.body.constraint.iter().collect();
        let mut seen = HashSet::new();
        while let Some(conjunct) = pending.pop() {
            if !seen.insert(std::ptr::from_ref(conjunct)) {
                continue;
            }
            if let ChcExpr::Op(ay_chc::ChcOp::And, arguments) = conjunct {
                pending.extend(arguments.iter().map(AsRef::as_ref));
                continue;
            }
            let guard = if let ChcExpr::Op(ay_chc::ChcOp::Implies, arguments) = conjunct
                && let [condition, body] = arguments.as_slice()
                && let Some(condition) = renamed_choice(condition, names)
            {
                ChcExpr::implies(condition, avoiding_node(body, names, &mut memo)?)
            } else {
                avoiding_node(conjunct, names, &mut memo)?
            };
            guards.push(guard);
        }
    }
    Some(ChcExpr::and_vec(guards))
}

fn renamed_choice(
    expression: &ChcExpr,
    names: &BTreeMap<ay_chc::ChcVar, String>,
) -> Option<ChcExpr> {
    let ChcExpr::Var(variable) = expression else { return None };
    if variable.sort != ay_chc::ChcSort::Bool
        || trust_mc_core::chc::is_translation_havoc_var(&variable.name)
    {
        return None;
    }
    Some(ChcExpr::var(ay_chc::ChcVar::new(names.get(variable)?.clone(), variable.sort.clone())))
}

fn avoiding_node(
    root: &ChcExpr,
    names: &BTreeMap<ay_chc::ChcVar, String>,
    memo: &mut HashMap<*const ChcExpr, ChcExpr>,
) -> Option<ChcExpr> {
    let mut pending = vec![(root, false)];
    while let Some((node, expanded)) = pending.pop() {
        let key = std::ptr::from_ref(node);
        if memo.contains_key(&key) {
            continue;
        }
        let children: Vec<_> = match node {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args.iter().map(AsRef::as_ref).collect(),
            ChcExpr::ConstArray(_, value) => vec![value.as_ref()],
            ChcExpr::Var(_)
            | ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => vec![],
            _ => return None,
        };
        if !expanded {
            pending.push((node, true));
            pending.extend(children.iter().map(|child| (*child, false)));
            continue;
        }
        let guard = match node {
            ChcExpr::Var(variable) => {
                ChcExpr::Bool(!trust_mc_core::chc::is_translation_havoc_var(&variable.name))
            }
            ChcExpr::Op(ay_chc::ChcOp::Ite, arguments)
                if arguments.len() == 3 && renamed_choice(&arguments[0], names).is_some() =>
            {
                ChcExpr::ite(
                    renamed_choice(&arguments[0], names)?,
                    memo.get(&std::ptr::from_ref(arguments[1].as_ref()))?.clone(),
                    memo.get(&std::ptr::from_ref(arguments[2].as_ref()))?.clone(),
                )
            }
            _ => ChcExpr::and_vec(
                children
                    .iter()
                    .map(|child| memo.get(&std::ptr::from_ref(*child)).cloned())
                    .collect::<Option<Vec<_>>>()?,
            ),
        };
        memo.insert(key, guard);
    }
    memo.get(&std::ptr::from_ref(root)).cloned()
}

/// `model`, the composer's model of the derivation `derivation` (whose renamed
/// constraints are `constraints`), in a form the consumer's replay reads — or
/// `model` itself when that form does not replay either.
///
/// The consumer replays a witness only from an exact, TOTAL model: one binding
/// for every variable of the derivation it rebuilds from its own clauses, each
/// in a form it parses (`replay_acyclic_direct_smt_witness`). A solver's model
/// need not be one. It may leave out a variable it eliminated through an
/// equality — the composer equates every clause's body arguments with the
/// previous clause's head arguments, so a fact's head variables are such — and
/// it may bind an array to a finite map (`array_map`), which the replay does not
/// parse. A large-block query (design step 8e) is one clause for a whole
/// function, so its model also binds the arrays of blocks the path never
/// reaches (measured: the large-block witness of a real `splat_index_param` dump
/// omitted the fact's index variable and bound an unread array to a map, and was
/// refused where the per-block witness, whose path names neither, was admitted).
///
/// So a variable the model leaves out takes the value of a variable a top-level
/// conjunct `x = y` equates it with, else the zero of its sort; a finite-map
/// array binding becomes the constant array of its default; and bindings of
/// names outside the derivation are dropped. The result is used only when the
/// consumer's own replay admits it, so nothing here is trusted: it changes which
/// witness is minted, never what a minted witness means. Near-linear in the
/// derivation (a union-find with path compression), plus at most two replays.
fn replayable_model(
    problem: &ChcProblem,
    derivation: &[u64],
    constraints: &[ChcExpr],
    model: serde_json::Value,
) -> serde_json::Value {
    let replays = |model: &serde_json::Value| {
        replay_acyclic_direct_smt_witness(
            problem,
            &AcyclicUnsafeWitness {
                model: model.clone(),
                derivation_clause_indices: derivation.to_vec(),
            },
        )
        .is_ok()
    };
    if replays(&model) {
        return model;
    }
    let Some(bindings) = model.as_object() else {
        return model;
    };
    let mut sorts: BTreeMap<String, ay_chc::ChcSort> = BTreeMap::new();
    for constraint in constraints {
        for variable in constraint.vars() {
            sorts.entry(variable.name).or_insert(variable.sort);
        }
    }

    // Classes of variables equated by a top-level conjunct `x = y` of one sort.
    let mut classes = ModelEqualityClasses::default();
    for conjunct in relevance_slicing::flat_conjuncts(constraints) {
        if let ChcExpr::Op(ay_chc::ChcOp::Eq, args) = &conjunct
            && let [lhs, rhs] = args.as_slice()
            && let (ChcExpr::Var(lhs), ChcExpr::Var(rhs)) = (lhs.as_ref(), rhs.as_ref())
            && lhs.sort == rhs.sort
        {
            classes.union(&lhs.name, &rhs.name);
        }
    }

    let mut completed = serde_json::Map::new();
    for (name, value) in bindings {
        if sorts.contains_key(name) {
            completed.insert(name.clone(), constant_array_of_map(value));
        }
    }
    let mut class_values: HashMap<String, serde_json::Value> = HashMap::new();
    for (name, value) in &completed {
        class_values.entry(classes.find(name)).or_insert_with(|| value.clone());
    }
    for (name, sort) in &sorts {
        if completed.contains_key(name) {
            continue;
        }
        let value = match class_values.get(&classes.find(name)) {
            Some(value) => value.clone(),
            None => match zero_model_value(sort) {
                Some(value) => value,
                None => return model,
            },
        };
        completed.insert(name.clone(), value);
    }
    let candidate = serde_json::Value::Object(completed);
    if replays(&candidate) { candidate } else { model }
}

/// Union-find over variable names, for `replayable_model`.
#[derive(Default)]
struct ModelEqualityClasses {
    parent: HashMap<String, String>,
}

impl ModelEqualityClasses {
    fn find(&mut self, name: &str) -> String {
        let mut root = name.to_owned();
        while let Some(parent) = self.parent.get(&root) {
            if *parent == root {
                break;
            }
            root = parent.clone();
        }
        // Path compression: every name on the walk now points at the root.
        let mut current = name.to_owned();
        while current != root {
            let next = self.parent.get(&current).cloned().unwrap_or_else(|| root.clone());
            self.parent.insert(current, root.clone());
            current = next;
        }
        root
    }

    fn union(&mut self, lhs: &str, rhs: &str) {
        let (lhs, rhs) = (self.find(lhs), self.find(rhs));
        if lhs != rhs {
            self.parent.insert(lhs, rhs);
        }
    }
}

/// A finite-map array binding (`array_map`) as the constant array of its
/// default; every other binding unchanged.
fn constant_array_of_map(value: &serde_json::Value) -> serde_json::Value {
    match value.get("kind").and_then(serde_json::Value::as_str) {
        Some("array_map") => match value.get("default") {
            Some(default) => serde_json::json!({
                "kind": "const_array",
                "default": constant_array_of_map(default),
            }),
            None => value.clone(),
        },
        Some("const_array") => match value.get("default") {
            Some(default) => serde_json::json!({
                "kind": "const_array",
                "default": constant_array_of_map(default),
            }),
            None => value.clone(),
        },
        _ => value.clone(),
    }
}

/// The zero of `sort` in the witness model's typed JSON (`smt_value_to_json`'s
/// shapes), for the sorts the replay parses; `None` for any other sort.
fn zero_model_value(sort: &ay_chc::ChcSort) -> Option<serde_json::Value> {
    match sort {
        ay_chc::ChcSort::Bool => Some(serde_json::json!({ "kind": "bool", "value": false })),
        ay_chc::ChcSort::Int => Some(serde_json::json!({ "kind": "int", "value": 0 })),
        ay_chc::ChcSort::BitVec(width) if *width > 0 => {
            let hex_digits = (*width as usize).div_ceil(4);
            Some(serde_json::json!({
                "kind": "bit_vec",
                "width": width,
                "value": "0",
                "hex": format!("0x{:0hex_digits$x}", 0),
            }))
        }
        ay_chc::ChcSort::Array(_, value_sort) => Some(serde_json::json!({
            "kind": "const_array",
            "default": zero_model_value(value_sort)?,
        })),
        _ => None,
    }
}

/// The choices through which `model` makes the derivation read a havoc, as
/// (renamed Bool variable, the value that avoids the read): empty when it reads
/// none; `None` when a read is under no choice (an argument, or a bare havoc).
#[cfg(test)]
fn havoc_reading_choices(
    problem: &ChcProblem,
    names: &[BTreeMap<ay_chc::ChcVar, String>],
    derivation: &[u64],
    model: &serde_json::Value,
) -> Option<Vec<(String, bool)>> {
    use trust_mc_core::chc::is_translation_havoc_var;
    let bindings = model.as_object()?;
    let mut choices = Vec::new();
    let mut flattened: HashSet<*const ChcExpr> = HashSet::new();
    for index in derivation {
        let index = usize::try_from(*index).ok()?;
        let clause = problem.clauses().get(index)?;
        let names = names.get(index)?;
        let head_args = match &clause.head {
            ClauseHead::Predicate(_, args) => args.as_slice(),
            _ => &[],
        };
        if clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args)
            .chain(head_args)
            .any(|expr| expr.vars().iter().any(|var| is_translation_havoc_var(&var.name)))
        {
            return None;
        }
        let mut reads = HavocReads::new(names, bindings);
        let mut pending: Vec<&ChcExpr> = clause.body.constraint.iter().collect();
        while let Some(expr) = pending.pop() {
            if let ChcExpr::Op(ay_chc::ChcOp::And, args) = expr {
                if flattened.insert(std::ptr::from_ref(expr)) {
                    pending.extend(args.iter().map(AsRef::as_ref));
                }
                continue;
            }
            choices.extend(reads.steering(expr)?);
        }
    }
    Some(choices)
}

/// Which conjuncts of one derivation READ a TRANSLATION HAVOC under the witness
/// model `model`, whose bindings `names` renames the derivation's variables
/// into (`alpha_renamed_variable_names`).
///
/// Two places a havoc occurs are NOT read, because the conjunct's truth value
/// cannot depend on it while every non-havoc variable keeps its model value:
///
/// * anywhere under a top-level `(=> g φ)` whose antecedent `g` is a non-havoc
///   Bool variable the model binds to exactly `false` — the implication holds
///   whatever `φ` is;
/// * in the unselected branch of `(ite g t e)` whose condition `g` is a
///   non-havoc Bool variable the model binds to exactly a Bool — the ite's value
///   is the selected branch's.
///
/// Every other occurrence is read. The large-block encoding (design step 8e)
/// puts each block's formulas under the block's own Booleans and selects a
/// block's inputs with `ite`s over its in-edge selectors, so under a model the
/// havocs read are exactly those of the blocks and edges the model's path takes.
///
/// Whether a node reads a havoc is a function of the node and the model alone
/// (which branch an `ite` selects never depends on where the node is reached
/// from), so it is memoized per shared node across every conjunct asked: the
/// whole derivation costs one walk of its distinct nodes.
pub(crate) struct HavocReads<'a> {
    names: &'a BTreeMap<ay_chc::ChcVar, String>,
    model: &'a serde_json::Map<String, serde_json::Value>,
    reads: HashMap<*const ChcExpr, bool>,
}

impl<'a> HavocReads<'a> {
    pub(crate) fn new(
        names: &'a BTreeMap<ay_chc::ChcVar, String>,
        model: &'a serde_json::Map<String, serde_json::Value>,
    ) -> Self {
        Self { names, model, reads: HashMap::new() }
    }

    /// The model's exact Bool value of a non-havoc Bool variable, if it binds one.
    fn fixed_bool(&self, expr: &ChcExpr) -> Option<bool> {
        use trust_mc_core::chc::is_translation_havoc_var;
        let ChcExpr::Var(var) = expr else { return None };
        if var.sort != ay_chc::ChcSort::Bool || is_translation_havoc_var(&var.name) {
            return None;
        }
        let binding = self.model.get(self.names.get(var)?)?.as_object()?;
        if binding.len() != 2 || binding.get("kind")?.as_str()? != "bool" {
            return None;
        }
        binding.get("value")?.as_bool()
    }

    /// Whether `conjunct`, a top-level conjunct of a derivation clause, reads a
    /// havoc under the model. `None` for an expression shape this walk does not
    /// know (the caller fails closed).
    pub(crate) fn conjunct(&mut self, conjunct: &ChcExpr) -> Option<bool> {
        if let ChcExpr::Op(ay_chc::ChcOp::Implies, args) = conjunct
            && let [antecedent, _] = args.as_slice()
            && self.fixed_bool(antecedent) == Some(false)
        {
            return Some(false);
        }
        self.node(conjunct)
    }

    /// The choices through which `conjunct` reads a havoc under the model, as
    /// (renamed variable, the value that avoids the read): a top-level
    /// implication's true plain-Boolean antecedent, or the plain-Boolean
    /// condition of an `ite` whose selected branch reads one. Empty when the
    /// conjunct reads none; `None` when a read is under no such choice.
    #[cfg(test)]
    pub(crate) fn steering(&mut self, conjunct: &ChcExpr) -> Option<Vec<(String, bool)>> {
        if !self.conjunct(conjunct)? {
            return Some(Vec::new());
        }
        if let ChcExpr::Op(ay_chc::ChcOp::Implies, args) = conjunct
            && let [antecedent, _] = args.as_slice()
            && self.fixed_bool(antecedent) == Some(true)
            && let ChcExpr::Var(var) = antecedent.as_ref()
        {
            return Some(vec![(self.names.get(var)?.clone(), false)]);
        }
        let mut choices = Vec::new();
        let mut seen: HashSet<*const ChcExpr> = HashSet::new();
        let mut pending = vec![conjunct];
        while let Some(node) = pending.pop() {
            if !seen.insert(std::ptr::from_ref(node)) || !self.node(node)? {
                continue;
            }
            match node {
                ChcExpr::Op(ay_chc::ChcOp::Ite, args) if args.len() == 3 => {
                    if let (Some(value), ChcExpr::Var(var)) =
                        (self.fixed_bool(&args[0]), args[0].as_ref())
                    {
                        // The condition reads no havoc, so the selected branch does.
                        choices.push((self.names.get(var)?.clone(), !value));
                    } else {
                        pending.extend(self.read_children(node)?);
                    }
                }
                ChcExpr::Var(_) => return None,
                _ => pending.extend(self.read_children(node)?),
            }
        }
        Some(choices)
    }

    /// The children of `node` the model reads.
    fn read_children<'e>(&self, node: &'e ChcExpr) -> Option<Vec<&'e ChcExpr>> {
        Some(match node {
            ChcExpr::Op(ay_chc::ChcOp::Ite, args) if args.len() == 3 => {
                match self.fixed_bool(&args[0]) {
                    Some(true) => vec![args[0].as_ref(), args[1].as_ref()],
                    Some(false) => vec![args[0].as_ref(), args[2].as_ref()],
                    None => args.iter().map(AsRef::as_ref).collect(),
                }
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args.iter().map(AsRef::as_ref).collect(),
            ChcExpr::ConstArray(_, value) => vec![value.as_ref()],
            ChcExpr::Var(_)
            | ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => Vec::new(),
            _ => return None,
        })
    }

    /// Whether `root` reads a havoc under the model; iterative, memoized.
    fn node(&mut self, root: &ChcExpr) -> Option<bool> {
        use trust_mc_core::chc::is_translation_havoc_var;
        let mut stack: Vec<(&ChcExpr, bool)> = vec![(root, false)];
        while let Some((node, expanded)) = stack.pop() {
            let key = std::ptr::from_ref(node);
            if self.reads.contains_key(&key) {
                continue;
            }
            let children = self.read_children(node)?;
            if expanded {
                let reads = match node {
                    ChcExpr::Var(var) => is_translation_havoc_var(&var.name),
                    _ => children
                        .iter()
                        .any(|child| self.reads.get(&std::ptr::from_ref(*child)) == Some(&true)),
                };
                self.reads.insert(key, reads);
            } else {
                stack.push((node, true));
                stack.extend(
                    children
                        .into_iter()
                        .filter(|child| !self.reads.contains_key(&std::ptr::from_ref(*child)))
                        .map(|child| (child, false)),
                );
            }
        }
        self.reads.get(&std::ptr::from_ref(root)).copied()
    }
}

/// Hard replay ceilings on the consumer's own fresh problem.  They are
/// deliberately independent of the producer's saturation caps.  What a hostile
/// serialized witness supplies is bounded by that problem, not by a number: its
/// trace may name each clause at most once (`trace.len() <= clauses`), and its
/// model must bind EXACTLY the variables of the derivation the consumer
/// rebuilds from its own clauses (`model.len() == variables.len()`, checked
/// before any binding is parsed). A ceiling on the trace length or on the
/// binding count would therefore refuse only large honest witnesses — under the
/// large-block encoding (design step 8e) a derivation is a whole function's
/// query — and both were deleted with it.
const MAX_REPLAY_PROBLEM_PREDICATES: usize = 65_536;
const MAX_REPLAY_PROBLEM_CLAUSES: usize = 262_144;

/// The values `witness` assigns to the head arguments of the first clause of its
/// derivation — the entry FACT, whose head arguments are the function's entry
/// inputs — in argument order, as the witness's own JSON renders them.
///
/// Test-only: it is how the TMC-1 differential (`native/array_gate_differential.rs`)
/// turns a refutation witness back into interpreter inputs. It names the witness's
/// variables exactly as `acyclic_error_derivation` and
/// `replay_acyclic_direct_smt_witness` do (`alpha_renamed_clauses`).
///
/// A solver may leave out of its model a variable it eliminated through an
/// equality, and the composer equates every clause's body arguments with the
/// previous clause's head arguments. So an entry argument the model omits is
/// FOLLOWED along the derivation — head position, the next clause's body argument
/// there, the head positions that clause passes it on at — to the first variable
/// of that chain the model assigns. `None` means no variable of the chain is
/// assigned: the derivation never pins the input, and the caller must treat it
/// as free (every value of it must reach the same violation). A derivation that
/// does not start at a fact, or a fact argument that is not a variable, is
/// refused.
#[cfg(all(test, feature = "native-trust-ir-bundle"))]
pub(crate) fn witness_entry_fact_assignment(
    problem: &ChcProblem,
    witness: &AcyclicUnsafeWitness,
) -> Result<Vec<Option<serde_json::Value>>, String> {
    let clauses = alpha_renamed_clauses(problem)
        .ok_or_else(|| "clauses exceed the exact alpha-renaming budget".to_string())?;
    let trace = witness
        .derivation_clause_indices
        .iter()
        .map(|index| {
            usize::try_from(*index)
                .ok()
                .and_then(|index| clauses.get(index))
                .ok_or_else(|| format!("derivation clause index {index} is out of range"))
        })
        .collect::<Result<Vec<&HornClause>, String>>()?;
    let first = trace.first().ok_or_else(|| "derivation trace is empty".to_string())?;
    if !first.body.predicates.is_empty() {
        return Err("derivation does not begin with a fact clause".to_string());
    }
    let ClauseHead::Predicate(_, args) = &first.head else {
        return Err("the derivation's fact clause has no predicate head".to_string());
    };
    let name = |expr: &ChcExpr| match expr {
        ChcExpr::Var(var) => Some(var.name.clone()),
        _ => None,
    };
    args.iter()
        .enumerate()
        .map(|(position, arg)| {
            let mut variable = name(arg).ok_or_else(|| {
                format!("entry fact head argument {position} is not a variable: {arg:?}")
            })?;
            let mut positions = vec![position];
            for next in trace.iter().skip(1) {
                if let Some(value) = witness.model.get(&variable) {
                    return Ok(Some(value.clone()));
                }
                let [(_, body_args)] = next.body.predicates.as_slice() else {
                    break;
                };
                let Some(passed) =
                    positions.iter().find_map(|at| body_args.get(*at).and_then(name))
                else {
                    break;
                };
                variable = passed;
                positions = match &next.head {
                    ClauseHead::Predicate(_, head_args) => head_args
                        .iter()
                        .enumerate()
                        .filter(|(_, head_arg)| {
                            name(head_arg).as_deref() == Some(variable.as_str())
                        })
                        .map(|(at, _)| at)
                        .collect(),
                    _ => Vec::new(),
                };
            }
            Ok(witness.model.get(&variable).cloned())
        })
        .collect()
}

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
    replay_acyclic_direct_smt_witness_inner(problem, witness, None)
}

/// The exact same reconstruction under a caller wall-clock ceiling. Unlike the
/// diagnostic CPU-budget policy, this never stretches/retries the caller's SMT
/// slice. A timeout changes admission to Unknown, never the checked formula.
pub(crate) fn replay_acyclic_direct_smt_witness_with_timeout(
    problem: &ChcProblem,
    witness: &AcyclicUnsafeWitness,
    timeout: Duration,
) -> Result<(), String> {
    replay_acyclic_direct_smt_witness_inner(problem, witness, Some(timeout))
}

fn replay_acyclic_direct_smt_witness_inner(
    problem: &ChcProblem,
    witness: &AcyclicUnsafeWitness,
    timeout: Option<Duration>,
) -> Result<(), String> {
    let started = Instant::now();
    if timeout.is_some_and(|limit| limit.is_zero()) {
        return Err("witness replay caller wall-clock ceiling expired".to_string());
    }
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
    if trace.len() > problem.clauses().len() {
        return Err(format!(
            "derivation trace length {} exceeds the problem's {} clauses",
            trace.len(),
            problem.clauses().len()
        ));
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

    let mut assignment = Vec::with_capacity(variables.len());
    for (name, sort) in variables {
        let encoded =
            model.get(&name).ok_or_else(|| format!("witness model is missing `{name}`"))?;
        let value = parse_model_value(&name, &sort, encoded)?;
        assignment.push((ay_chc::ChcVar::new(name, sort), value));
    }
    let constraints = derivation_under_assignment(constraints, assignment);

    let mut smt = problem.make_smt_context();
    let outcome = match timeout {
        None => solve_constraints(&mut smt, &constraints),
        Some(limit) => {
            let remaining = limit.saturating_sub(started.elapsed());
            if remaining.is_zero() {
                return Err("witness replay caller wall-clock ceiling expired".to_string());
            }
            let formula = ChcExpr::and_all(constraints.iter().cloned());
            let remaining = limit.saturating_sub(started.elapsed());
            if remaining.is_zero() {
                return Err("witness replay caller wall-clock ceiling expired".to_string());
            }
            let result = smt.check_sat_with_timeout(&formula, remaining.min(smt_query_timeout()));
            if started.elapsed() >= limit {
                return Err("witness replay caller wall-clock ceiling expired".to_string());
            }
            match classify_smt_result(&result) {
                SolveOutcomeTag::Sat => SolveOutcome::Sat(model_json(&result)),
                SolveOutcomeTag::Unsat => SolveOutcome::Unsat,
                SolveOutcomeTag::Undecided => SolveOutcome::Undecided,
            }
        }
    };
    match outcome {
        SolveOutcome::Sat(_) => Ok(()),
        SolveOutcome::Unsat => {
            Err("witness assignment does not satisfy the reconstructed derivation".to_string())
        }
        SolveOutcome::Undecided => {
            Err("witness replay was undecided within the strict SMT budget".to_string())
        }
    }
}

/// The derivation `constraints` with every variable fixed to its value in
/// `assignment`, a TOTAL assignment of the derivation's variables to constants:
/// `constraints[v := value]`, a closed formula, when the substitution is
/// complete; otherwise `constraints ∧ ⋀ v = value`. The two are satisfiable
/// exactly when the derivation holds under the assignment, so the replay's
/// verdict is the same either way.
///
/// The closed form is what a replay should ask: a large-block query (design
/// step 8e) binds a whole function's variables, and ay-chc decided the pinned
/// form far more slowly than the derivation itself — at a 1 024-way switch, a
/// model the solver found in 0.2 s took over 1 s to confirm through 6 151
/// equations, past the per-query budget, so an honest witness was refused. A
/// closed formula is folded to a constant before any search. ay-chc's
/// `substitute` is best-effort past its node budget (it can leave a variable in
/// place), so the closed form is used only when no variable is left in it.
fn derivation_under_assignment(
    constraints: Vec<ChcExpr>,
    assignment: Vec<(ay_chc::ChcVar, ChcExpr)>,
) -> Vec<ChcExpr> {
    let closed: Vec<ChcExpr> =
        constraints.iter().map(|constraint| constraint.substitute(&assignment)).collect();
    if closed.iter().all(mentions_no_variable) {
        return closed;
    }
    let mut pinned = constraints;
    pinned.extend(
        assignment.into_iter().map(|(variable, value)| ChcExpr::eq(ChcExpr::var(variable), value)),
    );
    pinned
}

/// Whether `expr` has no free variable: one walk over its distinct nodes.
fn mentions_no_variable(expr: &ChcExpr) -> bool {
    let mut seen: HashSet<*const ChcExpr> = HashSet::new();
    let mut pending: Vec<&ChcExpr> = vec![expr];
    while let Some(node) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(node)) {
            continue;
        }
        match node {
            ChcExpr::Var(_) => return false,
            ChcExpr::Op(_, args)
            | ChcExpr::FuncApp(_, _, args)
            | ChcExpr::PredicateApp(_, _, args) => {
                pending.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::ConstArray(_, value) => pending.push(value),
            _ => {}
        }
    }
    true
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
            // No 128-bit ceiling: a wider binding is read exactly through ay's
            // checked `SmtValue` constructor below, which is also what bounds
            // `width` (`InvalidBitVectorWidth` past ay's public cap) before any
            // width-sized rendering is allocated.
            if width != *expected_width || width == 0 {
                return Err(format!(
                    "model binding `{name}` has width {width}, expected {expected_width}"
                ));
            }
            let digits = object
                .get("value")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| format!("model binding `{name}` has an invalid bit-vector value"))?;
            // Inferred as ay's `BigUint` from the checked constructor it feeds:
            // the binding is parsed at full precision, never through `u128`.
            let parsed = digits
                .parse()
                .map_err(|_| format!("model binding `{name}` has an invalid bit-vector value"))?;
            let value =
                ay_chc::SmtValue::try_bitvec_from_biguint(parsed, width).map_err(|err| {
                    format!("model binding `{name}` has an unsupported bit-vector width: {err}")
                })?;
            // `try_bitvec_from_biguint` reduces modulo `2^width`, so an
            // over-wide binding would otherwise become a DIFFERENT value:
            // re-render the exact stored value and require the producer's
            // rendering to match it byte for byte.
            let (exact, exact_width) = value.bitvec_to_biguint().ok_or_else(|| {
                format!("model binding `{name}` is not an exact bit-vector value")
            })?;
            if exact_width != width || exact.to_str_radix(10) != digits {
                return Err(format!("model binding `{name}` exceeds its bit-vector width"));
            }
            let hex_digits = (width as usize).div_ceil(4);
            let expected_hex = format!("0x{exact:0hex_digits$x}");
            if object.get("hex").and_then(serde_json::Value::as_str) != Some(expected_hex.as_str())
            {
                return Err(format!("model binding `{name}` has a non-canonical hex rendering"));
            }
            // `bitvec_to_chc_expr` is ay's exact replay path: a `BitVec` leaf
            // through 128 bits, a `BvConcat` tree of <=128-bit leaves past it.
            value
                .bitvec_to_chc_expr()
                .ok_or_else(|| format!("model binding `{name}` has no exact bit-vector literal"))
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
    // `ChcExpr::vars` (behind `clause_vars`) and `ChcExpr::substitute` both have private traversal
    // limits in ay-chc. In particular, a variable below the depth limit can be
    // omitted by `vars`, remain unrenamed by the best-effort substitution, and
    // then also be omitted by a `renamed.vars()` post-check. That would restore
    // cross-clause capture and could turn a reachable path into a false UNSAT.
    // Inspect the public expression shape iteratively first, before calling
    // either budgeted operation. Anything at their boundary defers to PDR.
    if !problem.clauses().iter().all(clause_fits_alpha_substitution_limits) {
        return None;
    }

    let namespace = alpha_namespace(problem)?;

    problem
        .clauses()
        .iter()
        .enumerate()
        .map(|(clause_index, clause)| {
            let substitutions: Vec<_> = clause_vars(clause)
                .into_iter()
                .enumerate()
                .map(|(variable_index, variable)| {
                    let replacement = ChcExpr::var(ay_chc::ChcVar::new(
                        alpha_name(&namespace, clause_index, variable_index),
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

            clause_vars(&renamed)
                .iter()
                .all(|variable| variable.name.starts_with(&namespace))
                .then_some(renamed)
        })
        .collect()
}

/// The prefix `alpha_renamed_clauses` puts on every renamed variable: the first
/// `__trust_mc_direct_smt_alpha_{n}_` no variable of `problem` already starts with.
fn alpha_namespace(problem: &ChcProblem) -> Option<String> {
    let original_names: HashSet<String> =
        problem.clauses().iter().flat_map(clause_vars).map(|var| var.name).collect();
    let mut namespace_id = 0usize;
    loop {
        let candidate = format!("__trust_mc_direct_smt_alpha_{namespace_id}_");
        if original_names.iter().all(|name| !name.starts_with(&candidate)) {
            return Some(candidate);
        }
        namespace_id = namespace_id.checked_add(1)?;
    }
}

/// `HornClause::vars`, in the same order — the body's arguments, its constraint,
/// the head's arguments, each expression's own first-occurrence preorder
/// (`ChcExpr::vars`), duplicates dropped — in time linear in the clause.
/// ay-chc's `HornClause::vars` deduplicates with `Vec::contains`, quadratic in a
/// clause's distinct variables, and a large-block query (design step 8e) is a
/// whole function's clause: 20 000 variables took 0.24 s, 40 000 five times
/// that, in a debug build.
fn clause_vars(clause: &HornClause) -> Vec<ay_chc::ChcVar> {
    let mut seen: HashSet<ay_chc::ChcVar> = HashSet::new();
    let mut ordered = Vec::new();
    let mut add = |expr: &ChcExpr| {
        for var in expr.vars() {
            if seen.insert(var.clone()) {
                ordered.push(var);
            }
        }
    };
    for (_, args) in &clause.body.predicates {
        args.iter().for_each(&mut add);
    }
    if let Some(constraint) = &clause.body.constraint {
        add(constraint);
    }
    if let ClauseHead::Predicate(_, args) = &clause.head {
        args.iter().for_each(&mut add);
    }
    ordered
}

/// The renamed name of the `variable_index`-th variable (`clause_vars`
/// order) of clause `clause_index`.
fn alpha_name(namespace: &str, clause_index: usize, variable_index: usize) -> String {
    format!("{namespace}c{clause_index}_v{variable_index}")
}

/// For every clause of `problem`, the name `alpha_renamed_clauses` gives each of
/// its variables (identified by name AND sort, as the renaming does): the name a
/// witness model binds. `None` exactly when `alpha_renamed_clauses` declines.
pub(crate) fn alpha_renamed_variable_names(
    problem: &ChcProblem,
) -> Option<Vec<BTreeMap<ay_chc::ChcVar, String>>> {
    alpha_renamed_clauses(problem)?;
    let namespace = alpha_namespace(problem)?;
    Some(
        problem
            .clauses()
            .iter()
            .enumerate()
            .map(|(clause_index, clause)| {
                clause_vars(clause)
                    .into_iter()
                    .enumerate()
                    .map(|(variable_index, variable)| {
                        (variable, alpha_name(&namespace, clause_index, variable_index))
                    })
                    .collect()
            })
            .collect(),
    )
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

    let cpu_started = ay_sys::thread_cpu_time();
    let started = Instant::now();
    let phase_budget = slice_phase_budget();
    let probe_timeout = slice_probe_timeout();
    for slice in slices {
        if phase_budget_spent(phase_budget, started, cpu_started) {
            return false;
        }
        // A slice of guarded conjuncts alone is satisfiable (every guard false),
        // so its probe can only cost time: the large-block query of design step
        // 8e is mostly such conjuncts.
        if relevance_slicing::trivially_satisfiable(&slice, &conjuncts) {
            continue;
        }
        // A genuine SUBSET: each element is a clone of an original conjunct,
        // selected by index. Never a rewrite.
        let subset: Vec<ChcExpr> = slice.iter().map(|&index| conjuncts[index].clone()).collect();
        debug_assert!(subset.len() < conjuncts.len(), "relevance_slices must emit strict subsets");
        let formula = ChcExpr::and_all(subset);
        let result = check_sat_on_budget(smt, &formula, probe_timeout);
        // A SAT or undecided slice says nothing about the full conjunction.
        if classify_smt_result(&result) == SolveOutcomeTag::Unsat {
            return true;
        }
    }
    false
}

fn solve_constraints(smt: &mut SmtContext, constraints: &[ChcExpr]) -> SolveOutcome {
    #[cfg(test)]
    tests::SOLVE_CONSTRAINTS_CALLS.with(|calls| calls.set(calls.get() + 1));
    let formula = ChcExpr::and_all(constraints.iter().cloned());

    // The fused query first, on the per-query budget it always had: a body the
    // solver decides needs no slicing, and slicing costs a probe per slice — on
    // a large-block query (design step 8e), one clause for a whole function,
    // dozens of satisfiable probes per decision. Only an undecided body is
    // sliced; slicing can then turn it into a subset-justified `Unsat`, never
    // divert a satisfiable body or produce a witness. (This order spends no
    // extra wall-clock budget: the previous order ran the slices first and the
    // same full fused query after them.)
    let result = check_sat_on_budget(smt, &formula, smt_query_timeout());
    match classify_smt_result(&result) {
        SolveOutcomeTag::Sat => SolveOutcome::Sat(model_json(&result)),
        // Only a *definitive* UNSAT (plain, with core, or with Farkas certificate)
        // proves the body unsatisfiable and licenses pruning it.
        SolveOutcomeTag::Unsat => SolveOutcome::Unsat,
        SolveOutcomeTag::Undecided if slicing_proves_unsat(smt, constraints) => SolveOutcome::Unsat,
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
            let abstract_result = check_sat_on_budget(smt, &abstract_formula, smt_query_timeout());
            // Reuse the differential-oracle-pinned classifier: only a definitive
            // UNSAT tag (never `Unknown`, never `Sat`) may promote the verdict.
            match classify_smt_result(&abstract_result) {
                SolveOutcomeTag::Unsat => SolveOutcome::Unsat,
                _ => SolveOutcome::Undecided,
            }
        }
    }
}

/// The JSON model of a `Sat` result (`classify_smt_result` said `Sat`).
fn model_json(result: &SmtResult) -> serde_json::Value {
    // `Sat` tag ⟺ `result.is_sat()` ⟺ `SmtResult::Sat(_)` carries a model.
    let model =
        result.model().expect("classify_smt_result returned Sat ⟹ SmtResult::Sat carries a model");
    let mut assignments = serde_json::Map::new();
    for (name, value) in model {
        assignments.insert(name.clone(), smt_value_to_json(value));
    }
    serde_json::Value::Object(assignments)
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
        // Both bit-vector representations render through ay's exact extraction:
        // the allocation-free `BitVec` fast path and the wide `BigBitVec` one a
        // >128-bit witness arrives in. Narrowing the latter through `u128`
        // would print a different number, and dropping it into the `unknown`
        // arm below would cost the replay its binding.
        SmtValue::BitVec(..) | SmtValue::BigBitVec(..) => match value.bitvec_to_biguint() {
            Some((exact, width)) => {
                let hex_digits = (width as usize).div_ceil(4).max(1);
                serde_json::json!({
                    "kind": "bit_vec",
                    "width": width,
                    "value": exact.to_str_radix(10),
                    "hex": format!("0x{exact:0hex_digits$x}"),
                })
            }
            // Width 0 or past ay's public cap: a malformed variant, not a
            // value. Render it opaquely rather than invent a number for it.
            None => serde_json::json!({ "kind": "unknown", "debug": format!("{value:?}") }),
        },
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

/// Every combination of one fact per body predicate, each with the index of
/// the fact it takes from each predicate's list.
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
    type Item = (Vec<usize>, Vec<ReachFact>);

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
        let indices = self.indices.clone();

        if self.indices.is_empty() {
            self.done = true;
            return Some((indices, item));
        }

        for pos in (0..self.indices.len()).rev() {
            self.indices[pos] += 1;
            if self.indices[pos] < self.options[pos].len() {
                return Some((indices, item));
            }
            self.indices[pos] = 0;
        }
        self.done = true;
        Some((indices, item))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use ay_chc::{ChcOp, ChcSort, ChcVar, ClauseBody};

    thread_local! {
        /// How many bodies `solve_constraints` was asked about on this thread.
        pub(super) static SOLVE_CONSTRAINTS_CALLS: std::cell::Cell<u64> =
            const { std::cell::Cell::new(0) };
    }

    /// Each clause body is decided once per decision (`acyclic_error_derivation`'s
    /// `decided`): the round that only confirms the fixpoint asks the solver
    /// nothing again. It used to ask every body a second time, which doubled the
    /// wall time of a decision whose body its budget leaves undecided (the TMC-1
    /// `struct_elem#2` program's one array query, close to the native watchdog
    /// under load).
    #[test]
    fn every_clause_body_is_decided_once_per_decision() {
        //   x = 0       -> p(x)
        //   p(y), y > 5 -> false     (unsatisfiable: SAFE)
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![ChcSort::Int]);
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(x.clone(), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![x]),
        ));
        let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![y.clone()])], Some(ChcExpr::gt(y, ChcExpr::int(5)))),
            ClauseHead::False,
        ));
        SOLVE_CONSTRAINTS_CALLS.with(|calls| calls.set(0));
        assert!(matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Safe));
        assert_eq!(
            SOLVE_CONSTRAINTS_CALLS.with(std::cell::Cell::get),
            2,
            "one solve per clause body: the fact and the error query"
        );
    }

    /// Decision NATIVE-SOLVE-CANCEL: a search whose watchdog has cancelled it
    /// decides no further body and defers. It never claims `Safe` (nor a
    /// witness) for the bodies it did not decide.
    #[test]
    fn a_cancelled_decision_defers_without_asking_the_solver() {
        //   x = 0 -> p(x);  p(y), y > 5 -> false     (SAFE when decided)
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![ChcSort::Int]);
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(x.clone(), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![x]),
        ));
        let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![y.clone()])], Some(ChcExpr::gt(y, ChcExpr::int(5)))),
            ClauseHead::False,
        ));

        // Control: the same token type, never cancelled, decides SAFE.
        let live = CancellationToken::new();
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &live),
            AcyclicDecision::Safe
        ));

        let cancelled = CancellationToken::new();
        cancelled.cancel();
        SOLVE_CONSTRAINTS_CALLS.with(|calls| calls.set(0));
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &cancelled),
            AcyclicDecision::Inconclusive
        ));
        assert_eq!(
            SOLVE_CONSTRAINTS_CALLS.with(std::cell::Cell::get),
            0,
            "a cancelled search asks the solver about no body"
        );
    }

    #[test]
    fn a_cancelled_empty_decision_defers() {
        let problem = ChcProblem::new();
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &CancellationToken::new()),
            AcyclicDecision::Safe
        ));
        let cancelled = CancellationToken::new();
        cancelled.cancel();
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &cancelled),
            AcyclicDecision::Inconclusive
        ));
    }

    #[test]
    fn a_cancelled_unreachable_body_decision_defers() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![]);
        // No fact establishes p, so the body-combination loop never runs.
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![])], None),
            ClauseHead::False,
        ));
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &CancellationToken::new()),
            AcyclicDecision::Safe
        ));
        let cancelled = CancellationToken::new();
        cancelled.cancel();
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &cancelled),
            AcyclicDecision::Inconclusive
        ));
    }

    /// The reachable twin: cancellation defers rather than hand out the
    /// witness of a body it never decided.
    #[test]
    fn a_cancelled_decision_does_not_refute() {
        //   x = 0 -> p(x);  p(y), y = 0 -> false     (UNSAFE when decided)
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![ChcSort::Int]);
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(x.clone(), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![x]),
        ));
        let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![y.clone()])], Some(ChcExpr::eq(y, ChcExpr::int(0)))),
            ClauseHead::False,
        ));
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &CancellationToken::new()),
            AcyclicDecision::Unsafe(_)
        ));
        let cancelled = CancellationToken::new();
        cancelled.cancel();
        assert!(matches!(
            acyclic_direct_smt_decision_with_cancellation(&problem, &cancelled),
            AcyclicDecision::Inconclusive
        ));
    }

    /// `check_sat_on_budget`'s rule: only an undecided attempt whose wall slice
    /// ran out before it computed for half the budget is re-run, in a slice that
    /// delivers the whole budget at the share of a core it measured, between
    /// the budget and `MAX_BUDGET_STRETCH` times it.
    #[test]
    fn only_a_robbed_attempt_is_re_run_in_a_stretched_slice() {
        let budget = Duration::from_secs(1);
        let ms = Duration::from_millis;
        let ceiling = budget * MAX_BUDGET_STRETCH;
        let near = |found: Option<Duration>, want: Duration| {
            found.is_some_and(|found| found.abs_diff(want) <= Duration::from_micros(10))
        };
        // Robbed: its second of wall ran out at a fifth of a core.
        assert!(near(
            robbed_attempt_retry_slice(budget, budget, ms(1000), Some(ms(200))),
            ms(5000)
        ));
        // A slice shorter than the budget, robbed: the re-run still gets the
        // whole budget's CPU at the measured share.
        assert!(near(
            robbed_attempt_retry_slice(budget, ms(500), ms(500), Some(ms(400))),
            ms(1250)
        ));
        // Robbed nearly entirely, or entirely: the stretch stops at its ceiling.
        assert_eq!(
            robbed_attempt_retry_slice(budget, budget, ms(1000), Some(ms(10))),
            Some(ceiling)
        );
        assert_eq!(
            robbed_attempt_retry_slice(budget, budget, ms(1000), Some(Duration::ZERO)),
            Some(ceiling)
        );
        // A stretched re-run robbed again is stretched no further.
        assert_eq!(
            robbed_attempt_retry_slice(budget, ceiling, ceiling, Some(ms(499))),
            Some(ceiling)
        );
        // Spent: it computed for half the budget or more.
        assert_eq!(robbed_attempt_retry_slice(budget, budget, ms(1000), Some(ms(500))), None);
        assert_eq!(robbed_attempt_retry_slice(budget, ceiling, ceiling, Some(ms(900))), None);
        // Declined before its slice ran out: a structural `Unknown`.
        assert_eq!(robbed_attempt_retry_slice(budget, budget, ms(300), Some(ms(10))), None);
        // No per-thread CPU clock: the wall is the budget, as before.
        assert_eq!(robbed_attempt_retry_slice(budget, budget, ms(1000), None), None);
        // A budget too large to stretch saturates instead of overflowing.
        assert_eq!(
            robbed_attempt_retry_slice(
                Duration::MAX,
                Duration::MAX,
                Duration::MAX,
                Some(Duration::ZERO)
            ),
            Some(Duration::MAX)
        );
    }

    /// A phase is spent by the CPU its thread computed for, with the wall at
    /// `MAX_BUDGET_STRETCH` times its budget as the backstop; without a CPU
    /// reading, by the wall alone.
    #[test]
    fn a_phase_budget_is_spent_by_work_with_a_wall_backstop() {
        let now = Instant::now();
        let budget = Duration::from_secs(1);
        let Some(cpu_now) = ay_sys::thread_cpu_time() else {
            // No per-thread CPU clock on this platform: the wall rule only.
            assert!(!phase_budget_spent(budget, now, None));
            return;
        };
        // Just started: neither clock has run.
        assert!(!phase_budget_spent(budget, now, Some(cpu_now)));
        // Two seconds of wall, no work: robbed, not spent; past the backstop: spent.
        let two_seconds_ago = now.checked_sub(Duration::from_secs(2)).expect("monotonic clock");
        assert!(!phase_budget_spent(budget, two_seconds_ago, Some(cpu_now)));
        let past_backstop = now
            .checked_sub(budget * MAX_BUDGET_STRETCH + Duration::from_millis(1))
            .expect("monotonic clock");
        assert!(phase_budget_spent(budget, past_backstop, Some(cpu_now)));
        // The whole thread's CPU so far is more than a nanosecond of work.
        assert!(phase_budget_spent(Duration::from_nanos(1), now, Some(Duration::ZERO)));
        // Without a CPU reading the wall decides.
        assert!(phase_budget_spent(budget, two_seconds_ago, None));
        assert!(!phase_budget_spent(budget, now, None));
    }

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

    /// A derivation is never refused for its SIZE. The model must bind exactly
    /// the derivation's own variables, which the consumer counts from its own
    /// clauses, and the trace names each clause at most once — so the 65 536
    /// binding ceiling refused only large honest witnesses (a large-block query
    /// is a whole function's clause, design step 8e) and was deleted. A model of
    /// 20 000 bindings replays; one of 70 000 is judged on what it says (the
    /// pinned ay's `SmtContext` answers `unknown` past about 65 000 assertions —
    /// an ay ask, docs/DECISION_QUEUE.md 8e — so it may be undecided, but never
    /// refused for its size). Renaming and variable collection are linear
    /// (`clause_vars`).
    #[test]
    fn a_replay_is_judged_whatever_its_number_of_bindings() {
        for (variables, must_decide) in [(20_000usize, true), (70_000, false)] {
            let mut problem = ChcProblem::new();
            let conjuncts: Vec<ChcExpr> = (0..variables)
                .map(|index| ChcExpr::var(ChcVar::new(format!("b{index}"), ChcSort::Bool)))
                .collect();
            problem.add_clause(HornClause::new(
                ClauseBody::constraint(ChcExpr::and_vec(conjuncts)),
                ClauseHead::False,
            ));
            let names = alpha_renamed_variable_names(&problem).expect("the clause renames");
            let assignment = |value: bool| {
                let mut model = serde_json::Map::new();
                for renamed in names[0].values() {
                    model.insert(
                        renamed.clone(),
                        serde_json::json!({ "kind": "bool", "value": value }),
                    );
                }
                AcyclicUnsafeWitness {
                    model: serde_json::Value::Object(model),
                    derivation_clause_indices: vec![0],
                }
            };
            let undecided = |error: &str| !must_decide && error.contains("undecided");
            let holds = replay_acyclic_direct_smt_witness(&problem, &assignment(true));
            assert!(
                holds.as_ref().err().is_none_or(|error| undecided(error)),
                "{variables}: {holds:?}"
            );
            let fails = replay_acyclic_direct_smt_witness(&problem, &assignment(false));
            assert!(
                fails.as_ref().err().is_some_and(|error| {
                    error.contains("does not satisfy") || undecided(error)
                }),
                "{variables}: {fails:?}"
            );
        }
    }

    /// A large-block query's first model may reach `error` through a block whose
    /// input reads a translation havoc — `ite(r, c = havoc, c = 0)` with `r`
    /// true, the shape the lowering gives `c = ite(r, M, d)` — while another
    /// path reads none. The producer flips the choice (`r` false) and asks
    /// again, so the minted witness is one the consumer's havoc gate admits.
    #[test]
    fn a_havoc_free_model_is_preferred_through_a_selected_ite() {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("bb0", vec![ChcSort::Int]);
        let int = |name: &str| ChcExpr::var(ChcVar::new(name, ChcSort::Int));
        let boolean = |name: &str| ChcExpr::var(ChcVar::new(name, ChcSort::Bool));
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(entry, vec![int("bb0_v0")]),
        ));
        let constraint = ChcExpr::and_vec(vec![
            ChcExpr::ite(
                boolean("bb2_lbe_r"),
                ChcExpr::eq(int("bb2_lbe_c0"), int("havoc__f_x_0")),
                ChcExpr::eq(int("bb2_lbe_c0"), ChcExpr::int(0)),
            ),
            ChcExpr::implies(
                boolean("bb2_lbe_e0"),
                ChcExpr::and_vec(vec![
                    boolean("bb2_lbe_r"),
                    ChcExpr::eq(int("bb2_lbe_c0"), ChcExpr::int(5)),
                ]),
            ),
            ChcExpr::implies(boolean("bb1_lbe_e0"), ChcExpr::eq(int("bb0_v0"), ChcExpr::int(7))),
            ChcExpr::or_vec(vec![boolean("bb1_lbe_e0"), boolean("bb2_lbe_e0")]),
        ]);
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(entry, vec![int("bb0_v0")])], Some(constraint)),
            ClauseHead::False,
        ));
        let clauses = alpha_renamed_clauses(&problem).expect("renames");
        let names = alpha_renamed_variable_names(&problem).expect("renames");
        let ClauseHead::Predicate(_, fact_args) = &clauses[0].head else { panic!("a fact") };
        let (_, body_args) = &clauses[1].body.predicates[0];
        let mut constraints: Vec<ChcExpr> = body_args
            .iter()
            .zip(fact_args)
            .map(|(body, fact)| ChcExpr::eq(body.clone(), fact.clone()))
            .collect();
        constraints.push(clauses[1].body.constraint.clone().expect("a constraint"));
        let renamed = |clause: usize, name: &str, sort: ChcSort| {
            names[clause][&ChcVar::new(name, sort)].clone()
        };
        let bool_value = |value: bool| serde_json::json!({ "kind": "bool", "value": value });
        let int_value = |value: i64| serde_json::json!({ "kind": "int", "value": value });
        let mut model = serde_json::Map::new();
        model.insert(renamed(0, "bb0_v0", ChcSort::Int), int_value(0));
        model.insert(renamed(1, "bb0_v0", ChcSort::Int), int_value(0));
        model.insert(renamed(1, "bb2_lbe_r", ChcSort::Bool), bool_value(true));
        model.insert(renamed(1, "bb2_lbe_e0", ChcSort::Bool), bool_value(true));
        model.insert(renamed(1, "bb1_lbe_e0", ChcSort::Bool), bool_value(false));
        model.insert(renamed(1, "bb2_lbe_c0", ChcSort::Int), int_value(5));
        model.insert(renamed(1, "havoc__f_x_0", ChcSort::Int), int_value(5));
        let reading = serde_json::Value::Object(model);
        assert_eq!(
            havoc_reading_choices(&problem, &names, &[0, 1], &reading),
            Some(vec![(renamed(1, "bb2_lbe_r", ChcSort::Bool), false)])
        );
        let mut smt = problem.make_smt_context();

        // Decision NATIVE-SOLVE-CANCEL: a search its watchdog has cancelled
        // asks the solver no retry and yields no witness, where the live run
        // below retries once and returns the havoc-free model.
        let cancelled = CancellationToken::new();
        cancelled.cancel();
        SOLVE_CONSTRAINTS_CALLS.with(|calls| calls.set(0));
        assert_eq!(
            prefer_havoc_free_model(
                &problem,
                &mut smt,
                &[0, 1],
                &constraints,
                reading.clone(),
                &cancelled,
            ),
            None,
            "a cancelled havoc preference hands out no model"
        );
        assert_eq!(
            SOLVE_CONSTRAINTS_CALLS.with(std::cell::Cell::get),
            0,
            "a cancelled havoc preference asks the solver nothing"
        );

        let preferred = prefer_havoc_free_model(
            &problem,
            &mut smt,
            &[0, 1],
            &constraints,
            reading,
            &CancellationToken::new(),
        )
        .expect("a live havoc preference returns a model");
        assert_eq!(havoc_reading_choices(&problem, &names, &[0, 1], &preferred), Some(Vec::new()));
        let witness =
            AcyclicUnsafeWitness { model: preferred, derivation_clause_indices: vec![0, 1] };
        replay_acyclic_direct_smt_witness(&problem, &witness).expect("the preferred model replays");
    }

    #[test]
    fn nested_havoc_choices_search_only_for_replayable_counterexamples() {
        for force_havoc_read in [false, true] {
            let mut problem = ChcProblem::new();
            let entry = problem.declare_predicate("entry", vec![]);
            problem.add_clause(HornClause::new(
                ClauseBody::empty(),
                ClauseHead::Predicate(entry, vec![]),
            ));
            let integer = |name: &str| ChcExpr::var(ChcVar::new(name, ChcSort::Int));
            let boolean = |name: &str| ChcExpr::var(ChcVar::new(name, ChcSort::Bool));
            let mut constraints = vec![
                boolean("required"),
                ChcExpr::implies(
                    boolean("required"),
                    ChcExpr::eq(
                        integer("value"),
                        ChcExpr::ite(boolean("choice"), integer("havoc__nested"), ChcExpr::int(7)),
                    ),
                ),
                ChcExpr::eq(integer("value"), ChcExpr::int(7)),
            ];
            if force_havoc_read {
                constraints.push(boolean("choice"));
            }
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![(entry, vec![])], Some(ChcExpr::and_vec(constraints))),
                ClauseHead::False,
            ));
            let names = alpha_renamed_variable_names(&problem).unwrap();
            let clauses = alpha_renamed_clauses(&problem).unwrap();
            let constraints = vec![clauses[1].body.constraint.clone().unwrap()];
            let mut model = serde_json::Map::new();
            for name in ["required", "choice"] {
                model.insert(
                    names[1][&ChcVar::new(name, ChcSort::Bool)].clone(),
                    serde_json::json!({"kind": "bool", "value": true}),
                );
            }
            for name in ["value", "havoc__nested"] {
                model.insert(
                    names[1][&ChcVar::new(name, ChcSort::Int)].clone(),
                    serde_json::json!({"kind": "int", "value": 7}),
                );
            }
            let original = serde_json::Value::Object(model);
            let mut smt = problem.make_smt_context();
            let preferred = prefer_havoc_free_model(
                &problem,
                &mut smt,
                &[0, 1],
                &constraints,
                original.clone(),
                &CancellationToken::new(),
            )
            .expect("a live havoc preference returns a model");
            assert_eq!(
                crate::native::bounded_unroll::derivation_reads_translation_havoc(
                    &problem,
                    &[0, 1],
                    &preferred,
                ),
                Some(force_havoc_read)
            );
            if force_havoc_read {
                assert_eq!(
                    preferred, original,
                    "restricted UNSAT must retain the original non-proof model"
                );
                assert!(
                    matches!(acyclic_direct_smt_decision(&problem), AcyclicDecision::Unsafe(_)),
                    "a restricted witness search may never turn original SAT into Safe"
                );
            } else {
                let witness = AcyclicUnsafeWitness {
                    model: preferred,
                    derivation_clause_indices: vec![0, 1],
                };
                replay_acyclic_direct_smt_witness(&problem, &witness).expect(
                    "the alternate model must independently replay against the original query",
                );
            }
        }
    }

    /// The shape of a real `splat_index_param` dump's large-block witness
    /// (`[7u32; 8][i]`): the fact's index variable, which the composer equates
    /// with the query's, is missing from the solver's model, and an array of a
    /// block the path never reaches (under a false guard) is bound to a finite
    /// map. Neither replays; the composer's completion does.
    fn index_past_a_splat() -> (ChcProblem, Vec<ChcExpr>, serde_json::Value, String, String) {
        let mut problem = ChcProblem::new();
        let bv = |width| ChcSort::BitVec(width);
        let lanes = ChcSort::Array(Box::new(bv(64)), Box::new(bv(32)));
        let entry = problem.declare_predicate("bb0", vec![bv(64)]);
        let index = |name: &str| ChcExpr::var(ChcVar::new(name, bv(64)));
        let guard = ChcExpr::var(ChcVar::new("bb1_lbe_r", ChcSort::Bool));
        let splat = ChcExpr::var(ChcVar::new("bb1_v0", lanes.clone()));
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(entry, vec![index("bb0_v0")]),
        ));
        let constraint = ChcExpr::and_vec(vec![
            ChcExpr::bv_ule(ChcExpr::BitVec(8, 64), index("bb0_v0")),
            ChcExpr::implies(
                guard,
                ChcExpr::eq(ChcExpr::select(splat, index("bb0_v0")), ChcExpr::BitVec(7, 32)),
            ),
        ]);
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(entry, vec![index("bb0_v0")])], Some(constraint)),
            ClauseHead::False,
        ));
        let clauses = alpha_renamed_clauses(&problem).expect("renames");
        let names = alpha_renamed_variable_names(&problem).expect("renames");
        let ClauseHead::Predicate(_, fact_args) = &clauses[0].head else { panic!("a fact") };
        let (_, body_args) = &clauses[1].body.predicates[0];
        let mut constraints: Vec<ChcExpr> = body_args
            .iter()
            .zip(fact_args)
            .map(|(body, fact)| ChcExpr::eq(body.clone(), fact.clone()))
            .collect();
        constraints.push(clauses[1].body.constraint.clone().expect("a constraint"));
        let fact_index = names[0][&ChcVar::new("bb0_v0", bv(64))].clone();
        let query_index = names[1][&ChcVar::new("bb0_v0", bv(64))].clone();
        let word = |width: u32, value: u64| {
            let hex_digits = (width as usize).div_ceil(4);
            serde_json::json!({
                "kind": "bit_vec",
                "width": width,
                "value": value.to_string(),
                "hex": format!("0x{value:0hex_digits$x}"),
            })
        };
        let mut model = serde_json::Map::new();
        model.insert(query_index.clone(), word(64, 9));
        model.insert(
            names[1][&ChcVar::new("bb1_lbe_r", ChcSort::Bool)].clone(),
            serde_json::json!({ "kind": "bool", "value": false }),
        );
        model.insert(
            names[1][&ChcVar::new("bb1_v0", lanes)].clone(),
            serde_json::json!({
                "kind": "array_map",
                "default": word(32, 0),
                "entries": [{ "index": word(64, 9), "value": word(32, 7) }],
            }),
        );
        (problem, constraints, serde_json::Value::Object(model), fact_index, query_index)
    }

    #[test]
    fn a_model_is_completed_into_one_the_replay_reads() {
        let (problem, constraints, model, fact_index, query_index) = index_past_a_splat();
        let replay = |model: &serde_json::Value| {
            replay_acyclic_direct_smt_witness(
                &problem,
                &AcyclicUnsafeWitness {
                    model: model.clone(),
                    derivation_clause_indices: vec![0, 1],
                },
            )
        };
        assert!(replay(&model).is_err(), "the solver-shaped model is refused");
        let completed = replayable_model(&problem, &[0, 1], &constraints, model);
        replay(&completed).expect("the completed model replays");
        assert_eq!(completed[&fact_index], completed[&query_index], "taken from its equation");
        assert!(
            completed
                .as_object()
                .expect("an object")
                .values()
                .all(|value| value["kind"] != "array_map"),
            "{completed}"
        );
        // A model the replay already reads is minted as it is.
        assert_eq!(replayable_model(&problem, &[0, 1], &constraints, completed.clone()), completed);
    }

    /// The replay asks the derivation under a total model as a closed formula
    /// (`derivation_under_assignment`), which decides exactly as the pinned form
    /// `constraints ∧ ⋀ v = value` would; when a variable is left — here, an
    /// assignment that is not total — it falls back to the pinned form.
    #[test]
    fn a_replay_asks_the_derivation_under_its_model_as_a_closed_formula() {
        let x = ChcVar::new("x", ChcSort::BitVec(8));
        let b = ChcVar::new("b", ChcSort::Bool);
        let constraints = vec![
            ChcExpr::implies(
                ChcExpr::var(b.clone()),
                ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(3, 8)),
            ),
            ChcExpr::var(b.clone()),
        ];
        for (value, holds) in [(3, true), (4, false)] {
            let total = vec![
                (x.clone(), ChcExpr::BitVec(value, 8)),
                (b.clone(), ChcExpr::bool_const(true)),
            ];
            let closed = derivation_under_assignment(constraints.clone(), total);
            assert_eq!(closed.len(), constraints.len());
            assert!(closed.iter().all(mentions_no_variable), "{closed:?}");
            let mut smt = SmtContext::new();
            match solve_constraints(&mut smt, &closed) {
                SolveOutcome::Sat(_) => assert!(holds, "x = {value} must not replay"),
                SolveOutcome::Unsat => assert!(!holds, "x = {value} must replay"),
                SolveOutcome::Undecided => panic!("a closed formula is decided"),
            }
        }
        let partial = vec![(b.clone(), ChcExpr::bool_const(true))];
        let pinned = derivation_under_assignment(constraints.clone(), partial);
        assert_eq!(pinned.len(), constraints.len() + 1);
        assert!(!pinned.iter().all(mentions_no_variable));
        assert!(!mentions_no_variable(&ChcExpr::const_array(ChcSort::BitVec(8), ChcExpr::var(x))));
    }

    #[test]
    fn a_completion_the_replay_refuses_keeps_the_solver_model() {
        let (problem, constraints, model, _, query_index) = index_past_a_splat();
        // An index inside the splat would make the derivation false: no
        // completion can replay, so the solver's model is kept unchanged.
        let mut inside = model;
        inside[&query_index] = serde_json::json!({
            "kind": "bit_vec", "width": 64, "value": "3", "hex": "0x0000000000000003",
        });
        assert_eq!(replayable_model(&problem, &[0, 1], &constraints, inside.clone()), inside);
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

        // Precondition of the test: the FUSED query really is undecidable.
        let mut smt = SmtContext::new();
        let fused = ChcExpr::and_all(constraints.iter().cloned());
        smt.reset();
        let fused_result = smt.check_sat_with_timeout(&fused, smt_query_timeout());
        assert_eq!(
            classify_smt_result(&fused_result),
            SolveOutcomeTag::Undecided,
            "test precondition broke: the fused body is no longer undecidable ({fused_result:?}), \
             so this stopped being a fail-first witness for slicing"
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

    /// 2^200 - 2^127: 73 set bits sitting entirely above the `u128` window,
    /// over 127 zero low bits. Its low 128 bits (`2^127`) are what any `u128`
    /// step would print or rebuild instead of the value.
    const WIDE_200: &str = "1606938044258990275541791951157702133290471306479076951195648";

    /// A witness value past 128 bits survives the model round trip exactly: the
    /// renderer reads ay's wide `BigBitVec` through `bitvec_to_biguint`, and the
    /// replay parser rebuilds the same literal instead of narrowing it.
    #[test]
    fn a_wide_bit_vector_witness_round_trips_exactly() {
        // Inferred as ay's `BigUint` from the checked constructor it feeds.
        let parsed = WIDE_200.parse().expect("the fixture is an exact decimal literal");
        let value = SmtValue::try_bitvec_from_biguint(parsed, 200).expect("width 200 is in range");
        assert!(
            matches!(value, SmtValue::BigBitVec(..)),
            "a >128-bit model value must use ay's wide representation"
        );

        let json = smt_value_to_json(&value);
        assert_eq!(json["kind"], "bit_vec", "a wide witness must not render as `unknown`");
        assert_eq!(json["width"], 200);
        assert_eq!(json["value"], WIDE_200);
        assert_eq!(json["hex"], "0xffffffffffffffffff80000000000000000000000000000000");

        let replayed = parse_model_value("w", &ChcSort::BitVec(200), &json)
            .expect("an exact wide witness must replay");
        assert_eq!(
            replayed,
            value.bitvec_to_chc_expr().expect("the witness has an exact ay literal"),
            "replay must rebuild ay's exact concat-tree literal"
        );
        assert_ne!(
            replayed,
            ChcExpr::BitVec(1u128 << 127, 200),
            "the low 128 bits alone are what a u128 narrowing would rebuild"
        );
    }

    /// Fail-closed: the checked constructor reduces modulo `2^width`, so a
    /// binding one bit too wide would otherwise replay as a DIFFERENT value
    /// (2^200 becomes 0 at width 200) — the parser must refuse it.
    #[test]
    fn a_wide_binding_that_exceeds_its_sort_is_rejected() {
        let json = serde_json::json!({
            "kind": "bit_vec",
            "width": 200,
            "value": "1606938044258990275541962092341162602522202993782792835301376",
            "hex": "0x00000000000000000000000000000000000000000000000000",
        });
        let error = parse_model_value("w", &ChcSort::BitVec(200), &json)
            .expect_err("an over-wide binding must not replay");
        assert!(error.contains("exceeds its bit-vector width"), "got: {error}");
    }

    /// The <=128-bit wire shape is unchanged: same decimal, same zero-padded
    /// hex, same compact `BitVec` leaf on replay.
    #[test]
    fn a_narrow_bit_vector_witness_keeps_its_compact_rendering() {
        let value = SmtValue::try_bitvec_from_u128(0x90, 32).expect("width 32 is in range");
        let json = smt_value_to_json(&value);
        assert_eq!(json["kind"], "bit_vec");
        assert_eq!(json["value"], "144");
        assert_eq!(json["hex"], "0x00000090");
        assert_eq!(
            parse_model_value("b", &ChcSort::BitVec(32), &json).expect("a narrow witness replays"),
            ChcExpr::BitVec(0x90, 32)
        );
    }

    /// Model integers that serde_json's `Number` cannot hold (it spans only
    /// i64/u64). Before 3e6899dc3 the `SmtValue::Int` arm handed the `i128`
    /// straight to `json!`, which failed "number out of range" and the unwrap
    /// inside the macro ICE'd trustc (`direct_smt_cex.rs:361`, 18 dumps while
    /// verifying memchr 2.8.2 and libc 0.2.186). -2^64 is the exact value those
    /// crates' counterexamples still carry today.
    const OUT_OF_JSON_RANGE_INTS: [i128; 5] =
        [i128::MIN, -(1i128 << 64), (i64::MIN as i128) - 1, (u64::MAX as i128) + 1, i128::MAX];

    /// Rendering an out-of-range integer witness must not panic, must keep the
    /// exact value (as a decimal string), and must replay to the same literal.
    #[test]
    fn an_out_of_json_range_int_witness_renders_and_replays_exactly() {
        for value in OUT_OF_JSON_RANGE_INTS {
            let json = smt_value_to_json(&SmtValue::Int(value));
            assert_eq!(json["kind"], "int", "{value}: wrong kind in {json}");
            assert_eq!(json["value"], value.to_string(), "{value}: not an exact decimal string");
            assert_eq!(
                parse_model_value("x", &ChcSort::Int, &json).expect("an exact Int witness replays"),
                ChcExpr::int(value),
                "{value}: replay must rebuild the same literal"
            );
        }
    }

    /// The in-range wire shape is unchanged: a native JSON number at both
    /// boundaries of the i64 and u64 windows.
    #[test]
    fn an_in_json_range_int_witness_keeps_its_native_number() {
        for value in [i64::MIN as i128, -1, 0, i64::MAX as i128, u64::MAX as i128] {
            let json = smt_value_to_json(&SmtValue::Int(value));
            assert!(json["value"].is_number(), "{value}: expected a JSON number, got {json}");
            assert_eq!(
                parse_model_value("x", &ChcSort::Int, &json)
                    .expect("an in-range Int witness replays"),
                ChcExpr::int(value)
            );
        }
    }

    /// The crash's own call chain: a SAT body whose model assigns an integer
    /// outside the JSON number range goes through `solve_constraints` (the frame
    /// that called the panicking renderer) and must return the exact witness.
    #[test]
    fn solve_constraints_returns_an_out_of_json_range_int_model() {
        for value in OUT_OF_JSON_RANGE_INTS {
            let x = ChcVar::new("x", ChcSort::Int);
            let constraints = [ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(value))];
            let mut smt = SmtContext::new();
            let SolveOutcome::Sat(model) = solve_constraints(&mut smt, &constraints) else {
                panic!("x = {value} is satisfiable");
            };
            assert_eq!(model["x"]["kind"], "int", "{value}: {model}");
            assert_eq!(model["x"]["value"], value.to_string(), "{value}: {model}");
        }
    }
}

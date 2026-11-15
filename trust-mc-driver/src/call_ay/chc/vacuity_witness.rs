// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A checked certificate for the vacuity probe's `sat` answer, found in
//! process before the external solver is spawned.
//!
//! # Why
//!
//! The V4 vacuity probe (`vacuity_probe`) asks the external `ay` whether ANY
//! check-site block atom of a would-be CHC proof is derivable. Only a decided
//! `unsat` changes a verdict; `sat` changes nothing. On the corpus nearly every
//! probe is `sat`, and it is expensive: measured 2026-09-25 at ay `6818b5d06`,
//! `expected/function-contract/history/simple_pass.rs` proves its rows and then
//! spends 13.3 s of its 15 s harness budget on a probe that ends
//! `undetermined`. Run alone on the same probe file, `ay` answers `sat` after
//! 12.9 s, all of it in one exact acyclic-BMC path check of a 44-relation,
//! 51-clause program with ten `bvadd`s. The same constant gap sits on the other
//! `history/*` units, `modifies/global_{pass,replace_fail}` and `powf32`.
//!
//! # The certificate
//!
//! A Horn derivation of the probe relation `ay_vacuity_reach`: a tree of clause
//! instances, each instance's variables renamed apart, plus ONE total
//! assignment of values to every renamed variable under which
//!
//! * every instance's body constraint evaluates to `true`, and
//! * every body atom's arguments evaluate equal to the head arguments of the
//!   instance that derived that atom.
//!
//! Such an assignment is a derivation in the program's least model, by
//! induction up the tree: a clause holds for EVERY valuation of its variables,
//! so an instance whose premises are derived tuples and whose constraint holds
//! derives its head tuple. `ay_vacuity_reach` derivable is exactly the probe's
//! `sat`, so the probe's question is answered with no solver trusted.
//!
//! The search only PROPOSES the assignment. It composes facts forward,
//! extending each fact's assignment by exact evaluation where it can, and asks
//! the embedded `SmtContext` — whose `Sat` has known bit-vector gaps
//! (`model_eval`'s header) — only where it cannot. Nothing is accepted until
//! every constraint of the composed derivation evaluates to `true` under a
//! TOTAL assignment, in the driver's own exact evaluator
//! (`model_eval::eval_under`), which answers `None` — and so rejects the
//! certificate — for any term it does not evaluate exactly. A rejected or
//! missing certificate costs nothing but the search's slice: the external probe
//! then runs exactly as before. The search can only ever miss a reachable check
//! site; it cannot report one that is not.
//!
//! Measured 2026-09-25 on the 648 corpus units whose counted-row-74 log shows a
//! CHC proof: the probe stage fell from 447 s to 14 s in total, and 154 of 160
//! searches certified, each in at most 0.4 s. The other six were the three
//! vacuous harnesses (nothing to certify) and the three harnesses of
//! `valid-value-checks/char_validity.rs`, whose datatype testers the evaluator
//! does not read.
//!
//! Renaming is done here, with explicit size and depth limits, rather than by
//! `ChcExpr::substitute`, because that substitution silently keeps the original
//! sub-term when it hits its node budget — a partially renamed instance would
//! disconnect a constraint from its arguments and could "derive" any tuple.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Duration;

use ay::chc::{ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseHead, PredicateId};
use ay::chc::{SmtResult, SmtValue};

use crate::deadline::Deadline;

use super::model_eval::eval_under;

/// Facts kept per relation. One path per relation usually suffices; a few more
/// let the search route around a path whose values a later guard rejects.
const MAX_FACTS_PER_RELATION: usize = 4;
/// Body-fact combinations tried per clause per round.
const MAX_COMBINATIONS_PER_CLAUSE: usize = 32;
/// Cap on one embedded SMT check, inside the search's own slice.
const MAX_SMT_CHECK: Duration = Duration::from_secs(2);
/// Largest clause term (in nodes, counting shared sub-terms once per use) the
/// renamer walks. Beyond it the search declines rather than risk a partial
/// rename or an exploded DAG.
const MAX_TERM_NODES: usize = 200_000;
/// Deepest clause term the renamer and the evaluator will recurse into.
const MAX_TERM_DEPTH: usize = 400;
/// Passes of definition propagation when completing an assignment.
const MAX_DEFINITION_PASSES: usize = 32;
/// Prefix of every renamed variable: instance `i`'s copy of `v` is
/// `ay_vw<i>_<v>`. The digits end at the first `_`, so the map is injective and
/// no two instances' variables can meet. Original names never occur in a
/// composed formula, so they cannot meet a renamed one either.
const RENAME_PREFIX: &str = "ay_vw";

/// A checked derivation of the probe relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct CertifiedReach {
    /// Clause instances in the certified derivation tree.
    pub(super) clause_instances: usize,
    /// Embedded SMT checks the search spent.
    pub(super) smt_checks: usize,
}

/// What the search found. Only [`WitnessSearch::Certified`] means anything;
/// every other answer is "not shown here" and the external probe runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum WitnessSearch {
    Certified(CertifiedReach),
    NotFound { reason: &'static str, smt_checks: usize },
}

impl WitnessSearch {
    /// Stable label for the stage-timing marker.
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Certified(_) => "certified",
            Self::NotFound { reason, .. } => reason,
        }
    }
}

#[derive(Clone)]
struct Fact {
    args: Vec<ChcExpr>,
    constraints: Vec<ChcExpr>,
    clause_instances: usize,
    /// A total assignment of `constraints`' variables under which every one of
    /// them evaluates to `true`, when one was found; the next instance first
    /// tries to extend it by evaluation alone, before any solver call.
    assignment: Option<Arc<HashMap<String, SmtValue>>>,
}

/// Search for a checked derivation of `target` in the Horn program `smt`,
/// within `deadline`.
pub(super) fn certified_reach_witness(
    smt: &str,
    target: &str,
    deadline: Deadline,
) -> WitnessSearch {
    isolate_panics(|| search_reach_witness(smt, target, deadline))
}

/// Run `search`, answering "not found" if it panics. The search runs after the
/// proof itself has succeeded, and a panic anywhere inside it — the evaluator,
/// the renamer, the embedded `SmtContext` — is no certificate: the external
/// probe then decides, exactly as for any other miss, instead of the panic
/// killing the driver and losing the verdict.
fn isolate_panics(search: impl FnOnce() -> WitnessSearch) -> WitnessSearch {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(search))
        .unwrap_or(WitnessSearch::NotFound { reason: "panicked", smt_checks: 0 })
}

fn search_reach_witness(smt: &str, target: &str, deadline: Deadline) -> WitnessSearch {
    let Ok(problem) = ChcParser::parse(smt) else {
        return WitnessSearch::NotFound { reason: "parse-refused", smt_checks: 0 };
    };
    let Some(target_id) = problem.get_predicate_by_name(target).map(|p| p.id) else {
        return WitnessSearch::NotFound { reason: "no-target", smt_checks: 0 };
    };
    let target_clauses: Vec<usize> = problem
        .clauses()
        .iter()
        .enumerate()
        .filter(|(_, c)| matches!(&c.head, ClauseHead::Predicate(p, _) if *p == target_id))
        .map(|(idx, _)| idx)
        .collect();
    Search::new(&problem, target_clauses, deadline).run()
}

/// What one clause instance came to.
enum Attempt {
    /// A target-clause instance whose whole derivation re-evaluated `true`.
    Certified(CertifiedReach),
    /// A new fact for this relation.
    NewFact(PredicateId),
    /// Unsatisfiable, undecided, unvalidated, or skipped.
    Nothing,
    /// Stop searching, for this reason.
    Stop(&'static str),
}

/// Forward fact composition over the relations that can reach a target clause.
///
/// Scheduling matters more than completeness here: the composed formulas grow
/// with the derivation, so exploring past a check site before trying the
/// target clause wastes the slice (measured: on `history/simple_pass` a
/// file-order sweep spent 9 s on ever longer paths beyond the site it had
/// already derived). Every round therefore tries the target clauses first, and
/// every new fact immediately tries the target clauses that consume it.
struct Search<'p> {
    problem: &'p ChcProblem,
    smt_ctx: ay::chc::SmtContext,
    deadline: Deadline,
    target_clauses: Vec<usize>,
    explore_clauses: Vec<usize>,
    targets_using: HashMap<PredicateId, Vec<usize>>,
    facts: HashMap<PredicateId, Vec<Fact>>,
    tried: HashSet<(usize, Vec<usize>)>,
    instance: usize,
    smt_checks: usize,
    unvalidated: bool,
}

impl<'p> Search<'p> {
    fn new(problem: &'p ChcProblem, target_clauses: Vec<usize>, deadline: Deadline) -> Self {
        let clauses = problem.clauses();
        let target_set: HashSet<usize> = target_clauses.iter().copied().collect();
        let relevant = relations_reaching(
            problem,
            target_clauses
                .iter()
                .flat_map(|&idx| clauses[idx].body.predicates.iter().map(|(p, _)| *p)),
        );
        let explore_clauses = clauses
            .iter()
            .enumerate()
            .filter(|(idx, c)| {
                !target_set.contains(idx)
                    && matches!(&c.head, ClauseHead::Predicate(p, _) if relevant.contains(p))
            })
            .map(|(idx, _)| idx)
            .collect();
        let mut targets_using: HashMap<PredicateId, Vec<usize>> = HashMap::new();
        for &idx in &target_clauses {
            for (pred, _) in &clauses[idx].body.predicates {
                let users = targets_using.entry(*pred).or_default();
                if !users.contains(&idx) {
                    users.push(idx);
                }
            }
        }
        Self {
            problem,
            smt_ctx: problem.make_smt_context(),
            deadline,
            target_clauses,
            explore_clauses,
            targets_using,
            facts: HashMap::new(),
            tried: HashSet::new(),
            instance: 0,
            smt_checks: 0,
            unvalidated: false,
        }
    }

    fn not_found(&self, reason: &'static str) -> WitnessSearch {
        WitnessSearch::NotFound { reason, smt_checks: self.smt_checks }
    }

    fn run(mut self) -> WitnessSearch {
        if self.target_clauses.is_empty() {
            return self.not_found("no-target-clause");
        }
        loop {
            for idx in self.target_clauses.clone() {
                if let Some(done) = self.sweep(idx) {
                    return done;
                }
            }
            let mut changed = false;
            for idx in self.explore_clauses.clone() {
                let mut spent = 0usize;
                for combo in self.fresh_combos(idx) {
                    if spent >= MAX_COMBINATIONS_PER_CLAUSE || self.head_is_full(idx) {
                        break;
                    }
                    spent += 1;
                    match self.attempt(idx, &combo) {
                        Attempt::Certified(reach) => return WitnessSearch::Certified(reach),
                        Attempt::Stop(reason) => return self.not_found(reason),
                        Attempt::Nothing => {}
                        Attempt::NewFact(pred) => {
                            changed = true;
                            for target in self.targets_using.get(&pred).cloned().unwrap_or_default()
                            {
                                if let Some(done) = self.sweep(target) {
                                    return done;
                                }
                            }
                        }
                    }
                }
            }
            if !changed {
                return self.not_found(if self.unvalidated { "unvalidated" } else { "exhausted" });
            }
        }
    }

    /// Try every untried body-fact combination of target clause `idx`.
    fn sweep(&mut self, idx: usize) -> Option<WitnessSearch> {
        for (spent, combo) in self.fresh_combos(idx).into_iter().enumerate() {
            if spent >= MAX_COMBINATIONS_PER_CLAUSE {
                break;
            }
            match self.attempt(idx, &combo) {
                Attempt::Certified(reach) => return Some(WitnessSearch::Certified(reach)),
                Attempt::Stop(reason) => return Some(self.not_found(reason)),
                Attempt::Nothing | Attempt::NewFact(_) => {}
            }
        }
        None
    }

    /// Body-fact index tuples of clause `idx` not tried yet.
    fn fresh_combos(&self, idx: usize) -> Vec<Vec<usize>> {
        let counts: Vec<usize> = self.problem.clauses()[idx]
            .body
            .predicates
            .iter()
            .map(|(pred, _)| self.facts.get(pred).map_or(0, Vec::len))
            .collect();
        IndexCombinations::new(counts)
            .filter(|combo| !self.tried.contains(&(idx, combo.clone())))
            .take(MAX_COMBINATIONS_PER_CLAUSE)
            .collect()
    }

    fn head_is_full(&self, idx: usize) -> bool {
        match &self.problem.clauses()[idx].head {
            ClauseHead::Predicate(pred, _) => {
                self.facts.get(pred).map_or(0, Vec::len) >= MAX_FACTS_PER_RELATION
            }
            _ => true,
        }
    }

    /// Compose one renamed instance of clause `idx` over the body facts `combo`
    /// and ask the embedded solver for a model.
    fn attempt(&mut self, idx: usize, combo: &[usize]) -> Attempt {
        if !self.tried.insert((idx, combo.to_vec())) {
            return Attempt::Nothing;
        }
        if self.deadline.remaining().is_zero() {
            return Attempt::Stop("slice-spent");
        }
        let clause = &self.problem.clauses()[idx];
        let ClauseHead::Predicate(head_pred, _) = &clause.head else { return Attempt::Nothing };
        self.instance += 1;
        let Some(renamed) = RenamedClause::new(clause, self.instance) else {
            return Attempt::Stop("term-too-large");
        };

        let mut constraints = Vec::new();
        let mut own = Vec::new();
        let mut clause_instances = 1usize;
        // The body facts' assignments, merged. Facts built from different
        // models can disagree on a shared ancestor's variables; then there is
        // no seed and the solver decides.
        let mut seed: Option<HashMap<String, SmtValue>> = Some(HashMap::new());
        for (body_idx, body_args) in renamed.body_args.iter().enumerate() {
            let (pred, _) = &clause.body.predicates[body_idx];
            let fact = &self.facts[pred][combo[body_idx]];
            if fact.args.len() != body_args.len() {
                return Attempt::Nothing;
            }
            constraints.extend(fact.constraints.iter().cloned());
            clause_instances += fact.clause_instances;
            own.extend(
                body_args
                    .iter()
                    .zip(&fact.args)
                    .map(|(body_arg, fact_arg)| ChcExpr::eq(body_arg.clone(), fact_arg.clone())),
            );
            seed = match (seed, &fact.assignment) {
                (Some(mut merged), Some(values)) => {
                    let agrees = values.iter().all(|(name, value)| {
                        merged.insert(name.clone(), value.clone()).is_none_or(|old| old == *value)
                    });
                    agrees.then_some(merged)
                }
                _ => None,
            };
        }
        if let Some(constraint) = renamed.constraint {
            own.push(constraint);
        }

        // First try to extend the body facts' assignment through this
        // instance's own constraints by exact evaluation — most instances are
        // definitions and guards the inherited values already satisfy. Only
        // when that fails does the embedded solver see the whole derivation.
        let extended = seed.and_then(|mut seed| {
            let fresh = complete_assignment(&own, &seed)?;
            seed.extend(fresh);
            Some(seed)
        });
        constraints.extend(own);
        let assignment = match extended {
            Some(assignment) => Some(assignment),
            None => {
                self.smt_checks += 1;
                let formula = ChcExpr::and_all(constraints.iter().cloned());
                self.smt_ctx.reset();
                let budget = self.deadline.remaining().min(MAX_SMT_CHECK);
                let SmtResult::Sat(model) = self.smt_ctx.check_sat_with_timeout(&formula, budget)
                else {
                    return Attempt::Nothing;
                };
                let model: HashMap<String, SmtValue> = model.into_iter().collect();
                complete_assignment(&constraints, &model)
            }
        };

        if self.target_clauses.contains(&idx) {
            // The certificate: EVERY constraint of the whole derivation, not
            // only this instance's, re-evaluated under one total assignment.
            if let Some(assignment) = &assignment
                && complete_assignment(&constraints, assignment).is_some()
            {
                return Attempt::Certified(CertifiedReach {
                    clause_instances,
                    smt_checks: self.smt_checks,
                });
            }
            self.unvalidated = true;
            return Attempt::Nothing;
        }
        self.facts.entry(*head_pred).or_default().push(Fact {
            args: renamed.head_args.unwrap_or_default(),
            constraints,
            clause_instances,
            assignment: assignment.map(Arc::new),
        });
        Attempt::NewFact(*head_pred)
    }
}

/// Relations from which one of `seeds` is derivable along the clause graph
/// (the seeds included). Facts for any other relation cannot contribute.
fn relations_reaching(
    problem: &ChcProblem,
    seeds: impl IntoIterator<Item = PredicateId>,
) -> HashSet<PredicateId> {
    let mut relevant: HashSet<PredicateId> = seeds.into_iter().collect();
    loop {
        let mut changed = false;
        for clause in problem.clauses() {
            let ClauseHead::Predicate(head, _) = &clause.head else { continue };
            if !relevant.contains(head) {
                continue;
            }
            for (pred, _) in &clause.body.predicates {
                changed |= relevant.insert(*pred);
            }
        }
        if !changed {
            return relevant;
        }
    }
}

/// `Some(true)` if some variable of `expr` satisfies `pred`; `None` if the term
/// is deeper than [`MAX_TERM_DEPTH`].
fn any_var(expr: &ChcExpr, depth: usize, pred: &mut impl FnMut(&ChcVar) -> bool) -> Option<bool> {
    if depth > MAX_TERM_DEPTH {
        return None;
    }
    Some(match expr {
        ChcExpr::Var(v) => pred(v),
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            for arg in args {
                if any_var(arg, depth + 1, pred)? {
                    return Some(true);
                }
            }
            false
        }
        ChcExpr::ConstArray(_, inner) => any_var(inner, depth + 1, pred)?,
        _ => false,
    })
}

/// One clause instance with every variable renamed apart.
struct RenamedClause {
    body_args: Vec<Vec<ChcExpr>>,
    constraint: Option<ChcExpr>,
    head_args: Option<Vec<ChcExpr>>,
}

impl RenamedClause {
    /// `None` when any term is too large or too deep to rename COMPLETELY.
    fn new(clause: &ay::chc::HornClause, instance: usize) -> Option<Self> {
        let mut renamer = Renamer { instance, nodes: 0 };
        let mut body_args = Vec::with_capacity(clause.body.predicates.len());
        for (_, args) in &clause.body.predicates {
            body_args.push(args.iter().map(|a| renamer.rename(a, 0)).collect::<Option<Vec<_>>>()?);
        }
        let constraint = match &clause.body.constraint {
            Some(c) => Some(renamer.rename(c, 0)?),
            None => None,
        };
        let head_args = match &clause.head {
            ClauseHead::Predicate(_, args) => {
                Some(args.iter().map(|a| renamer.rename(a, 0)).collect::<Option<Vec<_>>>()?)
            }
            _ => None,
        };
        Some(Self { body_args, constraint, head_args })
    }
}

struct Renamer {
    instance: usize,
    nodes: usize,
}

impl Renamer {
    /// A complete copy of `expr` with every variable renamed, or `None`.
    /// Parser-internal markers and unknown variants are refused.
    fn rename(&mut self, expr: &ChcExpr, depth: usize) -> Option<ChcExpr> {
        self.nodes += 1;
        if depth > MAX_TERM_DEPTH || self.nodes > MAX_TERM_NODES {
            return None;
        }
        let args = |this: &mut Self, args: &[Arc<ChcExpr>]| -> Option<Vec<Arc<ChcExpr>>> {
            args.iter().map(|a| this.rename(a, depth + 1).map(Arc::new)).collect()
        };
        Some(match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
                expr.clone()
            }
            ChcExpr::Var(v) => ChcExpr::Var(ChcVar::new(
                format!("{RENAME_PREFIX}{}_{}", self.instance, v.name),
                v.sort.clone(),
            )),
            ChcExpr::Op(op, a) => ChcExpr::Op(*op, args(self, a)?),
            ChcExpr::PredicateApp(name, id, a) => {
                ChcExpr::PredicateApp(name.clone(), *id, args(self, a)?)
            }
            ChcExpr::FuncApp(name, sort, a) => {
                ChcExpr::FuncApp(name.clone(), sort.clone(), args(self, a)?)
            }
            ChcExpr::ConstArray(sort, inner) => {
                ChcExpr::ConstArray(sort.clone(), Arc::new(self.rename(inner, depth + 1)?))
            }
            // Parser-internal markers, and any variant a later ay adds (the enum
            // is non-exhaustive): not a term this renamer knows to copy whole.
            _ => return None,
        })
    }
}

/// Every variable of `constraints` with its one sort, or `None` when a name is
/// used at two sorts or a term is too deep to walk.
fn variable_sorts(constraints: &[ChcExpr]) -> Option<HashMap<String, ChcSort>> {
    let mut sorts: HashMap<String, ChcSort> = HashMap::new();
    let mut clash = false;
    for constraint in constraints {
        any_var(constraint, 0, &mut |v| {
            match sorts.get(&v.name) {
                Some(sort) => clash |= *sort != v.sort,
                None => {
                    sorts.insert(v.name.clone(), v.sort.clone());
                }
            }
            false
        })?;
    }
    (!clash).then_some(sorts)
}

fn value_has_sort(value: &SmtValue, sort: &ChcSort) -> bool {
    match (value, sort) {
        (SmtValue::Bool(_), ChcSort::Bool) | (SmtValue::Int(_), ChcSort::Int) => true,
        (SmtValue::BitVec(_, w), ChcSort::BitVec(sw)) => w == sw && *w <= 128,
        (SmtValue::ConstArray(default), ChcSort::Array(_, element)) => {
            value_has_sort(default, element)
        }
        (SmtValue::ArrayMap { default, entries }, ChcSort::Array(index, element)) => {
            value_has_sort(default, element)
                && entries
                    .iter()
                    .all(|(i, e)| value_has_sort(i, index) && value_has_sort(e, element))
        }
        _ => false,
    }
}

fn default_value(sort: &ChcSort) -> Option<SmtValue> {
    match sort {
        ChcSort::Bool => Some(SmtValue::Bool(false)),
        ChcSort::Int => Some(SmtValue::Int(0)),
        ChcSort::BitVec(w) if (1..=128).contains(w) => Some(SmtValue::BitVec(0, *w)),
        ChcSort::Array(_, element) => Some(SmtValue::ConstArray(Box::new(default_value(element)?))),
        _ => None,
    }
}

/// Top-level conjuncts of `expr`, read through nested `and`.
fn conjuncts<'e>(expr: &'e ChcExpr, out: &mut Vec<&'e ChcExpr>) {
    match expr {
        ChcExpr::Op(ay::chc::ChcOp::And, args) => {
            for arg in args {
                conjuncts(arg, out);
            }
        }
        _ => out.push(expr),
    }
}

/// A TOTAL assignment of the variables of `constraints` under which every one
/// of them evaluates to `true`, built from `seed`, or `None`.
///
/// The assignment takes `seed`'s value for each variable whose value has the
/// variable's sort, then completes the rest through the definitions the
/// constraints themselves state (`(= v t)` with `t` already evaluable), then
/// gives anything still unassigned a default of its sort. How it was built does
/// not matter to soundness: `Some` is returned only after the exact evaluation
/// of every constraint to `true`, and any variable, operator or sort the
/// evaluator does not handle makes it answer `None`.
fn complete_assignment(
    constraints: &[ChcExpr],
    seed: &HashMap<String, SmtValue>,
) -> Option<HashMap<String, SmtValue>> {
    let sorts = variable_sorts(constraints)?;
    let mut assignment: HashMap<String, SmtValue> = HashMap::with_capacity(sorts.len());
    for (name, sort) in &sorts {
        if let Some(value) = seed.get(name)
            && value_has_sort(value, sort)
        {
            assignment.insert(name.clone(), value.clone());
        }
    }

    if assignment.len() < sorts.len() {
        let mut flat = Vec::new();
        for constraint in constraints {
            conjuncts(constraint, &mut flat);
        }
        // Conjuncts arrive in derivation order, so definitions usually settle
        // in one or two passes; the cap bounds a pathological chain, and
        // whatever it leaves unassigned only gets a default and is still
        // checked below.
        for _ in 0..MAX_DEFINITION_PASSES {
            let mut changed = false;
            for conjunct in &flat {
                let ChcExpr::Op(ay::chc::ChcOp::Eq, args) = conjunct else { continue };
                let [lhs, rhs] = args.as_slice() else { continue };
                for (var_side, term_side) in [(lhs, rhs), (rhs, lhs)] {
                    let ChcExpr::Var(v) = var_side.as_ref() else { continue };
                    if assignment.contains_key(&v.name) {
                        continue;
                    }
                    if let Some(value) = eval_under(term_side, &assignment)
                        && sorts.get(&v.name).is_some_and(|sort| value_has_sort(&value, sort))
                    {
                        assignment.insert(v.name.clone(), value);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (name, sort) in &sorts {
            if !assignment.contains_key(name) {
                assignment.insert(name.clone(), default_value(sort)?);
            }
        }
    }

    constraints
        .iter()
        .all(|c| matches!(eval_under(c, &assignment), Some(SmtValue::Bool(true))))
        .then_some(assignment)
}

/// Whether `constraints` all evaluate to `true` under a total assignment
/// completed from `model` (see [`complete_assignment`]).
#[cfg(test)]
fn assignment_certifies(constraints: &[ChcExpr], model: &HashMap<String, SmtValue>) -> bool {
    complete_assignment(constraints, model).is_some()
}

/// Odometer over `counts[0] × counts[1] × …` index tuples (one empty tuple for
/// a body with no relation atoms).
struct IndexCombinations {
    counts: Vec<usize>,
    next: Option<Vec<usize>>,
}

impl IndexCombinations {
    fn new(counts: Vec<usize>) -> Self {
        let next = (!counts.contains(&0)).then(|| vec![0; counts.len()]);
        Self { counts, next }
    }
}

impl Iterator for IndexCombinations {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Vec<usize>> {
        let current = self.next.take()?;
        let mut advanced = current.clone();
        for pos in (0..advanced.len()).rev() {
            advanced[pos] += 1;
            if advanced[pos] < self.counts[pos] {
                self.next = Some(advanced);
                return Some(current);
            }
            advanced[pos] = 0;
        }
        Some(current)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn far() -> Deadline {
        Deadline::after(Duration::from_secs(60))
    }

    fn certified(smt: &str) -> bool {
        matches!(
            certified_reach_witness(smt, "ay_vacuity_reach", far()),
            WitnessSearch::Certified(_)
        )
    }

    /// A chain whose state columns reuse ONE set of declared variable names in
    /// every rule — the encoder's own shape. Without renaming, composing the
    /// rules identifies `x` of one rule with `x` of the next and the reachable
    /// site looks unreachable.
    const CHAIN: &str = "\
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-var x__out (_ BitVec 8))
(declare-rel f__bb0 ((_ BitVec 8)))
(declare-rel f__bb1 ((_ BitVec 8)))
(declare-rel f__bb2 ((_ BitVec 8)))
(declare-rel ay_vacuity_reach ())
(rule (=> (bvugt x #x0a) (f__bb0 x)))
(rule (=> (and (f__bb0 x) (= x__out (bvadd x #x01))) (f__bb1 x__out)))
(rule (=> (and (f__bb1 x) (= x__out (bvadd x #x01)) (bvult x #x20)) (f__bb2 x__out)))
(rule (=> (f__bb2 x) ay_vacuity_reach))
(query ay_vacuity_reach)
";

    #[test]
    fn a_reachable_site_behind_guards_and_definitions_is_certified() {
        let found = certified_reach_witness(CHAIN, "ay_vacuity_reach", far());
        let WitnessSearch::Certified(reach) = found else {
            panic!("expected a certified derivation, got {found:?}");
        };
        // fact -> bb0 -> bb1 -> bb2 -> reach
        assert_eq!(reach.clause_instances, 4);
    }

    #[test]
    fn contradictory_guards_are_never_certified() {
        let smt = CHAIN.replace("(bvugt x #x0a)", "(and (bvugt x #x0a) (bvult x #x05))");
        assert!(!certified(&smt));
    }

    #[test]
    fn a_contradiction_only_through_a_definition_is_never_certified() {
        // x + 1 == 0 forces x == 255; x == 5 contradicts it.
        let smt = CHAIN.replace(
            "(rule (=> (bvugt x #x0a) (f__bb0 x)))",
            "(rule (=> (and (= (bvadd x #x01) #x00) (= x #x05)) (f__bb0 x)))",
        );
        assert!(!certified(&smt));
    }

    #[test]
    fn a_guard_that_a_later_definition_violates_is_never_certified() {
        // bb2 needs the incremented value below 0x0c, but the entry pins x to
        // (0x20, 0x80), where one increment neither wraps nor decreases.
        let smt = CHAIN
            .replace("(bvugt x #x0a)", "(and (bvugt x #x20) (bvult x #x80))")
            .replace("(bvult x #x20)", "(bvult x #x0c)");
        assert!(!certified(&smt));
    }

    #[test]
    fn a_site_reachable_only_through_bit_vector_wraparound_is_certified() {
        // x > 0x20, then x + 1 < 0x0c: only x = 0xff reaches bb2 (0xff + 1 wraps
        // to 0x00). The evaluator's modular arithmetic must agree.
        let smt = CHAIN
            .replace("(bvugt x #x0a)", "(bvugt x #x20)")
            .replace("(bvult x #x20)", "(bvult x #x0c)");
        assert!(certified(&smt));
    }

    #[test]
    fn a_bare_nullary_site_is_certified_through_its_derivation() {
        let smt = "\
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-rel f__bb0 ((_ BitVec 8)))
(declare-rel f__bb6 ())
(declare-rel ay_vacuity_reach ())
(rule (=> true (f__bb0 x)))
(rule (=> (and (f__bb0 x) (= x #x07)) f__bb6))
(rule (=> f__bb6 ay_vacuity_reach))
(query ay_vacuity_reach)
";
        assert!(certified(smt));
    }

    #[test]
    fn an_underivable_nullary_site_is_never_certified() {
        let smt = "\
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-rel f__bb0 ((_ BitVec 8)))
(declare-rel f__bb6 ())
(declare-rel ay_vacuity_reach ())
(rule (=> true (f__bb0 x)))
(rule (=> f__bb6 ay_vacuity_reach))
(query ay_vacuity_reach)
";
        assert!(!certified(smt));
    }

    #[test]
    fn signed_and_shift_guards_are_certified_when_satisfiable() {
        let smt = "\
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 16))
(declare-rel f__bb0 ((_ BitVec 8)))
(declare-rel f__bb1 ((_ BitVec 16)))
(declare-rel ay_vacuity_reach ())
(rule (=> (bvslt x #x00) (f__bb0 x)))
(rule (=> (and (f__bb0 x) (= y ((_ sign_extend 8) x)) (bvslt y (bvshl #x0001 #x0004))) (f__bb1 y)))
(rule (=> (f__bb1 y) ay_vacuity_reach))
(query ay_vacuity_reach)
";
        assert!(certified(smt));
    }

    #[test]
    fn an_array_site_is_certified_through_select_and_store() {
        let smt = "\
(set-logic HORN)
(declare-var a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-var b (Array (_ BitVec 8) (_ BitVec 8)))
(declare-var i (_ BitVec 8))
(declare-rel f__bb0 ((Array (_ BitVec 8) (_ BitVec 8))))
(declare-rel f__bb1 ((Array (_ BitVec 8) (_ BitVec 8))))
(declare-rel ay_vacuity_reach ())
(rule (=> (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00)) (f__bb0 a)))
(rule (=> (and (f__bb0 a) (= b (store a #x03 #x2a))) (f__bb1 b)))
(rule (=> (and (f__bb1 a) (= (select a #x03) #x2a)) ay_vacuity_reach))
(query ay_vacuity_reach)
";
        assert!(certified(smt));
        // The store wrote 0x2a; a site that needs 0x2b behind it is unreachable.
        assert!(!certified(&smt.replace("(= (select a #x03) #x2a)", "(= (select a #x03) #x2b)")));
    }

    #[test]
    fn an_unevaluable_term_is_never_certified() {
        // The evaluator reads no uninterpreted function, so no assignment can
        // be checked, however satisfiable the guard is.
        let smt = "\
(set-logic HORN)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-var x (_ BitVec 8))
(declare-rel f__bb0 ((_ BitVec 8)))
(declare-rel ay_vacuity_reach ())
(rule (=> (= (g x) #x01) (f__bb0 x)))
(rule (=> (f__bb0 x) ay_vacuity_reach))
(query ay_vacuity_reach)
";
        let found = certified_reach_witness(smt, "ay_vacuity_reach", far());
        assert!(!matches!(found, WitnessSearch::Certified(_)), "got {found:?}");
    }

    /// ay-bindings' unsigned `u128` multiplication-overflow flag in the
    /// encoder's own rule shape (`__out` definitions, which the parser inlines
    /// into the head): the high half of a 256-bit product. With
    /// `a = (x ^ x) | 2^64` the product is 2^128, so the flag is ALWAYS set and
    /// the site behind `(not o)` is unreachable (the probe of
    /// `vacuity_u128_mul_overflow_flag_must_not_prove`; Kani: every check
    /// UNREACHABLE). The definitions pin every value without a solver, so this
    /// is the path on which an evaluator computing the 256-bit term in a `u128`
    /// decided the flag by itself: a shift-overflow panic under overflow
    /// checks, a certificate for an unreachable site without them.
    const U128_MUL_FLAG: &str = "\
(set-logic HORN)
(declare-var x (_ BitVec 128))
(declare-var a (_ BitVec 128))
(declare-var a__out (_ BitVec 128))
(declare-var o Bool)
(declare-var o__out Bool)
(declare-rel f__bb0 ((_ BitVec 128) (_ BitVec 128) Bool))
(declare-rel f__bb2 ((_ BitVec 128) (_ BitVec 128) Bool))
(declare-rel f__bb4 ((_ BitVec 128)))
(declare-rel ay_vacuity_reach ())
(rule (=> true (f__bb0 x a o)))
(rule (=> (and (and (f__bb0 x a o) \
(= a__out (bvor (bvxor x x) #x00000000000000010000000000000000))) \
(= o__out (not (= ((_ extract 255 128) (bvmul \
((_ zero_extend 128) (bvor (bvxor x x) #x00000000000000010000000000000000)) \
((_ zero_extend 128) #x00000000000000010000000000000000))) \
#x00000000000000000000000000000000)))) (f__bb2 x a__out o__out)))
(rule (=> (and (f__bb2 x a o) (not o)) (f__bb4 x)))
(rule (=> (f__bb4 x) ay_vacuity_reach))
(query ay_vacuity_reach)
";

    #[test]
    fn a_site_behind_a_u128_multiplication_overflow_flag_is_never_certified() {
        let found = certified_reach_witness(U128_MUL_FLAG, "ay_vacuity_reach", far());
        assert!(
            matches!(found, WitnessSearch::NotFound { reason, .. } if reason != "panicked"),
            "the 256-bit flag must be refused, not certified and not a panic: {found:?}"
        );
    }

    #[test]
    fn a_reachable_site_behind_the_u128_flag_falls_back_without_a_certificate() {
        // `a = 1`: the product fits, the flag is clear and the site IS
        // reachable. The evaluator cannot read the 256-bit term exactly, so
        // the search must answer "not found" (the external probe decides) —
        // never panic, which killed the driver on correct proofs.
        let smt = U128_MUL_FLAG.replace(
            "(bvor (bvxor x x) #x00000000000000010000000000000000)",
            "(bvor (bvxor x x) #x00000000000000000000000000000001)",
        );
        assert_ne!(smt, U128_MUL_FLAG);
        let found = certified_reach_witness(&smt, "ay_vacuity_reach", far());
        assert!(
            matches!(found, WitnessSearch::NotFound { reason, .. } if reason != "panicked"),
            "got {found:?}"
        );
    }

    #[test]
    fn a_panic_inside_the_search_is_not_found_not_a_crash() {
        let found = isolate_panics(|| panic!("an evaluator or embedded-solver bug"));
        assert_eq!(found, WitnessSearch::NotFound { reason: "panicked", smt_checks: 0 });
        let passed =
            isolate_panics(|| WitnessSearch::NotFound { reason: "exhausted", smt_checks: 2 });
        assert_eq!(passed, WitnessSearch::NotFound { reason: "exhausted", smt_checks: 2 });
    }

    #[test]
    fn a_missing_target_or_unparseable_text_is_not_found() {
        assert_eq!(
            certified_reach_witness(CHAIN, "no_such_relation", far()),
            WitnessSearch::NotFound { reason: "no-target", smt_checks: 0 }
        );
        assert_eq!(
            certified_reach_witness("(rule", "ay_vacuity_reach", far()),
            WitnessSearch::NotFound { reason: "parse-refused", smt_checks: 0 }
        );
    }

    #[test]
    fn a_spent_slice_answers_not_found() {
        let spent = Deadline::after(Duration::ZERO);
        assert!(matches!(
            certified_reach_witness(CHAIN, "ay_vacuity_reach", spent),
            WitnessSearch::NotFound { reason: "slice-spent", .. }
        ));
    }

    #[test]
    fn the_certificate_rejects_an_assignment_that_violates_a_constraint() {
        let x = || ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)));
        let constraints = vec![ChcExpr::eq(x(), ChcExpr::BitVec(3, 8))];
        let wrong = HashMap::from([("x".to_string(), SmtValue::BitVec(4, 8))]);
        assert!(!assignment_certifies(&constraints, &wrong));
        let right = HashMap::from([("x".to_string(), SmtValue::BitVec(3, 8))]);
        assert!(assignment_certifies(&constraints, &right));
        // An empty model is completed through the definition itself.
        assert!(assignment_certifies(&constraints, &HashMap::new()));
    }

    #[test]
    fn index_combinations_cover_the_product_once() {
        let all: Vec<_> = IndexCombinations::new(vec![2, 3]).collect();
        assert_eq!(all.len(), 6);
        assert_eq!(all.iter().collect::<HashSet<_>>().len(), 6);
        assert_eq!(IndexCombinations::new(vec![]).collect::<Vec<_>>(), vec![Vec::<usize>::new()]);
        assert_eq!(IndexCombinations::new(vec![2, 0]).count(), 0);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Whether an error relation DEPENDS on a value no clause defines
//! (fix/chc-false-certificates review follow-up, 2026-09-27).
//!
//! [`super::havoc_reads`] finds the freed values of a CHC system: reads of
//! state no clause writes, and reads a clause does not bind. A counterexample
//! that needs one of them is not evidence of a real failure. The first version
//! of the gate refused every counterexample with such a read anywhere in the
//! violated check's backward cone, and its cut-system replay gave up whenever a
//! relation slot carried a freed value in one clause and a computed value in
//! another. In straight-line code the cone of a check holds every earlier
//! block, so a real, data-independent bug downstream of an unrelated freed read
//! lost its `Genuine` label (review probe `g7_unattr_real_bug.rs`).
//!
//! This module traces where freed values can FLOW:
//!
//! - a slot (relation, position) is tainted when some clause writes a tainted
//!   value into it (a head argument that mentions one);
//! - in a clause, a variable is tainted when it is freed, sits in a tainted
//!   body slot, or is DEFINED (`(= v rhs)`, `v` bound by no body predicate) from
//!   a tainted right-hand side.
//!
//! A clause whose only tainted mentions are such definitions (each tainted
//! variable defined once, acyclically) and tainted head slots merely CARRIES
//! freed values: its constraint holds for every value of them. Any other
//! tainted mention — a guard, a second definition of the same variable, a
//! tainted variable in an untainted slot — makes the clause DEPENDENT.
//!
//! The cut system drops every tainted slot, every carrying definition and every
//! dependent clause. Removing constraints and slots from a clause that only
//! carries freed values changes nothing a derivation needs: given a derivation
//! of the cut system, and ANY values of the freed reads, the tainted slots are
//! computed forward through their definitions, and every kept constraint holds
//! because it mentions no tainted variable. So:
//!
//! - when no clause in the target's backward cone is dependent, EVERY
//!   derivation of the target in the original system is one for every value of
//!   the freed reads, and the solver's counterexample is real
//!   ([`Independence::Independent`]);
//! - otherwise a derivation of the target in the cut system, found by the exact
//!   acyclic composer and REPLAYED against a second, independently built copy
//!   ([`replay_error_derivation_tainted`]), is one of the original system for
//!   every value of the freed reads.
//!
//! A guard that reads a tainted variable but is a TAUTOLOGY (its negation is
//! UNSAT, decided by the SMT context within a small budget) constrains
//! nothing, so it does not make its clause dependent:
//! `assert!(v as u16 <= 255)` on a `v: u8` copied from an unwritten cell is
//! the `g7_unattr_real_bug.rs` shape.
//!
//! Slot taint is path-insensitive: a slot fed by a freed value on one path and
//! a computed value on another taints every reader. The second cut strategy,
//! [`Strategy::DropSources`], keeps such readers: it removes every clause that
//! reads a freed value at all (a copy into another slot included) and drops
//! only the slots that never carry anything else, the construction of
//! [`super::freed_var_replay`]. The gate tries both.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::time::{Duration, Instant};

use ay_chc::{
    ChcExpr, ChcOp, ChcParser, ChcProblem, ClauseBody, ClauseHead, HornClause, PredicateId,
    SmtContext,
};

use super::{AcyclicDecision, acyclic_direct_smt_decision, replay_acyclic_direct_smt_witness};

/// Per-query budget of a tautology check.
const TAUTOLOGY_QUERY_TIMEOUT: Duration = Duration::from_millis(250);

/// Total budget of tautology checks for one certification.
const TAUTOLOGY_TOTAL_BUDGET: Duration = Duration::from_secs(5);

/// How the cut system handles a freed value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Strategy {
    /// Keep clauses that only carry a freed value through definitions and
    /// slots; drop the tainted slots and the clauses that depend on it.
    Carry,
    /// Drop every clause that reads a freed value; drop only the slots that
    /// never carry anything else.
    DropSources,
}

/// Decides whether a guard is a tautology, with a cache and a total budget.
pub(super) struct Tautologies {
    smt: SmtContext,
    cache: HashMap<String, bool>,
    started: Option<Instant>,
}

impl Tautologies {
    pub(super) fn new() -> Self {
        Self { smt: SmtContext::new(), cache: HashMap::new(), started: None }
    }

    /// Whether `conjunct` holds for every value of its variables: its negation
    /// is definitively UNSAT. Anything undecided, or past the budget, is
    /// `false` (the clause stays dependent: fail closed).
    fn holds(&mut self, conjunct: &ChcExpr) -> bool {
        let key = format!("{conjunct:?}");
        if let Some(known) = self.cache.get(&key) {
            return *known;
        }
        let started = *self.started.get_or_insert_with(Instant::now);
        if started.elapsed() >= TAUTOLOGY_TOTAL_BUDGET {
            return false;
        }
        self.smt.reset();
        let valid = self
            .smt
            .check_sat_with_timeout(&ChcExpr::not(conjunct.clone()), TAUTOLOGY_QUERY_TIMEOUT)
            .is_unsat();
        self.cache.insert(key, valid);
        valid
    }
}

/// Clause ceiling for the cut system (the same as the freed-var replay).
const MAX_CUT_CLAUSES: usize = 4096;

/// Name of the aggregate error relation every `error_pN` feeds.
const AGGREGATE_ERROR: &str = "error";

/// The freed values of one system.
pub(super) struct FreedReads<'a> {
    /// Normalized state names whose every occurrence (either spelling, and a
    /// scalarized cell of the array) is a freed value: state no clause writes.
    pub names: &'a BTreeSet<String>,
    /// Variables freed in one clause only (an unbound read), by clause index.
    pub clause_local: &'a HashMap<usize, BTreeSet<String>>,
}

impl FreedReads<'_> {
    fn is_freed_name(&self, name: &str) -> bool {
        let own = trust_mc_core::chc::normalize_approx_var(name);
        if self.names.contains(own) {
            return true;
        }
        trust_mc_core::chc::scalarized_cell_parent(own).is_some_and(|p| self.names.contains(p))
    }
}

/// How the cut system treats one clause.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ClausePlan {
    /// Reads a freed value where a derivation depends on it: removed.
    Dependent(&'static str),
    /// Kept, without these top-level conjuncts (definitions of tainted
    /// variables) and without its tainted slots.
    Kept(Vec<usize>),
}

/// The taint of a system's freed values.
pub(super) struct Taint {
    positions: HashSet<(PredicateId, usize)>,
    plans: Vec<ClausePlan>,
}

/// The verdict for one target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Independence {
    /// No clause in the target's backward cone depends on a freed value.
    Independent,
    /// These clauses (indices) in the cone depend on one.
    Dependent(Vec<usize>),
}

/// Every variable name `expr` mentions, or `None` for an unknown shape.
fn var_names(expr: &ChcExpr, names: &mut HashSet<String>) -> Option<()> {
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        match node {
            ChcExpr::Var(var) => {
                names.insert(var.name.clone());
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => pending.extend(args.iter().map(|arg| arg.as_ref())),
            ChcExpr::ConstArray(_, value) => pending.push(value.as_ref()),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
            _ => return None,
        }
    }
    Some(())
}

/// The top-level conjuncts of `expr` (`expr` itself when it is not an `and`).
pub(super) fn top_level_conjuncts(expr: &ChcExpr) -> Vec<&ChcExpr> {
    let mut out = Vec::new();
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        match node {
            ChcExpr::Op(ChcOp::And, args) => {
                // Keep source order: push in reverse.
                pending.extend(args.iter().rev().map(|arg| arg.as_ref()));
            }
            other => out.push(other),
        }
    }
    out
}

/// `(v, rhs)` when `conjunct` is `(= v rhs)` (or `(= rhs v)` with a
/// non-variable left side) and `v` is a variable no body predicate binds.
fn definition<'e>(
    conjunct: &'e ChcExpr,
    body_vars: &HashSet<String>,
) -> Option<(&'e str, &'e ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq, args) = conjunct else { return None };
    let [lhs, rhs] = args.as_slice() else { return None };
    match (lhs.as_ref(), rhs.as_ref()) {
        (ChcExpr::Var(v), rhs) if !body_vars.contains(&v.name) => Some((v.name.as_str(), rhs)),
        (lhs, ChcExpr::Var(v))
            if !matches!(lhs, ChcExpr::Var(_)) && !body_vars.contains(&v.name) =>
        {
            Some((v.name.as_str(), lhs))
        }
        _ => None,
    }
}

/// One top-level conjunct of a clause constraint, pre-digested.
struct Conjunct {
    expr: ChcExpr,
    vars: HashSet<String>,
    /// `(v, variables of rhs)` when the conjunct defines `v`.
    def: Option<(String, HashSet<String>)>,
}

/// One clause, pre-digested for the fixpoint.
struct ClauseInfo {
    /// Per body predicate: its id and the variables of each argument, with
    /// whether the argument is a bare variable.
    body: Vec<(PredicateId, Vec<(HashSet<String>, bool)>)>,
    body_vars: HashSet<String>,
    all_vars: HashSet<String>,
    conjuncts: Vec<Conjunct>,
    head: Option<(PredicateId, Vec<HashSet<String>>)>,
}

fn digest(problem: &ChcProblem) -> Option<Vec<ClauseInfo>> {
    let mut infos = Vec::with_capacity(problem.clauses().len());
    for clause in problem.clauses() {
        let mut body = Vec::with_capacity(clause.body.predicates.len());
        let mut body_vars = HashSet::new();
        for (pred, args) in &clause.body.predicates {
            let mut digested = Vec::with_capacity(args.len());
            for arg in args {
                let mut names = HashSet::new();
                var_names(arg, &mut names)?;
                body_vars.extend(names.iter().cloned());
                digested.push((names, matches!(arg, ChcExpr::Var(_))));
            }
            body.push((*pred, digested));
        }
        let mut all_vars = body_vars.clone();
        let mut conjuncts = Vec::new();
        if let Some(constraint) = &clause.body.constraint {
            for conjunct in top_level_conjuncts(constraint) {
                let mut vars = HashSet::new();
                var_names(conjunct, &mut vars)?;
                all_vars.extend(vars.iter().cloned());
                let def = match definition(conjunct, &body_vars) {
                    Some((v, rhs)) => {
                        let mut rhs_vars = HashSet::new();
                        var_names(rhs, &mut rhs_vars)?;
                        Some((v.to_string(), rhs_vars))
                    }
                    None => None,
                };
                conjuncts.push(Conjunct { expr: conjunct.clone(), vars, def });
            }
        }
        let head = match &clause.head {
            ClauseHead::Predicate(pred, args) => {
                let mut digested = Vec::with_capacity(args.len());
                for arg in args {
                    let mut names = HashSet::new();
                    var_names(arg, &mut names)?;
                    all_vars.extend(names.iter().cloned());
                    digested.push(names);
                }
                Some((*pred, digested))
            }
            _ => None,
        };
        infos.push(ClauseInfo { body, body_vars, all_vars, conjuncts, head });
    }
    Some(infos)
}

/// The tainted variables of one clause under the slot taint `positions`.
fn clause_taint(
    info: &ClauseInfo,
    index: usize,
    positions: &HashSet<(PredicateId, usize)>,
    freed: &FreedReads<'_>,
) -> HashSet<String> {
    let mut tainted: HashSet<String> = HashSet::new();
    for (pred, args) in &info.body {
        for (i, (names, _)) in args.iter().enumerate() {
            if positions.contains(&(*pred, i)) {
                tainted.extend(names.iter().cloned());
            }
        }
    }
    tainted.extend(info.all_vars.iter().filter(|name| freed.is_freed_name(name)).cloned());
    if let Some(local) = freed.clause_local.get(&index) {
        tainted.extend(local.iter().cloned());
    }
    loop {
        let before = tainted.len();
        for conjunct in &info.conjuncts {
            if let Some((v, rhs_vars)) = &conjunct.def
                && !tainted.contains(v)
                && rhs_vars.iter().any(|name| tainted.contains(name))
            {
                tainted.insert(v.clone());
            }
        }
        if tainted.len() == before {
            return tainted;
        }
    }
}

/// Whether the definitions `defs` (variable, right-hand-side variables) are
/// acyclic among themselves.
fn defs_acyclic(defs: &[(&str, &HashSet<String>)]) -> bool {
    let mut remaining: HashSet<&str> = defs.iter().map(|(v, _)| *v).collect();
    loop {
        let ready: Vec<&str> = defs
            .iter()
            .filter(|(v, rhs)| {
                remaining.contains(v) && rhs.iter().all(|n| !remaining.contains(n.as_str()))
            })
            .map(|(v, _)| *v)
            .collect();
        if ready.is_empty() {
            return remaining.is_empty();
        }
        for v in ready {
            remaining.remove(v);
        }
    }
}

/// The plan for one clause given its tainted variables. A guard over a
/// tainted variable is removed when `tautologies` proves it holds for every
/// value; without an oracle (a clause outside every target's cone) it makes
/// the clause dependent.
fn clause_plan(
    info: &ClauseInfo,
    positions: &HashSet<(PredicateId, usize)>,
    tainted: &HashSet<String>,
    mut tautologies: Option<&mut Tautologies>,
) -> ClausePlan {
    let hits = |names: &HashSet<String>| names.iter().any(|n| tainted.contains(n));
    for (pred, args) in &info.body {
        for (i, (names, is_var)) in args.iter().enumerate() {
            let slot_tainted = positions.contains(&(*pred, i));
            if !slot_tainted && hits(names) {
                return ClausePlan::Dependent("a tainted variable in an untainted body slot");
            }
            if slot_tainted && !is_var {
                return ClausePlan::Dependent("a compound argument in a tainted body slot");
            }
        }
    }
    let mut removed = Vec::new();
    let mut defs: Vec<(&str, &HashSet<String>)> = Vec::new();
    for (k, conjunct) in info.conjuncts.iter().enumerate() {
        if !hits(&conjunct.vars) {
            continue;
        }
        match &conjunct.def {
            Some((v, rhs)) if tainted.contains(v) && !info.body_vars.contains(v) => {
                if defs.iter().any(|(seen, _)| *seen == v.as_str()) {
                    return ClausePlan::Dependent("a tainted variable defined twice");
                }
                defs.push((v.as_str(), rhs));
                removed.push(k);
            }
            _ => {
                if tautologies.as_deref_mut().is_some_and(|oracle| oracle.holds(&conjunct.expr)) {
                    removed.push(k);
                } else {
                    return ClausePlan::Dependent("a guard reads a tainted variable");
                }
            }
        }
    }
    if !defs_acyclic(&defs) {
        return ClausePlan::Dependent("tainted definitions form a cycle");
    }
    if let Some((pred, args)) = &info.head {
        for (i, names) in args.iter().enumerate() {
            if !positions.contains(&(*pred, i)) && hits(names) {
                return ClausePlan::Dependent("a tainted value in an untainted head slot");
            }
        }
    }
    ClausePlan::Kept(removed)
}

/// The relations some derivation can reach: produced, to a fixpoint, by a
/// clause whose body relations are all derivable. A clause over any other
/// relation never fires, so it depends on nothing.
fn derivable_relations(problem: &ChcProblem) -> HashSet<PredicateId> {
    let mut live: HashSet<PredicateId> = HashSet::new();
    loop {
        let before = live.len();
        for clause in problem.clauses() {
            if let ClauseHead::Predicate(head, _) = &clause.head
                && clause.body.predicates.iter().all(|(pred, _)| live.contains(pred))
            {
                live.insert(*head);
            }
        }
        if live.len() == before {
            return live;
        }
    }
}

/// Trace the freed values of `problem` (module documentation) under the
/// [`Strategy::Carry`] strategy. Guards are checked for tautology only in
/// clauses whose head is in `relevant`.
pub(super) fn analyze(
    problem: &ChcProblem,
    freed: &FreedReads<'_>,
    relevant: &HashSet<PredicateId>,
    tautologies: &mut Tautologies,
) -> Result<Taint, String> {
    let infos = digest(problem)
        .ok_or_else(|| "unrecognized expression shape while tracing freed values".to_string())?;
    // Clauses by body relation, to revisit only what a new slot can reach.
    let mut readers: HashMap<PredicateId, Vec<usize>> = HashMap::new();
    for (index, info) in infos.iter().enumerate() {
        for (pred, _) in &info.body {
            readers.entry(*pred).or_default().push(index);
        }
    }
    let mut positions: HashSet<(PredicateId, usize)> = HashSet::new();
    let mut pending: Vec<usize> = (0..infos.len()).collect();
    let mut queued: HashSet<usize> = pending.iter().copied().collect();
    while let Some(index) = pending.pop() {
        queued.remove(&index);
        let info = &infos[index];
        let tainted = clause_taint(info, index, &positions, freed);
        let Some((pred, args)) = &info.head else { continue };
        for (i, names) in args.iter().enumerate() {
            if names.iter().any(|n| tainted.contains(n)) && positions.insert((*pred, i)) {
                for reader in readers.get(pred).into_iter().flatten() {
                    if queued.insert(*reader) {
                        pending.push(*reader);
                    }
                }
            }
        }
    }
    let derivable = derivable_relations(problem);
    let mut plans = Vec::with_capacity(infos.len());
    for (index, info) in infos.iter().enumerate() {
        if info.body.iter().any(|(pred, _)| !derivable.contains(pred)) {
            plans.push(ClausePlan::Kept(Vec::new()));
            continue;
        }
        let tainted = clause_taint(info, index, &positions, freed);
        let in_cone = info.head.as_ref().is_some_and(|(pred, _)| relevant.contains(pred));
        plans.push(clause_plan(info, &positions, &tainted, in_cone.then_some(&mut *tautologies)));
    }
    Ok(Taint { positions, plans })
}

/// The [`Strategy::DropSources`] plan: the slots whose every head argument is
/// a freed name carried bare are dropped, and every clause that mentions a
/// freed value anywhere else is removed.
fn analyze_drop_sources(problem: &ChcProblem, freed: &FreedReads<'_>) -> Result<Taint, String> {
    let infos = digest(problem)
        .ok_or_else(|| "unrecognized expression shape while tracing freed values".to_string())?;
    let mut seen: HashSet<(PredicateId, usize)> = HashSet::new();
    let mut impure: HashSet<(PredicateId, usize)> = HashSet::new();
    for (clause, info) in problem.clauses().iter().zip(&infos) {
        let (ClauseHead::Predicate(pred, args), Some(_)) = (&clause.head, &info.head) else {
            continue;
        };
        for (i, arg) in args.iter().enumerate() {
            seen.insert((*pred, i));
            if !matches!(arg, ChcExpr::Var(var) if freed.is_freed_name(&var.name)) {
                impure.insert((*pred, i));
            }
        }
    }
    let positions: HashSet<(PredicateId, usize)> = seen.difference(&impure).copied().collect();
    let derivable = derivable_relations(problem);
    let mut plans = Vec::with_capacity(infos.len());
    for (index, info) in infos.iter().enumerate() {
        if info.body.iter().any(|(pred, _)| !derivable.contains(pred)) {
            plans.push(ClausePlan::Kept(Vec::new()));
            continue;
        }
        let mut tainted = clause_taint(info, index, &positions, freed);
        // No definition carries a freed value in this strategy: only the freed
        // names, the clause-local reads and the dropped slots' variables.
        tainted.retain(|name| {
            freed.is_freed_name(name)
                || freed.clause_local.get(&index).is_some_and(|local| local.contains(name))
                || info.body.iter().any(|(pred, args)| {
                    args.iter().enumerate().any(|(i, (names, _))| {
                        positions.contains(&(*pred, i)) && names.contains(name)
                    })
                })
        });
        let hits = |names: &HashSet<String>| names.iter().any(|n| tainted.contains(n));
        let body_ok = info.body.iter().all(|(pred, args)| {
            args.iter()
                .enumerate()
                .all(|(i, (names, _))| positions.contains(&(*pred, i)) || !hits(names))
        });
        let head_ok = info.head.as_ref().is_none_or(|(pred, args)| {
            args.iter()
                .enumerate()
                .all(|(i, names)| positions.contains(&(*pred, i)) || !hits(names))
        });
        let constraint_ok = info.conjuncts.iter().all(|conjunct| !hits(&conjunct.vars));
        plans.push(if body_ok && head_ok && constraint_ok {
            ClausePlan::Kept(Vec::new())
        } else {
            ClausePlan::Dependent("the clause reads a freed value")
        });
    }
    Ok(Taint { positions, plans })
}

/// The relations that can contribute to deriving `target`.
pub(super) fn backward_cone(problem: &ChcProblem, target: PredicateId) -> HashSet<PredicateId> {
    let mut live: HashSet<PredicateId> = HashSet::from([target]);
    loop {
        let before = live.len();
        for clause in problem.clauses() {
            if let ClauseHead::Predicate(head, _) = &clause.head
                && live.contains(head)
            {
                live.extend(clause.body.predicates.iter().map(|(pred, _)| *pred));
            }
        }
        if live.len() == before {
            return live;
        }
    }
}

impl Taint {
    /// Whether `target`'s derivations depend on a freed value.
    pub(super) fn independence(&self, problem: &ChcProblem, target: PredicateId) -> Independence {
        let cone = backward_cone(problem, target);
        let dependent: Vec<usize> = problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(index, clause)| {
                matches!(&clause.head, ClauseHead::Predicate(head, _) if cone.contains(head))
                    && matches!(self.plans[*index], ClausePlan::Dependent(_))
            })
            .map(|(index, _)| index)
            .collect();
        if dependent.is_empty() {
            Independence::Independent
        } else {
            Independence::Dependent(dependent)
        }
    }

    /// Why clause `index` depends on a freed value, if it does.
    pub(super) fn dependence_reason(&self, index: usize) -> Option<&'static str> {
        match self.plans.get(index) {
            Some(ClausePlan::Dependent(why)) => Some(why),
            _ => None,
        }
    }
}

/// Build the cut system for `target` under `strategy` (module documentation).
fn tainted_cut_problem(
    chc_text: &str,
    target: &str,
    freed: &FreedReads<'_>,
    strategy: Strategy,
    tautologies: &mut Tautologies,
) -> Result<ChcProblem, String> {
    let parsed =
        ChcParser::parse(chc_text).map_err(|error| format!("CHC parse failed: {error}"))?;
    let target_id = parsed
        .lookup_predicate(target)
        .ok_or_else(|| format!("the system declares no relation `{target}`"))?;
    if parsed.get_predicate(target_id).is_none_or(|pred| !pred.arg_sorts.is_empty()) {
        return Err(format!("`{target}` is not a nullary error relation"));
    }
    let taint = match strategy {
        Strategy::Carry => {
            analyze(&parsed, freed, &backward_cone(&parsed, target_id), tautologies)?
        }
        Strategy::DropSources => analyze_drop_sources(&parsed, freed)?,
    };
    let mut cut = ChcProblem::new();
    for (pred, decl) in parsed.predicates().iter().enumerate() {
        let id = PredicateId::new(pred as u32);
        let sorts = decl
            .arg_sorts
            .iter()
            .enumerate()
            .filter(|(i, _)| !taint.positions.contains(&(id, *i)))
            .map(|(_, sort)| sort.clone())
            .collect();
        if cut.declare_predicate(decl.name.clone(), sorts).index() != pred {
            return Err("predicate ids moved while rebuilding the system".to_string());
        }
    }
    let project = |pred: PredicateId, args: &[ChcExpr]| -> Vec<ChcExpr> {
        args.iter()
            .enumerate()
            .filter(|(i, _)| !taint.positions.contains(&(pred, *i)))
            .map(|(_, arg)| arg.clone())
            .collect()
    };
    let aggregate = parsed.lookup_predicate(AGGREGATE_ERROR);
    let mut kept_clauses = Vec::new();
    for (index, clause) in parsed.clauses().iter().enumerate() {
        let ClausePlan::Kept(removed) = &taint.plans[index] else { continue };
        let head = match &clause.head {
            ClauseHead::False => continue,
            ClauseHead::Predicate(pred, _) if Some(*pred) == aggregate && *pred != target_id => {
                continue;
            }
            ClauseHead::Predicate(pred, args) => ClauseHead::Predicate(*pred, project(*pred, args)),
            _ => return Err("unrecognized clause head shape".to_string()),
        };
        let constraint = clause.body.constraint.as_ref().and_then(|constraint| {
            let kept: Vec<ChcExpr> = top_level_conjuncts(constraint)
                .into_iter()
                .enumerate()
                .filter(|(k, _)| !removed.contains(k))
                .map(|(_, conjunct)| conjunct.clone())
                .collect();
            match kept.len() {
                0 => None,
                1 => kept.into_iter().next(),
                _ => Some(ChcExpr::Op(
                    ChcOp::And,
                    kept.into_iter().map(std::sync::Arc::new).collect(),
                )),
            }
        });
        let body = clause
            .body
            .predicates
            .iter()
            .map(|(pred, args)| (*pred, project(*pred, args)))
            .collect();
        kept_clauses.push(HornClause::new(ClauseBody::new(body, constraint), head));
    }
    let mut live: HashSet<PredicateId> = HashSet::from([target_id]);
    loop {
        let before = live.len();
        for clause in &kept_clauses {
            if let ClauseHead::Predicate(head, _) = &clause.head
                && live.contains(head)
            {
                live.extend(clause.body.predicates.iter().map(|(pred, _)| *pred));
            }
        }
        if live.len() == before {
            break;
        }
    }
    let mut count = 0usize;
    for clause in kept_clauses {
        if matches!(&clause.head, ClauseHead::Predicate(head, _) if live.contains(head)) {
            count += 1;
            if count > MAX_CUT_CLAUSES {
                return Err(format!("the cut system exceeds {MAX_CUT_CLAUSES} clauses"));
            }
            cut.add_clause(clause);
        }
    }
    cut.add_clause(HornClause::new(
        ClauseBody::new(vec![(target_id, Vec::new())], None),
        ClauseHead::False,
    ));
    Ok(cut)
}

/// Replay-validate that `target` (a nullary error relation: an `error_pN`, or
/// the aggregate `error` when the counterexample names no check) derives in
/// the cut system of `chc_text` under `freed` (module documentation). `Ok`
/// carries a one-line summary; every other outcome is an error.
pub(super) fn replay_error_derivation_tainted(
    chc_text: &str,
    target: &str,
    freed: &FreedReads<'_>,
    strategy: Strategy,
    tautologies: &mut Tautologies,
) -> Result<String, String> {
    let producer = tainted_cut_problem(chc_text, target, freed, strategy, tautologies)?;
    let witness = match acyclic_direct_smt_decision(&producer) {
        AcyclicDecision::Unsafe(witness) => witness,
        AcyclicDecision::Safe => {
            return Err(format!(
                "`{target}` is underivable once the clauses that depend on a freed value are removed"
            ));
        }
        AcyclicDecision::Inconclusive => {
            return Err(format!("the cut system for `{target}` is cyclic, nonlinear or undecided"));
        }
    };
    let consumer = tainted_cut_problem(chc_text, target, freed, strategy, tautologies)?;
    replay_acyclic_direct_smt_witness(&consumer, &witness)?;
    Ok(format!(
        "`{target}` replayed on a fresh {strategy:?} cut system without the clauses that depend \
         on {} freed name(s) and {} clause-local read(s) ({} clauses on the derivation)",
        freed.names.len(),
        freed.clause_local.values().map(BTreeSet::len).sum::<usize>(),
        witness.derivation_clause_indices.len()
    ))
}

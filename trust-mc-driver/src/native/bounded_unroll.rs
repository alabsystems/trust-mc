// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! k-bounded CHC unrolling — the REFUTATION-ONLY escalation lane for cyclic
//! typed CHC problems (loop bodies).
//!
//! ## Why this exists
//!
//! A loop-carried safety obligation (e.g. an accumulator overflow reachable
//! only after N iterations) lowers to a CYCLIC CHC system. PDR must synthesize
//! an invariant to prove it and must find a bounded trace to refute it; on
//! BV-heavy loop problems it frequently does neither within budget, so the
//! obligation dies as Unknown even when a genuine counterexample exists a few
//! iterations in. The acyclic direct-SMT composer
//! (`crate::direct_smt_cex::acyclic_direct_smt_decision`) already produces
//! concrete, machine-checked witness models — but only for acyclic problems.
//! This module bridges the gap: it builds an ACYCLIC under-approximation of a
//! cyclic problem so the existing composer can search for a real
//! counterexample through up to `k` loop iterations.
//!
//! ## Construction (predicate-renaming unroll)
//!
//! For levels `0..=k`, every predicate `P` gets a per-level copy `P@l`. Every
//! original clause is copied per level with ONLY its predicates re-labeled:
//!
//! - a clause whose body→head edge is a DFS *retreating* (back) edge of the
//!   predicate dependency graph advances the level (`P@l -> Q@(l+1)`);
//! - every other clause stays within its level (`P@l -> Q@l`);
//! - the level-`k` copies of back-edge clauses are DROPPED — the (k+1)-th
//!   back-edge traversal is unrepresented, exactly an `assume false` on that
//!   edge;
//! - entry facts (no body predicate) are emitted at level 0 only; queries
//!   (`false` heads) are emitted at every level.
//!
//! Constraints, arguments, and variables are copied byte-for-byte (CHC
//! variables are clause-local, so no renaming is needed or performed).
//!
//! ## Soundness (load-bearing)
//!
//! REFUTATION direction: every unrolled clause is one original clause with its
//! predicates renamed, so ERASING the levels maps any derivation of the
//! unrolled system 1:1 onto a derivation of the ORIGINAL system. A satisfiable
//! derivation of the query target found on the unrolled problem is therefore a
//! real counterexample of the original problem — the soundness of a witness
//! does NOT rest on the back-edge classification or on any semantic argument
//! about loops, only on this syntactic projection.
//!
//! PROOF direction: the unrolled system is an UNDER-approximation — traces
//! needing more than `k` back-edge traversals are unrepresented — so finding
//! NO derivation proves NOTHING. Callers must never surface a `Safe` decision
//! obtained on an unrolled problem; the only admissible outcome of this lane
//! is `Unsafe(model)` (see `try_bounded_unroll_refutation_lane` in
//! `native.rs`, which enforces this structurally).
//!
//! Every input this transform does not model exactly declines (`None`), never
//! approximates: nonlinear clause bodies, fixedpoint polarity, stripped-forall
//! over-approximations, datatype definitions, action decompositions, reserved
//! name collisions, and unrecognized (`#[non_exhaustive]`) clause-head shapes
//! all fail closed.

use ay_chc::{ChcExpr, ChcOp, ChcProblem, ClauseBody, ClauseHead, HornClause};

/// Escalation ladder of back-edge budgets, cheapest first. Any rung's
/// `Unsafe` is a real counterexample regardless of the rung (see module
/// soundness note), so trying small `k` first only saves time — it can never
/// change a verdict. 64 covers a full pass over the common fixed-size-array
/// reduction shapes (`[T; 64]`) while keeping the composer's fact caps in
/// reach.
pub(crate) const BOUNDED_UNROLL_K_LADDER: [u32; 3] = [4, 16, 64];

/// Reserved marker embedded in every per-level predicate name. An input whose
/// predicate names already contain it declines: the level suffix must remain
/// injective (a collision could alias two distinct predicates and fabricate a
/// derivation that does not project back onto the original problem).
const UNROLL_LEVEL_MARKER: &str = "__trust_mc_bmc_unroll_l";

/// Hard construction ceilings shared by producer minting and consumer replay.
/// The production ladder multiplies the original graph by up to 65 levels;
/// decline before allocating when a retained input would exceed these exact
/// replay budgets.
const MAX_UNROLLED_PREDICATES: usize = 65_536;
const MAX_UNROLLED_CLAUSES: usize = 262_144;

/// Result of a successful k-bounded unroll.
pub(crate) struct BoundedUnrolledChc {
    /// The acyclic under-approximated problem (see module docs).
    pub(crate) problem: ChcProblem,
    /// The back-edge traversal budget the problem represents.
    pub(crate) k: u32,
}

/// Build the k-bounded acyclic under-approximation of a cyclic CHC problem.
///
/// Returns `None` — fail-closed, the caller keeps its Unknown — when the
/// problem is not in the exactly-modeled domain: already acyclic (nothing to
/// unroll; the direct-SMT lane handles it as-is), a nonlinear clause body, a
/// non-`False`/`Predicate` head shape, fixedpoint polarity, a stripped body
/// `forall`, datatype definitions, an action decomposition, a reserved-marker
/// name collision, or an arithmetic overflow while sizing the copies.
pub(crate) fn bounded_unroll_chc_for_refutation(
    problem: &ChcProblem,
    k: u32,
) -> Option<BoundedUnrolledChc> {
    // Only cyclic problems need unrolling; an acyclic problem is already in
    // the direct-SMT composer's domain and unrolling it would only duplicate
    // work (and clauses).
    if !problem.has_cycles() {
        return None;
    }
    // The direct-SMT composer admits only linear Horn clauses (≤1 body
    // predicate); a nonlinear body would also make the single back-edge
    // classification below ambiguous. Decline.
    if problem.clauses().iter().any(|clause| clause.body.predicates.len() > 1) {
        return None;
    }
    // Problem-level state the plain copy below would silently drop or
    // misinterpret. `fixedpoint_format` inverts sat/unsat polarity;
    // `stripped_body_forall` marks an over-approximated parse whose
    // counterexamples may be fabricated; datatype definitions would not be
    // re-declared on the copy; an action decomposition carries per-clause
    // `ActionId`s this copy does not preserve. All fail closed.
    if problem.is_fixedpoint_format()
        || problem.has_stripped_body_forall()
        || !problem.datatype_defs().is_empty()
        || problem.has_action_decomposition()
    {
        return None;
    }
    if problem.predicates().iter().any(|pred| pred.name.contains(UNROLL_LEVEL_MARKER)) {
        return None;
    }
    // GROUNDEDNESS (load-bearing refutation gate). The lowering accounting the
    // witness mint checks (`TypedChcLoweringAccounting`) covers only the
    // `ChcVc` -> ay-problem stage; the trust-ir -> `ChcVc` translation is
    // allowed to model an unresolvable value reference or a summarized total
    // call as a FRESH clause variable — a sound over-approximation for proofs
    // that makes a satisfying model potentially unreal (the model may assign
    // the free variable a value the program never produces; measured: a
    // dominance-referenced loop-carried block param encoded free let this lane
    // "refute" a safe `t += 1` loop before this gate existed). Decline the
    // whole problem unless every clause is grounded: outside the unique entry
    // fact at a dependency root,
    // every variable must be derivable from the body relation's arguments
    // through defining equalities.
    if !problem_is_grounded_for_refutation(problem) {
        return None;
    }

    let predicate_count = problem.predicates().len();
    let back_edges = dfs_retreating_edges(problem, predicate_count);

    let levels = (k as usize).checked_add(1)?;
    if predicate_count.checked_mul(levels)? > MAX_UNROLLED_PREDICATES
        || problem.clauses().len().checked_mul(levels)? > MAX_UNROLLED_CLAUSES
    {
        return None;
    }
    let mut unrolled = ChcProblem::new();
    // Per-level predicate copies: `level_predicates[level][original_index]`.
    let mut level_predicates = Vec::with_capacity(levels);
    for level in 0..levels {
        let mut row = Vec::with_capacity(predicate_count);
        for predicate in problem.predicates() {
            row.push(unrolled.declare_predicate(
                format!("{}{}{}", predicate.name, UNROLL_LEVEL_MARKER, level),
                predicate.arg_sorts.clone(),
            ));
        }
        level_predicates.push(row);
    }

    for level in 0..levels {
        for clause in problem.clauses() {
            // Entry facts (no body predicate) seed derivations; a derivation
            // enters the level structure at level 0 and only back edges
            // advance it, so level-0 facts are complete for the ≤k domain.
            if clause.body.predicates.is_empty() && level > 0 {
                continue;
            }
            let body_predicates: Vec<_> = clause
                .body
                .predicates
                .iter()
                .map(|(id, args)| (level_predicates[level][id.index()], args.clone()))
                .collect();
            let head = match &clause.head {
                // Queries keep their `false` head at every level: a violation
                // reached after any ≤k back-edge traversals must stay a query.
                ClauseHead::False => ClauseHead::False,
                ClauseHead::Predicate(id, args) => {
                    let is_back_edge =
                        clause.body.predicates.first().is_some_and(|(body, _)| {
                            back_edges.contains(&(body.index(), id.index()))
                        });
                    let head_level = if is_back_edge { level + 1 } else { level };
                    if head_level >= levels {
                        // Truncation: the (k+1)-th back-edge traversal is
                        // unrepresented — semantically `assume false` on that
                        // edge. Under-approximation only; see module docs.
                        continue;
                    }
                    ClauseHead::Predicate(level_predicates[head_level][id.index()], args.clone())
                }
                // `ClauseHead` is #[non_exhaustive]; an unrecognized future
                // head shape cannot be re-labeled faithfully — decline.
                _ => return None,
            };
            unrolled.add_clause(HornClause::new(
                ClauseBody::new(body_predicates, clause.body.constraint.clone()),
                head,
            ));
        }
    }

    // The construction is acyclic by design (retreating edges strictly
    // increase the level; the retained same-level edges are the DFS forest
    // minus its retreating edges, which is acyclic). Verify anyway: an
    // acyclicity bug here would push the composer out of its complete domain,
    // and the check is cheap. Fail closed.
    if unrolled.has_cycles() {
        return None;
    }

    Some(BoundedUnrolledChc { problem: unrolled, k })
}

/// Decide whether every clause of `problem` is GROUNDED, i.e. free of the
/// fresh-variable havoc the trust-ir -> `ChcVc` translation may introduce.
///
/// Rules, conservative by construction:
/// - Exactly ONE FACT clause (no body predicate) may exist. Its head must be a
///   predicate dependency root with no incoming transition edge. Its free
///   variables are then the function's entry inputs — a model choosing them
///   chooses a real input. A second fact, an unconditional query, or a fact
///   for an internal/loop predicate declines: the typed CHC problem does not
///   carry enough source identity to distinguish a real entry input from a
///   producer-introduced fresh value in any of those shapes.
/// - Every other clause starts from the body relation's ARGUMENT variables
///   (bound by the incoming derivation) and may extend the grounded set only
///   through defining equalities `(= v e)` among the constraint's top-level
///   conjuncts, where every variable of `e` is already grounded. When a
///   fixpoint of that rule leaves ANY variable of the clause (constraint or
///   head arguments) ungrounded, the value is a translation havoc and a
///   model over it need not correspond to a real execution — decline.
/// - Any expression node this walker does not recognize (`ChcExpr` is
///   `#[non_exhaustive]`) declines, and the walk is iterative with an explicit
///   node budget so adversarially deep terms fail closed instead of missing
///   variables (a missed variable would be silently treated as absent — the
///   unsound direction).
fn problem_is_grounded_for_refutation(problem: &ChcProblem) -> bool {
    let mut bodyless = problem.clauses().iter().filter(|clause| clause.body.predicates.is_empty());
    let Some(entry_fact) = bodyless.next() else {
        return false;
    };
    if bodyless.next().is_some() {
        return false;
    }
    let ClauseHead::Predicate(entry_predicate, entry_args) = &entry_fact.head else {
        // In particular, an unconditional query (`true -> false`) is not an
        // entry fact and cannot introduce program inputs.
        return false;
    };

    // The unique fact must seed a dependency root. A bodyless rule for a
    // predicate that is also derived by any transition can inject arbitrary
    // values into the middle of a real execution and fabricate a refutation.
    if problem.clauses().iter().any(|clause| {
        !clause.body.predicates.is_empty()
            && matches!(&clause.head, ClauseHead::Predicate(id, _) if id == entry_predicate)
    }) {
        return false;
    }

    // Even entry expressions must be fully inventoryable. Free variables are
    // allowed here, but an unrecognized node must not be able to hide one.
    if entry_fact
        .body
        .constraint
        .as_ref()
        .is_some_and(|constraint| collect_expr_vars(constraint).is_none())
        || entry_args.iter().any(|arg| collect_expr_vars(arg).is_none())
    {
        return false;
    }

    problem
        .clauses()
        .iter()
        .filter(|clause| !clause.body.predicates.is_empty())
        .all(clause_is_grounded_for_refutation)
}

/// Node budget for the iterative expression walks below. Far above anything
/// the native translator emits per clause; hitting it declines (fail-closed).
const GROUNDING_NODE_BUDGET: usize = 200_000;

fn clause_is_grounded_for_refutation(clause: &HornClause) -> bool {
    if clause.body.predicates.is_empty() {
        // The caller validates and excludes the unique entry fact before this
        // helper. No other bodyless shape is admissible.
        return false;
    }

    // Grounded seed: the body relation's argument variables. An argument that
    // is not a plain variable contributes its variables too — the incoming
    // fact constrains the whole argument term.
    // Identity includes the sort. Treating only the textual name as identity
    // would let a body argument `x:Int` accidentally ground an unrelated
    // free `x:Bool` in the same clause.
    let mut grounded: std::collections::BTreeSet<ay_chc::ChcVar> =
        std::collections::BTreeSet::new();
    for (_, args) in &clause.body.predicates {
        for arg in args {
            match collect_expr_vars(arg) {
                Some(vars) => grounded.extend(vars),
                None => return false,
            }
        }
    }

    // Top-level conjuncts of the constraint (flattening nested `and`s).
    let mut conjuncts: Vec<&ChcExpr> = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        let mut pending = vec![constraint];
        while let Some(expr) = pending.pop() {
            if conjuncts.len() + pending.len() > GROUNDING_NODE_BUDGET {
                return false;
            }
            match expr {
                ChcExpr::Op(ChcOp::And, args) => pending.extend(args.iter().map(AsRef::as_ref)),
                other => conjuncts.push(other),
            }
        }
    }

    // Fixpoint: a conjunct `(= v e)` (either orientation) grounds `v` once
    // every variable of `e` is grounded.
    loop {
        let mut changed = false;
        for conjunct in &conjuncts {
            let ChcExpr::Op(ChcOp::Eq, args) = conjunct else { continue };
            let [lhs, rhs] = args.as_slice() else { continue };
            for (var_side, def_side) in [(lhs, rhs), (rhs, lhs)] {
                let ChcExpr::Var(var) = var_side.as_ref() else { continue };
                if grounded.contains(var) {
                    continue;
                }
                let Some(def_vars) = collect_expr_vars(def_side) else { return false };
                if def_vars.iter().all(|variable| grounded.contains(variable)) {
                    grounded.insert(var.clone());
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Every variable anywhere in the clause must now be grounded.
    let mut clause_vars = Vec::new();
    for conjunct in &conjuncts {
        match collect_expr_vars(conjunct) {
            Some(vars) => clause_vars.extend(vars),
            None => return false,
        }
    }
    if let ClauseHead::Predicate(_, args) = &clause.head {
        for arg in args {
            match collect_expr_vars(arg) {
                Some(vars) => clause_vars.extend(vars),
                None => return false,
            }
        }
    }
    clause_vars.iter().all(|variable| grounded.contains(variable))
}

/// Collect every variable name in `expr` iteratively. `None` when the budget
/// is exceeded or an unrecognized (`#[non_exhaustive]`) node kind appears —
/// both fail closed, since a MISSED variable would be silently treated as
/// grounded/absent.
fn collect_expr_vars(expr: &ChcExpr) -> Option<Vec<ay_chc::ChcVar>> {
    let mut vars = Vec::new();
    let mut visited = 0usize;
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        visited += 1;
        if visited > GROUNDING_NODE_BUDGET {
            return None;
        }
        match node {
            ChcExpr::Var(var) => vars.push(var.clone()),
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                pending.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
            ChcExpr::ConstArray(_, value) => pending.push(value.as_ref()),
            // New expression shapes must opt in explicitly before the
            // grounding gate can trust its own variable inventory.
            _ => return None,
        }
    }
    Some(vars)
}

/// Classify the retreating (back) edges of the predicate dependency graph by
/// iterative DFS from every node in deterministic order.
///
/// An edge `u -> v` is retreating iff `v` is on the active DFS stack when the
/// edge is examined. Removing all retreating edges of a DFS forest leaves an
/// acyclic graph, so level-advancing exactly this set breaks every cycle.
/// Which edges are chosen affects only WHICH derivations fit inside a given
/// `k` (completeness of the bounded search), never the soundness of a found
/// witness — see the module docs.
fn dfs_retreating_edges(problem: &ChcProblem, predicate_count: usize) -> Vec<(usize, usize)> {
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); predicate_count];
    for (from, to) in problem.dependency_edges() {
        if from.index() < predicate_count && to.index() < predicate_count {
            successors[from.index()].push(to.index());
        }
    }

    const WHITE: u8 = 0; // unvisited
    const GRAY: u8 = 1; // on the active DFS stack
    const BLACK: u8 = 2; // finished
    let mut color = vec![WHITE; predicate_count];
    let mut retreating = Vec::new();

    for root in 0..predicate_count {
        if color[root] != WHITE {
            continue;
        }
        // Explicit stack of (node, next successor index) — no recursion, so
        // pathological predicate graphs cannot overflow the thread stack.
        let mut stack: Vec<(usize, usize)> = vec![(root, 0)];
        color[root] = GRAY;
        while let Some(&mut (node, ref mut next)) = stack.last_mut() {
            if let Some(&succ) = successors[node].get(*next) {
                *next += 1;
                match color[succ] {
                    GRAY => retreating.push((node, succ)),
                    WHITE => {
                        color[succ] = GRAY;
                        stack.push((succ, 0));
                    }
                    _ => {}
                }
            } else {
                color[node] = BLACK;
                stack.pop();
            }
        }
    }

    retreating.sort_unstable();
    retreating.dedup();
    retreating
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_chc::{ChcExpr, ChcSort, ChcVar};

    /// `entry -> loop(0)`, `loop(i) ∧ i < bound -> loop(i+1)`,
    /// `loop(i) ∧ i = target -> false`. The query is derivable iff
    /// `target < bound` and needs exactly `target` back-edge traversals.
    fn counter_loop_problem(bound: i128, target: i128) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("entry", vec![]);
        let looppred = problem.declare_predicate("loop", vec![ChcSort::Int]);
        let i = || ChcExpr::var(ChcVar::new("i", ChcSort::Int));
        problem
            .add_clause(HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(entry, vec![])));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(entry, vec![])], Some(ChcExpr::eq(i(), ChcExpr::int(0)))),
            ClauseHead::Predicate(looppred, vec![i()]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(looppred, vec![i()])],
                Some(ChcExpr::lt(i(), ChcExpr::int(bound))),
            ),
            ClauseHead::Predicate(looppred, vec![ChcExpr::add(i(), ChcExpr::int(1))]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(looppred, vec![i()])],
            Some(ChcExpr::eq(i(), ChcExpr::int(target))),
        )));
        problem
    }

    #[test]
    fn unrolled_problem_is_acyclic_and_budget_sized() {
        let problem = counter_loop_problem(100, 3);
        assert!(problem.has_cycles(), "fixture must be cyclic");
        let unrolled =
            bounded_unroll_chc_for_refutation(&problem, 4).expect("cyclic linear problem unrolls");
        assert!(!unrolled.problem.has_cycles(), "unroll output must be acyclic");
        assert_eq!(unrolled.k, 4);
        // 5 levels each of the entry and loop predicates.
        assert_eq!(unrolled.problem.predicates().len(), 10);
        // 1 fact (level 0 only) + 5 entry-to-loop clauses + 4 loop
        // transitions (level-4 back edge dropped) + 5 queries.
        assert_eq!(unrolled.problem.clauses().len(), 15);
    }

    #[test]
    fn acyclic_input_declines() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![ChcSort::Int]);
        let x = || ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        problem.add_clause(HornClause::fact(ChcExpr::eq(x(), ChcExpr::int(1)), p, vec![x()]));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(p, vec![x()])],
            Some(ChcExpr::gt(x(), ChcExpr::int(0))),
        )));
        assert!(!problem.has_cycles());
        assert!(bounded_unroll_chc_for_refutation(&problem, 4).is_none());
    }

    #[test]
    fn nonlinear_body_declines() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("p", vec![ChcSort::Int]);
        let x = || ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        problem.add_clause(HornClause::fact(ChcExpr::eq(x(), ChcExpr::int(0)), p, vec![x()]));
        // Self-loop to make it cyclic AND nonlinear (two body predicates).
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![x()]), (p, vec![x()])], None),
            ClauseHead::Predicate(p, vec![ChcExpr::add(x(), ChcExpr::int(1))]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(p, vec![x()])],
            Some(ChcExpr::gt(x(), ChcExpr::int(0))),
        )));
        assert!(bounded_unroll_chc_for_refutation(&problem, 4).is_none());
    }

    #[test]
    fn reserved_marker_collision_declines() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate(format!("p{UNROLL_LEVEL_MARKER}0"), vec![ChcSort::Int]);
        let x = || ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        problem.add_clause(HornClause::fact(ChcExpr::eq(x(), ChcExpr::int(0)), p, vec![x()]));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![x()])], None),
            ClauseHead::Predicate(p, vec![ChcExpr::add(x(), ChcExpr::int(1))]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(p, vec![x()])],
            Some(ChcExpr::gt(x(), ChcExpr::int(0))),
        )));
        assert!(problem.has_cycles());
        assert!(bounded_unroll_chc_for_refutation(&problem, 4).is_none());
    }

    #[test]
    fn witness_within_budget_is_found_and_beyond_budget_is_not_misreported() {
        // Reachable at 3 back edges: k=4 finds it via the direct-SMT composer.
        let reachable = counter_loop_problem(100, 3);
        let unrolled = bounded_unroll_chc_for_refutation(&reachable, 4).expect("unrolls");
        match crate::direct_smt_cex::acyclic_direct_smt_decision(&unrolled.problem) {
            crate::direct_smt_cex::AcyclicDecision::Unsafe(witness) => {
                assert!(
                    witness.model.is_object(),
                    "witness model is a concrete assignment: {}",
                    witness.model
                );
                crate::direct_smt_cex::replay_acyclic_direct_smt_witness(
                    &unrolled.problem,
                    &witness,
                )
                .expect("producer witness must independently replay");
            }
            other => panic!(
                "depth-3 violation must refute inside a k=4 unroll, got {}",
                match other {
                    crate::direct_smt_cex::AcyclicDecision::Safe => "Safe",
                    crate::direct_smt_cex::AcyclicDecision::Inconclusive => "Inconclusive",
                    crate::direct_smt_cex::AcyclicDecision::Unsafe(_) => unreachable!(),
                }
            ),
        }

        // Reachable only at 10 back edges: the k=4 prefix finds NO derivation.
        // The composer reports the truncated prefix exhaustively-safe — which
        // is exactly why the caller must never surface Safe from this lane.
        let deeper = counter_loop_problem(100, 10);
        let unrolled = bounded_unroll_chc_for_refutation(&deeper, 4).expect("unrolls");
        assert!(
            !matches!(
                crate::direct_smt_cex::acyclic_direct_smt_decision(&unrolled.problem),
                crate::direct_smt_cex::AcyclicDecision::Unsafe(_)
            ),
            "a violation beyond the unroll budget must not be refuted at that budget"
        );
    }

    /// The exact spurious-refutation shape the grounding gate exists for: a
    /// loop transition whose loop-carried state appears as a FREE variable
    /// (the trust-ir translator's fresh-symbolic havoc for an unresolvable
    /// reference). Without the gate, the composer "refutes" it by assigning
    /// the free variable a value the program never produces — measured on a
    /// safe `t += 1` loop before the gate landed.
    #[test]
    fn ungrounded_loop_carried_state_declines() {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("entry", vec![]);
        let p = problem.declare_predicate("loop", vec![ChcSort::Int]);
        let i = || ChcExpr::var(ChcVar::new("i", ChcSort::Int));
        // Havoc'd loop-carried value: `t` occurs only in the head/query, never
        // among the body relation's arguments.
        let t = || ChcExpr::var(ChcVar::new("t", ChcSort::Int));
        problem
            .add_clause(HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(entry, vec![])));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(entry, vec![])], Some(ChcExpr::eq(i(), ChcExpr::int(0)))),
            ClauseHead::Predicate(p, vec![i()]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![i()])], Some(ChcExpr::lt(i(), ChcExpr::int(10)))),
            // Head references the ungrounded `t`.
            ClauseHead::Predicate(p, vec![ChcExpr::add(t(), ChcExpr::int(1))]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(p, vec![i()])],
            Some(ChcExpr::gt(t(), ChcExpr::int(1000))),
        )));
        assert!(problem.has_cycles());
        assert!(
            bounded_unroll_chc_for_refutation(&problem, 4).is_none(),
            "ungrounded loop-carried state must decline the unroll entirely"
        );
    }

    /// A second bodyless fact is not another entry point by assertion. Its
    /// free value could be a producer-introduced havoc, so the entire lane
    /// must decline even when the first fact is a valid dependency root.
    #[test]
    fn second_free_fact_declines() {
        let mut problem = counter_loop_problem(100, 3);
        let injected = problem.declare_predicate("injected", vec![ChcSort::Int]);
        let havoc = ChcExpr::var(ChcVar::new("havoc", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(injected, vec![havoc]),
        ));

        assert!(problem.has_cycles());
        assert!(
            bounded_unroll_chc_for_refutation(&problem, 4).is_none(),
            "a second bodyless free fact must not be mistaken for program input"
        );
    }

    /// Even a UNIQUE bodyless fact is inadmissible when its head has an
    /// incoming transition edge. Such an internal seed can jump directly into
    /// a loop with an arbitrary value and fabricate a short counterexample.
    #[test]
    fn internal_free_fact_declines() {
        let mut problem = ChcProblem::new();
        let looppred = problem.declare_predicate("loop", vec![ChcSort::Int]);
        let value = || ChcExpr::var(ChcVar::new("value", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(looppred, vec![value()]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(looppred, vec![value()])]),
            ClauseHead::Predicate(looppred, vec![ChcExpr::add(value(), ChcExpr::int(1))]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(looppred, vec![value()])],
            Some(ChcExpr::gt(value(), ChcExpr::int(2))),
        )));

        assert!(problem.has_cycles());
        assert!(
            bounded_unroll_chc_for_refutation(&problem, 4).is_none(),
            "an internal bodyless free fact must not seed a refutation"
        );
    }

    /// Grounded variable identity is `(name, sort)`, not just a string. A
    /// body argument named `x:Int` cannot authorize a free `x:Bool` hidden in
    /// the transition constraint.
    #[test]
    fn same_name_different_sort_does_not_ground_free_value() {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("entry", vec![]);
        let looppred = problem.declare_predicate("loop", vec![ChcSort::Int]);
        let int_x = || ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let bool_x = ChcExpr::var(ChcVar::new("x", ChcSort::Bool));
        problem
            .add_clause(HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(entry, vec![])));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(entry, vec![])]),
            ClauseHead::Predicate(looppred, vec![ChcExpr::int(0)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(looppred, vec![int_x()])], Some(bool_x)),
            ClauseHead::Predicate(looppred, vec![int_x()]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(looppred, vec![int_x()])],
            Some(ChcExpr::gt(int_x(), ChcExpr::int(2))),
        )));

        assert!(problem.has_cycles());
        assert!(bounded_unroll_chc_for_refutation(&problem, 4).is_none());
    }

    /// Defining equalities ground intermediates: `(= v (+ i 1))` makes `v`
    /// usable in the head without declining.
    #[test]
    fn equality_defined_intermediates_stay_grounded() {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("entry", vec![]);
        let p = problem.declare_predicate("loop", vec![ChcSort::Int]);
        let i = || ChcExpr::var(ChcVar::new("i", ChcSort::Int));
        let v = || ChcExpr::var(ChcVar::new("v", ChcSort::Int));
        problem
            .add_clause(HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(entry, vec![])));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(entry, vec![])], Some(ChcExpr::eq(i(), ChcExpr::int(0)))),
            ClauseHead::Predicate(p, vec![i()]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![i()])],
                Some(ChcExpr::and_vec(vec![
                    ChcExpr::lt(i(), ChcExpr::int(100)),
                    ChcExpr::eq(v(), ChcExpr::add(i(), ChcExpr::int(1))),
                ])),
            ),
            ClauseHead::Predicate(p, vec![v()]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(p, vec![i()])],
            Some(ChcExpr::eq(i(), ChcExpr::int(3))),
        )));
        assert!(problem.has_cycles());
        assert!(
            bounded_unroll_chc_for_refutation(&problem, 4).is_some(),
            "equality-defined intermediates are grounded, not havoc"
        );
    }

    #[test]
    fn unreachable_query_is_never_refuted_by_the_unroll() {
        // target ≥ bound: no execution reaches it at ANY depth. No unroll
        // budget may fabricate a witness.
        let unreachable = counter_loop_problem(5, 7);
        for k in BOUNDED_UNROLL_K_LADDER {
            let unrolled = bounded_unroll_chc_for_refutation(&unreachable, k).expect("unrolls");
            assert!(
                !matches!(
                    crate::direct_smt_cex::acyclic_direct_smt_decision(&unrolled.problem),
                    crate::direct_smt_cex::AcyclicDecision::Unsafe(_)
                ),
                "unreachable query fabricated a witness at k={k}"
            );
        }
    }
}

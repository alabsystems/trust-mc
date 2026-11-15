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
use trust_mc_core::chc::is_translation_havoc_var;

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
/// - A TRANSLATION HAVOC (a variable whose name carries
///   `trust_mc_core::chc::TRANSLATION_HAVOC_VAR_PREFIX`, the translator's fresh
///   unconstrained value) is NEVER grounded, wherever it occurs — the entry fact
///   included. An equality on it is a constraint the solver satisfies by choosing
///   it, not a definition: the error clause of `assert(r != 263)` over a havoc
///   `r` is `(= r 263)`, which the rule above would otherwise read as defining
///   `r` and so "refute" a program that never produces 263 (measured: a safe loop
///   calling a summarized element reader, TMC-1 review 2026-09-30). The
///   structural rules above cannot tell `(= havoc 263)` from a defining
///   `(= v (+ i 1))`; the name, which the producer stamps and the normalized
///   input digest binds, can.
/// - Any expression node this walker does not recognize (`ChcExpr` is
///   `#[non_exhaustive]`) declines, and the walk is iterative with an explicit
///   node budget so adversarially deep terms fail closed instead of missing
///   variables (a missed variable would be silently treated as absent — the
///   unsound direction).
pub(crate) fn problem_is_grounded_for_refutation(problem: &ChcProblem) -> bool {
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
    // allowed here — they are the function's inputs — but an unrecognized node
    // must not be able to hide one, and a translation havoc is not an input.
    let entry_vars_are_inputs = |expr: &ChcExpr| {
        collect_expr_vars(expr)
            .is_some_and(|vars| !vars.iter().any(|var| is_translation_havoc_var(&var.name)))
    };
    if !entry_fact.body.constraint.as_ref().is_none_or(entry_vars_are_inputs)
        || !entry_args.iter().all(entry_vars_are_inputs)
    {
        return false;
    }

    problem
        .clauses()
        .iter()
        .filter(|clause| !clause.body.predicates.is_empty())
        .all(clause_is_grounded_for_refutation)
}

/// Whether the derivation `clause_indices` (indices into `problem.clauses()`)
/// READS a TRANSLATION HAVOC under `model`, the witness's assignment to the
/// derivation's alpha-renamed variables (`direct_smt_cex::alpha_renamed_clauses`).
/// `None` when an index is out of range, the renaming declines, or a clause
/// cannot be inventoried (an unrecognized node): the caller cannot tell, and
/// must decline.
///
/// The consumer's replay of an ACYCLIC direct-SMT witness asks this of the
/// derivation the witness names: such a witness carries no grounding gate of its
/// own (the bounded-unroll lane's is `problem_is_grounded_for_refutation`), and a
/// model that assigns a havoc is a claim about the encoding, not about the program.
///
/// A clause reads a havoc when one occurs in a body or head argument, or where a
/// top-level conjunct of its constraint reads it under the model
/// (`direct_smt_cex::HavocReads`): every occurrence except
/// those under an implication whose plain non-havoc Bool antecedent the model
/// sets `false`, and those in the unselected branch of an `ite` whose plain
/// non-havoc Bool condition the model fixes. The large-block encoding of an
/// acyclic function (trust-mc-trust-bmc, `translate_chc_large_block.rs`) puts
/// every formula of a block under one of that block's Booleans and selects a
/// block's inputs by `ite`s over its in-edge selectors, so the havocs of a block
/// or an edge off the witness's path are not read; per-block CHC has neither
/// shape around a havoc and is judged exactly as before.
///
/// Soundness. Let `M` be the witness model, which the replay
/// (`replay_acyclic_direct_smt_witness`) checks satisfies the derivation. Change
/// the value of any set of havoc variables in `M`, leaving every other variable
/// as it is. Arguments contain no havoc, so they are unchanged; a conjunct that
/// reads no havoc keeps its value, because each occurrence it does not read sits
/// under a false antecedent (the implication holds whatever its consequent is) or
/// in an `ite` branch its fixed condition does not select (the `ite`'s value is
/// the other branch's). The derivation therefore holds for EVERY value of the
/// havocs it mentions — in particular for the values a real execution gives
/// them — which is exactly what the havoc-free condition this gate had before
/// guaranteed, and what makes the counterexample a claim about the program.
///
/// Cost: linear in the derivation, each shared node of a clause walked once
/// (`HavocReads` memoizes per node: under a fixed model, whether a node reads a
/// havoc does not depend on where it is reached from; the arguments' walk shares
/// one visited set). No node budget bounds it: a large-block query is a whole
/// function's clause, and the walk is the size of the consumer's own problem,
/// not of anything the witness supplies.
pub(crate) fn derivation_reads_translation_havoc(
    problem: &ChcProblem,
    clause_indices: &[u64],
    model: &serde_json::Value,
) -> Option<bool> {
    let clauses = problem.clauses();
    let renamed = crate::direct_smt_cex::alpha_renamed_variable_names(problem)?;
    let model = model.as_object()?;
    let mut argument_nodes: std::collections::HashSet<*const ChcExpr> =
        std::collections::HashSet::new();
    for &index in clause_indices {
        let index = usize::try_from(index).ok()?;
        let clause = clauses.get(index)?;
        let names = renamed.get(index)?;
        let body_args = clause.body.predicates.iter().flat_map(|(_, args)| args.iter());
        let head_args = match &clause.head {
            ClauseHead::Predicate(_, args) => args.as_slice(),
            _ => &[],
        };
        for expr in body_args.chain(head_args) {
            if mentions_translation_havoc(expr, &mut argument_nodes)? {
                return Some(true);
            }
        }
        let Some(constraint) = &clause.body.constraint else {
            continue;
        };
        let mut reads = crate::direct_smt_cex::HavocReads::new(names, model);
        let mut pending = vec![constraint];
        let mut flattened: std::collections::HashSet<*const ChcExpr> =
            std::collections::HashSet::new();
        while let Some(expr) = pending.pop() {
            if let ChcExpr::Op(ChcOp::And, args) = expr {
                if flattened.insert(std::ptr::from_ref(expr)) {
                    pending.extend(args.iter().map(AsRef::as_ref));
                }
                continue;
            }
            if reads.conjunct(expr)? {
                return Some(true);
            }
        }
    }
    Some(false)
}

/// Whether `expr` mentions a translation havoc anywhere (an argument is read
/// whole). Each node is walked once across calls sharing `seen` (a node found
/// havoc-free stays so). `None` for a shape the walk does not know.
fn mentions_translation_havoc(
    expr: &ChcExpr,
    seen: &mut std::collections::HashSet<*const ChcExpr>,
) -> Option<bool> {
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(node)) {
            continue;
        }
        match node {
            ChcExpr::Var(var) => {
                if is_translation_havoc_var(&var.name) {
                    return Some(true);
                }
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => pending.extend(args.iter().map(AsRef::as_ref)),
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
    Some(false)
}

/// Node budget for the bounded-unroll grounding walks below
/// (`clause_is_grounded_for_refutation`, `collect_expr_vars`): far above anything
/// the native translator emits per clause of a CYCLIC function, the only
/// functions this lane unrolls (an acyclic function is one large-block query,
/// replayed by the direct-SMT lane, whose havoc gate has no budget); hitting it
/// declines (fail-closed).
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
                Some(vars) => grounded
                    .extend(vars.into_iter().filter(|var| !is_translation_havoc_var(&var.name))),
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
    // every variable of `e` is grounded — unless `v` is a translation havoc,
    // which no constraint defines.
    loop {
        let mut changed = false;
        for conjunct in &conjuncts {
            let ChcExpr::Op(ChcOp::Eq, args) = conjunct else { continue };
            let [lhs, rhs] = args.as_slice() else { continue };
            for (var_side, def_side) in [(lhs, rhs), (rhs, lhs)] {
                let ChcExpr::Var(var) = var_side.as_ref() else { continue };
                if grounded.contains(var) || is_translation_havoc_var(&var.name) {
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

    /// `bb0(x) ← ⊤` and `error ← bb0(x) ∧ φ`, the shape of a large-block query
    /// (`entry` here), plus the query clause. Returns the problem and the index
    /// of the error clause.
    fn one_query_problem(constraint: ChcExpr) -> (ChcProblem, u64) {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("bb0", vec![ChcSort::Int]);
        let error = problem.declare_predicate("error", vec![]);
        let x = ChcExpr::var(ChcVar::new("bb0_v0", ChcSort::Int));
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(entry, vec![x.clone()]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(entry, vec![x])], Some(constraint)),
            ClauseHead::Predicate(error, vec![]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(vec![(error, vec![])], None)));
        (problem, 1)
    }

    fn bool_var(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
    }

    fn int_var(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    /// The witness model binding `values` by their names in the error clause.
    fn model_of(problem: &ChcProblem, clause: u64, values: &[(&str, bool)]) -> serde_json::Value {
        let names = crate::direct_smt_cex::alpha_renamed_variable_names(problem)
            .expect("the fixture renames");
        let names = &names[clause as usize];
        let mut model = serde_json::Map::new();
        for (name, value) in values {
            let var = ChcVar::new(*name, ChcSort::Bool);
            let renamed = names.get(&var).expect("the variable occurs in the clause").clone();
            model.insert(renamed, serde_json::json!({ "kind": "bool", "value": value }));
        }
        serde_json::Value::Object(model)
    }

    #[test]
    fn a_havoc_under_a_false_block_boolean_is_not_read() {
        // `(=> r (= havoc 3))` with `r` false: the block is off the path.
        let havoc = int_var("havoc__f_x_0");
        let guarded = ChcExpr::implies(bool_var("bb2_lbe_r"), ChcExpr::eq(havoc, ChcExpr::int(3)));
        let reached = ChcExpr::implies(
            bool_var("bb1_lbe_e0"),
            ChcExpr::gt(int_var("bb0_v0"), ChcExpr::int(0)),
        );
        let (problem, clause) =
            one_query_problem(ChcExpr::and_vec(vec![guarded, reached, bool_var("bb1_lbe_e0")]));
        let trace = [0, clause, 2];
        let off = model_of(&problem, clause, &[("bb2_lbe_r", false), ("bb1_lbe_e0", true)]);
        assert_eq!(derivation_reads_translation_havoc(&problem, &trace, &off), Some(false));
        // The same block ON the path reads its havoc.
        let on = model_of(&problem, clause, &[("bb2_lbe_r", true), ("bb1_lbe_e0", true)]);
        assert_eq!(derivation_reads_translation_havoc(&problem, &trace, &on), Some(true));
        // A model that does not bind the antecedent proves nothing.
        let unbound = model_of(&problem, clause, &[("bb1_lbe_e0", true)]);
        assert_eq!(derivation_reads_translation_havoc(&problem, &trace, &unbound), Some(true));
        // A binding that is not exactly a Bool `false` is not a false antecedent.
        let mut odd = off.clone();
        let names = crate::direct_smt_cex::alpha_renamed_variable_names(&problem).expect("renames");
        let renamed = names[clause as usize][&ChcVar::new("bb2_lbe_r", ChcSort::Bool)].clone();
        odd[&renamed] = serde_json::json!({ "kind": "bool", "value": false, "extra": 1 });
        assert_eq!(derivation_reads_translation_havoc(&problem, &trace, &odd), Some(true));
    }

    #[test]
    fn only_a_plain_non_havoc_boolean_antecedent_disables_a_conjunct() {
        let havoc = || ChcExpr::eq(int_var("havoc__f_x_0"), ChcExpr::int(3));
        // A havoc antecedent: its value is the solver's choice.
        let by_havoc = ChcExpr::implies(bool_var("havoc__f_b_1"), havoc());
        // A compound antecedent, even one that is false under the model.
        let compound = ChcExpr::implies(ChcExpr::not(bool_var("bb2_lbe_r")), havoc());
        // A havoc outside any implication.
        let bare = havoc();
        // The same implication spelled as a disjunction.
        let disjunction = ChcExpr::or_vec(vec![ChcExpr::not(bool_var("bb2_lbe_r")), havoc()]);
        for (conjunct, values) in [
            (by_havoc, vec![("havoc__f_b_1", false)]),
            (compound, vec![("bb2_lbe_r", true)]),
            (bare, vec![]),
            (disjunction, vec![("bb2_lbe_r", true)]),
        ] {
            let (problem, clause) = one_query_problem(ChcExpr::and_vec(vec![
                conjunct.clone(),
                ChcExpr::gt(int_var("bb0_v0"), ChcExpr::int(0)),
            ]));
            let model = model_of(&problem, clause, &values);
            assert_eq!(
                derivation_reads_translation_havoc(&problem, &[0, clause, 2], &model),
                Some(true),
                "{conjunct:?}"
            );
        }
    }

    #[test]
    fn a_havoc_in_an_unselected_ite_branch_is_not_read() {
        // `c = ite(s, havoc, 0)`: the selection of a large-block column.
        let selection =
            ChcExpr::ite(bool_var("bb3_lbe_s0"), int_var("havoc__f_x_0"), ChcExpr::int(0));
        let definition = ChcExpr::eq(int_var("bb4_lbe_c0"), selection);
        let (problem, clause) = one_query_problem(ChcExpr::and_vec(vec![
            definition,
            ChcExpr::gt(int_var("bb0_v0"), ChcExpr::int(0)),
        ]));
        let trace = [0, clause, 2];
        let unselected = model_of(&problem, clause, &[("bb3_lbe_s0", false)]);
        assert_eq!(derivation_reads_translation_havoc(&problem, &trace, &unselected), Some(false));
        let selected = model_of(&problem, clause, &[("bb3_lbe_s0", true)]);
        assert_eq!(derivation_reads_translation_havoc(&problem, &trace, &selected), Some(true));
        let unbound = model_of(&problem, clause, &[]);
        assert_eq!(derivation_reads_translation_havoc(&problem, &trace, &unbound), Some(true));
        // A havoc in the condition is always read.
        let by_havoc = ChcExpr::eq(
            int_var("bb4_lbe_c0"),
            ChcExpr::ite(bool_var("havoc__f_b_1"), ChcExpr::int(1), ChcExpr::int(0)),
        );
        let (problem, clause) = one_query_problem(ChcExpr::and_vec(vec![
            by_havoc,
            ChcExpr::gt(int_var("bb0_v0"), ChcExpr::int(0)),
        ]));
        let model = model_of(&problem, clause, &[("havoc__f_b_1", false)]);
        assert_eq!(
            derivation_reads_translation_havoc(&problem, &[0, clause, 2], &model),
            Some(true)
        );
    }

    /// One shared node, two conjuncts: the first is off the path (its guard is
    /// false), the second reads the node unguarded. The memo of what a node
    /// reads must not carry the first conjunct's skip into the second.
    #[test]
    fn a_shared_node_is_read_wherever_a_conjunct_reads_it() {
        let shared = ChcExpr::eq(int_var("havoc__f_x_0"), ChcExpr::int(3));
        let off = ChcExpr::implies(bool_var("bb2_lbe_r"), shared.clone());
        let on = ChcExpr::or_vec(vec![bool_var("bb1_lbe_e0"), shared]);
        let (problem, clause) = one_query_problem(ChcExpr::and_vec(vec![off, on]));
        let model = model_of(&problem, clause, &[("bb2_lbe_r", false), ("bb1_lbe_e0", true)]);
        assert_eq!(
            derivation_reads_translation_havoc(&problem, &[0, clause, 2], &model),
            Some(true)
        );
        // A long derivation of conjuncts that all share one deep subterm is
        // walked once per node: 2 000 conjuncts over a 2 000-node chain.
        let mut chain =
            ChcExpr::ite(bool_var("bb3_lbe_s0"), int_var("havoc__f_y_1"), ChcExpr::int(0));
        for _ in 0..2_000 {
            chain = ChcExpr::add(chain, ChcExpr::int(1));
        }
        let conjuncts: Vec<ChcExpr> = (0..2_000)
            .map(|i| ChcExpr::lt(ChcExpr::int(i), chain.clone()))
            .chain([ChcExpr::gt(int_var("bb0_v0"), ChcExpr::int(0))])
            .collect();
        let (problem, clause) = one_query_problem(ChcExpr::and_vec(conjuncts));
        let unselected = model_of(&problem, clause, &[("bb3_lbe_s0", false)]);
        assert_eq!(
            derivation_reads_translation_havoc(&problem, &[0, clause, 2], &unselected),
            Some(false)
        );
        let selected = model_of(&problem, clause, &[("bb3_lbe_s0", true)]);
        assert_eq!(
            derivation_reads_translation_havoc(&problem, &[0, clause, 2], &selected),
            Some(true)
        );
    }

    #[test]
    fn a_havoc_in_an_argument_is_always_read() {
        let mut problem = ChcProblem::new();
        let entry = problem.declare_predicate("bb0", vec![ChcSort::Int]);
        let error = problem.declare_predicate("error", vec![]);
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(entry, vec![int_var("havoc__f_x_0")]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(entry, vec![int_var("bb0_v0")])],
                Some(ChcExpr::implies(
                    bool_var("bb1_lbe_r"),
                    ChcExpr::gt(int_var("bb0_v0"), ChcExpr::int(0)),
                )),
            ),
            ClauseHead::Predicate(error, vec![]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(vec![(error, vec![])], None)));
        let model = model_of(&problem, 1, &[("bb1_lbe_r", false)]);
        assert_eq!(derivation_reads_translation_havoc(&problem, &[0, 1, 2], &model), Some(true));
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

    /// The TMC-1 review's false refutation, at the CHC level: a safe loop whose
    /// error clause equates a TRANSLATION HAVOC with a constant — `assert(r !=
    /// 263)` over a summarized read the caller could not model, `(= r 263)`. Read
    /// as a definition, the equality "grounds" `r` and the composer refutes a
    /// program that never produces 263. A havoc is never grounded, so the lane
    /// declines; the same clause over a variable the program defines (no havoc
    /// name) is the equality-defined intermediate it always admitted.
    #[test]
    fn an_equality_on_a_translation_havoc_never_grounds_it() {
        let with_read_named = |name: String| {
            let mut problem = counter_loop_problem(5, 9);
            let looppred = problem
                .predicates()
                .iter()
                .find(|predicate| predicate.name == "loop")
                .expect("the fixture's loop predicate")
                .id;
            let i = || ChcExpr::var(ChcVar::new("i", ChcSort::Int));
            let read = ChcExpr::var(ChcVar::new(name, ChcSort::Int));
            problem.add_clause(HornClause::query(ClauseBody::new(
                vec![(looppred, vec![i()])],
                Some(ChcExpr::and_vec(vec![
                    ChcExpr::lt(i(), ChcExpr::int(5)),
                    ChcExpr::eq(read, ChcExpr::int(263)),
                ])),
            )));
            problem
        };
        let havoc = with_read_named(format!(
            "{}f_call_element_read_2",
            trust_mc_core::chc::TRANSLATION_HAVOC_VAR_PREFIX
        ));
        assert!(havoc.has_cycles());
        assert!(!problem_is_grounded_for_refutation(&havoc));
        assert!(
            bounded_unroll_chc_for_refutation(&havoc, 4).is_none(),
            "an equality on a havoc is a constraint, not a definition"
        );
        let defined = with_read_named("f_call_element_read_2".to_string());
        assert!(
            problem_is_grounded_for_refutation(&defined),
            "the control: the same equality on a non-havoc name grounds it, which is why \
             the havoc's name has to carry its identity"
        );
    }

    /// A havoc is not a program input even in the entry fact, where free variables
    /// otherwise stand for the function's inputs: the same entry fact over an
    /// input is grounded, over a havoc it is not.
    #[test]
    fn a_translation_havoc_in_the_entry_fact_is_not_an_input() {
        let with_entry_value_named = |name: String| {
            let mut problem = ChcProblem::new();
            let entry = problem.declare_predicate("entry", vec![ChcSort::Int]);
            let looppred = problem.declare_predicate("loop", vec![ChcSort::Int]);
            let value = || ChcExpr::var(ChcVar::new("value", ChcSort::Int));
            let seed = ChcExpr::var(ChcVar::new(name, ChcSort::Int));
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![], Some(ChcExpr::eq(value(), seed))),
                ClauseHead::Predicate(entry, vec![value()]),
            ));
            problem.add_clause(HornClause::new(
                ClauseBody::predicates_only(vec![(entry, vec![value()])]),
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
            problem
        };
        assert!(
            problem_is_grounded_for_refutation(&with_entry_value_named("input".to_string())),
            "the control: a free entry value is an input"
        );
        let havoc = format!("{}seed_0", trust_mc_core::chc::TRANSLATION_HAVOC_VAR_PREFIX);
        assert!(!problem_is_grounded_for_refutation(&with_entry_value_named(havoc)));
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

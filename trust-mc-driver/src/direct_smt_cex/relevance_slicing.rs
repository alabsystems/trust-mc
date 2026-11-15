// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Sound relevance slicing (cone of influence) for the acyclic direct-SMT decision.
//!
//! # What this is
//!
//! The production TrustIr → CHC lowering fuses an entire function's panic-freedom
//! obligation into ONE clause body whose constraint is a single top-level
//! conjunction of tens of conjuncts over tens of variables (measured on real
//! `ny-cert` dumps: up to 61 conjuncts / 38 variables in one body). Deciding that
//! monolith is what burns the per-query budget and, on bit-vector-heavy bodies,
//! blows the driver's wall-clock ceiling entirely.
//!
//! This module produces candidate **subsets** of that conjunct list. The caller
//! ([`super::solve_constraints`]) sends each subset to the solver and consumes
//! **only a definitive UNSAT**.
//!
//! # Soundness (the whole argument, in one line)
//!
//! For a conjunction `PHI = C1 ∧ … ∧ Cn` and any index set `S ⊆ {1..n}`:
//!
//! ```text
//!   PHI  ⟹  AND_{i∈S} Ci          (conjunction elimination)
//!   ⟹  UNSAT(AND_{i∈S} Ci)  ⟹  UNSAT(PHI)
//! ```
//!
//! That implication needs NOTHING else to hold. In particular it does **not**
//! depend on:
//!
//! * the slice being a *good* slice — any subset works;
//! * the variable analysis in [`connected_components`] being correct or complete
//!   (`ChcExpr::vars()` truncates at ay's expression recursion depth, and
//!   `ChcExpr` is `#[non_exhaustive]`, so the census may be partial) — a wrong
//!   partition yields a different subset, and every subset is sound;
//!   the analysis affects only *which* proofs we find, never their validity;
//! * uninterpreted-function / array symbols being disjoint across parts —
//!   relevant only to the converse (SAT of all parts ⟹ SAT of the whole), which
//!   this module DELIBERATELY never uses;
//! * any theory-specific reasoning.
//!
//! The two structural facts that DO carry weight are enforced here and pinned by
//! tests:
//!
//! 1. [`flat_conjuncts`] only ever splits at `Op(And, ..)` nodes, so the returned
//!    list `C1..Cn` satisfies `AND(C1..Cn) ≡ AND(input)` **exactly** (`And` is
//!    associative/commutative and `ChcExpr::and_all` re-associates freely). Any
//!    non-`And` node — `Or`, `Not`, `Implies`, an atom — is taken WHOLE as a
//!    single conjunct and is never entered, so a top-level disjunction degenerates
//!    to a one-element list and slicing declines (see `MIN_CONJUNCTS` and the
//!    `>= 2 components` gate in [`relevance_slices`]).
//! 2. Slices are `Vec<usize>` index sets into that list; the caller materializes
//!    them by *indexing and cloning*. No conjunct is ever rewritten, simplified,
//!    normalized, or weakened — that would break the implication direction above.
//!
//! # What this is NOT
//!
//! It is NOT a refutation lane. A SAT (or unknown) slice teaches nothing about
//! `PHI`: `AND(S)` can be satisfiable while `PHI` is not. The caller must never
//! surface a slice model as a counterexample, and never short-circuits on
//! anything but UNSAT. See `slice_sat_never_short_circuits_or_refutes` in
//! `super::tests`.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ay_chc::ChcExpr;

/// Do not slice bodies smaller than this. Small bodies already decide inside the
/// per-query budget, so probing them would be pure added latency on the common
/// (fast) path. Chosen from the real-dump census: every body that blew the
/// wall-clock ceiling carried far more than this.
pub(super) const MIN_CONJUNCTS: usize = 8;

/// Hard ceiling on how many candidate slices are ever emitted. Bounds the probe
/// loop independently of the caller's wall-clock deadline.
pub(super) const MAX_SLICES: usize = 64;

/// Only spend tier-2 (depth-1 cone) probes inside a component at least this
/// large. Below it, tier 1 already produced a small enough query.
const TIER2_MIN_COMPONENT: usize = 12;

/// Cap on tier-2 seeds, so a single large component cannot generate a probe per
/// conjunct.
const TIER2_MAX_SEEDS: usize = 16;

/// How far a tier-2 cone closes over shared variables. Depth 1 is "the seed plus
/// everything sharing a variable with it"; depth 2 adds their neighbours. Beyond
/// that a cone tends to swallow the whole component, at which point it is no
/// longer a reduction.
const TIER2_MAX_DEPTH: usize = 2;

/// Flatten a constraint list into its top-level conjunct list.
///
/// SOUNDNESS: recursion happens ONLY through `ChcExpr::conjuncts`, ay's canonical
/// `Op(And, ..)` flattener, which descends exclusively into `And` children and
/// pushes every other node (including a depth-truncated `And`) verbatim.
/// Therefore `AND(flat_conjuncts(cs)) ≡ AND(cs)` — an exact, equivalence-
/// preserving restructuring, never a weakening. Duplicates are retained (the
/// caller's `and_all` folds them); dropping them would also be sound but is not
/// relied upon.
pub(super) fn flat_conjuncts(constraints: &[ChcExpr]) -> Vec<ChcExpr> {
    let mut out = Vec::new();
    for constraint in constraints {
        for conjunct in constraint.conjuncts() {
            out.push(conjunct.clone());
        }
    }
    out
}

/// Candidate relevance slices over `conjuncts`, as index sets.
///
/// Every returned slice is guaranteed (and asserted by tests) to be:
/// * non-empty,
/// * strictly increasing (hence duplicate-free),
/// * in range `0..conjuncts.len()`,
/// * a STRICT subset (`len < conjuncts.len()`) — probing the whole body again is
///   the caller's own job and would only double its cost.
///
/// Ordering is ascending by slice size: the cheapest queries run first, which is
/// also where the observed contradictions live (a `x > 0 ∧ x ≤ 0` pair over one
/// variable is a two-element component).
///
/// Returns an empty vector when slicing cannot pay — fewer than `MIN_CONJUNCTS`
/// conjuncts, or a body whose variable graph is a single connected component with
/// no tier-2 reduction available. A top-level `Or`/`Implies`/atom body flattens to
/// one conjunct and is therefore always declined.
pub(super) fn relevance_slices(conjuncts: &[ChcExpr]) -> Vec<Vec<usize>> {
    let total = conjuncts.len();
    if total < MIN_CONJUNCTS {
        return Vec::new();
    }

    let var_sets = conjunct_var_sets(conjuncts);
    let components = connected_components(&var_sets);

    let mut candidates: Vec<Vec<usize>> = Vec::new();

    // Tier 1 — variable-connected components. Their union is the whole body, so
    // when the body IS unsatisfiable and the parts really are variable-disjoint,
    // some part carries the contradiction. (That converse is a completeness
    // remark only; nothing here depends on it.)
    for component in &components {
        push_candidate(&mut candidates, component.clone(), total);
    }

    // Tier 2 — variable cones of influence inside the largest component, for
    // bodies whose graph does not split (or splits into one dominant part). A
    // depth-k cone is the seed closed k times under "shares a variable with":
    // still a plain subset of the conjunct list, so the soundness argument is
    // unchanged. Seeds are the most SPECIFIC conjuncts first (fewest variables),
    // which is where the observed contradictions live — `shift ≥ 32` against
    // `shift < 32`, `_0_value_sign > 0` against `_0_value_sign ≤ 0`.
    if let Some(largest) = components.iter().max_by_key(|c| c.len())
        && largest.len() >= TIER2_MIN_COMPONENT
    {
        let mut seeds: Vec<usize> = largest.clone();
        seeds.sort_by_key(|&index| (var_sets[index].len(), index));
        for &seed in seeds.iter().take(TIER2_MAX_SEEDS) {
            let mut cone = vec![seed];
            for _ in 0..TIER2_MAX_DEPTH {
                let grown = grow_cone(&cone, largest, &var_sets);
                if grown.len() == cone.len() {
                    break;
                }
                cone = grown;
                push_candidate(&mut candidates, cone.clone(), total);
                if cone.len() == largest.len() {
                    break;
                }
            }
        }
    }

    // Cheapest first, then deterministic by content.
    candidates.sort_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
    candidates.dedup();
    candidates.truncate(MAX_SLICES);
    candidates
}

/// Whether `slice` is satisfiable by construction, so probing it can never
/// yield the UNSAT this phase consumes and the caller skips it. Skipping a probe
/// only declines a proof, never makes one.
///
/// The witness is "every Bool variable false, then each defined variable its
/// definition's value". It satisfies the slice when every conjunct is one of:
///
/// 1. an implication `(=> g φ)` whose antecedent `g` is a Bool variable — false,
///    so the implication holds whatever `φ` is;
/// 2. a negated Bool variable `(not g)`;
/// 3. a definition `(= c e)` of a non-Bool variable `c` that occurs neither in
///    `e` nor in any other conjunct of the slice outside kind 1 — `c` takes
///    `e`'s value, and nothing else it must satisfy reads `c`.
///
/// The large-block query of design step 8e is made of exactly these, except the
/// disjunction of its error sites and a block's own path constraints; a slice
/// without those is satisfiable.
pub(super) fn trivially_satisfiable(slice: &[usize], conjuncts: &[ChcExpr]) -> bool {
    let bool_var =
        |expr: &ChcExpr| matches!(expr, ChcExpr::Var(var) if var.sort == ay_chc::ChcSort::Bool);
    let guarded = |expr: &ChcExpr| {
        matches!(expr, ChcExpr::Op(ay_chc::ChcOp::Implies, args)
            if args.first().is_some_and(|antecedent| bool_var(antecedent)))
    };
    // Each variable's occurrences among the slice's conjuncts outside kind 1,
    // counted once per conjunct: one pass over the slice, each conjunct's
    // variables collected once (linear in the slice, whatever its number of
    // definitions).
    let mut definitions: Vec<ay_chc::ChcVar> = Vec::new();
    let mut occurrences: BTreeMap<ay_chc::ChcVar, usize> = BTreeMap::new();
    for &index in slice {
        let Some(conjunct) = conjuncts.get(index) else {
            return false;
        };
        if guarded(conjunct) {
            continue;
        }
        match conjunct {
            // Kind 2 mentions only a Bool variable, which no definition defines.
            ChcExpr::Op(ay_chc::ChcOp::Not, args)
                if args.len() == 1 && bool_var(args[0].as_ref()) => {}
            ChcExpr::Op(ay_chc::ChcOp::Eq, args) if args.len() == 2 => {
                let ChcExpr::Var(defined) = args[0].as_ref() else {
                    return false;
                };
                if defined.sort == ay_chc::ChcSort::Bool {
                    return false;
                }
                let read = args[1].vars();
                if read.iter().any(|var| var == defined) {
                    return false;
                }
                *occurrences.entry(defined.clone()).or_insert(0) += 1;
                for var in read {
                    *occurrences.entry(var).or_insert(0) += 1;
                }
                definitions.push(defined.clone());
            }
            _ => return false,
        }
    }
    // A defined variable may occur in no other conjunct but a guarded one: its
    // own definition is its only occurrence.
    definitions.iter().all(|defined| occurrences.get(defined) == Some(&1))
}

/// Accept `slice` as a candidate iff it is non-empty and a STRICT subset of the
/// `total` conjuncts. Indices are sorted and deduplicated here so the invariants
/// documented on [`relevance_slices`] hold by construction rather than by
/// caller discipline.
fn push_candidate(candidates: &mut Vec<Vec<usize>>, mut slice: Vec<usize>, total: usize) {
    slice.sort_unstable();
    slice.dedup();
    if slice.is_empty() || slice.len() >= total {
        return;
    }
    candidates.push(slice);
}

/// Variable NAMES referenced by each conjunct.
///
/// Keying on the name (not the `(name, sort)` pair) merges more conjuncts into a
/// component than strictly necessary, which is the conservative direction for
/// slice QUALITY. It is soundness-neutral either way.
fn conjunct_var_sets(conjuncts: &[ChcExpr]) -> Vec<BTreeSet<String>> {
    conjuncts.iter().map(|conjunct| conjunct.vars().into_iter().map(|v| v.name).collect()).collect()
}

/// Partition conjunct indices into variable-connectivity components (union-find
/// over "shares at least one variable name"). Conjuncts with no variables at all
/// each form their own singleton component — which is exactly right: a ground
/// `false` conjunct then becomes a one-element slice that refutes instantly.
///
/// Components are returned with their indices ascending, ordered by first member.
fn connected_components(var_sets: &[BTreeSet<String>]) -> Vec<Vec<usize>> {
    let n = var_sets.len();
    let mut parent: Vec<usize> = (0..n).collect();

    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }

    let mut owner: HashMap<&str, usize> = HashMap::new();
    for (index, vars) in var_sets.iter().enumerate() {
        for var in vars {
            match owner.get(var.as_str()) {
                Some(&other) => {
                    let (a, b) = (find(&mut parent, index), find(&mut parent, other));
                    if a != b {
                        parent[a] = b;
                    }
                }
                None => {
                    owner.insert(var.as_str(), index);
                }
            }
        }
    }

    let mut groups: Vec<(usize, Vec<usize>)> = Vec::new();
    let mut slot: HashMap<usize, usize> = HashMap::new();
    for index in 0..n {
        let root = find(&mut parent, index);
        match slot.get(&root) {
            Some(&pos) => groups[pos].1.push(index),
            None => {
                slot.insert(root, groups.len());
                groups.push((index, vec![index]));
            }
        }
    }
    groups.into_iter().map(|(_, members)| members).collect()
}

/// One step of cone growth: `cone` plus every member of `component` that shares a
/// variable name with something already in `cone`. The result always CONTAINS
/// `cone`, so repeated application is monotone and terminates at the component.
fn grow_cone(cone: &[usize], component: &[usize], var_sets: &[BTreeSet<String>]) -> Vec<usize> {
    let mut frontier: BTreeSet<&str> = BTreeSet::new();
    for &index in cone {
        for name in &var_sets[index] {
            frontier.insert(name.as_str());
        }
    }
    let mut grown: Vec<usize> = cone.to_vec();
    for &index in component {
        if !cone.contains(&index)
            && var_sets[index].iter().any(|name| frontier.contains(name.as_str()))
        {
            grown.push(index);
        }
    }
    grown
}

#[cfg(test)]
mod tests {
    use super::*;

    use ay_chc::{ChcOp, ChcSort, ChcVar};

    fn ivar(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    /// `x_i > 0` for a distinct variable per index — pairwise variable-disjoint.
    fn disjoint_atoms(count: usize) -> Vec<ChcExpr> {
        (0..count).map(|i| ChcExpr::gt(ivar(&format!("x{i}")), ChcExpr::int(0))).collect()
    }

    /// EVERY emitted slice must be a well-formed STRICT subset of the conjunct
    /// list. This is the structural half of the soundness argument: the caller
    /// materializes slices by indexing, so "is a subset" is exactly "indices are
    /// in range, sorted, deduplicated, non-empty, and fewer than all of them".
    #[test]
    fn every_slice_is_a_wellformed_strict_subset() {
        let mut conjuncts = disjoint_atoms(20);
        // Mix in a connected clump and a variable-free ground conjunct.
        conjuncts.push(ChcExpr::gt(ivar("a"), ivar("b")));
        conjuncts.push(ChcExpr::gt(ivar("b"), ivar("c")));
        conjuncts.push(ChcExpr::gt(ivar("c"), ivar("a")));
        conjuncts.push(ChcExpr::eq(ChcExpr::int(1), ChcExpr::int(2)));

        let slices = relevance_slices(&conjuncts);
        assert!(!slices.is_empty(), "a 24-conjunct body with 21 components must slice");
        for slice in &slices {
            assert!(!slice.is_empty(), "empty slice");
            assert!(slice.len() < conjuncts.len(), "slice is not a STRICT subset: {slice:?}");
            assert!(
                slice.windows(2).all(|w| w[0] < w[1]),
                "slice indices must be strictly increasing (sorted + deduplicated): {slice:?}"
            );
            assert!(
                slice.iter().all(|&i| i < conjuncts.len()),
                "slice index out of range: {slice:?}"
            );
        }
        assert!(slices.len() <= MAX_SLICES, "slice count must respect MAX_SLICES");
    }

    /// A ground contradiction with no variables lands in its own singleton slice,
    /// so the cheapest probe refutes the whole body immediately.
    #[test]
    fn variable_free_conjunct_becomes_its_own_slice() {
        let mut conjuncts = disjoint_atoms(9);
        conjuncts.push(ChcExpr::bool_const(false));
        let ground = conjuncts.len() - 1;
        let slices = relevance_slices(&conjuncts);
        assert!(
            slices.contains(&vec![ground]),
            "variable-free conjunct must be reachable as a singleton slice"
        );
    }

    /// A body whose top level is a DISJUNCTION flattens to ONE conjunct. Slicing
    /// must decline: the only subsets are the empty set (vacuous) and the whole
    /// formula (no reduction). This is the fail-closed answer to "is the top node
    /// genuinely a conjunction?".
    #[test]
    fn top_level_disjunction_declines_to_slice() {
        let big_or = ChcExpr::or_vec(
            (0..40).map(|i| ChcExpr::gt(ivar(&format!("y{i}")), ChcExpr::int(0))).collect(),
        );
        let conjuncts = flat_conjuncts(std::slice::from_ref(&big_or));
        assert_eq!(conjuncts.len(), 1, "an Or node must never be split into conjuncts");
        assert!(
            relevance_slices(&conjuncts).is_empty(),
            "a single-conjunct body has no strict non-empty subset worth probing"
        );
    }

    /// A NEGATED conjunction is not a conjunction. `Not(And(..))` must stay whole.
    #[test]
    fn negated_conjunction_is_not_entered() {
        let inner = ChcExpr::and_vec(
            (0..12).map(|i| ChcExpr::gt(ivar(&format!("z{i}")), ChcExpr::int(0))).collect(),
        );
        let negated = ChcExpr::not(inner);
        let conjuncts = flat_conjuncts(std::slice::from_ref(&negated));
        assert_eq!(conjuncts.len(), 1, "Not(And(..)) must be an opaque single conjunct");
        assert!(relevance_slices(&conjuncts).is_empty());
    }

    /// Flattening is EXACT: it splits at `And` and nowhere else, and preserves
    /// every leaf. (`and_all` deduplicates, so compare as sets of distinct leaves.)
    #[test]
    fn flattening_splits_only_at_and_nodes() {
        let a = ChcExpr::gt(ivar("a"), ChcExpr::int(0));
        let b = ChcExpr::or_vec(vec![
            ChcExpr::gt(ivar("b"), ChcExpr::int(0)),
            ChcExpr::gt(ivar("c"), ChcExpr::int(0)),
        ]);
        let c = ChcExpr::not(ChcExpr::gt(ivar("d"), ChcExpr::int(0)));
        let nested =
            ChcExpr::and_vec(vec![a.clone(), ChcExpr::and_vec(vec![b.clone(), c.clone()])]);

        let flat = flat_conjuncts(std::slice::from_ref(&nested));
        assert_eq!(flat, vec![a, b, c], "nested Ands flatten; Or/Not stay whole");
        assert!(!flat.iter().any(|e| matches!(e, ChcExpr::Op(ChcOp::And, _))));
    }

    /// Components partition the conjunct set: every index appears exactly once.
    /// (Not required for soundness — required for the completeness remark, and it
    /// is what makes tier 1 exhaust the body.)
    #[test]
    fn components_partition_every_conjunct_exactly_once() {
        let conjuncts = {
            let mut v = disjoint_atoms(6);
            v.push(ChcExpr::gt(ivar("x0"), ivar("x1")));
            v.push(ChcExpr::eq(ChcExpr::int(3), ChcExpr::int(3)));
            v
        };
        let components = connected_components(&conjunct_var_sets(&conjuncts));
        let mut seen: Vec<usize> = components.iter().flatten().copied().collect();
        seen.sort_unstable();
        assert_eq!(seen, (0..conjuncts.len()).collect::<Vec<_>>());
        // x0 and x1 are joined by the shared-variable conjunct.
        assert!(
            components.iter().any(|c| c.len() == 3),
            "x0, x1 and the linking conjunct must merge into one component: {components:?}"
        );
    }

    /// The whole body is never emitted as a "slice" — that is the caller's own
    /// query and probing it here would just double the cost.
    #[test]
    fn single_component_body_emits_no_full_body_slice() {
        // A chain over 10 variables: one component, 10 conjuncts, below
        // TIER2_MIN_COMPONENT so tier 2 does not fire either.
        let conjuncts: Vec<ChcExpr> = (0..10)
            .map(|i| ChcExpr::gt(ivar(&format!("v{i}")), ivar(&format!("v{}", i + 1))))
            .collect();
        let slices = relevance_slices(&conjuncts);
        assert!(
            slices.iter().all(|s| s.len() < conjuncts.len()),
            "no slice may equal the full body"
        );
    }

    fn bvar(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
    }

    /// The witness `trivially_satisfiable` relies on — every Bool variable false,
    /// each defined variable its definition's value — satisfies exactly the
    /// slices it accepts, and anything that could force a contradiction is
    /// probed.
    #[test]
    fn only_slices_satisfied_by_all_guards_false_are_skipped() {
        let guarded = ChcExpr::implies(bvar("g"), ChcExpr::gt(ivar("x"), ivar("x")));
        let negated = ChcExpr::not(bvar("s"));
        let defined = ChcExpr::eq(ivar("c"), ChcExpr::ite(bvar("s"), ivar("y"), ChcExpr::int(0)));
        let reads_c = ChcExpr::implies(bvar("h"), ChcExpr::lt(ivar("c"), ChcExpr::int(0)));
        let conjuncts = vec![guarded, negated, defined.clone(), reads_c];
        assert!(trivially_satisfiable(&[0, 1, 2, 3], &conjuncts));
        // A bare Bool variable, a disjunction, an atom: each may force something.
        for forcing in [
            bvar("f"),
            ChcExpr::or_vec(vec![bvar("f"), bvar("g")]),
            ChcExpr::gt(ivar("x"), ChcExpr::int(0)),
        ] {
            let mut with = conjuncts.clone();
            with.push(forcing.clone());
            assert!(!trivially_satisfiable(&[0, 1, 2, 3, 4], &with), "{forcing:?}");
        }
        // A defined variable read outside a guarded conjunct is not free.
        let mut with = conjuncts.clone();
        with.push(ChcExpr::eq(ivar("d"), ChcExpr::add(ivar("c"), ChcExpr::int(1))));
        assert!(!trivially_satisfiable(&[0, 1, 2, 3, 4], &with));
        // A variable defined twice, or in terms of itself, is not free.
        let mut with = conjuncts.clone();
        with.push(ChcExpr::eq(ivar("c"), ChcExpr::int(5)));
        assert!(!trivially_satisfiable(&[0, 1, 2, 3, 4], &with));
        let selfish = vec![ChcExpr::eq(ivar("c"), ChcExpr::add(ivar("c"), ChcExpr::int(1)))];
        assert!(!trivially_satisfiable(&[0], &selfish));
        // A Bool definition is not free: "every Bool variable false" fixes it.
        let bool_def = vec![ChcExpr::eq(bvar("b"), ChcExpr::Bool(true))];
        assert!(!trivially_satisfiable(&[0], &bool_def));
    }
}

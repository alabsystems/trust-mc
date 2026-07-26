// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC auto-invariant candidate extraction — LIBRARY lane.
//!
//! The single implementation behind both the CLI lane
//! (`call_ay::chc::auto_invariants`, mode-gated by `--ay-chc-auto-invariants`)
//! and the library-only native typed-CHC runner (`native.rs`), which the
//! COMPILER drives: the CLI machinery was unreachable from
//! `NativeTrustIrChcPdrRunner`, so production PDR runs solved loop obligations
//! with zero invariant seeds and returned Inconclusive on shapes
//! (accumulator loops, counted loops) whose invariant is a one-line template.
//!
//! Every candidate is a HINT, never an axiom: the consumer is
//! `PdrConfig::user_hints` → `apply_lemma_hints`, which validates each hint
//! via `is_inductive_blocking` before installing it as a frame lemma —
//! "hints are validated, they are never trusted" — so an unsound candidate
//! costs one SMT check and is dropped.
//!
//! Templates:
//! * W0 (range): `idx`-vs-const/state comparisons mined from the transition
//!   constraint + `idx >= 0` for each detected unit-step counter.
//! * W1 (houdini): `inc_idx <= preserved_idx` equality-preservation bounds.
//! * W2 (houdini): `other >= inc_idx` difference bounds.
//! * W3 (scaled accumulator, NEW): for `acc' = acc + d` beside a unit-step
//!   counter `i' = i ± 1`, with constant constraint bounds `lo <= d <= hi`,
//!   the linear candidates `acc <= i * hi` / `acc >= i * lo` / `acc >= 0` —
//!   the invariant shape of the foreach/accumulator loop class
//!   (`sum of N u8 elements <= 255 * i`), which plain PDR generalization
//!   does not discover. Int sorts only (BV wraparound is not linearizable
//!   this way; fail-closed by skipping).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay::chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, LemmaHint, PredicateId};

const AUTO_RANGE_SOURCE: &str = "trust_mc-auto-inv-range";
const AUTO_HOUDINI_SOURCE: &str = "trust_mc-auto-inv-houdini-seed";
const AUTO_NATIVE_SOURCE: &str = "trust_mc-auto-inv-native";
const AUTO_HINT_PRIORITY: u16 = 58;

/// Maximum candidate hints per predicate before budget cap.
/// AY's PDR validates each hint, so more candidates = more SMT checks.
/// 64 is generous for linear-arithmetic invariants over range loops.
pub(crate) const MAX_CANDIDATES_PER_PREDICATE: usize = 64;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct AutoInvariantStats {
    pub(crate) recursive_clauses: usize,
    pub(crate) range_like_clauses: usize,
    pub(crate) generated: usize,
    /// Candidates dropped because the per-predicate budget was exceeded.
    pub(crate) budget_capped: usize,
    /// Extra candidates added by Houdini widening (equality-preservation,
    /// difference-bound, scaled-accumulator templates) beyond Range mode.
    pub(crate) widening_added: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ComparisonAtom {
    State(usize),
    Const(i128),
}

/// Which hint-source label the caller wants stamped on generated hints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HintSource {
    /// CLI `--ay-chc-auto-invariants=range`.
    // This shared source is compiled once for the library and once for the CLI;
    // the library build intentionally uses only `Native`.
    #[allow(dead_code)]
    Range,
    /// CLI `--ay-chc-auto-invariants=houdini`.
    #[allow(dead_code)]
    Houdini,
    /// The library-only native typed-CHC lane (always houdini-widened).
    // The CLI build intentionally uses only `Range` and `Houdini`.
    #[allow(dead_code)]
    Native,
}

impl HintSource {
    const fn label(self) -> &'static str {
        match self {
            Self::Range => AUTO_RANGE_SOURCE,
            Self::Houdini => AUTO_HOUDINI_SOURCE,
            Self::Native => AUTO_NATIVE_SOURCE,
        }
    }

    const fn houdini(self) -> bool {
        matches!(self, Self::Houdini | Self::Native)
    }
}

pub(crate) fn generate_lemma_hint_candidates(
    problem: &ChcProblem,
    source_kind: HintSource,
) -> (Vec<LemmaHint>, AutoInvariantStats) {
    let source = source_kind.label();
    let houdini = source_kind.houdini();
    let mut stats = AutoInvariantStats::default();
    let mut hints = Vec::new();
    let mut seen: HashSet<(PredicateId, ChcExpr)> = HashSet::new();
    let mut per_predicate_count: HashMap<PredicateId, usize> = HashMap::new();

    for clause in problem.clauses() {
        let (predicate_id, head_args) = match &clause.head {
            ClauseHead::Predicate(id, args) => (*id, args),
            ClauseHead::False => continue,
            _ => continue,
        };

        let Some((_, body_args)) =
            clause.body.predicates.iter().find(|(id, _)| *id == predicate_id)
        else {
            continue;
        };
        stats.recursive_clauses += 1;

        let Some(predicate) = problem.get_predicate(predicate_id) else {
            continue;
        };
        if predicate.arg_sorts.len() != head_args.len() {
            continue;
        }

        let body_var_to_state = int_body_var_to_state_map(body_args, &predicate.arg_sorts);
        if body_var_to_state.is_empty() {
            continue;
        }

        let incremented =
            detect_incremented_indices(head_args, &predicate.arg_sorts, &body_var_to_state);
        if incremented.is_empty() {
            continue;
        }

        let Some(constraint) = &clause.body.constraint else {
            continue;
        };

        let pred_count = per_predicate_count.entry(predicate_id).or_insert(0);
        let mut clause_generated = 0usize;
        let mut comparisons = Vec::new();
        collect_comparisons(constraint, &mut comparisons);

        for (op, lhs, rhs) in &comparisons {
            if *pred_count >= MAX_CANDIDATES_PER_PREDICATE {
                stats.budget_capped += 1;
                continue;
            }
            let candidate = candidate_from_comparison(
                op,
                lhs,
                rhs,
                predicate_id,
                &predicate.arg_sorts,
                &body_var_to_state,
                &incremented,
            );
            if let Some(formula) = candidate {
                let key = (predicate_id, formula.clone());
                if seen.insert(key) {
                    hints.push(LemmaHint::new(predicate_id, formula, AUTO_HINT_PRIORITY, source));
                    clause_generated += 1;
                    *pred_count += 1;
                }
            }
        }

        for idx in &incremented {
            if *pred_count >= MAX_CANDIDATES_PER_PREDICATE {
                stats.budget_capped += 1;
                continue;
            }
            let sort = &predicate.arg_sorts[*idx];
            let state_var = canonical_state_expr(predicate_id, *idx, sort);
            let candidate = make_ge(state_var, make_zero(sort), sort);
            let key = (predicate_id, candidate.clone());
            if seen.insert(key) {
                hints.push(LemmaHint::new(predicate_id, candidate, AUTO_HINT_PRIORITY, source));
                clause_generated += 1;
                *pred_count += 1;
            }
        }

        // Houdini widening: generate additional candidate shapes that Range
        // mode does not produce. AY's PDR validates these via its internal
        // inductiveness checks and discards any that fail.
        if houdini {
            let widening_before = hints.len();

            // W1: For non-incremented integer state variables that are
            // preserved across the transition, emit `inc_idx <= preserved_idx`.
            // Captures `idx <= end` for range loops where `end` is invariant.
            generate_equality_preservation_candidates(
                predicate_id,
                &predicate.arg_sorts,
                &body_var_to_state,
                head_args,
                &incremented,
                &mut hints,
                &mut seen,
                pred_count,
                source,
            );

            // W2: Difference-bound candidates between each incremented index
            // and every other integer state variable (e.g., `end >= idx`).
            generate_difference_bound_candidates(
                predicate_id,
                &predicate.arg_sorts,
                &body_var_to_state,
                &incremented,
                &mut hints,
                &mut seen,
                pred_count,
                source,
            );

            // W3: Scaled-accumulator candidates for `acc' = acc + d` beside a
            // unit-step counter, `d` constraint-bounded by constants.
            generate_scaled_accumulator_candidates(
                predicate_id,
                &predicate.arg_sorts,
                &body_var_to_state,
                head_args,
                &incremented,
                &comparisons,
                &mut hints,
                &mut seen,
                pred_count,
                source,
            );

            let added = hints.len() - widening_before;
            stats.widening_added += added;
            clause_generated += added;
        }

        if clause_generated > 0 {
            stats.range_like_clauses += 1;
        }
    }

    stats.generated = hints.len();
    (hints, stats)
}

/// W1: For non-incremented integer state variables that are preserved across
/// the transition (`head_arg == body_var` for the same state index), emit
/// `inc_idx <= preserved_idx`. This captures `idx <= end` for range loops
/// where the endpoint is loop-invariant.
#[allow(clippy::too_many_arguments)]
fn generate_equality_preservation_candidates(
    predicate_id: PredicateId,
    arg_sorts: &[ChcSort],
    body_var_to_state: &HashMap<String, usize>,
    head_args: &[ChcExpr],
    incremented: &HashSet<usize>,
    hints: &mut Vec<LemmaHint>,
    seen: &mut HashSet<(PredicateId, ChcExpr)>,
    pred_count: &mut usize,
    source: &'static str,
) {
    for (idx, (head_arg, sort)) in head_args.iter().zip(arg_sorts).enumerate() {
        if !is_numeric_sort(sort) || incremented.contains(&idx) {
            continue;
        }
        if *pred_count >= MAX_CANDIDATES_PER_PREDICATE {
            break;
        }
        // Check that head_arg is the body variable mapping to state index `idx`,
        // meaning the state variable is preserved across the transition.
        let is_preserved = match head_arg {
            ChcExpr::Var(var) => body_var_to_state.get(&var.name).copied() == Some(idx),
            _ => false,
        };
        if !is_preserved {
            continue;
        }
        // For each incremented index, emit `inc_idx <= preserved_idx`.
        for &inc_idx in incremented {
            if *pred_count >= MAX_CANDIDATES_PER_PREDICATE {
                break;
            }
            let inc_var = canonical_state_expr(predicate_id, inc_idx, &arg_sorts[inc_idx]);
            let preserved_var = canonical_state_expr(predicate_id, idx, &arg_sorts[idx]);
            let candidate = make_le(inc_var, preserved_var, sort);
            let key = (predicate_id, candidate.clone());
            if seen.insert(key) {
                hints.push(LemmaHint::new(predicate_id, candidate, AUTO_HINT_PRIORITY, source));
                *pred_count += 1;
            }
        }
    }
}

/// W2: For each incremented index and each other non-incremented integer state
/// variable, generate `other >= inc` (i.e., `end - idx >= 0` style).
fn generate_difference_bound_candidates(
    predicate_id: PredicateId,
    arg_sorts: &[ChcSort],
    body_var_to_state: &HashMap<String, usize>,
    incremented: &HashSet<usize>,
    hints: &mut Vec<LemmaHint>,
    seen: &mut HashSet<(PredicateId, ChcExpr)>,
    pred_count: &mut usize,
    source: &'static str,
) {
    let numeric_state_indices: Vec<usize> = body_var_to_state
        .values()
        .copied()
        .filter(|idx| arg_sorts.get(*idx).map_or(false, is_numeric_sort))
        .collect();

    for &inc_idx in incremented {
        for &other_idx in &numeric_state_indices {
            if other_idx == inc_idx || incremented.contains(&other_idx) {
                continue;
            }
            if *pred_count >= MAX_CANDIDATES_PER_PREDICATE {
                return;
            }
            let other_var = canonical_state_expr(predicate_id, other_idx, &arg_sorts[other_idx]);
            let inc_var = canonical_state_expr(predicate_id, inc_idx, &arg_sorts[inc_idx]);
            let candidate = make_ge(other_var, inc_var, &arg_sorts[other_idx]);
            let key = (predicate_id, candidate.clone());
            if seen.insert(key) {
                hints.push(LemmaHint::new(predicate_id, candidate, AUTO_HINT_PRIORITY, source));
                *pred_count += 1;
            }
        }
    }
}

/// W3: scaled-accumulator candidates.
///
/// Detects a head arg `acc' = acc + d` (either operand order) where `acc` is
/// the body variable for the SAME state index and `d` is a TRANSITION INPUT —
/// a plain body variable that maps to NO state argument (the loaded element in
/// a foreach-accumulate loop). Requires a unit-step counter `i' = i ± 1` in
/// the same clause (from `incremented`), and mines constant bounds `lo`/`hi`
/// on `d` from the clause constraint's comparisons.
///
/// Emitted candidates over canonical state variables:
/// * Int: `acc <= i * hi` (hi >= 0), `acc >= i * lo` (lo <= 0),
///   `acc >= 0` (lo >= 0).
/// * BitVec (the REAL trust-mc codegen sorts — Rust integers lower to
///   BitVec(32)/BitVec(64), so an Int-only template would miss every real
///   verification problem): unsigned-flavored `acc bvule i bvmul hi` when
///   `0 <= hi` fits the width, for a same-width counter. The BV product WRAPS
///   by SMT semantics; a candidate whose wrapped reading is not actually
///   inductive for the transition system simply fails PDR's validation and is
///   dropped — while for the foreach-accumulate class (bounded trip count ×
///   bounded element, e.g. 256 × 255 < 2^32) the unwrapped reading IS the
///   inductive invariant and closes the accumulator-overflow obligation.
///
/// SOUNDNESS: pure candidates — ay's PDR `apply_lemma_hints` validates each
/// against init + transition (`is_inductive_blocking`) before installing; a
/// validated BV formula is a true invariant of the BV system by construction,
/// wraparound included (an accumulator initialized non-zero, or a genuinely
/// wrapping product, fails validation and the hint is dropped).
#[allow(clippy::too_many_arguments)]
fn generate_scaled_accumulator_candidates(
    predicate_id: PredicateId,
    arg_sorts: &[ChcSort],
    body_var_to_state: &HashMap<String, usize>,
    head_args: &[ChcExpr],
    incremented: &HashSet<usize>,
    comparisons: &[(ChcOp, ChcExpr, ChcExpr)],
    hints: &mut Vec<LemmaHint>,
    seen: &mut HashSet<(PredicateId, ChcExpr)>,
    pred_count: &mut usize,
    source: &'static str,
) {
    for (acc_idx, (head_arg, acc_sort)) in head_args.iter().zip(arg_sorts).enumerate() {
        if !is_numeric_sort(acc_sort) || incremented.contains(&acc_idx) {
            continue;
        }
        let Some(addend) = accumulator_addend(head_arg, body_var_to_state, acc_idx) else {
            continue;
        };
        let (lo, hi) = constant_bounds_for_var(&addend, comparisons);
        if lo.is_none() && hi.is_none() {
            continue;
        }
        let acc_var = canonical_state_expr(predicate_id, acc_idx, acc_sort);
        for &inc_idx in incremented {
            // The scaled product needs acc and counter in ONE sort: Int with
            // Int, or same-width BitVec (a mixed pair has no well-sorted
            // `i * hi` term — skip fail-closed).
            if arg_sorts[inc_idx] != *acc_sort {
                continue;
            }
            let i_var = canonical_state_expr(predicate_id, inc_idx, &arg_sorts[inc_idx]);
            let scaled = |c: i128| -> Option<ChcExpr> {
                match acc_sort {
                    ChcSort::Int => {
                        let c64 = i64::try_from(c).ok()?;
                        Some(ChcExpr::Op(
                            ChcOp::Mul,
                            vec![Arc::new(ChcExpr::int(c64)), Arc::new(i_var.clone())],
                        ))
                    }
                    ChcSort::BitVec(w) => {
                        // Non-negative, width-fitting constants only (a
                        // negative or oversized bound has no faithful
                        // unsigned BV literal — fail closed).
                        let literal = nonnegative_bitvec_literal(c, *w)?;
                        Some(ChcExpr::Op(
                            ChcOp::BvMul,
                            vec![Arc::new(literal), Arc::new(i_var.clone())],
                        ))
                    }
                    _ => None,
                }
            };
            let mut candidates: Vec<ChcExpr> = Vec::new();
            if let Some(hi) = hi
                && hi >= 0
                && let Some(product) = scaled(hi)
            {
                // Unsigned flavor for BV (`bvule`): the accumulate class is
                // unsigned counts/sums; make_le's signed BvSLe agrees on
                // sign-bit-clear values but breaks at the unsigned midpoint.
                candidates.push(match acc_sort {
                    ChcSort::BitVec(_) => ChcExpr::Op(
                        ChcOp::BvULe,
                        vec![Arc::new(acc_var.clone()), Arc::new(product)],
                    ),
                    _ => make_le(acc_var.clone(), product, acc_sort),
                });
            }
            if let Some(lo) = lo {
                if lo <= 0
                    && matches!(acc_sort, ChcSort::Int)
                    && let Some(product) = scaled(lo).or_else(|| {
                        let lo64 = i64::try_from(lo).ok()?;
                        Some(ChcExpr::Op(
                            ChcOp::Mul,
                            vec![Arc::new(ChcExpr::int(lo64)), Arc::new(i_var.clone())],
                        ))
                    })
                {
                    candidates.push(make_ge(acc_var.clone(), product, acc_sort));
                }
                if lo >= 0 && matches!(acc_sort, ChcSort::Int) {
                    candidates.push(make_ge(acc_var.clone(), make_zero(acc_sort), acc_sort));
                }
            }
            for candidate in candidates {
                if *pred_count >= MAX_CANDIDATES_PER_PREDICATE {
                    return;
                }
                let key = (predicate_id, candidate.clone());
                if seen.insert(key) {
                    hints.push(LemmaHint::new(predicate_id, candidate, AUTO_HINT_PRIORITY, source));
                    *pred_count += 1;
                }
            }
        }
    }
}

/// Build an unsigned bit-vector literal without performing a signed shift.
///
/// `i128` can represent every unsigned value of widths up to 127. At width 128
/// it represents the lower half; larger constants are rejected earlier while
/// mining bounds because they cannot be represented by that signed carrier.
/// A zero-width bit-vector is not a valid SMT sort and is rejected fail-closed.
fn nonnegative_bitvec_literal(c: i128, width: u32) -> Option<ChcExpr> {
    let value = u128::try_from(c).ok()?;
    if width == 0 || (width < u128::BITS && value >= (1_u128 << width)) {
        return None;
    }
    Some(ChcExpr::BitVec(value, width))
}

/// The addend variable name of an `acc' = acc + d` head arg, where `acc` is
/// the body var for `acc_idx` and `d` is a body var mapping to NO state
/// (a transition input). `None` for any other shape (fail-closed).
fn accumulator_addend(
    head_arg: &ChcExpr,
    body_var_to_state: &HashMap<String, usize>,
    acc_idx: usize,
) -> Option<String> {
    let ChcExpr::Op(op, args) = head_arg else {
        return None;
    };
    if !is_add_op(op) || args.len() != 2 {
        return None;
    }
    let classify = |e: &ChcExpr| -> Option<(String, Option<usize>)> {
        match e {
            ChcExpr::Var(var) => {
                Some((var.name.clone(), body_var_to_state.get(&var.name).copied()))
            }
            _ => None,
        }
    };
    let (a_name, a_state) = classify(args[0].as_ref())?;
    let (b_name, b_state) = classify(args[1].as_ref())?;
    match (a_state, b_state) {
        (Some(idx), None) if idx == acc_idx => Some(b_name),
        (None, Some(idx)) if idx == acc_idx => Some(a_name),
        _ => None,
    }
}

/// Mine constant bounds on `var` from the clause constraint comparisons:
/// `(lo, hi)` from atoms of the shapes `var OP const` / `const OP var`.
///
/// Int atoms read via the signed orderings; BitVec atoms via the UNSIGNED
/// orderings only (`bvule`-family — trust-mc's u8/u32 range facts; a signed BV
/// comparison is skipped rather than misread, fail-closed).
fn constant_bounds_for_var(
    var: &str,
    comparisons: &[(ChcOp, ChcExpr, ChcExpr)],
) -> (Option<i128>, Option<i128>) {
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    let mut note_hi = |c: i128| hi = Some(hi.map_or(c, |h: i128| h.min(c)));
    let mut note_lo = |c: i128| lo = Some(lo.map_or(c, |l: i128| l.max(c)));
    let const_of = |e: &ChcExpr| -> Option<i128> {
        match e {
            ChcExpr::Int(c) => Some(*c),
            // Do not wrap the unsigned upper half of BV128 into a negative
            // signed bound. The current bound carrier is i128, so values that
            // do not fit are ignored fail-closed.
            ChcExpr::BitVec(c, _) => i128::try_from(*c).ok(),
            _ => None,
        }
    };
    for (op, lhs, rhs) in comparisons {
        match (lhs, rhs) {
            (ChcExpr::Var(v), c_expr) if v.name == var => {
                let Some(c) = const_of(c_expr) else { continue };
                // `var OP c`
                match op {
                    ChcOp::Le | ChcOp::BvULe => note_hi(c),
                    ChcOp::Lt | ChcOp::BvULt => note_hi(c.saturating_sub(1)),
                    ChcOp::Ge | ChcOp::BvUGe => note_lo(c),
                    ChcOp::Gt | ChcOp::BvUGt => note_lo(c.saturating_add(1)),
                    _ => {}
                }
            }
            (c_expr, ChcExpr::Var(v)) if v.name == var => {
                let Some(c) = const_of(c_expr) else { continue };
                // `c OP var`
                match op {
                    ChcOp::Le | ChcOp::BvULe => note_lo(c),
                    ChcOp::Lt | ChcOp::BvULt => note_lo(c.saturating_add(1)),
                    ChcOp::Ge | ChcOp::BvUGe => note_hi(c),
                    ChcOp::Gt | ChcOp::BvUGt => note_hi(c.saturating_sub(1)),
                    _ => {}
                }
            }
            _ => {}
        }
    }
    (lo, hi)
}

pub(crate) fn int_body_var_to_state_map(
    body_args: &[ChcExpr],
    arg_sorts: &[ChcSort],
) -> HashMap<String, usize> {
    let mut map = HashMap::new();
    for (idx, (arg, sort)) in body_args.iter().zip(arg_sorts).enumerate() {
        if !is_numeric_sort(sort) {
            continue;
        }
        if let ChcExpr::Var(var) = arg {
            map.entry(var.name.clone()).or_insert(idx);
        }
    }
    map
}

pub(crate) fn detect_incremented_indices(
    head_args: &[ChcExpr],
    arg_sorts: &[ChcSort],
    body_var_to_state: &HashMap<String, usize>,
) -> HashSet<usize> {
    let mut incremented = HashSet::new();
    for (idx, (head_arg, sort)) in head_args.iter().zip(arg_sorts).enumerate() {
        if !is_numeric_sort(sort) {
            continue;
        }
        if is_add_one_of_state_idx(head_arg, body_var_to_state, idx)
            || is_sub_one_of_state_idx(head_arg, body_var_to_state, idx)
        {
            incremented.insert(idx);
        }
    }
    incremented
}

fn is_add_one_of_state_idx(
    expr: &ChcExpr,
    body_var_to_state: &HashMap<String, usize>,
    expected_state_idx: usize,
) -> bool {
    let ChcExpr::Op(op, args) = expr else {
        return false;
    };
    if !is_add_op(op) {
        return false;
    }
    if args.len() != 2 {
        return false;
    }

    let lhs = args[0].as_ref();
    let rhs = args[1].as_ref();

    matches_state_plus_const_one(lhs, rhs, body_var_to_state, expected_state_idx)
        || matches_state_plus_const_one(rhs, lhs, body_var_to_state, expected_state_idx)
}

fn is_sub_one_of_state_idx(
    expr: &ChcExpr,
    body_var_to_state: &HashMap<String, usize>,
    expected_state_idx: usize,
) -> bool {
    let ChcExpr::Op(op, args) = expr else {
        return false;
    };
    if !is_sub_op(op) || args.len() != 2 {
        return false;
    }

    matches_state_plus_const_one(
        args[0].as_ref(),
        args[1].as_ref(),
        body_var_to_state,
        expected_state_idx,
    )
}

fn matches_state_plus_const_one(
    state_side: &ChcExpr,
    const_side: &ChcExpr,
    body_var_to_state: &HashMap<String, usize>,
    expected_state_idx: usize,
) -> bool {
    is_const_one(const_side)
        && matches!(
            state_side,
            ChcExpr::Var(var)
                if body_var_to_state.get(&var.name).copied() == Some(expected_state_idx)
        )
}

pub(crate) fn collect_comparisons(expr: &ChcExpr, out: &mut Vec<(ChcOp, ChcExpr, ChcExpr)>) {
    let ChcExpr::Op(op, args) = expr else {
        return;
    };

    if args.len() == 2 && is_comparison_op(op) {
        out.push((*op, (*args[0]).clone(), (*args[1]).clone()));
    }

    for arg in args {
        collect_comparisons(arg, out);
    }
}

fn comparison_atom(
    expr: &ChcExpr,
    body_var_to_state: &HashMap<String, usize>,
) -> Option<ComparisonAtom> {
    match expr {
        ChcExpr::Var(var) => body_var_to_state.get(&var.name).copied().map(ComparisonAtom::State),
        ChcExpr::Int(value) => Some(ComparisonAtom::Const(*value)),
        ChcExpr::BitVec(value, _) => Some(ComparisonAtom::Const(*value as i128)),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn candidate_from_comparison(
    op: &ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    predicate_id: PredicateId,
    arg_sorts: &[ChcSort],
    body_var_to_state: &HashMap<String, usize>,
    incremented: &HashSet<usize>,
) -> Option<ChcExpr> {
    let lhs = comparison_atom(lhs, body_var_to_state)?;
    let rhs = comparison_atom(rhs, body_var_to_state)?;

    match (lhs, rhs) {
        (ComparisonAtom::State(i), ComparisonAtom::State(j))
            if incremented.contains(&i) || incremented.contains(&j) =>
        {
            let sort_i = arg_sorts.get(i)?;
            let sort_j = arg_sorts.get(j)?;
            if !is_numeric_sort(sort_i) || !is_numeric_sort(sort_j) {
                return None;
            }
            let lhs = canonical_state_expr(predicate_id, i, sort_i);
            let rhs = canonical_state_expr(predicate_id, j, sort_j);
            if is_le_direction(op) {
                Some(make_le(lhs, rhs, sort_i))
            } else {
                Some(make_ge(lhs, rhs, sort_i))
            }
        }
        (ComparisonAtom::State(i), ComparisonAtom::Const(c)) if incremented.contains(&i) => {
            let sort = arg_sorts.get(i)?;
            if !is_numeric_sort(sort) {
                return None;
            }
            let lhs = canonical_state_expr(predicate_id, i, sort);
            let rhs = match sort {
                ChcSort::BitVec(w) => ChcExpr::BitVec(c as u128, *w),
                _ => ChcExpr::int(c as i64),
            };
            if is_le_direction(op) {
                Some(make_le(lhs, rhs, sort))
            } else {
                Some(make_ge(lhs, rhs, sort))
            }
        }
        (ComparisonAtom::Const(c), ComparisonAtom::State(i)) if incremented.contains(&i) => {
            let sort = arg_sorts.get(i)?;
            if !is_numeric_sort(sort) {
                return None;
            }
            let lhs = canonical_state_expr(predicate_id, i, sort);
            let rhs = match sort {
                ChcSort::BitVec(w) => ChcExpr::BitVec(c as u128, *w),
                _ => ChcExpr::int(c as i64),
            };
            // Reversed: const OP state → invert direction.
            if is_le_direction(op) {
                Some(make_ge(lhs, rhs, sort))
            } else {
                Some(make_le(lhs, rhs, sort))
            }
        }
        _ => None,
    }
}

pub(crate) fn canonical_state_expr(
    predicate_id: PredicateId,
    state_idx: usize,
    sort: &ChcSort,
) -> ChcExpr {
    ChcExpr::var(ChcVar::new(format!("__p{}_a{state_idx}", predicate_id.index()), sort.clone()))
}

// ---- sort-polymorphic helpers (shared with the CLI lane's proof-core) ----

/// Returns true for numeric sorts: Int or BitVec of any width.
pub(crate) fn is_numeric_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Int | ChcSort::BitVec(_))
}

/// Returns true if the expression is the constant 1 in any numeric sort.
pub(crate) fn is_const_one(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::Int(1) | ChcExpr::BitVec(1, _))
}

/// Returns true for addition ops (Int `+` or BV `bvadd`).
pub(crate) fn is_add_op(op: &ChcOp) -> bool {
    matches!(op, ChcOp::Add | ChcOp::BvAdd)
}

/// Returns true for subtraction ops (Int `-` or BV `bvsub`).
pub(crate) fn is_sub_op(op: &ChcOp) -> bool {
    matches!(op, ChcOp::Sub | ChcOp::BvSub)
}

/// Returns true for comparison ops (Int or BV, signed or unsigned).
pub(crate) fn is_comparison_op(op: &ChcOp) -> bool {
    matches!(
        op,
        ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
            | ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
    )
}

/// Classify a comparison direction (less-or-equal vs greater-or-equal).
pub(crate) fn is_le_direction(op: &ChcOp) -> bool {
    matches!(op, ChcOp::Lt | ChcOp::Le | ChcOp::BvULt | ChcOp::BvULe | ChcOp::BvSLt | ChcOp::BvSLe)
}

/// Create a `<=` expression for the appropriate sort.
/// Uses signed comparison for BV (safe: signed ≡ unsigned for non-negative values).
pub(crate) fn make_le(a: ChcExpr, b: ChcExpr, sort: &ChcSort) -> ChcExpr {
    match sort {
        ChcSort::BitVec(_) => ChcExpr::Op(ChcOp::BvSLe, vec![Arc::new(a), Arc::new(b)]),
        _ => ChcExpr::le(a, b),
    }
}

/// Create a `>=` expression for the appropriate sort.
pub(crate) fn make_ge(a: ChcExpr, b: ChcExpr, sort: &ChcSort) -> ChcExpr {
    match sort {
        ChcSort::BitVec(_) => ChcExpr::Op(ChcOp::BvSGe, vec![Arc::new(a), Arc::new(b)]),
        _ => ChcExpr::ge(a, b),
    }
}

/// Create a zero constant for the appropriate sort.
pub(crate) fn make_zero(sort: &ChcSort) -> ChcExpr {
    match sort {
        ChcSort::BitVec(w) => ChcExpr::BitVec(0, *w),
        _ => ChcExpr::int(0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay::chc::ChcParser;

    #[test]
    fn scaled_accumulator_template_generates_linear_bound() {
        // acc' = acc + d with 0 <= d <= 255 beside i' = i + 1 — the
        // foreach-accumulate shape. Expect `acc <= 255 * i` and `acc >= 0`.
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel inv (Int Int))
            (declare-var i Int)
            (declare-var acc Int)
            (declare-var d Int)
            (rule (=> (and (= i 0) (= acc 0)) (inv i acc)))
            (rule (=> (and (inv i acc) (< i 256) (>= d 0) (<= d 255))
                      (inv (+ i 1) (+ acc d))))
            (query inv)
            "#,
        )
        .expect("valid CHC script");

        let pred = problem.lookup_predicate("inv").expect("predicate exists");
        let (hints, stats) = generate_lemma_hint_candidates(&problem, HintSource::Native);
        assert!(stats.generated > 0);

        let acc = canonical_state_expr(pred, 1, &ChcSort::Int);
        let i = canonical_state_expr(pred, 0, &ChcSort::Int);
        let expected_scaled = make_le(
            acc.clone(),
            ChcExpr::Op(ChcOp::Mul, vec![Arc::new(ChcExpr::int(255)), Arc::new(i)]),
            &ChcSort::Int,
        );
        let expected_nonneg = make_ge(acc, make_zero(&ChcSort::Int), &ChcSort::Int);
        assert!(
            hints.iter().any(|hint| hint.formula == expected_scaled),
            "expected the scaled accumulator bound acc <= 255*i, got {:?}",
            hints.iter().map(|h| &h.formula).collect::<Vec<_>>()
        );
        assert!(
            hints.iter().any(|hint| hint.formula == expected_nonneg),
            "expected the non-negative accumulator bound"
        );
    }

    #[test]
    fn scaled_accumulator_template_generates_bv_bound() {
        // The REAL trust-mc codegen shape: u32 accumulator + u8 element →
        // BitVec(32) state with bvule range facts (foreach_cast_accumulator).
        // Expect the unsigned scaled bound `acc bvule (bv255 bvmul i)`.
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
            (declare-var i (_ BitVec 32))
            (declare-var acc (_ BitVec 32))
            (declare-var d (_ BitVec 32))
            (rule (=> (and (= i (_ bv0 32)) (= acc (_ bv0 32))) (inv i acc)))
            (rule (=> (and (inv i acc) (bvult i (_ bv256 32)) (bvule d (_ bv255 32)))
                      (inv (bvadd i (_ bv1 32)) (bvadd acc d))))
            (query inv)
            "#,
        )
        .expect("valid BV CHC script");

        let pred = problem.lookup_predicate("inv").expect("predicate exists");
        let (hints, _) = generate_lemma_hint_candidates(&problem, HintSource::Native);
        let bv32 = ChcSort::BitVec(32);
        let acc = canonical_state_expr(pred, 1, &bv32);
        let i = canonical_state_expr(pred, 0, &bv32);
        let expected = ChcExpr::Op(
            ChcOp::BvULe,
            vec![
                Arc::new(acc),
                Arc::new(ChcExpr::Op(
                    ChcOp::BvMul,
                    vec![Arc::new(ChcExpr::BitVec(255, 32)), Arc::new(i)],
                )),
            ],
        );
        assert!(
            hints.iter().any(|hint| hint.formula == expected),
            "expected the unsigned scaled BV bound, got {:?}",
            hints.iter().map(|h| &h.formula).collect::<Vec<_>>()
        );
    }

    #[test]
    fn scaled_accumulator_template_accepts_max_bv127_bound() {
        // Regression: `1i128 << 127` is i128::MIN, so the old signed width
        // check rejected every non-negative BV127 bound. Use the largest
        // valid BV127 literal to exercise the exact boundary without overflow.
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel inv ((_ BitVec 127) (_ BitVec 127)))
            (declare-var i (_ BitVec 127))
            (declare-var acc (_ BitVec 127))
            (declare-var d (_ BitVec 127))
            (rule (=> (and (= i (_ bv0 127)) (= acc (_ bv0 127))) (inv i acc)))
            (rule (=> (and (inv i acc)
                           (bvult i (_ bv2 127))
                           (bvule d (_ bv170141183460469231731687303715884105727 127)))
                      (inv (bvadd i (_ bv1 127)) (bvadd acc d))))
            (query inv)
            "#,
        )
        .expect("valid BV127 CHC script");

        let pred = problem.lookup_predicate("inv").expect("predicate exists");
        let (hints, _) = generate_lemma_hint_candidates(&problem, HintSource::Native);
        let bv127 = ChcSort::BitVec(127);
        let expected = ChcExpr::Op(
            ChcOp::BvULe,
            vec![
                Arc::new(canonical_state_expr(pred, 1, &bv127)),
                Arc::new(ChcExpr::Op(
                    ChcOp::BvMul,
                    vec![
                        Arc::new(ChcExpr::BitVec(i128::MAX as u128, 127)),
                        Arc::new(canonical_state_expr(pred, 0, &bv127)),
                    ],
                )),
            ],
        );
        assert!(
            hints.iter().any(|hint| hint.formula == expected),
            "expected max-width BV127 scaled bound, got {:?}",
            hints.iter().map(|h| &h.formula).collect::<Vec<_>>()
        );
    }

    #[test]
    fn scaled_accumulator_template_skips_unrepresentable_bv128_bound() {
        // 2^127 is a valid unsigned BV128 literal but does not fit the i128
        // bound carrier. It must be ignored, not wrapped to i128::MIN and
        // accidentally reinterpreted as a signed lower bound.
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel inv ((_ BitVec 128) (_ BitVec 128)))
            (declare-var i (_ BitVec 128))
            (declare-var acc (_ BitVec 128))
            (declare-var d (_ BitVec 128))
            (rule (=> (and (= i (_ bv0 128)) (= acc (_ bv0 128))) (inv i acc)))
            (rule (=> (and (inv i acc)
                           (bvult i (_ bv2 128))
                           (bvule d (_ bv170141183460469231731687303715884105728 128)))
                      (inv (bvadd i (_ bv1 128)) (bvadd acc d))))
            (query inv)
            "#,
        )
        .expect("valid BV128 CHC script");

        let (hints, _) = generate_lemma_hint_candidates(&problem, HintSource::Native);
        let has_bv_mul = hints.iter().any(|hint| {
            fn contains_bv_mul(expr: &ChcExpr) -> bool {
                match expr {
                    ChcExpr::Op(ChcOp::BvMul, _) => true,
                    ChcExpr::Op(_, args) => args.iter().any(|arg| contains_bv_mul(arg)),
                    _ => false,
                }
            }
            contains_bv_mul(&hint.formula)
        });
        assert!(!has_bv_mul, "unrepresentable BV128 bound must fail closed");
    }

    #[test]
    fn scaled_accumulator_literal_width_boundaries_are_unsigned() {
        let max_signed = i128::MAX;
        assert_eq!(nonnegative_bitvec_literal(max_signed, 126), None);
        assert_eq!(
            nonnegative_bitvec_literal(max_signed, 127),
            Some(ChcExpr::BitVec(max_signed as u128, 127))
        );
        assert_eq!(
            nonnegative_bitvec_literal(max_signed, 128),
            Some(ChcExpr::BitVec(max_signed as u128, 128))
        );
        assert_eq!(nonnegative_bitvec_literal(-1, 128), None);
        assert_eq!(nonnegative_bitvec_literal(0, 0), None);
    }

    #[test]
    fn scaled_accumulator_refuses_state_addend() {
        // Adversarial twin: `acc' = acc + end` where `end` IS a state var —
        // not a transition input; the W3 template must not fire (W2's
        // difference bound may still, but no Mul-shaped candidate).
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel inv (Int Int Int))
            (declare-var i Int)
            (declare-var acc Int)
            (declare-var end Int)
            (rule (=> (and (= i 0) (= acc 0)) (inv i acc end)))
            (rule (=> (and (inv i acc end) (< i end))
                      (inv (+ i 1) (+ acc end) end)))
            (query inv)
            "#,
        )
        .expect("valid CHC script");

        let (hints, _) = generate_lemma_hint_candidates(&problem, HintSource::Native);
        let has_mul = hints.iter().any(|hint| {
            let mut found = false;
            fn walk(e: &ChcExpr, found: &mut bool) {
                if let ChcExpr::Op(op, args) = e {
                    if matches!(op, ChcOp::Mul) {
                        *found = true;
                    }
                    for a in args {
                        walk(a, found);
                    }
                }
            }
            walk(&hint.formula, &mut found);
            found
        });
        assert!(!has_mul, "a state-var addend must not mint a scaled bound");
    }
}

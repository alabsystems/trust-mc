// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC auto-invariant seed extraction.

use super::auto_invariants::{canonical_state_expr, generate_auto_invariant_hints};
use crate::args::AYChcAutoInvariantsMode;
use ay::chc::{ChcExpr, ChcParser};

#[test]
fn mode_off_generates_no_hints() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-var i Int)
        (declare-var end Int)
        (rule (=> true (inv i end)))
        (rule (=> (and (inv i end) (< i end)) (inv (+ i 1) end)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Off);
    assert!(hints.is_empty(), "off mode should not emit hints");
    assert_eq!(stats.generated, 0);
}

#[test]
fn range_mode_extracts_progress_and_bound_candidates() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-var i Int)
        (declare-var end Int)
        (rule (=> (and (>= i 0) (< i end)) (inv i end)))
        (rule (=> (and (inv i end) (< i end)) (inv (+ i 1) end)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let pred = problem.lookup_predicate("inv").expect("predicate exists");
    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);

    let expected_non_negative =
        ChcExpr::ge(canonical_state_expr(pred, 0, &ay::chc::ChcSort::Int), ChcExpr::int(0));
    let expected_upper_bound = ChcExpr::le(
        canonical_state_expr(pred, 0, &ay::chc::ChcSort::Int),
        canonical_state_expr(pred, 1, &ay::chc::ChcSort::Int),
    );

    assert!(
        hints.iter().any(|hint| hint.formula == expected_non_negative),
        "expected non-negative progress candidate"
    );
    assert!(
        hints.iter().any(|hint| hint.formula == expected_upper_bound),
        "expected idx <= end range candidate"
    );
    assert!(
        hints.iter().all(|hint| hint.source == "trust_mc-auto-inv-range"),
        "range mode should use range source label"
    );
    assert!(stats.range_like_clauses >= 1, "range clause should be counted in stats");
}

#[test]
fn duplicate_recursive_clauses_do_not_duplicate_candidates() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-var i Int)
        (declare-var end Int)
        (rule (=> true (inv i end)))
        (rule (=> (and (inv i end) (< i end)) (inv (+ i 1) end)))
        (rule (=> (and (inv i end) (< i end)) (inv (+ i 1) end)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);
    assert_eq!(
        hints.len(),
        2,
        "duplicate clauses should collapse to two unique hints (progress bound + non-negativity)"
    );
    assert_eq!(stats.generated, 2, "stats should report deduplicated count");
}

#[test]
fn non_progressing_transition_produces_no_candidates() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-var i Int)
        (declare-var end Int)
        (rule (=> true (inv i end)))
        (rule (=> (and (inv i end) (< i end)) (inv i end)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);
    assert!(hints.is_empty(), "non-progressing transitions should not be promoted");
    assert_eq!(stats.generated, 0);
}

#[test]
fn range_mode_extracts_countdown_lower_bound_candidate() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-var i Int)
        (declare-var lo Int)
        (rule (=> (and (>= i lo) (>= lo 0)) (inv i lo)))
        (rule (=> (and (inv i lo) (> i lo)) (inv (- i 1) lo)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let pred = problem.lookup_predicate("inv").expect("predicate exists");
    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);

    let expected_lower_bound = ChcExpr::ge(
        canonical_state_expr(pred, 0, &ay::chc::ChcSort::Int),
        canonical_state_expr(pred, 1, &ay::chc::ChcSort::Int),
    );
    let expected_non_negative =
        ChcExpr::ge(canonical_state_expr(pred, 0, &ay::chc::ChcSort::Int), ChcExpr::int(0));

    assert!(stats.range_like_clauses >= 1, "countdown clause should be counted");
    assert!(
        hints.iter().any(|hint| hint.formula == expected_lower_bound),
        "expected countdown lower-bound candidate"
    );
    assert!(
        hints.iter().any(|hint| hint.formula == expected_non_negative),
        "expected countdown non-negative candidate"
    );
}

#[test]
fn houdini_mode_generates_widening_candidates() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-var i Int)
        (declare-var end Int)
        (rule (=> (and (>= i 0) (< i end)) (inv i end)))
        (rule (=> (and (inv i end) (< i end)) (inv (+ i 1) end)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let pred = problem.lookup_predicate("inv").expect("predicate exists");

    let (range_hints, range_stats) =
        generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);
    let (houdini_hints, houdini_stats) =
        generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Houdini);

    assert!(
        houdini_hints.len() > range_hints.len(),
        "Houdini mode should generate more candidates than Range mode \
         (houdini={}, range={})",
        houdini_hints.len(),
        range_hints.len()
    );
    assert!(houdini_stats.widening_added > 0, "Houdini stats should track widening additions");
    assert_eq!(range_stats.widening_added, 0, "Range mode should not add widening candidates");

    // Houdini should produce `end >= i` (difference-bound) via W2.
    let expected_diff_bound = ChcExpr::ge(
        canonical_state_expr(pred, 1, &ay::chc::ChcSort::Int),
        canonical_state_expr(pred, 0, &ay::chc::ChcSort::Int),
    );
    assert!(
        houdini_hints.iter().any(|h| h.formula == expected_diff_bound),
        "Houdini should generate difference-bound candidate `end >= idx`"
    );

    assert!(
        houdini_hints.iter().all(|h| h.source == "trust_mc-auto-inv-houdini-seed"),
        "Houdini mode should use houdini source label"
    );
}

#[test]
fn houdini_equality_preservation_emits_bound_for_preserved_vars() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int Int))
        (declare-var i Int)
        (declare-var start Int)
        (declare-var end Int)
        (rule (=> (and (>= i start) (< i end)) (inv i start end)))
        (rule (=> (and (inv i start end) (< i end)) (inv (+ i 1) start end)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let pred = problem.lookup_predicate("inv").expect("predicate exists");
    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Houdini);

    let expected_le_start = ChcExpr::le(
        canonical_state_expr(pred, 0, &ay::chc::ChcSort::Int),
        canonical_state_expr(pred, 1, &ay::chc::ChcSort::Int),
    );
    let expected_le_end = ChcExpr::le(
        canonical_state_expr(pred, 0, &ay::chc::ChcSort::Int),
        canonical_state_expr(pred, 2, &ay::chc::ChcSort::Int),
    );

    assert!(
        hints.iter().any(|h| h.formula == expected_le_start),
        "Houdini should emit `i <= start` for preserved start"
    );
    assert!(
        hints.iter().any(|h| h.formula == expected_le_end),
        "Houdini should emit `i <= end` for preserved end"
    );
    assert!(stats.widening_added >= 2, "at least 2 widening candidates expected");
}

#[test]
fn budget_cap_prevents_unbounded_candidate_growth() {
    use super::auto_invariants::MAX_CANDIDATES_PER_PREDICATE;

    let mut comparisons = String::new();
    for c in 0..=(MAX_CANDIDATES_PER_PREDICATE + 10) {
        comparisons.push_str(&format!("(< i {c}) "));
    }
    let script = format!(
        "(set-logic HORN)\n\
         (declare-rel inv (Int Int))\n\
         (declare-var i Int)\n\
         (declare-var end Int)\n\
         (rule (=> true (inv i end)))\n\
         (rule (=> (and (inv i end) {comparisons} (< i end)) (inv (+ i 1) end)))\n\
         (query inv)\n"
    );

    let problem = ChcParser::parse(&script).expect("valid CHC script");
    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);

    assert!(
        hints.len() <= MAX_CANDIDATES_PER_PREDICATE,
        "hints ({}) should not exceed per-predicate budget ({})",
        hints.len(),
        MAX_CANDIDATES_PER_PREDICATE
    );
    assert!(
        stats.budget_capped > 0,
        "budget_capped stat should be nonzero when budget is exceeded"
    );
}

#[test]
fn range_mode_does_not_set_widening_or_budget_stats() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv (Int Int))
        (declare-var i Int)
        (declare-var end Int)
        (rule (=> true (inv i end)))
        (rule (=> (and (inv i end) (< i end)) (inv (+ i 1) end)))
        (query inv)
        "#,
    )
    .expect("valid CHC script");

    let (_, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);
    assert_eq!(stats.widening_added, 0, "Range mode should not produce widening candidates");
    assert_eq!(stats.budget_capped, 0, "small problem should not hit budget cap");
}

/// Part of #2875: verify that BV-sorted predicates are detected by the
/// sort-polymorphic helpers (BV-aware detection). This mirrors the Int-based
/// `range_mode_extracts_progress_and_bound_candidates` test using BitVec(32).
#[test]
fn bv_range_mode_extracts_bitvec_candidates() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
        (declare-var i (_ BitVec 32))
        (declare-var end (_ BitVec 32))
        (rule (=> (and (bvule (_ bv0 32) i) (bvslt i end)) (inv i end)))
        (rule (=> (and (inv i end) (bvslt i end)) (inv (bvadd i (_ bv1 32)) end)))
        (query inv)
        "#,
    )
    .expect("valid BV CHC script");

    let pred = problem.lookup_predicate("inv").expect("predicate exists");
    let bv32 = ay::chc::ChcSort::BitVec(32);

    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);

    // Should detect incremented index and generate candidates.
    assert!(
        stats.range_like_clauses >= 1,
        "BV range clause should be counted (got {})",
        stats.range_like_clauses
    );
    assert!(!hints.is_empty(), "BV range loop should produce at least one candidate hint");

    // Check for `i >= 0` (using BvSGe).
    let expected_non_negative = super::sort_helpers::make_ge(
        canonical_state_expr(pred, 0, &bv32),
        super::sort_helpers::make_zero(&bv32),
        &bv32,
    );
    assert!(
        hints.iter().any(|hint| hint.formula == expected_non_negative),
        "expected BV non-negative progress candidate: {expected_non_negative:?}\n\
         actual hints: {hints:?}"
    );

    // Check for `i <= end` (using BvSLe).
    let expected_upper_bound = super::sort_helpers::make_le(
        canonical_state_expr(pred, 0, &bv32),
        canonical_state_expr(pred, 1, &bv32),
        &bv32,
    );
    assert!(
        hints.iter().any(|hint| hint.formula == expected_upper_bound),
        "expected BV idx <= end range candidate: {expected_upper_bound:?}\n\
         actual hints: {hints:?}"
    );
}

/// Part of #2875: BV Houdini mode should generate widening candidates
/// (equality-preservation and difference-bound) for BV-sorted predicates.
#[test]
fn bv_houdini_mode_generates_bitvec_widening_candidates() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
        (declare-var i (_ BitVec 32))
        (declare-var end (_ BitVec 32))
        (rule (=> (and (bvule (_ bv0 32) i) (bvslt i end)) (inv i end)))
        (rule (=> (and (inv i end) (bvslt i end)) (inv (bvadd i (_ bv1 32)) end)))
        (query inv)
        "#,
    )
    .expect("valid BV CHC script");

    let pred = problem.lookup_predicate("inv").expect("predicate exists");
    let bv32 = ay::chc::ChcSort::BitVec(32);

    let (range_hints, _) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);
    let (houdini_hints, houdini_stats) =
        generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Houdini);

    assert!(
        houdini_hints.len() > range_hints.len(),
        "BV Houdini should generate more candidates than Range \
         (houdini={}, range={})",
        houdini_hints.len(),
        range_hints.len()
    );
    assert!(houdini_stats.widening_added > 0, "BV Houdini stats should track widening additions");

    // Should produce `end >= i` (difference-bound) via W2.
    let expected_diff_bound = super::sort_helpers::make_ge(
        canonical_state_expr(pred, 1, &bv32),
        canonical_state_expr(pred, 0, &bv32),
        &bv32,
    );
    assert!(
        houdini_hints.iter().any(|h| h.formula == expected_diff_bound),
        "BV Houdini should generate difference-bound candidate `end >= idx`"
    );
}

#[test]
fn bv_range_mode_extracts_bvsub_countdown_candidate() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
        (declare-var i (_ BitVec 32))
        (declare-var lo (_ BitVec 32))
        (rule (=> (and (bvsge i lo) (bvsge lo (_ bv0 32))) (inv i lo)))
        (rule (=> (and (inv i lo) (bvsgt i lo)) (inv (bvsub i (_ bv1 32)) lo)))
        (query inv)
        "#,
    )
    .expect("valid BV CHC script");

    let pred = problem.lookup_predicate("inv").expect("predicate exists");
    let bv32 = ay::chc::ChcSort::BitVec(32);

    let (hints, stats) = generate_auto_invariant_hints(&problem, AYChcAutoInvariantsMode::Range);

    let expected_lower_bound = super::sort_helpers::make_ge(
        canonical_state_expr(pred, 0, &bv32),
        canonical_state_expr(pred, 1, &bv32),
        &bv32,
    );
    assert!(stats.range_like_clauses >= 1, "BV countdown clause should be counted");
    assert!(
        hints.iter().any(|hint| hint.formula == expected_lower_bound),
        "expected BV countdown lower-bound candidate: {expected_lower_bound:?}\n\
         actual hints: {hints:?}"
    );
}

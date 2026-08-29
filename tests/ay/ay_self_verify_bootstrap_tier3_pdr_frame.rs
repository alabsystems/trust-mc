// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! AY self-verification bootstrap Tier 3: PDR Frame + MustSummaries invariants.
//!
//! Standalone models from:
//! - `ay-chc/src/pdr/frame.rs`: Frame dedup, revision monotonicity, MustSummaries
//!
//! Flat-scalar encoding: BTreeMap/BTreeSet/Vec replaced with fixed arrays.
//! Integer-coded ChcExpr to avoid 4-variant enum discriminant collapse (#3521).
//!
//! Source: 6 harnesses total
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ========================================================================
// Integer-coded ChcExpr (avoids 4-variant enum discriminant collapse #3521)
// ========================================================================

// ChcExpr encoded as u8:
//   0 = BoolTrue, 1 = BoolFalse, 2 = Int(42), 3 = Var(0)
const EXPR_TRUE: u8 = 0;
const EXPR_FALSE: u8 = 1;
const EXPR_INT: u8 = 2;

type PredicateId = u32;

// ========================================================================
// Lemma — flat scalar fields
// ========================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lemma {
    predicate: PredicateId,
    formula: u8,
    level: u32,
    algebraically_verified: bool,
}

impl Lemma {
    fn new(predicate: PredicateId, formula: u8, level: u32) -> Self {
        Self { predicate, formula, level, algebraically_verified: false }
    }
}

// ========================================================================
// Frame — flat-capacity (max 8 lemmas)
// ========================================================================

const MAX_LEMMAS: usize = 8;

#[derive(Clone, Copy)]
struct Frame {
    // Lemma storage (fields split for flat encoding)
    lem_pred: [PredicateId; MAX_LEMMAS],
    lem_form: [u8; MAX_LEMMAS],
    lem_level: [u32; MAX_LEMMAS],
    lem_alg: [bool; MAX_LEMMAS],
    lemma_len: usize,
    // Dedup: track (predicate, formula) keys
    seen_pred: [PredicateId; MAX_LEMMAS],
    seen_form: [u8; MAX_LEMMAS],
    seen_len: usize,
    // Revision counts per predicate (max 4 predicates)
    rev_preds: [PredicateId; 4],
    rev_counts: [u64; 4],
    rev_len: usize,
}

impl Frame {
    fn new() -> Self {
        Self {
            lem_pred: [0; MAX_LEMMAS],
            lem_form: [0; MAX_LEMMAS],
            lem_level: [0; MAX_LEMMAS],
            lem_alg: [false; MAX_LEMMAS],
            lemma_len: 0,
            seen_pred: [0; MAX_LEMMAS],
            seen_form: [0; MAX_LEMMAS],
            seen_len: 0,
            rev_preds: [0; 4],
            rev_counts: [0; 4],
            rev_len: 0,
        }
    }

    fn has_seen(&self, pred: PredicateId, formula: u8) -> bool {
        let mut i = 0;
        while i < self.seen_len {
            if self.seen_pred[i] == pred && self.seen_form[i] == formula {
                return true;
            }
            i += 1;
        }
        false
    }

    fn add_lemma(&mut self, lemma: Lemma) {
        if self.has_seen(lemma.predicate, lemma.formula) {
            return; // deduplicate
        }
        if self.seen_len < MAX_LEMMAS {
            self.seen_pred[self.seen_len] = lemma.predicate;
            self.seen_form[self.seen_len] = lemma.formula;
            self.seen_len += 1;
        }
        // Update revision counter
        let mut found = false;
        let mut i = 0;
        while i < self.rev_len {
            if self.rev_preds[i] == lemma.predicate {
                self.rev_counts[i] += 1;
                found = true;
                break;
            }
            i += 1;
        }
        if !found && self.rev_len < 4 {
            self.rev_preds[self.rev_len] = lemma.predicate;
            self.rev_counts[self.rev_len] = 1;
            self.rev_len += 1;
        }
        if self.lemma_len < MAX_LEMMAS {
            self.lem_pred[self.lemma_len] = lemma.predicate;
            self.lem_form[self.lemma_len] = lemma.formula;
            self.lem_level[self.lemma_len] = lemma.level;
            self.lem_alg[self.lemma_len] = lemma.algebraically_verified;
            self.lemma_len += 1;
        }
    }

    fn predicate_lemma_revision(&self, pred: PredicateId) -> u64 {
        let mut i = 0;
        while i < self.rev_len {
            if self.rev_preds[i] == pred {
                return self.rev_counts[i];
            }
            i += 1;
        }
        0
    }
}

// ========================================================================
// MustSummaries — minimal capacity for inline-friendly verification
// ========================================================================
//
// Reduced to scalar fields to eliminate loops and keep all methods under
// the 16-block MIR inline gate. Harnesses only need 1 entry slot (dedup
// adds same entry twice; true_subsumes uses has_true_for path).
// The inline translator bails on while-loop back-edges (cycle detection),
// so all search logic must be loop-free. See #3836.

#[derive(Clone, Copy)]
struct MustSummaries {
    // Single entry slot — sufficient for dedup/subsumption proofs
    ent_level: u32,
    ent_pred: PredicateId,
    ent_form: u8,
    has_entry: bool,
    // Single true-key slot
    ht_level: u32,
    ht_pred: PredicateId,
    has_true: bool,
}

impl MustSummaries {
    fn new() -> Self {
        Self {
            ent_level: 0,
            ent_pred: 0,
            ent_form: 0,
            has_entry: false,
            ht_level: 0,
            ht_pred: 0,
            has_true: false,
        }
    }

    fn has_true_for(&self, level: u32, pred: PredicateId) -> bool {
        self.has_true && self.ht_level == level && self.ht_pred == pred
    }

    fn contains(&self, level: u32, pred: PredicateId, formula: u8) -> bool {
        self.has_entry
            && self.ent_level == level
            && self.ent_pred == pred
            && self.ent_form == formula
    }

    fn reject_existing(&self, level: u32, pred: PredicateId, formula: u8) -> bool {
        formula == EXPR_FALSE
            || self.has_true_for(level, pred)
            || self.contains(level, pred, formula)
    }

    fn record_true_key(&mut self, level: u32, pred: PredicateId) {
        if !self.has_true {
            self.ht_level = level;
            self.ht_pred = pred;
            self.has_true = true;
        }
    }

    fn push_entry(&mut self, level: u32, pred: PredicateId, formula: u8) {
        if !self.has_entry {
            self.ent_level = level;
            self.ent_pred = pred;
            self.ent_form = formula;
            self.has_entry = true;
        }
    }

    fn add(&mut self, level: u32, pred: PredicateId, formula: u8) -> bool {
        if self.reject_existing(level, pred, formula) {
            return false;
        }
        if formula == EXPR_TRUE {
            self.record_true_key(level, pred);
        }
        self.push_entry(level, pred, formula);
        true
    }
}

// ========================================================================
// Helper: generate symbolic values
// ========================================================================

fn any_predicate_id() -> PredicateId {
    let p: u8 = kani::any();
    kani::assume(p < 4);
    p as PredicateId
}

fn any_simple_expr() -> u8 {
    let choice: u8 = kani::any();
    kani::assume(choice < 4);
    choice
}

fn any_lemma() -> Lemma {
    let predicate = any_predicate_id();
    let formula = any_simple_expr();
    let level: u32 = {
        let l: u8 = kani::any();
        kani::assume(l < 5);
        l as u32
    };
    let algebraically_verified: bool = kani::any();

    Lemma { predicate, formula, level, algebraically_verified }
}

// ========================================================================
// Harnesses
// ========================================================================

/// Adding the same lemma twice results in no duplicate.
#[kani::proof]
fn proof_frame_add_lemma_deduplicates() {
    let mut frame = Frame::new();
    let lemma = any_lemma();
    let lemma_clone = lemma;

    frame.add_lemma(lemma);
    let count_after_first = frame.lemma_len;

    frame.add_lemma(lemma_clone);
    let count_after_second = frame.lemma_len;

    assert!(count_after_first == count_after_second);
}

/// Revision counter is monotonically non-decreasing.
#[kani::proof]
fn proof_frame_revision_monotonic() {
    let mut frame = Frame::new();
    let pred = any_predicate_id();

    let rev_before = frame.predicate_lemma_revision(pred);

    let lemma = Lemma::new(pred, any_simple_expr(), 1);
    frame.add_lemma(lemma);

    let rev_after = frame.predicate_lemma_revision(pred);

    assert!(rev_after >= rev_before);
}

/// MustSummaries deduplicates identical non-special formulas.
#[kani::proof]
fn proof_must_summaries_deduplicates() {
    let mut summaries = MustSummaries::new();
    let pred = any_predicate_id();
    let level: u32 = {
        let l: u8 = kani::any();
        kani::assume(l < 3);
        l as u32
    };
    let formula = any_simple_expr();
    kani::assume(formula >= EXPR_INT);

    let _first_add = summaries.add(level, pred, formula);
    let second_add = summaries.add(level, pred, formula);

    assert!(!second_add, "Duplicate formula should be rejected");
}

/// After adding true, subsequent non-true formulas are rejected (subsumed).
#[kani::proof]
fn proof_must_summaries_true_subsumes() {
    let mut summaries = MustSummaries::new();
    let pred = any_predicate_id();
    let level: u32 = 1;

    let added_true = summaries.add(level, pred, EXPR_TRUE);
    kani::assume(added_true);

    let added_int = summaries.add(level, pred, EXPR_INT);

    assert!(!added_int, "Non-true formula should be rejected after true");
}

/// MustSummaries rejects false formulas.
#[kani::proof]
fn proof_must_summaries_rejects_false() {
    let mut summaries = MustSummaries::new();
    let pred = any_predicate_id();
    let level: u32 = 1;

    let added = summaries.add(level, pred, EXPR_FALSE);

    assert!(!added, "false formula should be rejected");
}

/// Frame starts empty with zero revision.
#[kani::proof]
fn proof_frame_new_is_empty() {
    let frame = Frame::new();
    let pred = any_predicate_id();

    assert!(frame.lemma_len == 0);
    assert!(frame.predicate_lemma_revision(pred) == 0);
}

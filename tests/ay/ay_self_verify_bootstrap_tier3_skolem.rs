// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// NOTE: Demoted PROOF→UNKNOWN pending false proof defense re-measurement (ay#8578).

//! AY self-verification bootstrap Tier 3m: String theory SkolemCache harnesses.
//!
//! These harnesses verify the SkolemCache data structure used in ay's string
//! theory solver for deduplicating split lemma generation. The cache tracks
//! which splits have already been emitted and supports incremental push/pop.
//!
//! Ported from `ay-theories/strings/src/skolem.rs`.
//!
//! The standalone mirror uses flat scalar fields (no Vec, no HashMap, no arrays)
//! to avoid CHC encoding gaps on containers and nested struct dispatch.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// Standalone SkolemCache — flat scalar encoding
// Kind tags: 0=EmptySplit, 1=ConstSplit, 2=VarSplit
// Key = (t1, t2, kind, char_offset) — 4 u32 scalars
// Capacity: 2 key slots + 1 scope level (sufficient for all 7 harnesses)
// ============================================================

const KIND_EMPTY: u32 = 0;
const KIND_CONST: u32 = 1;
const KIND_VAR: u32 = 2;
const DUMMY: u32 = u32::MAX;

struct SkolemCache {
    // Key slot 0
    k0_t1: u32,
    k0_t2: u32,
    k0_kind: u32,
    k0_off: u32,
    // Key slot 1
    k1_t1: u32,
    k1_t2: u32,
    k1_kind: u32,
    k1_off: u32,
    // Number of active keys
    key_len: u32,
    // Scope: saved key_len at push time
    scope_len: u32,
    has_scope: bool,
}

impl SkolemCache {
    fn new() -> Self {
        Self {
            k0_t1: 0,
            k0_t2: 0,
            k0_kind: 0,
            k0_off: 0,
            k1_t1: 0,
            k1_t2: 0,
            k1_kind: 0,
            k1_off: 0,
            key_len: 0,
            scope_len: 0,
            has_scope: false,
        }
    }

    fn mark_empty_split(&mut self, x: u32) -> bool {
        let t1 = x;
        let t2 = DUMMY;
        let kind = KIND_EMPTY;
        let off: u32 = 0;
        // inline contains + insert
        if (self.key_len >= 1
            && self.k0_t1 == t1
            && self.k0_t2 == t2
            && self.k0_kind == kind
            && self.k0_off == off)
            || (self.key_len >= 2
                && self.k1_t1 == t1
                && self.k1_t2 == t2
                && self.k1_kind == kind
                && self.k1_off == off)
        {
            return false;
        }
        if self.key_len == 0 {
            self.k0_t1 = t1;
            self.k0_t2 = t2;
            self.k0_kind = kind;
            self.k0_off = off;
            self.key_len = 1;
        } else if self.key_len == 1 {
            self.k1_t1 = t1;
            self.k1_t2 = t2;
            self.k1_kind = kind;
            self.k1_off = off;
            self.key_len = 2;
        }
        true
    }

    fn mark_const_split(&mut self, x: u32, constant: u32, char_offset: u32) -> bool {
        let t1 = x;
        let t2 = constant;
        let kind = KIND_CONST;
        let off = char_offset;
        if (self.key_len >= 1
            && self.k0_t1 == t1
            && self.k0_t2 == t2
            && self.k0_kind == kind
            && self.k0_off == off)
            || (self.key_len >= 2
                && self.k1_t1 == t1
                && self.k1_t2 == t2
                && self.k1_kind == kind
                && self.k1_off == off)
        {
            return false;
        }
        if self.key_len == 0 {
            self.k0_t1 = t1;
            self.k0_t2 = t2;
            self.k0_kind = kind;
            self.k0_off = off;
            self.key_len = 1;
        } else if self.key_len == 1 {
            self.k1_t1 = t1;
            self.k1_t2 = t2;
            self.k1_kind = kind;
            self.k1_off = off;
            self.key_len = 2;
        }
        true
    }

    fn normalize_var_pair(x: u32, y: u32) -> (u32, u32) {
        if x <= y { (x, y) } else { (y, x) }
    }

    fn mark_var_split(&mut self, x: u32, y: u32) -> bool {
        let (lhs, rhs) = Self::normalize_var_pair(x, y);
        let t1 = lhs;
        let t2 = rhs;
        let kind = KIND_VAR;
        let off: u32 = 0;
        if (self.key_len >= 1
            && self.k0_t1 == t1
            && self.k0_t2 == t2
            && self.k0_kind == kind
            && self.k0_off == off)
            || (self.key_len >= 2
                && self.k1_t1 == t1
                && self.k1_t2 == t2
                && self.k1_kind == kind
                && self.k1_off == off)
        {
            return false;
        }
        if self.key_len == 0 {
            self.k0_t1 = t1;
            self.k0_t2 = t2;
            self.k0_kind = kind;
            self.k0_off = off;
            self.key_len = 1;
        } else if self.key_len == 1 {
            self.k1_t1 = t1;
            self.k1_t2 = t2;
            self.k1_kind = kind;
            self.k1_off = off;
            self.key_len = 2;
        }
        true
    }

    fn push(&mut self) {
        self.scope_len = self.key_len;
        self.has_scope = true;
    }

    fn pop(&mut self) {
        if self.has_scope {
            self.key_len = self.scope_len;
            self.has_scope = false;
        }
    }

    fn reset(&mut self) {
        self.key_len = 0;
        self.has_scope = false;
    }
}

// ============================================================
// Harnesses
// ============================================================

/// Port of ay::strings::skolem::proof_empty_split_idempotent
#[kani::proof]
fn ay_strings_empty_split_idempotent() {
    let id: u32 = kani::any();
    let mut cache = SkolemCache::new();
    let first = cache.mark_empty_split(id);
    let second = cache.mark_empty_split(id);
    assert!(first, "first mark on fresh cache must return true");
    assert!(!second, "second mark on same term must return false");
}

/// Port of ay::strings::skolem::proof_const_split_offset_distinguishes
#[kani::proof]
fn ay_strings_const_split_offset_distinguishes() {
    let x_id: u32 = kani::any();
    let c_id: u32 = kani::any();
    let off1: u8 = kani::any();
    let off2: u8 = kani::any();
    kani::assume(off1 != off2);

    let mut cache = SkolemCache::new();
    let first = cache.mark_const_split(x_id, c_id, off1 as u32);
    let second = cache.mark_const_split(x_id, c_id, off2 as u32);
    assert!(first, "first offset must be new");
    assert!(second, "different offset must also be new");
}

/// Port of ay::strings::skolem::proof_var_split_symmetry
#[kani::proof]
fn ay_strings_var_split_symmetry() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();

    let (a1, b1) = SkolemCache::normalize_var_pair(x_id, y_id);
    let (a2, b2) = SkolemCache::normalize_var_pair(y_id, x_id);
    assert!(a1 == a2, "symmetric inputs must produce same first element");
    assert!(b1 == b2, "symmetric inputs must produce same second element");
}

/// Port of ay::strings::skolem::proof_var_pair_ordered
#[kani::proof]
fn ay_strings_var_pair_ordered() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();

    let (lo, hi) = SkolemCache::normalize_var_pair(x_id, y_id);
    assert!(lo <= hi, "normalized pair must be ordered: lo <= hi");
}

/// Port of ay::strings::skolem::proof_push_pop_scope_restoration
#[kani::proof]
fn ay_strings_push_pop_scope_restoration() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();
    kani::assume(x_id != y_id);

    let mut cache = SkolemCache::new();

    assert!(cache.mark_empty_split(x_id));
    cache.push();

    assert!(cache.mark_empty_split(y_id));
    assert!(!cache.mark_empty_split(y_id), "y already marked in this scope");

    cache.pop();

    assert!(!cache.mark_empty_split(x_id), "x was marked before push, must persist");
    assert!(cache.mark_empty_split(y_id), "y was marked after push, must be undone by pop");
}

/// Port of ay::strings::skolem::proof_var_split_symmetric_dedup
#[kani::proof]
fn ay_strings_var_split_symmetric_dedup() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();

    let mut cache = SkolemCache::new();
    let first = cache.mark_var_split(x_id, y_id);
    let second = cache.mark_var_split(y_id, x_id);
    assert!(first, "first var split on fresh cache must be true");
    assert!(!second, "symmetric pair must deduplicate");
}

/// Port of ay::strings::skolem::proof_reset_clears_all_marks
#[kani::proof]
fn ay_strings_reset_clears_all_marks() {
    let x_id: u32 = kani::any();
    let mut cache = SkolemCache::new();

    assert!(cache.mark_empty_split(x_id));
    assert!(!cache.mark_empty_split(x_id));
    cache.reset();
    assert!(cache.mark_empty_split(x_id), "reset must clear all marks");
}

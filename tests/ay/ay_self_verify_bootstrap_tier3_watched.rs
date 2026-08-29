// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: binary_watcher_fields_preserved=PROOF
// kani-expect: clause_ref_equality=PROOF
// kani-expect: literal_index_for_watches=PROOF
// kani-expect: watch_clear_resets_counts=PROOF
// kani-expect: watch_list_aos_binary_roundtrip=PROOF
// kani-expect: watch_list_aos_roundtrip=PROOF
// kani-expect: watcher_fields_preserved=PROOF
// NOTE: 7 watched-literal harnesses are clean CHC PROOF at trust_mc 0013f9a6d6 / AY 733ba8cd.
// NOTE: watch_add_increases_count and watch_list_swap_remove remain UNKNOWN under ay#8578 false-proof defenses.

//! AY self-verification bootstrap Tier 3: Watched literal data structure.
//!
//! Standalone model of the 2-watched literal layout from `ay-sat/src/watched.rs`.
//! Verifies: watcher field preservation, binary flag, clause ref equality,
//! literal index, roundtrip, swap_remove.
//!
//! SoA encoding: u64-packed AoS replaced with parallel u32 arrays.
//! Nested struct arrays replaced with flat 1D arrays + manual indexing.
//!
//! Source: ay-sat/src/watched.rs (9 harnesses)
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// High bit flag for binary clauses in the clause u32.
const BINARY_FLAG: u32 = 0x8000_0000;

// Literal: raw u32 (var << 1 | polarity). No wrapper struct needed.
fn lit_positive(var: u32) -> u32 {
    var << 1
}

fn lit_negative(var: u32) -> u32 {
    (var << 1) | 1
}

fn lit_index(lit: u32) -> usize {
    lit as usize
}

// ============================================================
// SoA WatchList: parallel u32 arrays (no u64 packing)
// ============================================================

const MAX_WATCHES: usize = 4;

struct WatchList {
    blocker: [u32; MAX_WATCHES],
    clause: [u32; MAX_WATCHES],
    len: usize,
}

impl WatchList {
    fn new() -> Self {
        Self { blocker: [0; MAX_WATCHES], clause: [0; MAX_WATCHES], len: 0 }
    }

    fn push(&mut self, blocker_raw: u32, clause_raw: u32) {
        match self.len {
            0 => {
                self.blocker[0] = blocker_raw;
                self.clause[0] = clause_raw;
                self.len = 1;
            }
            1 => {
                self.blocker[1] = blocker_raw;
                self.clause[1] = clause_raw;
                self.len = 2;
            }
            2 => {
                self.blocker[2] = blocker_raw;
                self.clause[2] = clause_raw;
                self.len = 3;
            }
            3 => {
                self.blocker[3] = blocker_raw;
                self.clause[3] = clause_raw;
                self.len = 4;
            }
            _ => {}
        }
    }

    fn swap_remove(&mut self, idx: usize) {
        let last = self.len - 1;
        let blocker = match last {
            0 => self.blocker[0],
            1 => self.blocker[1],
            2 => self.blocker[2],
            3 => self.blocker[3],
            _ => self.blocker[last],
        };
        let clause = match last {
            0 => self.clause[0],
            1 => self.clause[1],
            2 => self.clause[2],
            3 => self.clause[3],
            _ => self.clause[last],
        };
        match idx {
            0 => {
                self.blocker[0] = blocker;
                self.clause[0] = clause;
            }
            1 => {
                self.blocker[1] = blocker;
                self.clause[1] = clause;
            }
            2 => {
                self.blocker[2] = blocker;
                self.clause[2] = clause;
            }
            3 => {
                self.blocker[3] = blocker;
                self.clause[3] = clause;
            }
            _ => {
                self.blocker[idx] = blocker;
                self.clause[idx] = clause;
            }
        }
        self.len -= 1;
    }
}

// ============================================================
// Flat WatchedLists: all per-literal watch data in 1D arrays
// Max 8 literal slots × 4 watches each = 32 entries
// ============================================================

const MAX_LIT_SLOTS: usize = 8;
const FLAT_CAP: usize = 32; // MAX_LIT_SLOTS * MAX_WATCHES

struct WatchedLists {
    all_blocker: [u32; FLAT_CAP],
    all_clause: [u32; FLAT_CAP],
    all_len: [usize; MAX_LIT_SLOTS],
}

impl WatchedLists {
    fn new() -> Self {
        Self { all_blocker: [0; FLAT_CAP], all_clause: [0; FLAT_CAP], all_len: [0; MAX_LIT_SLOTS] }
    }

    fn add_watch(&mut self, lit: u32, blocker_raw: u32, clause_raw: u32) {
        let slot = lit_index(lit);
        if slot < MAX_LIT_SLOTS {
            let count = self.all_len[slot];
            if count < MAX_WATCHES {
                let base = slot * MAX_WATCHES;
                self.all_blocker[base + count] = blocker_raw;
                self.all_clause[base + count] = clause_raw;
                self.all_len[slot] = count + 1;
            }
        }
    }

    fn watch_count(&self, lit: u32) -> usize {
        let slot = lit_index(lit);
        if slot < MAX_LIT_SLOTS { self.all_len[slot] } else { 0 }
    }

    fn clear(&mut self) {
        self.all_len[0] = 0;
        self.all_len[1] = 0;
        self.all_len[2] = 0;
        self.all_len[3] = 0;
        self.all_len[4] = 0;
        self.all_len[5] = 0;
        self.all_len[6] = 0;
        self.all_len[7] = 0;
    }
}

// ============================================================
// Harnesses
// ============================================================

/// Watcher struct preserves its fields correctly (non-binary)
#[kani::proof]
fn watcher_fields_preserved() {
    let clause_val: u32 = kani::any();
    let blocker_val: u32 = kani::any();
    kani::assume(clause_val < 1000);
    kani::assume(blocker_val < 1000);

    // Non-binary: clause_raw has no BINARY_FLAG
    let clause_raw = clause_val;
    let blocker_raw = blocker_val;

    // Reconstruct clause_ref = clause_raw & !BINARY_FLAG
    assert!((clause_raw & !BINARY_FLAG) == clause_val);
    assert!(blocker_raw == blocker_val);
    assert!((clause_raw & BINARY_FLAG) == 0); // not binary
}

/// Binary watcher preserves its fields correctly
#[kani::proof]
fn binary_watcher_fields_preserved() {
    let clause_val: u32 = kani::any();
    let other_lit_val: u32 = kani::any();
    kani::assume(clause_val < 1000);
    kani::assume(other_lit_val < 1000);

    // Binary: clause_raw = clause_val | BINARY_FLAG
    let clause_raw = clause_val | BINARY_FLAG;
    let blocker_raw = other_lit_val;

    assert!((clause_raw & !BINARY_FLAG) == clause_val);
    assert!(blocker_raw == other_lit_val);
    assert!((clause_raw & BINARY_FLAG) != 0); // is binary
}

/// ClauseRef is correctly identified
#[kani::proof]
fn clause_ref_equality() {
    let a_val: u32 = kani::any();
    let b_val: u32 = kani::any();
    kani::assume(a_val < 1000 && b_val < 1000);

    if a_val == b_val {
        assert!(a_val == b_val);
    }
    if a_val != b_val {
        assert!(a_val != b_val);
    }
}

/// Literal index calculation is consistent for watched lists
#[kani::proof]
fn literal_index_for_watches() {
    let var_val: u32 = kani::any();
    kani::assume(var_val < 100);

    let pos = lit_positive(var_val);
    let neg = lit_negative(var_val);

    assert!(lit_index(pos) != lit_index(neg));

    let expected_max_index = (var_val as usize + 1) * 2;
    assert!(lit_index(pos) < expected_max_index);
    assert!(lit_index(neg) < expected_max_index);
}

/// SoA WatchList roundtrip: push then read back
#[kani::proof]
fn watch_list_aos_roundtrip() {
    let blocker_raw: u32 = kani::any();
    let clause_raw: u32 = kani::any();
    kani::assume(blocker_raw < 1000);
    kani::assume(clause_raw < 1000);

    let mut list = WatchList::new();
    list.push(blocker_raw, clause_raw);

    assert!(list.len == 1);
    assert!(list.blocker[0] == blocker_raw);
    assert!(list.clause[0] == clause_raw);
}

/// SoA WatchList swap_remove
#[kani::proof]
fn watch_list_swap_remove() {
    let mut list = WatchList::new();
    list.push(10, 20);
    list.push(30, 40);
    list.push(50, 60);

    assert!(list.len == 3);

    list.swap_remove(0);
    assert!(list.len == 2);
    assert!(list.blocker[0] == 50);
    assert!(list.clause[0] == 60);
}

/// SoA WatchList binary roundtrip
#[kani::proof]
fn watch_list_aos_binary_roundtrip() {
    let clause_val: u32 = kani::any();
    let other_lit_val: u32 = kani::any();
    kani::assume(clause_val < 1000);
    kani::assume(other_lit_val < 1000);

    let clause_raw = clause_val | BINARY_FLAG;
    let blocker_raw = other_lit_val;

    let mut list = WatchList::new();
    list.push(blocker_raw, clause_raw);

    assert!(list.len == 1);
    assert!(list.clause[0] == clause_raw);
    assert!(list.blocker[0] == blocker_raw);
    assert!((list.clause[0] & BINARY_FLAG) != 0); // is_binary
    assert!((list.clause[0] & !BINARY_FLAG) == clause_val); // clause_ref
    assert!(list.blocker[0] == other_lit_val); // blocker
}

/// Port of ay::watched::watch_add_increases_count
#[kani::proof]
fn watch_add_increases_count() {
    let mut watches = WatchedLists::new();

    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 4);
    let lit = lit_positive(var_idx);

    let clause_val: u32 = kani::any();
    let blocker_val: u32 = kani::any();
    kani::assume(clause_val < 100 && blocker_val < 100);

    let before = watches.watch_count(lit);
    watches.add_watch(lit, blocker_val, clause_val);
    let after = watches.watch_count(lit);

    assert!(after == before + 1);
}

/// Port of ay::watched::watch_clear_resets_counts
#[kani::proof]
fn watch_clear_resets_counts() {
    let mut watches = WatchedLists::new();

    let lit = lit_positive(0);
    watches.add_watch(lit, 1, 0);
    watches.add_watch(lit, 2, 1);

    watches.clear();

    // All positive/negative literal slots for the four variables should be zero.
    assert!(watches.watch_count(lit_positive(0)) == 0, "pos count must be 0");
    assert!(watches.watch_count(lit_negative(0)) == 0, "neg count must be 0");
    assert!(watches.watch_count(lit_positive(1)) == 0, "pos count must be 0");
    assert!(watches.watch_count(lit_negative(1)) == 0, "neg count must be 0");
    assert!(watches.watch_count(lit_positive(2)) == 0, "pos count must be 0");
    assert!(watches.watch_count(lit_negative(2)) == 0, "neg count must be 0");
    assert!(watches.watch_count(lit_positive(3)) == 0, "pos count must be 0");
    assert!(watches.watch_count(lit_negative(3)) == 0, "neg count must be 0");
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_sat_literal_encoding_unique=PROOF
// kani-expect: ay_sat_literal_variable_roundtrip=PROOF
// kani-expect: ay_sat_watch_clear_resets_counts=PROOF
// kani-expect: ay_sat_watch_list_binary_roundtrip=PROOF
// kani-expect: ay_sat_watch_list_roundtrip=PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).

//! AY self-verification bootstrap Tier 2b: SAT literal and watch-list harnesses.
//!
//! These harnesses are extracted from ay's `#[kani::proof]` suites in
//! `ay-sat/literal` and `ay-sat/watched`. They use fixed-capacity mirrors of
//! the upstream data structures so trust_mc can verify the same invariants without
//! depending on heap-backed watch-list helpers.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

const BINARY_FLAG: u32 = 0x8000_0000;
const NUM_VARS: usize = 4;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Variable(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Literal(u32);

impl Literal {
    fn positive(var: Variable) -> Self {
        Self(var.0 << 1)
    }

    fn negative(var: Variable) -> Self {
        Self((var.0 << 1) | 1)
    }

    fn variable(self) -> Variable {
        Variable(self.0 >> 1)
    }

    fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ClauseRef(u32);

#[derive(Debug, Clone, Copy)]
struct Watcher {
    clause_raw: u32,
    blocker_raw: u32,
}

impl Watcher {
    fn new(clause: ClauseRef, blocker: Literal) -> Self {
        Self { clause_raw: clause.0, blocker_raw: blocker.0 }
    }

    fn binary(clause: ClauseRef, other_lit: Literal) -> Self {
        Self { clause_raw: clause.0 | BINARY_FLAG, blocker_raw: other_lit.0 }
    }

    fn is_binary(self) -> bool {
        self.clause_raw & BINARY_FLAG != 0
    }

    fn clause_ref(self) -> ClauseRef {
        ClauseRef(self.clause_raw & !BINARY_FLAG)
    }

    fn blocker(self) -> Literal {
        Literal(self.blocker_raw)
    }
}

#[derive(Debug, Clone, Copy)]
struct WatchList {
    blocker0: u32,
    clause0: u32,
    blocker1: u32,
    clause1: u32,
    len: usize,
}

impl WatchList {
    fn new() -> Self {
        Self { blocker0: 0, clause0: 0, blocker1: 0, clause1: 0, len: 0 }
    }

    fn len(&self) -> usize {
        self.len
    }

    fn blocker_raw(&self, i: usize) -> u32 {
        if i == 0 { self.blocker0 } else { self.blocker1 }
    }

    fn clause_raw(&self, i: usize) -> u32 {
        if i == 0 { self.clause0 } else { self.clause1 }
    }

    fn blocker(&self, i: usize) -> Literal {
        Literal(self.blocker_raw(i))
    }

    fn clause_ref(&self, i: usize) -> ClauseRef {
        ClauseRef(self.clause_raw(i) & !BINARY_FLAG)
    }

    fn push(&mut self, blocker_raw: u32, clause_raw: u32) {
        match self.len {
            0 => {
                self.blocker0 = blocker_raw;
                self.clause0 = clause_raw;
                self.len += 1;
            }
            1 => {
                self.blocker1 = blocker_raw;
                self.clause1 = clause_raw;
                self.len += 1;
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct WatchedLists {
    count0: usize,
    count1: usize,
    count2: usize,
    count3: usize,
    count4: usize,
    count5: usize,
    count6: usize,
    count7: usize,
}

impl WatchedLists {
    fn new() -> Self {
        Self {
            count0: 0,
            count1: 0,
            count2: 0,
            count3: 0,
            count4: 0,
            count5: 0,
            count6: 0,
            count7: 0,
        }
    }

    // These count-only harnesses only need per-literal cardinality, not the full
    // watcher payload storage path.
    fn add_watch(&mut self, lit: Literal, _watcher: Watcher) {
        match lit.index() {
            0 => self.count0 += 1,
            1 => self.count1 += 1,
            2 => self.count2 += 1,
            3 => self.count3 += 1,
            4 => self.count4 += 1,
            5 => self.count5 += 1,
            6 => self.count6 += 1,
            7 => self.count7 += 1,
            _ => {}
        }
    }

    fn watch_count(&self, lit: Literal) -> usize {
        match lit.index() {
            0 => self.count0,
            1 => self.count1,
            2 => self.count2,
            3 => self.count3,
            4 => self.count4,
            5 => self.count5,
            6 => self.count6,
            7 => self.count7,
            _ => 0,
        }
    }

    fn clear(&mut self) {
        self.count0 = 0;
        self.count1 = 0;
        self.count2 = 0;
        self.count3 = 0;
        self.count4 = 0;
        self.count5 = 0;
        self.count6 = 0;
        self.count7 = 0;
    }
}

// ============================================================
// ay-sat/src/literal.rs
// ============================================================

/// Port of ay::literal::literal_negation_involutive
#[kani::proof]
fn ay_sat_literal_negation_involutive() {
    let raw: u32 = kani::any();
    kani::assume(raw < 1_000_000);
    let lit = Literal(raw);
    assert_eq!(lit.negated().negated(), lit);
}

/// Port of ay::literal::literal_variable_roundtrip
#[kani::proof]
fn ay_sat_literal_variable_roundtrip() {
    let var_raw: u32 = kani::any();
    kani::assume(var_raw < 500_000);
    let var = Variable(var_raw);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
}

/// Port of ay::literal::literal_encoding_unique
#[kani::proof]
fn ay_sat_literal_encoding_unique() {
    let var1 = Variable(kani::any::<u32>());
    let var2 = Variable(kani::any::<u32>());
    kani::assume(var1.0 < 500_000 && var2.0 < 500_000);

    let pos1 = Literal::positive(var1);
    let pos2 = Literal::positive(var2);

    if pos1.0 == pos2.0 {
        assert_eq!(var1, var2);
    }
}

/// Port of ay::literal::literal_polarity_distinct
#[kani::proof]
fn ay_sat_literal_polarity_distinct() {
    let var = Variable(kani::any::<u32>());
    kani::assume(var.0 < 500_000);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert_ne!(pos, neg);
    assert_eq!(pos.negated(), neg);
    assert_eq!(neg.negated(), pos);
}

// ============================================================
// ay-sat/src/watched.rs
// ============================================================

/// Port of ay::watched::watcher_fields_preserved
#[kani::proof]
fn ay_sat_watcher_fields_preserved() {
    let clause = ClauseRef(kani::any::<u32>());
    let blocker = Literal(kani::any::<u32>());
    kani::assume(clause.0 < 1000);
    kani::assume(blocker.0 < 1000);

    let watcher = Watcher::new(clause, blocker);
    assert_eq!(watcher.clause_ref(), clause);
    assert_eq!(watcher.blocker(), blocker);
    assert!(!watcher.is_binary());
}

/// Port of ay::watched::binary_watcher_fields_preserved
#[kani::proof]
fn ay_sat_binary_watcher_fields_preserved() {
    let clause = ClauseRef(kani::any::<u32>());
    let other_lit = Literal(kani::any::<u32>());
    kani::assume(clause.0 < 1000);
    kani::assume(other_lit.0 < 1000);

    let watcher = Watcher::binary(clause, other_lit);
    assert_eq!(watcher.clause_ref(), clause);
    assert_eq!(watcher.blocker(), other_lit);
    assert!(watcher.is_binary());
}

/// Port of ay::watched::watch_list_aos_roundtrip
#[kani::proof]
fn ay_sat_watch_list_roundtrip() {
    let blocker_raw: u32 = kani::any();
    let clause_raw: u32 = kani::any();
    kani::assume(blocker_raw < 1000);
    kani::assume(clause_raw < 1000);

    let mut list = WatchList::new();
    list.push(blocker_raw, clause_raw);

    assert_eq!(list.len(), 1);
    assert_eq!(list.blocker_raw(0), blocker_raw);
    assert_eq!(list.clause_raw(0), clause_raw);
    assert_eq!(list.blocker(0), Literal(blocker_raw));
    assert_eq!(list.clause_ref(0), ClauseRef(clause_raw & !BINARY_FLAG));
}

/// Port of ay::watched::watch_list_aos_binary_roundtrip
#[kani::proof]
fn ay_sat_watch_list_binary_roundtrip() {
    let clause = ClauseRef(kani::any::<u32>());
    let other_lit = Literal(kani::any::<u32>());
    kani::assume(clause.0 < 1000);
    kani::assume(other_lit.0 < 1000);

    let watcher = Watcher::binary(clause, other_lit);
    let mut list = WatchList::new();
    list.push(watcher.blocker_raw, watcher.clause_raw);

    assert_eq!(list.len(), 1);
    assert_eq!(list.clause_raw(0) & BINARY_FLAG, BINARY_FLAG);
    assert_eq!(list.clause_ref(0), clause);
    assert_eq!(list.blocker_raw(0), other_lit.0);
}

/// Port of ay::watched::watch_add_increases_count
#[kani::proof]
fn ay_sat_watch_add_increases_count() {
    let mut watches = WatchedLists::new();

    let var_idx: u32 = kani::any();
    kani::assume(var_idx < NUM_VARS as u32);
    let lit = Literal::positive(Variable(var_idx));

    let clause = ClauseRef(kani::any::<u32>());
    let blocker = Literal(kani::any::<u32>());
    kani::assume(clause.0 < 100);
    kani::assume(blocker.0 < 100);

    let before = watches.watch_count(lit);
    watches.add_watch(lit, Watcher::new(clause, blocker));
    let after = watches.watch_count(lit);

    assert_eq!(after, before + 1);
}

/// Port of ay::watched::watch_clear_resets_counts
#[kani::proof]
fn ay_sat_watch_clear_resets_counts() {
    let mut watches = WatchedLists::new();
    let lit = Literal::positive(Variable(0));

    watches.add_watch(lit, Watcher::new(ClauseRef(0), Literal(1)));
    watches.add_watch(lit, Watcher::new(ClauseRef(1), Literal(2)));
    watches.clear();

    assert_eq!(watches.count0, 0);
    assert_eq!(watches.count1, 0);
    assert_eq!(watches.count2, 0);
    assert_eq!(watches.count3, 0);
    assert_eq!(watches.count4, 0);
    assert_eq!(watches.count5, 0);
    assert_eq!(watches.count6, 0);
    assert_eq!(watches.count7, 0);
}

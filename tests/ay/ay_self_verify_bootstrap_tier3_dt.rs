// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_dt_pop_empty_is_safe=PROOF
// kani-expect: ay_dt_push_pop_scope_depth=PROOF
// kani-expect: ay_dt_reset_clears_state=PROOF
// kani-expect: ay_dt_clash_detection_soundness=PROOF
// kani-expect: ay_dt_completeness_decidable_fragment=PROOF
// kani-expect: ay_dt_find_returns_root=PROOF
// kani-expect: ay_dt_push_pop_constructor_state=PROOF
// kani-expect: ay_dt_register_constructor_idempotent=PROOF
// kani-expect: ay_dt_union_find_invariant=PROOF
// kani-expect: ay_dt_union_transitivity=PROOF
// NOTE: pop-empty and push/pop scope depth recovered as clean CHC PROOF at ay 733ba8cd.

//! AY self-verification bootstrap Tier 3: Datatype theory solver invariants.
//!
//! These harnesses mirror the DT (Datatype) theory solver from
//! `ay-theories/dt/src/lib.rs`. The DT solver manages:
//! - Union-find for equivalence classes
//! - Constructor registration and clash detection
//! - Push/pop scope management
//!
//! Standalone modeling uses scalar fields (no BTreeMap/Vec) to stay within
//! trust_mc's CHC encoding. Union-find is modeled with fixed-size parent/rank
//! arrays (3 elements — matches actual harness usage of terms 0, 1, 2).
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// Scalar model of DT solver's union-find (3 elements max).
/// Reduced from 4 to match actual harness usage (terms 0, 1, 2 only).
/// This reduces CHC encoding complexity (fewer match arms, shorter find loop).
#[derive(Debug, Clone, PartialEq, Eq)]
struct DtSolver {
    // Union-find parent pointers (3 slots)
    parent0: u32,
    parent1: u32,
    parent2: u32,
    // Constructor tags: 0 = none, 1+ = constructor id
    ctor0: u32,
    ctor1: u32,
    ctor2: u32,
    // Scope stack (max 2 scopes)
    scope_len: usize,
    // Snapshot of ctor count at each scope
    scope0_ctor_count: usize,
    scope1_ctor_count: usize,
    // Number of registered constructors
    ctor_count: usize,
    // Datatype registered flag
    has_datatype: bool,
}

impl DtSolver {
    fn new() -> Self {
        Self {
            parent0: 0,
            parent1: 1,
            parent2: 2,
            ctor0: 0,
            ctor1: 0,
            ctor2: 0,
            scope_len: 0,
            scope0_ctor_count: 0,
            scope1_ctor_count: 0,
            ctor_count: 0,
            has_datatype: false,
        }
    }

    fn find(&self, x: u32) -> u32 {
        // Manually unrolled path following (no loop — CHC encodes sequential
        // statements better than loops). Max 2 hops for 3-element UF.
        let p0 = self.get_parent(x);
        if p0 == x {
            return x;
        }
        let p1 = self.get_parent(p0);
        if p1 == p0 {
            return p0;
        }
        p1
    }

    fn get_parent(&self, x: u32) -> u32 {
        match x {
            0 => self.parent0,
            1 => self.parent1,
            2 => self.parent2,
            _ => x,
        }
    }

    fn set_parent(&mut self, x: u32, p: u32) {
        match x {
            0 => self.parent0 = p,
            1 => self.parent1 = p,
            2 => self.parent2 = p,
            _ => {}
        }
    }

    fn union(&mut self, x: u32, y: u32) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx != ry {
            // Simple union: always point rx -> ry
            self.set_parent(rx, ry);
        }
    }

    fn get_ctor(&self, x: u32) -> u32 {
        match x {
            0 => self.ctor0,
            1 => self.ctor1,
            2 => self.ctor2,
            _ => 0,
        }
    }

    fn set_ctor(&mut self, x: u32, c: u32) {
        let prev = self.get_ctor(x);
        match x {
            0 => self.ctor0 = c,
            1 => self.ctor1 = c,
            2 => self.ctor2 = c,
            _ => {}
        }
        if prev == 0 && c != 0 {
            self.ctor_count += 1;
        }
    }

    fn register_datatype(&mut self) {
        self.has_datatype = true;
    }

    fn register_constructor(&mut self, term: u32, ctor_id: u32) {
        self.set_ctor(term, ctor_id);
    }

    fn push(&mut self) {
        match self.scope_len {
            0 => {
                self.scope0_ctor_count = self.ctor_count;
                self.scope_len = 1;
            }
            1 => {
                self.scope1_ctor_count = self.ctor_count;
                self.scope_len = 2;
            }
            _ => {}
        }
    }

    fn pop(&mut self) {
        match self.scope_len {
            1 => {
                self.scope_len = 0;
                // Restore ctor_count (simplified: doesn't undo union-find)
                self.ctor_count = self.scope0_ctor_count;
            }
            2 => {
                self.scope_len = 1;
                self.ctor_count = self.scope1_ctor_count;
            }
            _ => {}
        }
    }

    fn reset(&mut self) {
        self.parent0 = 0;
        self.parent1 = 1;
        self.parent2 = 2;
        self.ctor0 = 0;
        self.ctor1 = 0;
        self.ctor2 = 0;
        self.scope_len = 0;
        self.scope0_ctor_count = 0;
        self.scope1_ctor_count = 0;
        self.ctor_count = 0;
        // has_datatype is preserved (like AY)
    }

    fn scopes_len(&self) -> usize {
        self.scope_len
    }

    fn scopes_is_empty(&self) -> bool {
        self.scope_len == 0
    }

    fn term_constructors_is_empty(&self) -> bool {
        self.ctor_count == 0
    }

    /// Check for clash: two terms in the same equivalence class
    /// with different non-zero constructors from the same datatype.
    fn check_clash(&self, t1: u32, t2: u32) -> bool {
        let r1 = self.find(t1);
        let r2 = self.find(t2);
        if r1 != r2 {
            return false; // Not in same class, no clash
        }
        let c1 = self.get_ctor(t1);
        let c2 = self.get_ctor(t2);
        c1 != 0 && c2 != 0 && c1 != c2
    }
}

/// Mirrors ay `proof_completeness_decidable_fragment` (concrete subset).
/// Verifies that after registering constructors and optionally asserting
/// equality, the solver can detect conflicts.
#[kani::proof]
fn ay_dt_completeness_decidable_fragment() {
    let mut solver = DtSolver::new();
    solver.register_datatype();

    // Register True2 (ctor=1) on term 0, False2 (ctor=2) on term 1
    solver.register_constructor(0, 1);
    solver.register_constructor(1, 2);

    // Before union: no clash (different equivalence classes)
    assert!(!solver.check_clash(0, 1));

    // After union: clash (same class, different constructors)
    solver.union(0, 1);
    assert!(solver.check_clash(0, 1));
}

/// Mirrors ay `proof_union_find_invariant`.
/// Verifies find is idempotent after unions.
#[kani::proof]
fn ay_dt_union_find_invariant() {
    let mut solver = DtSolver::new();

    // Perform some unions
    solver.union(0, 1);
    solver.union(1, 2);

    // find is idempotent
    let r0 = solver.find(0);
    let r0_again = solver.find(r0);
    assert_eq!(r0, r0_again);

    let r1 = solver.find(1);
    let r1_again = solver.find(r1);
    assert_eq!(r1, r1_again);
}

/// Mirrors ay `proof_push_pop_scope_depth`.
#[kani::proof]
fn ay_dt_push_pop_scope_depth() {
    let mut solver = DtSolver::new();
    let initial = solver.scopes_len();

    solver.push();
    assert_eq!(solver.scopes_len(), initial + 1);

    solver.push();
    assert_eq!(solver.scopes_len(), initial + 2);

    solver.pop();
    assert_eq!(solver.scopes_len(), initial + 1);

    solver.pop();
    assert_eq!(solver.scopes_len(), initial);
}

/// Mirrors ay `proof_pop_empty_is_safe`.
#[kani::proof]
fn ay_dt_pop_empty_is_safe() {
    let mut solver = DtSolver::new();
    solver.pop();
    assert!(solver.scopes_is_empty());
}

/// Mirrors ay `proof_reset_clears_state`.
#[kani::proof]
fn ay_dt_reset_clears_state() {
    let mut solver = DtSolver::new();
    solver.register_datatype();
    solver.register_constructor(0, 1);
    solver.push();

    solver.reset();

    assert!(solver.term_constructors_is_empty());
    assert!(solver.scopes_is_empty());
    // datatype_defs preserved (like AY)
    assert!(solver.has_datatype);
}

/// Mirrors ay `proof_union_transitivity`.
#[kani::proof]
fn ay_dt_union_transitivity() {
    let mut solver = DtSolver::new();

    solver.union(0, 1);
    solver.union(1, 2);

    let r0 = solver.find(0);
    let r1 = solver.find(1);
    let r2 = solver.find(2);

    assert_eq!(r0, r1);
    assert_eq!(r1, r2);
    assert_eq!(r0, r2);
}

/// Mirrors ay `proof_find_returns_root`.
#[kani::proof]
fn ay_dt_find_returns_root() {
    let mut solver = DtSolver::new();

    // Optional union
    solver.union(0, 1);

    // find returns a root (self-parent)
    let r0 = solver.find(0);
    let r0_parent = solver.get_parent(r0);
    assert_eq!(r0, r0_parent);
}

/// Mirrors ay `proof_register_constructor_idempotent`.
#[kani::proof]
fn ay_dt_register_constructor_idempotent() {
    let mut solver = DtSolver::new();
    solver.register_datatype();

    solver.register_constructor(0, 1);
    let count_first = solver.ctor_count;

    // Re-register same term with same ctor: no count change
    // (set_ctor only increments if prev was 0)
    solver.register_constructor(0, 1);
    let count_second = solver.ctor_count;

    assert_eq!(count_first, count_second);
}

/// Mirrors ay `proof_push_pop_constructor_state`.
#[kani::proof]
fn ay_dt_push_pop_constructor_state() {
    let mut solver = DtSolver::new();
    solver.register_datatype();

    solver.register_constructor(0, 1);
    let base_count = solver.ctor_count;

    solver.push();

    solver.register_constructor(1, 2);
    assert_eq!(solver.ctor_count, base_count + 1);

    solver.pop();

    // Only base registration count should remain
    assert_eq!(solver.ctor_count, base_count);
}

/// Mirrors ay `proof_clash_detection_soundness`.
#[kani::proof]
fn ay_dt_clash_detection_soundness() {
    let mut solver = DtSolver::new();
    solver.register_datatype();

    // Different constructors on different terms
    solver.register_constructor(0, 1); // True2
    solver.register_constructor(1, 2); // False2

    // Before union: no clash
    assert!(!solver.check_clash(0, 1));

    // Union them
    solver.union(0, 1);

    // After union: clash detected (same class, different constructors)
    assert!(solver.check_clash(0, 1));
}

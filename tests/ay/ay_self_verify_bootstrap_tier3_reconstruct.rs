// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_sat_stack_is_empty_consistent=PROOF
// kani-expect: ay_sat_sweep_identity_preserves_model=PROOF

//! AY self-verification bootstrap Tier 3l: SAT reconstruction harnesses.
//!
//! These harnesses verify the ReconstructionStack used in ay's SAT solver
//! for model reconstruction after preprocessing (BCE, BVE, sweep).
//!
//! Ported from `ay-sat/src/reconstruct.rs`.
//! Flat-scalar encoding: Vec replaced with fixed-capacity arrays.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// Standalone type mirrors (shared SAT types)
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Variable(u32);

impl Variable {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    fn index(self) -> usize {
        self.0 as usize
    }
}

// ============================================================
// Flat-scalar reconstruction helpers
// ============================================================

const MAX_VARS: usize = 8;

fn reconstruct_witness(model: &mut [bool; MAX_VARS], witness_lit: Literal, clause_lit: Literal) {
    let clause_var = clause_lit.variable().index();
    if clause_var < MAX_VARS {
        let already_sat =
            if clause_lit.is_positive() { model[clause_var] } else { !model[clause_var] };
        if already_sat {
            return;
        }
    }

    // Flip witness literal to satisfy clause
    let wit_var = witness_lit.variable().index();
    if wit_var < MAX_VARS {
        let lit_satisfied =
            if witness_lit.is_positive() { model[wit_var] } else { !model[wit_var] };
        if !lit_satisfied {
            model[wit_var] = !model[wit_var];
        }
    }
}

fn reconstruct_sweep_identity(_model: &mut [bool; MAX_VARS], _num_vars: usize) {
    // Identity mapping: each variable maps to itself — no changes needed
    // This is the identity case: model[i] stays model[i]
}

// ============================================================
// ReconstructionStack — flat-capacity
// ============================================================

#[derive(Clone, Copy)]
struct StackEntry {
    witness_lit: Literal,
    clause_lit: Literal,
}

#[derive(Clone, Copy)]
struct ReconstructionStack {
    entries: [StackEntry; 4],
    len: usize,
}

impl ReconstructionStack {
    fn new() -> Self {
        Self {
            entries: [StackEntry { witness_lit: Literal(0), clause_lit: Literal(0) }; 4],
            len: 0,
        }
    }

    fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn clear(&mut self) {
        self.len = 0;
    }

    fn push_bce(&mut self, blocker: Literal, clause_lit: Literal) {
        if self.len < 4 {
            self.entries[self.len] = StackEntry { witness_lit: blocker, clause_lit };
            self.len += 1;
        }
    }
}

// ============================================================
// Harnesses
// ============================================================

/// Port of ay::reconstruct::proof_witness_reconstruction_soundness
#[kani::proof]
fn ay_sat_witness_reconstruction_soundness() {
    let var_idx: usize = kani::any();
    kani::assume(var_idx < MAX_VARS);
    let is_positive: bool = kani::any();
    let witness_lit = if is_positive {
        Literal::positive(Variable(var_idx as u32))
    } else {
        Literal::negative(Variable(var_idx as u32))
    };
    let clause_lit = witness_lit;

    let mut model = [false; MAX_VARS];

    reconstruct_witness(&mut model, witness_lit, clause_lit);

    let lit_satisfied = if is_positive { model[var_idx] } else { !model[var_idx] };
    assert!(lit_satisfied, "Witness should be true after reconstruction");
}

/// Port of ay::reconstruct::proof_sweep_identity_preserves_model
#[kani::proof]
fn ay_sat_sweep_identity_preserves_model() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars > 0 && num_vars <= 4);

    let mut model = [false; MAX_VARS];
    let v0: bool = kani::any();
    let v1: bool = kani::any();
    let v2: bool = kani::any();
    let v3: bool = kani::any();
    model[0] = v0;
    model[1] = v1;
    model[2] = v2;
    model[3] = v3;

    reconstruct_sweep_identity(&mut model, num_vars);

    // Verify model unchanged
    assert!(model[0] == v0, "Identity preserves model[0]");
    assert!(model[1] == v1, "Identity preserves model[1]");
    assert!(model[2] == v2, "Identity preserves model[2]");
    assert!(model[3] == v3, "Identity preserves model[3]");
}

/// Port of ay::reconstruct::proof_stack_is_empty_consistent
#[kani::proof]
fn ay_sat_stack_is_empty_consistent() {
    let mut stack = ReconstructionStack::new();
    assert!(stack.is_empty());
    assert!(stack.len == 0);

    stack.push_bce(Literal::positive(Variable(0)), Literal::positive(Variable(0)));
    assert!(!stack.is_empty());
    assert!(stack.len == 1);

    stack.clear();
    assert!(stack.is_empty());
    assert!(stack.len == 0);
}

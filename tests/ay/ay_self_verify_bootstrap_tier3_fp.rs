// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: Recovered to 11/11 CHC PROOF at origin/main 4152479628.

//! AY self-verification bootstrap Tier 3k: FP standalone solver invariants.
//!
//! These harnesses mirror the bounded, currently-supported FP standalone subset
//! from `ay-theories/fp/src/verification.rs`, plus the concrete
//! push/pop/reset semantics implemented in `ay-theories/fp/src/theory_impl.rs`.
//! The upstream `proof_nested_push_pop_depth` check is included in bounded
//! standalone form and is currently discharged by CHC.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

#[derive(Debug, Clone, PartialEq, Eq)]
struct FpSolverStandalone {
    clause_count: usize,
    next_var: u32,
    trail_len: usize,
    scope0: usize,
    scope1: usize,
    scope2: usize,
    scope3: usize,
    scope_len: u8,
}

impl FpSolverStandalone {
    fn new() -> Self {
        Self {
            clause_count: 0,
            next_var: 1,
            trail_len: 0,
            scope0: 0,
            scope1: 0,
            scope2: 0,
            scope3: 0,
            scope_len: 0,
        }
    }

    fn push(&mut self) {
        match self.scope_len {
            0 => {
                self.scope0 = self.trail_len;
                self.scope_len = 1;
            }
            1 => {
                self.scope1 = self.trail_len;
                self.scope_len = 2;
            }
            2 => {
                self.scope2 = self.trail_len;
                self.scope_len = 3;
            }
            3 => {
                self.scope3 = self.trail_len;
                self.scope_len = 4;
            }
            _ => {}
        }
    }

    fn pop(&mut self) {
        match self.scope_len {
            1 => {
                self.scope_len = 0;
                self.trail_len = self.scope0;
            }
            2 => {
                self.scope_len = 1;
                self.trail_len = self.scope1;
            }
            3 => {
                self.scope_len = 2;
                self.trail_len = self.scope2;
            }
            4 => {
                self.scope_len = 3;
                self.trail_len = self.scope3;
            }
            _ => {}
        }
    }

    fn reset(&mut self) {
        self.clause_count = 0;
        self.next_var = 1;
        self.trail_len = 0;
        self.scope0 = 0;
        self.scope1 = 0;
        self.scope2 = 0;
        self.scope3 = 0;
        self.scope_len = 0;
    }

    fn clauses_is_empty(&self) -> bool {
        self.clause_count == 0
    }

    fn trail_is_empty(&self) -> bool {
        self.trail_len == 0
    }

    fn trail_stack_len(&self) -> u8 {
        self.scope_len
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FpPrecision {
    Float32,
    Float64,
}

/// Rounding mode for FP operations (mirrors ay-theories/fp RoundingMode).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RoundingMode {
    RNE,
    RNA,
    RTP,
    RTN,
    RTZ,
}

impl RoundingMode {
    fn name(self) -> u8 {
        match self {
            Self::RNE => 0,
            Self::RNA => 1,
            Self::RTP => 2,
            Self::RTN => 3,
            Self::RTZ => 4,
        }
    }

    /// Integer-coded inverse of `name()`.
    /// Uses a sentinel for invalid inputs to avoid `Option<enum>` encoding.
    fn from_name(n: u8) -> u8 {
        match n {
            0 => Self::RNE.name(),
            1 => Self::RNA.name(),
            2 => Self::RTP.name(),
            3 => Self::RTN.name(),
            4 => Self::RTZ.name(),
            _ => u8::MAX,
        }
    }
}

impl FpPrecision {
    fn exponent_bits(self) -> u32 {
        match self {
            Self::Float32 => 8,
            Self::Float64 => 11,
        }
    }

    fn significand_bits(self) -> u32 {
        match self {
            Self::Float32 => 24,
            Self::Float64 => 53,
        }
    }

    fn total_bits(self) -> u32 {
        self.exponent_bits() + self.significand_bits()
    }

    fn bias(self) -> u32 {
        (1 << (self.exponent_bits() - 1)) - 1
    }
}

#[kani::proof]
fn ay_fp_push_increments_stack_depth() {
    let mut solver = FpSolverStandalone::new();
    let initial_depth = solver.trail_stack_len();
    solver.push();
    assert_eq!(solver.trail_stack_len(), initial_depth + 1);
}

#[kani::proof]
fn ay_fp_pop_decrements_stack_depth() {
    let mut solver = FpSolverStandalone::new();
    solver.push();
    let depth_after_push = solver.trail_stack_len();
    solver.pop();
    assert_eq!(solver.trail_stack_len(), depth_after_push - 1);
}

#[kani::proof]
fn ay_fp_pop_empty_is_safe() {
    let mut solver = FpSolverStandalone::new();
    solver.pop();
    assert_eq!(solver.trail_stack_len(), 0);
}

#[kani::proof]
fn ay_fp_reset_clears_state() {
    let mut solver = FpSolverStandalone::new();
    solver.push();
    solver.push();
    solver.clause_count = 1;
    solver.trail_len = 1;
    solver.reset();
    assert!(solver.clauses_is_empty());
    assert!(solver.trail_is_empty());
    assert_eq!(solver.trail_stack_len(), 0);
    assert_eq!(solver.next_var, 1);
}

#[kani::proof]
fn ay_fp_push_pop_restores_depth() {
    let mut solver = FpSolverStandalone::new();
    let original_depth = solver.trail_stack_len();
    solver.push();
    solver.pop();
    assert_eq!(solver.trail_stack_len(), original_depth);
}

#[kani::proof]
fn ay_fp_bias_formula() {
    assert_eq!(FpPrecision::Float32.bias(), (1u32 << 7) - 1);
    assert_eq!(FpPrecision::Float64.bias(), (1u32 << 10) - 1);
}

/// Mirrors ay `proof_precision_exponent_positive`.
#[kani::proof]
fn ay_fp_precision_exponent_positive() {
    assert!(FpPrecision::Float32.exponent_bits() > 0);
    assert!(FpPrecision::Float64.exponent_bits() > 0);
}

/// Mirrors ay `proof_precision_significand_positive`.
#[kani::proof]
fn ay_fp_precision_significand_positive() {
    assert!(FpPrecision::Float32.significand_bits() > 0);
    assert!(FpPrecision::Float64.significand_bits() > 0);
}

/// Mirrors ay `proof_total_bits_formula`.
#[kani::proof]
fn ay_fp_total_bits_formula() {
    assert_eq!(
        FpPrecision::Float32.total_bits(),
        FpPrecision::Float32.exponent_bits() + FpPrecision::Float32.significand_bits()
    );
    assert_eq!(
        FpPrecision::Float64.total_bits(),
        FpPrecision::Float64.exponent_bits() + FpPrecision::Float64.significand_bits()
    );
}

/// Mirrors ay `proof_nested_push_pop_depth`.
#[kani::proof]
fn ay_fp_nested_push_pop_depth() {
    let mut solver = FpSolverStandalone::new();
    solver.push();
    solver.push();
    solver.push();
    assert_eq!(solver.trail_stack_len(), 3);
    solver.pop();
    assert_eq!(solver.trail_stack_len(), 2);
    solver.pop();
    assert_eq!(solver.trail_stack_len(), 1);
    solver.pop();
    assert_eq!(solver.trail_stack_len(), 0);
}

/// Mirrors ay `proof_rounding_mode_roundtrip`.
/// Uses integer encoding instead of String to stay within CHC encoding.
#[kani::proof]
fn ay_fp_rounding_mode_roundtrip() {
    let name: u8 = kani::any();
    kani::assume(name < 5);
    assert_eq!(RoundingMode::from_name(name), name);
}

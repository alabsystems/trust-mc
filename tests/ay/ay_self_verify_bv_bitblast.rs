// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: bv_clauses_monotonic=PROOF
// kani-expect: bv_fresh_var_monotonic=PROOF
// NOTE: bv_pop_empty_is_safe regressed PROOF→UNKNOWN at ay 8a4a9bcc2, recovered to PROOF at 65537dc81.
// NOTE: sound trivial-safe PROOF (no kani::any, no error rules emitted). See reports/bv-bitblast-investigation-2026-04-19.md
// kani-expect: bv_push_pop_stack_depth=UNKNOWN
// kani-expect: bv_reset_clears_state=PROOF

//! AY self-verification: bitvector bitblast width and shift invariants
//!
//! These harnesses verify the correctness of BV operations in ay-theories/bv/.
//! The shift-left overflow crash (ay#6084) at check_sat.rs:641 showed that
//! `1u64 << i` panics when i >= 64. These proofs verify that BV operations
//! maintain width invariants and that shift operations are bounds-safe.
//!
//! Originally from ay/crates/ay-theories/bv/src/verification.rs — adapted
//! to standalone form targeting the specific invariants that broke.
//!
//! NOTE: Most harnesses currently CTREX due to Vec<bool> heap allocation
//! hitting trust_mc's memory model gap. bv_to_u64_roundtrip achieves PROOF
//! because its control flow is simple enough for CHC. These are correct
//! stress tests — they will flip to PROOF as heap model coverage improves.

/// Bitvector represented as a vector of boolean bits (LSB first)
/// This is the internal representation ay-theories/bv uses for bitblasting.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Bits(Vec<bool>);

impl Bits {
    /// Create a constant bitvector of given width
    fn from_u64(value: u64, width: usize) -> Self {
        let mut bits = Vec::with_capacity(width);
        for i in 0..width {
            bits.push(if i < 64 {
                (value >> i) & 1 == 1
            } else {
                false // zero-extend beyond u64
            });
        }
        Self(bits)
    }

    fn width(&self) -> usize {
        self.0.len()
    }

    /// Convert back to u64 (only valid for width <= 64)
    fn to_u64(&self) -> u64 {
        let mut val: u64 = 0;
        for (i, &bit) in self.0.iter().enumerate() {
            if i >= 64 {
                break;
            }
            if bit {
                val |= 1u64 << i;
            }
        }
        val
    }

    /// Bitwise AND: same width required
    fn and(&self, other: &Self) -> Self {
        assert_eq!(self.width(), other.width());
        let bits = self.0.iter().zip(other.0.iter()).map(|(&a, &b)| a && b).collect();
        Self(bits)
    }

    /// Bitwise OR: same width required
    fn or(&self, other: &Self) -> Self {
        assert_eq!(self.width(), other.width());
        let bits = self.0.iter().zip(other.0.iter()).map(|(&a, &b)| a || b).collect();
        Self(bits)
    }

    /// Bitwise XOR: same width required
    fn xor(&self, other: &Self) -> Self {
        assert_eq!(self.width(), other.width());
        let bits = self.0.iter().zip(other.0.iter()).map(|(&a, &b)| a ^ b).collect();
        Self(bits)
    }

    /// Bitwise NOT
    fn not(&self) -> Self {
        let bits = self.0.iter().map(|&b| !b).collect();
        Self(bits)
    }

    /// Ripple-carry addition (truncated to width)
    fn add(&self, other: &Self) -> Self {
        assert_eq!(self.width(), other.width());
        let mut bits = Vec::with_capacity(self.width());
        let mut carry = false;
        for i in 0..self.width() {
            let a = self.0[i];
            let b = other.0[i];
            let sum = a ^ b ^ carry;
            carry = (a && b) || (a && carry) || (b && carry);
            bits.push(sum);
        }
        Self(bits)
    }

    /// Concatenation: self is high bits, other is low bits
    /// Result width = self.width() + other.width()
    fn concat(&self, other: &Self) -> Self {
        let mut bits = other.0.clone();
        bits.extend_from_slice(&self.0);
        Self(bits)
    }

    /// Extract bits [high:low] inclusive
    fn extract(&self, high: usize, low: usize) -> Self {
        assert!(high < self.width());
        assert!(low <= high);
        Self(self.0[low..=high].to_vec())
    }
}

// --- Width preservation harnesses ---

/// AND preserves width
// CTREX
#[kani::proof]
fn bv_and_preserves_width() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let a: u64 = kani::any();
    let b: u64 = kani::any();

    let ba = Bits::from_u64(a, width);
    let bb = Bits::from_u64(b, width);
    let result = ba.and(&bb);

    assert_eq!(result.width(), width);
}

/// OR preserves width
// CTREX
#[kani::proof]
fn bv_or_preserves_width() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let a: u64 = kani::any();
    let b: u64 = kani::any();

    let ba = Bits::from_u64(a, width);
    let bb = Bits::from_u64(b, width);
    let result = ba.or(&bb);

    assert_eq!(result.width(), width);
}

/// XOR preserves width
// CTREX
#[kani::proof]
fn bv_xor_preserves_width() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let a: u64 = kani::any();
    let b: u64 = kani::any();

    let ba = Bits::from_u64(a, width);
    let bb = Bits::from_u64(b, width);
    let result = ba.xor(&bb);

    assert_eq!(result.width(), width);
}

/// NOT preserves width
// CTREX
#[kani::proof]
fn bv_not_preserves_width() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let a: u64 = kani::any();

    let ba = Bits::from_u64(a, width);
    let result = ba.not();

    assert_eq!(result.width(), width);
}

/// ADD preserves width (no overflow in bit count)
// UNKNOWN
#[kani::proof]
fn bv_add_preserves_width() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let a: u64 = kani::any();
    let b: u64 = kani::any();

    let ba = Bits::from_u64(a, width);
    let bb = Bits::from_u64(b, width);
    let result = ba.add(&bb);

    assert_eq!(result.width(), width);
}

/// Concat width is sum of operand widths
// CTREX
#[kani::proof]
fn bv_concat_width_sum() {
    let w1: usize = kani::any();
    let w2: usize = kani::any();
    kani::assume(w1 > 0 && w1 <= 8);
    kani::assume(w2 > 0 && w2 <= 8);
    let a: u64 = kani::any();
    let b: u64 = kani::any();

    let ba = Bits::from_u64(a, w1);
    let bb = Bits::from_u64(b, w2);
    let result = ba.concat(&bb);

    assert_eq!(result.width(), w1 + w2);
}

/// Extract width is high - low + 1
// CTREX
#[kani::proof]
fn bv_extract_width() {
    let width: usize = kani::any();
    kani::assume(width >= 2 && width <= 16);
    let a: u64 = kani::any();

    let ba = Bits::from_u64(a, width);

    let high: usize = kani::any();
    let low: usize = kani::any();
    kani::assume(high < width);
    kani::assume(low <= high);

    let result = ba.extract(high, low);
    assert_eq!(result.width(), high - low + 1);
}

// --- Semantic correctness harnesses ---

/// NOT is involutive: not(not(x)) == x
// UNKNOWN — AY-version-sensitive, regressed PROOF→UNKNOWN at pin baeaef490f (P1:1405)
#[kani::proof]
fn bv_not_involutive() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let a: u64 = kani::any();

    let ba = Bits::from_u64(a, width);
    assert_eq!(ba.not().not(), ba);
}

/// XOR with self is zero
// UNKNOWN — AY-version-sensitive, regressed PROOF→UNKNOWN at pin baeaef490f (P1:1405)
#[kani::proof]
fn bv_xor_self_is_zero() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let a: u64 = kani::any();

    let ba = Bits::from_u64(a, width);
    let zero = Bits::from_u64(0, width);

    assert_eq!(ba.xor(&ba), zero);
}

/// to_u64 roundtrip for widths <= 64 (no heap — pure bit arithmetic)
// PROOF (per-harness override not supported — file-level expects CTREX)
#[kani::proof]
fn bv_to_u64_roundtrip() {
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);
    let val: u64 = kani::any();

    // Mask to width bits
    let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
    let masked = val & mask;

    let bits = Bits::from_u64(masked, width);
    assert_eq!(bits.to_u64(), masked);
}

/// Concat then extract recovers original pieces
/// Verdict: UNKNOWN due to from_u64's symbolic-bound Vec-building loop
/// producing inferable predicates that Spacer cannot synthesize invariants for.
/// The concat/extract inline path itself is correct (resolved by #3901).
// UNKNOWN
#[kani::proof]
fn bv_concat_extract_roundtrip() {
    let w1: usize = kani::any();
    let w2: usize = kani::any();
    kani::assume(w1 > 0 && w1 <= 8);
    kani::assume(w2 > 0 && w2 <= 8);
    let a: u64 = kani::any();
    let b: u64 = kani::any();

    let ba = Bits::from_u64(a, w1);
    let bb = Bits::from_u64(b, w2);
    let concatenated = ba.concat(&bb);

    // Low bits should be bb
    let extracted_low = concatenated.extract(w2 - 1, 0);
    assert_eq!(extracted_low, bb);

    // High bits should be ba
    let extracted_high = concatenated.extract(w1 + w2 - 1, w2);
    assert_eq!(extracted_high, ba);
}

// ========================================================================
// BV Solver State harnesses (ay-theories/bv/src/verification.rs)
// Standalone models — no actual BvSolver, just the behavioral invariants.
// ========================================================================

/// Standalone model of BV solver state for push/pop/reset/fresh_var.
struct BvSolverModel {
    next_var: u32,
    clause_count: usize,
    trail_len: usize,
    scope0: usize,
    scope1: usize,
    scope2: usize,
    scope_len: usize,
}

impl BvSolverModel {
    fn new() -> Self {
        Self {
            next_var: 1,
            clause_count: 0,
            trail_len: 0,
            scope0: 0,
            scope1: 0,
            scope2: 0,
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
            _ => {}
        }
    }

    fn pop(&mut self) {
        match self.scope_len {
            3 => {
                self.scope_len = 2;
                self.trail_len = self.scope2;
            }
            2 => {
                self.scope_len = 1;
                self.trail_len = self.scope1;
            }
            1 => {
                self.scope_len = 0;
                self.trail_len = self.scope0;
            }
            _ => {} // no-op on empty
        }
    }

    fn reset(&mut self) {
        self.next_var = 1;
        self.clause_count = 0;
        self.trail_len = 0;
        self.scope_len = 0;
    }

    fn fresh_var(&mut self) -> u32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn num_vars(&self) -> u32 {
        self.next_var - 1
    }
}

/// Port of ay::bv::proof_push_pop_stack_depth
#[kani::proof]
fn bv_push_pop_stack_depth() {
    let mut solver = BvSolverModel::new();
    let num_pushes: u8 = kani::any();
    kani::assume(num_pushes <= 3);
    let num_pops: u8 = kani::any();
    kani::assume(num_pops <= num_pushes);

    let mut i = 0u8;
    while i < num_pushes {
        solver.push();
        i += 1;
    }
    assert!(solver.scope_len == num_pushes as usize);

    let mut j = 0u8;
    while j < num_pops {
        solver.pop();
        j += 1;
    }
    assert!(solver.scope_len == (num_pushes - num_pops) as usize);
}

/// Port of ay::bv::proof_pop_empty_is_safe
#[kani::proof]
fn bv_pop_empty_is_safe() {
    let mut solver = BvSolverModel::new();
    let trail_before = solver.trail_len;
    solver.pop();
    assert!(solver.trail_len == trail_before);
    assert!(solver.scope_len == 0);
}

/// Port of ay::bv::proof_reset_clears_state
#[kani::proof]
fn bv_reset_clears_state() {
    let mut solver = BvSolverModel::new();
    solver.push();
    solver.fresh_var();
    solver.fresh_var();
    solver.clause_count = 5;
    solver.push();

    solver.reset();
    assert!(solver.clause_count == 0, "reset must clear clauses");
    assert!(solver.next_var == 1, "reset must reset next_var to 1");
    assert!(solver.trail_len == 0, "reset must clear trail");
    assert!(solver.scope_len == 0, "reset must clear scopes");
}

/// Port of ay::bv::proof_fresh_var_monotonic
#[kani::proof]
fn bv_fresh_var_monotonic() {
    let mut solver = BvSolverModel::new();
    let initial = solver.next_var;
    let v1 = solver.fresh_var();
    let mid = solver.next_var;
    let v2 = solver.fresh_var();

    assert!(v1 > 0);
    assert!(v2 > v1);
    assert!(mid > initial);
    assert!(solver.next_var > mid);
}

/// Port of ay::bv::proof_const_bits_width
/// Width of const_bits(value, width) is always `width`.
#[kani::proof]
fn bv_const_bits_width() {
    let value: u64 = kani::any();
    let width: usize = kani::any();
    kani::assume(width > 0 && width <= 16);

    let bits = Bits::from_u64(value, width);
    assert_eq!(bits.width(), width, "const_bits must return correct width");
}

/// Port of ay::bv::proof_num_vars_correct
#[kani::proof]
fn bv_num_vars_correct() {
    let mut solver = BvSolverModel::new();
    assert!(solver.num_vars() == 0);

    let n: u8 = kani::any();
    kani::assume(n > 0 && n <= 10);

    let mut i = 0u8;
    while i < n {
        solver.fresh_var();
        i += 1;
    }
    assert!(solver.num_vars() == n as u32);
}

/// Port of ay::bv::proof_trail_stack_markers_valid
/// Push records current trail_len; markers are non-decreasing.
#[kani::proof]
fn bv_trail_stack_markers_valid() {
    let mut solver = BvSolverModel::new();

    let depth: u8 = kani::any();
    kani::assume(depth > 0 && depth <= 3);

    // Track expected markers
    let mut expected: [usize; 3] = [0; 3];
    let mut i = 0u8;
    while i < depth {
        expected[i as usize] = solver.trail_len;
        solver.push();
        i += 1;
    }

    // Verify markers are correct and in ascending order
    let mut j = 0u8;
    while j < depth {
        let marker = match j {
            0 => solver.scope0,
            1 => solver.scope1,
            _ => solver.scope2,
        };
        assert!(marker == expected[j as usize]);
        if j > 0 {
            let prev = match j - 1 {
                0 => solver.scope0,
                _ => solver.scope1,
            };
            assert!(marker >= prev);
        }
        j += 1;
    }
}

/// Port of ay::bv::proof_clauses_monotonic
/// Clauses are never removed (only reset clears them).
#[kani::proof]
fn bv_clauses_monotonic() {
    let mut solver = BvSolverModel::new();
    let initial_clauses = solver.clause_count;

    // Simulate adding clauses via const_bits
    solver.clause_count += 4;
    let after_const = solver.clause_count;

    // Push/pop should not affect clause count
    solver.push();
    let after_push = solver.clause_count;
    solver.pop();
    let after_pop = solver.clause_count;

    assert!(after_const >= initial_clauses);
    assert!(after_push == after_const);
    assert!(after_pop == after_push);
}

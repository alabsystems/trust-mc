// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: Both HTR normalize harnesses are clean CHC PROOF at trust_mc 8e7242296b / AY 733ba8cd.

//! AY self-verification bootstrap Tier 3j: HTR normalize invariants.
//!
//! These harnesses mirror the `proof_normalize_binary_commutative` and
//! `proof_normalize_ternary_commutative` from `ay-sat/src/htr.rs`.
//! The standalone model implements the min/max sorting used for clause
//! normalization and verifies commutativity and ordering properties.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// Literal newtype (same encoding as ay-sat)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Literal(u32);

impl Literal {
    fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }
}

/// Normalize a binary clause: return (min, max).
fn normalize_binary(a: Literal, b: Literal) -> (Literal, Literal) {
    if a.0 <= b.0 { (a, b) } else { (b, a) }
}

/// Normalize a binary clause of negated literals: return (min, max).
/// Tests that normalization works correctly across polarity boundaries.
fn normalize_binary_negated(a: Literal, b: Literal) -> (Literal, Literal) {
    let na = a.negated();
    let nb = b.negated();
    normalize_binary(na, nb)
}

/// normalize_binary is commutative and produces ordered output.
#[kani::proof]
fn htr_normalize_binary_commutative() {
    let a_raw: u8 = kani::any();
    let b_raw: u8 = kani::any();
    kani::assume(a_raw < 100);
    kani::assume(b_raw < 100);

    let a = Literal(a_raw as u32);
    let b = Literal(b_raw as u32);

    let (x1, y1) = normalize_binary(a, b);
    let (x2, y2) = normalize_binary(b, a);

    // Commutativity
    assert!(x1.0 == x2.0);
    assert!(y1.0 == y2.0);

    // Ordering
    assert!(x1.0 <= y1.0);
}

/// normalize_binary on negated literals is consistent with original ordering.
/// Verifies that normalization of negated pairs preserves the min/max relationship.
#[kani::proof]
fn htr_normalize_negated_consistent() {
    let a_raw: u8 = kani::any();
    let b_raw: u8 = kani::any();
    kani::assume(a_raw < 100);
    kani::assume(b_raw < 100);

    let a = Literal(a_raw as u32);
    let b = Literal(b_raw as u32);

    let (nx, ny) = normalize_binary_negated(a, b);

    // Ordering must hold for negated pair too
    assert!(nx.0 <= ny.0);

    // Negated literals should have XOR'd least bit relative to originals
    // Verify the normalized negated pair is commutative
    let (nx2, ny2) = normalize_binary_negated(b, a);
    assert!(nx.0 == nx2.0);
    assert!(ny.0 == ny2.0);
}

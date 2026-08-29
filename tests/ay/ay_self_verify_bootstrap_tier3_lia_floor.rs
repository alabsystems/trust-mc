// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_lia_floor_ceil_negative=PROOF
// kani-expect: ay_lia_is_integer_when_divisible=PROOF

//! AY self-verification bootstrap Tier 3: LIA floor/ceil and integer-check
//! harnesses.
//!
//! These harnesses mirror `proof_floor_ceil_negative` and
//! `proof_is_integer_when_divisible` from `ay-theories/lia/src/verification.rs`.
//!
//! The ay originals use `num_bigint::BigRational`. We model rational arithmetic
//! with `i64` pairs `(numer, denom)` — sufficient for the bounded ranges these
//! harnesses exercise.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// Minimal rational number model (numer/denom, denom > 0).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Rational {
    numer: i64,
    denom: i64,
}

impl Rational {
    fn new(numer: i64, denom: i64) -> Self {
        assert!(denom > 0, "Denominator must be positive");
        Self { numer, denom }
    }
}

/// floor(numer/denom) using Euclidean division.
fn floor_rational(r: &Rational) -> i64 {
    if r.numer >= 0 {
        r.numer / r.denom
    } else {
        // For negative numerators: floor division rounds toward negative infinity
        // -1/2 -> -1, -3/2 -> -2
        let abs_numer = -r.numer;
        let q = abs_numer / r.denom;
        let rem = abs_numer % r.denom;
        if rem == 0 { -q } else { -(q + 1) }
    }
}

/// ceil(numer/denom) using Euclidean division.
fn ceil_rational(r: &Rational) -> i64 {
    if r.numer >= 0 {
        let q = r.numer / r.denom;
        let rem = r.numer % r.denom;
        if rem == 0 { q } else { q + 1 }
    } else {
        // For negative numerators: ceil rounds toward zero
        // -1/2 -> 0, -3/2 -> -1
        let abs_numer = -r.numer;
        -(abs_numer / r.denom)
    }
}

/// is_integer: true when numer is evenly divisible by denom.
fn is_integer(r: &Rational) -> bool {
    r.numer % r.denom == 0
}

/// Port of ay::lia::proof_floor_ceil_negative
#[kani::proof]
fn ay_lia_floor_ceil_negative() {
    // Test -1/2 = -0.5: floor should be -1, ceil should be 0
    let rat = Rational::new(-1, 2);
    let floor = floor_rational(&rat);
    let ceil = ceil_rational(&rat);
    assert!(floor == -1, "floor(-0.5) = -1");
    assert!(ceil == 0, "ceil(-0.5) = 0");

    // Test -3/2 = -1.5: floor should be -2, ceil should be -1
    let rat2 = Rational::new(-3, 2);
    let floor2 = floor_rational(&rat2);
    let ceil2 = ceil_rational(&rat2);
    assert!(floor2 == -2, "floor(-1.5) = -2");
    assert!(ceil2 == -1, "ceil(-1.5) = -1");
}

/// Port of ay::lia::proof_is_integer_when_divisible
///
/// Uses representative concrete cases to verify `is_integer` behaviour.
#[kani::proof]
fn ay_lia_is_integer_when_divisible() {
    let idx: u8 = kani::any();
    kani::assume(idx < 8);

    // k*d / d = k (integer) for representative (k, d) pairs. Keep these
    // scalar to avoid adding array/select obligations to this LIA harness.
    let (numer, denom) = match idx {
        0 => (0, 1),
        1 => (1, 1),
        2 => (-1, 1),
        3 => (6, 3),
        4 => (-12, 4),
        5 => (49, 7),
        6 => (0, 5),
        _ => (-9, 3),
    };

    let rat = Rational { numer, denom };
    assert!(is_integer(&rat), "k*d/d should be integer");

    // Also test a non-integer case
    let non_int = Rational { numer: 1, denom: 2 };
    assert!(!is_integer(&non_int), "1/2 is not integer");
}

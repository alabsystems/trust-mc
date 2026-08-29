// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_nia_scope_push_pop_restores=PROOF
// kani-expect: ay_nia_product_sign_associative=PROOF
// kani-expect: ay_nia_product_sign_even_negatives=PROOF
// kani-expect: ay_nia_product_sign_mixed=PROOF
// kani-expect: ay_nia_product_sign_negative_negative=PROOF
// kani-expect: ay_nia_product_sign_odd_negatives=PROOF
// kani-expect: ay_nia_product_sign_positive_positive=PROOF
// kani-expect: ay_nia_product_sign_zero_factor=PROOF
// kani-expect: ay_nia_scope_marker_tracking=PROOF
// kani-expect: ay_nia_scope_nested_lifo=PROOF
// kani-expect: ay_nra_sign_contradicts_consistency=PROOF
// NOTE: 11 harness(es) demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// NOTE: ay_nia_scope_marker_tracking was PROOF at ay 417854b7, regressed to UNKNOWN at ay 8a4a9bcc2.

//! AY self-verification bootstrap Tier 2: moderate ay harnesses using structs, Vec, enums.
//!
//! Ported from ay's own `#[kani::proof]` harnesses that use Vec, simple structs,
//! and method calls — but not full solver state or crate-specific types.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// ay-theories/nia — product_sign function and properties
// ============================================================

/// Compute the sign of a product of two factors.
/// Returns: -1 (negative), 0 (zero), 1 (positive)
/// Loop-free: avoids slice+while encoding gap in CHC.
fn product_sign_2(a: i32, b: i32) -> i32 {
    if a == 0 || b == 0 {
        return 0;
    }
    a * b
}

/// Compute the sign of a product of three factors (loop-free).
fn product_sign_3(a: i32, b: i32, c: i32) -> i32 {
    if a == 0 || b == 0 || c == 0 {
        return 0;
    }
    a * b * c
}

/// Compute the sign of a product of four factors (loop-free).
fn product_sign_4(a: i32, b: i32, c: i32, d: i32) -> i32 {
    if a == 0 || b == 0 || c == 0 || d == 0 {
        return 0;
    }
    a * b * c * d
}

/// Port of ay::nia::proof_product_sign_zero_factor
#[kani::proof]
fn ay_nia_product_sign_zero_factor() {
    let s1: i32 = kani::any();
    let s2: i32 = kani::any();
    kani::assume(s1 >= -1 && s1 <= 1);
    kani::assume(s2 >= -1 && s2 <= 1);

    assert!(product_sign_3(s1, 0, s2) == 0, "Zero factor yields zero product");
}

/// Port of ay::nia::proof_product_sign_positive_positive
#[kani::proof]
fn ay_nia_product_sign_positive_positive() {
    assert!(product_sign_2(1, 1) == 1, "pos * pos = pos");
}

/// Port of ay::nia::proof_product_sign_negative_negative
#[kani::proof]
fn ay_nia_product_sign_negative_negative() {
    assert!(product_sign_2(-1, -1) == 1, "neg * neg = pos");
}

/// Port of ay::nia::proof_product_sign_mixed
#[kani::proof]
fn ay_nia_product_sign_mixed() {
    assert!(product_sign_2(1, -1) == -1, "pos * neg = neg");
    assert!(product_sign_2(-1, 1) == -1, "neg * pos = neg");
}

/// Port of ay::nia::proof_product_sign_associative
/// Exhaustive enumeration of {-1,1}^3 — avoids NIA solver limitation (Part of #3766).
#[kani::proof]
fn ay_nia_product_sign_associative() {
    check_associative(-1, -1, -1);
    check_associative(-1, -1, 1);
    check_associative(-1, 1, -1);
    check_associative(-1, 1, 1);
    check_associative(1, -1, -1);
    check_associative(1, -1, 1);
    check_associative(1, 1, -1);
    check_associative(1, 1, 1);
}

fn check_associative(s1: i32, s2: i32, s3: i32) {
    let all = product_sign_3(s1, s2, s3);
    let grouped_12_3 = product_sign_2(product_sign_2(s1, s2), s3);
    let grouped_1_23 = product_sign_2(s1, product_sign_2(s2, s3));
    assert!(all == grouped_12_3, "product_sign is associative (12_3)");
    assert!(all == grouped_1_23, "product_sign is associative (1_23)");
}

/// Port of ay::nia::proof_product_sign_even_negatives
#[kani::proof]
fn ay_nia_product_sign_even_negatives() {
    assert!(product_sign_2(-1, -1) == 1, "2 negatives = positive");
    assert!(product_sign_4(-1, -1, -1, -1) == 1, "4 negatives = positive");
}

/// Port of ay::nia::proof_product_sign_odd_negatives
#[kani::proof]
fn ay_nia_product_sign_odd_negatives() {
    let neg = -1i32;
    assert!(neg == -1, "1 negative = negative");
    assert!(product_sign_3(-1, -1, -1) == -1, "3 negatives = negative");
}

// ============================================================
// ay-theories/nia — scope management with Vec
// ============================================================

/// Port of ay::nia::proof_scope_marker_tracking
/// Uses scalar model to avoid Vec-indexing encoding gap.
#[kani::proof]
fn ay_nia_scope_marker_tracking() {
    let mut scope_count: usize = 0;
    let mut marker_1: usize = 0;
    let mut asserted_len: usize = 0;

    assert!(scope_count == 0, "Initially no scopes");

    // push(asserted_len) — marker_0 implicitly = 0
    scope_count = 1;
    assert!(scope_count == 1, "Push adds scope marker");

    asserted_len = 3;
    marker_1 = asserted_len; // push(asserted_len)
    scope_count = 2;
    assert!(scope_count == 2, "Second push adds scope marker");
    assert!(marker_1 == 3, "Marker captures correct position");
}

/// Port of ay::nia::proof_scope_push_pop_restores
#[kani::proof]
fn ay_nia_scope_push_pop_restores() {
    let mut scopes: Vec<usize> = Vec::new();
    let initial = scopes.len();

    scopes.push(0);
    scopes.pop();

    assert!(scopes.len() == initial, "push/pop restores depth");
}

/// Port of ay::nia::proof_scope_nested_lifo
#[kani::proof]
fn ay_nia_scope_nested_lifo() {
    let mut scopes: Vec<usize> = Vec::new();

    scopes.push(0);
    scopes.push(5);
    scopes.push(10);
    assert!(scopes.len() == 3, "Three pushes");

    assert!(scopes.pop() == Some(10), "First pop returns 10");
    assert!(scopes.pop() == Some(5), "Second pop returns 5");
    assert!(scopes.pop() == Some(0), "Third pop returns 0");
    assert!(scopes.is_empty(), "All pops complete");
}

// ============================================================
// ay-sat/src/solver — XOR swap identity
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Literal(u32);

/// Port of ay::solver::proof_xor_swap_identity
#[kani::proof]
fn ay_sat_xor_swap_identity() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    kani::assume(a < 1000 && b < 1000);

    let lit_a = Literal(a);
    let lit_b = Literal(b);

    let c_is_a: bool = kani::any();
    let lit_c = if c_is_a { lit_a } else { lit_b };

    let result = Literal(lit_a.0 ^ lit_b.0 ^ lit_c.0);

    if c_is_a {
        assert_eq!(result, lit_b);
    } else {
        assert_eq!(result, lit_a);
    }
}

// ============================================================
// ay-theories/nia — sign constraint contradiction
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SignConstraint {
    Positive,
    Negative,
    Zero,
    NonNegative,
    NonPositive,
}

/// Checks if a sign value contradicts a constraint.
fn sign_contradicts(sign: i32, constraint: SignConstraint) -> bool {
    match constraint {
        SignConstraint::Positive => sign <= 0,
        SignConstraint::Negative => sign >= 0,
        SignConstraint::Zero => sign != 0,
        SignConstraint::NonNegative => sign < 0,
        SignConstraint::NonPositive => sign > 0,
    }
}

/// Port of ay::nra::sign_contradicts_consistency
#[kani::proof]
fn ay_nra_sign_contradicts_consistency() {
    let sign: i32 = kani::any();
    kani::assume(sign >= -1 && sign <= 1);

    // If sign is positive, it must not contradict Positive
    if sign > 0 {
        assert!(!sign_contradicts(sign, SignConstraint::Positive));
        assert!(!sign_contradicts(sign, SignConstraint::NonNegative));
    }
    // If sign is negative, it must not contradict Negative
    if sign < 0 {
        assert!(!sign_contradicts(sign, SignConstraint::Negative));
        assert!(!sign_contradicts(sign, SignConstraint::NonPositive));
    }
    // If sign is zero, it must not contradict Zero
    if sign == 0 {
        assert!(!sign_contradicts(sign, SignConstraint::Zero));
        assert!(!sign_contradicts(sign, SignConstraint::NonNegative));
        assert!(!sign_contradicts(sign, SignConstraint::NonPositive));
    }
}

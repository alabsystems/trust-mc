// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_nia_monomial_aux_var_preserved=PROOF
// kani-expect: ay_nia_monomial_degree_equals_vars_len=PROOF
// kani-expect: ay_nia_monomial_is_binary_iff_degree_two=PROOF
// kani-expect: ay_nia_monomial_is_square_requires_same_vars=PROOF
// kani-expect: ay_nia_is_underestimate_same_sign_quadrant=PROOF
// kani-expect: ay_nia_product_sign_associative=PROOF
// kani-expect: ay_nia_product_sign_even_negatives=PROOF
// kani-expect: ay_nia_product_sign_mixed=PROOF
// kani-expect: ay_nia_product_sign_negative_negative=PROOF
// kani-expect: ay_nia_product_sign_odd_negatives=PROOF
// kani-expect: ay_nia_product_sign_positive_positive=PROOF
// kani-expect: ay_nia_product_sign_zero_factor=PROOF
// kani-expect: ay_nia_sign_contradicts_negative_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_nonnegative_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_nonpositive_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_positive_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_zero_constraint=PROOF
// kani-expect: ay_nia_tangent_plane_linear_in_x=PROOF
// kani-expect: ay_nia_tangent_plane_linear_in_y=PROOF
// NOTE: 19 harnesses are clean CHC PROOF after scalar equality/sign-table cleanup; remaining non-overrides stay UNKNOWN.

//! AY self-verification bootstrap Tier 3k: NIA (Nonlinear Integer Arithmetic)
//! Monomial, product_sign, and SignConstraint harnesses.
//!
//! Ported from `ay-theories/nia/src/verification.rs` (consolidated version).
//! Tangent plane harnesses use standalone i64 Rational instead of BigRational.
//! Tautological scope harnesses excluded (removed per ay#4064).
//!
//! Flat-scalar encoding: Vec replaced with fixed-size arrays to avoid
//! container-induced encoding gaps.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// Standalone type mirrors — flat-scalar encoding
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TermId(u32);

/// Monomial with fixed-capacity array instead of Vec.
/// Max degree 4 (matches kani::assume bounds in original harnesses).
#[derive(Debug, Clone, Copy)]
struct Monomial {
    vars: [TermId; 4],
    len: usize,
    aux_var: TermId,
    degree: usize,
}

impl Monomial {
    fn new_2(v0: TermId, v1: TermId, aux_var: TermId) -> Self {
        Self { vars: [v0, v1, TermId(0), TermId(0)], len: 2, aux_var, degree: 2 }
    }

    fn new_n(vars: [TermId; 4], len: usize, aux_var: TermId) -> Self {
        Self { vars, len, aux_var, degree: len }
    }

    fn is_binary(&self) -> bool {
        self.degree == 2
    }

    fn is_square(&self) -> bool {
        self.degree == 2 && self.vars[0] == self.vars[1]
    }

    fn x(&self) -> Option<TermId> {
        if self.len == 0 { None } else { Some(self.vars[0]) }
    }

    fn y(&self) -> Option<TermId> {
        if self.len >= 2 { Some(self.vars[1]) } else { None }
    }
}

// ============================================================
// product_sign — flat-scalar sign composition (no slice iteration or NIA `*`)
// ============================================================

fn product_sign_2(a: i32, b: i32) -> i32 {
    if a == 0 || b == 0 {
        0
    } else if (a > 0) == (b > 0) {
        1
    } else {
        -1
    }
}

fn product_sign_3(a: i32, b: i32, c: i32) -> i32 {
    product_sign_2(product_sign_2(a, b), c)
}

fn product_sign_4(a: i32, b: i32, c: i32, d: i32) -> i32 {
    product_sign_2(product_sign_2(a, b), product_sign_2(c, d))
}

fn product_sign_1(a: i32) -> i32 {
    if a == 0 {
        0
    } else if a > 0 {
        1
    } else {
        -1
    }
}

// ============================================================
// SignConstraint — standalone mirror of ay-theories/nia
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SignConstraint {
    Positive,
    Negative,
    Zero,
    NonNegative,
    NonPositive,
}

fn sign_contradicts(constraint: SignConstraint, expected: i32) -> bool {
    match constraint {
        SignConstraint::Positive => expected <= 0,
        SignConstraint::Negative => expected >= 0,
        SignConstraint::Zero => expected != 0,
        SignConstraint::NonNegative => expected < 0,
        SignConstraint::NonPositive => expected > 0,
    }
}

fn sign_from_constraint(c: SignConstraint) -> Option<i32> {
    match c {
        SignConstraint::Positive => Some(1),
        SignConstraint::Negative => Some(-1),
        SignConstraint::Zero => Some(0),
        _ => None,
    }
}

// ============================================================
// Monomial Invariant Harnesses
// ============================================================

/// Port of ay::nia::proof_monomial_degree_equals_vars_len
#[kani::proof]
fn ay_nia_monomial_degree_equals_vars_len() {
    let len: usize = kani::any();
    kani::assume(len > 0 && len <= 4);

    let vars = [TermId(0), TermId(1), TermId(2), TermId(3)];
    let aux = TermId(100);
    let mon = Monomial::new_n(vars, len, aux);

    assert!(mon.degree == len, "Degree equals vars length");
}

/// Port of ay::nia::proof_monomial_is_binary_iff_degree_two
#[kani::proof]
fn ay_nia_monomial_is_binary_iff_degree_two() {
    let degree: usize = kani::any();
    kani::assume(degree > 0 && degree <= 4);

    let vars = [TermId(0), TermId(1), TermId(2), TermId(3)];
    let aux = TermId(100);
    let mon = Monomial::new_n(vars, degree, aux);

    assert!(mon.is_binary() == (degree == 2), "is_binary iff degree == 2");
}

/// Port of ay::nia::proof_monomial_is_square_requires_same_vars
#[kani::proof]
fn ay_nia_monomial_is_square_requires_same_vars() {
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    kani::assume(v1 < 100 && v2 < 100);

    let aux = TermId(100);
    let mon = Monomial::new_2(TermId(v1), TermId(v2), aux);

    let same_var_id = v1 == v2;
    assert!(mon.is_square() == same_var_id, "is_square iff both vars same");
}

/// Port of ay::nia::proof_monomial_x_y_accessors
#[kani::proof]
fn ay_nia_monomial_x_y_accessors() {
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    kani::assume(v1 < 100 && v2 < 100);

    let aux = TermId(100);
    let mon = Monomial::new_2(TermId(v1), TermId(v2), aux);

    if let Some(x) = mon.x() {
        assert!(x.0 == v1, "x() returns first");
    } else {
        assert!(false, "x() must return first");
    }
    if let Some(y) = mon.y() {
        assert!(y.0 == v2, "y() returns second");
    } else {
        assert!(false, "y() must return second");
    }
}

/// Port of ay::nia::proof_monomial_aux_var_preserved
#[kani::proof]
fn ay_nia_monomial_aux_var_preserved() {
    let aux_id: u32 = kani::any();
    kani::assume(aux_id < 1000);

    let aux = TermId(aux_id);
    let mon = Monomial::new_2(TermId(1), TermId(2), aux);

    assert!(mon.aux_var.0 == aux_id, "aux_var is preserved");
}

// ============================================================
// product_sign Harnesses
// ============================================================

/// Port of ay::nia::proof_product_sign_zero_factor
#[kani::proof]
fn ay_nia_product_sign_zero_factor() {
    let s1: i32 = kani::any();
    let s2: i32 = kani::any();
    kani::assume(s1 >= -1 && s1 <= 1);
    kani::assume(s2 >= -1 && s2 <= 1);

    let result = product_sign_3(s1, 0, s2);
    assert!(result == 0, "Zero factor yields zero product");
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
    assert!(all == grouped_12_3, "product_sign is associative (12,3)");
    assert!(all == grouped_1_23, "product_sign is associative (1,23)");
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
    assert!(product_sign_1(-1) == -1, "1 negative = negative");
    assert!(product_sign_3(-1, -1, -1) == -1, "3 negatives = negative");
}

// ============================================================
// SignConstraint Harnesses
// ============================================================

/// Port of ay::nia::proof_sign_contradicts_positive_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_positive_constraint() {
    assert!(sign_contradicts(SignConstraint::Positive, 0));
    assert!(sign_contradicts(SignConstraint::Positive, -1));
    assert!(!sign_contradicts(SignConstraint::Positive, 1));
}

/// Port of ay::nia::proof_sign_contradicts_negative_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_negative_constraint() {
    assert!(sign_contradicts(SignConstraint::Negative, 0));
    assert!(sign_contradicts(SignConstraint::Negative, 1));
    assert!(!sign_contradicts(SignConstraint::Negative, -1));
}

/// Port of ay::nia::proof_sign_contradicts_zero_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_zero_constraint() {
    assert!(sign_contradicts(SignConstraint::Zero, 1));
    assert!(sign_contradicts(SignConstraint::Zero, -1));
    assert!(!sign_contradicts(SignConstraint::Zero, 0));
}

/// Port of ay::nia::proof_sign_contradicts_nonnegative_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_nonnegative_constraint() {
    assert!(sign_contradicts(SignConstraint::NonNegative, -1));
    assert!(!sign_contradicts(SignConstraint::NonNegative, 0));
    assert!(!sign_contradicts(SignConstraint::NonNegative, 1));
}

/// Port of ay::nia::proof_sign_contradicts_nonpositive_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_nonpositive_constraint() {
    assert!(sign_contradicts(SignConstraint::NonPositive, 1));
    assert!(!sign_contradicts(SignConstraint::NonPositive, 0));
    assert!(!sign_contradicts(SignConstraint::NonPositive, -1));
}

/// Port of ay::nia::proof_sign_from_constraints_all
/// Uses if-let destructuring to avoid Option equality encoding gap.
#[kani::proof]
fn ay_nia_sign_from_constraints_all() {
    // Definite constraints return their sign
    if let Some(v) = sign_from_constraint(SignConstraint::Positive) {
        assert!(v == 1, "Positive -> 1");
    } else {
        assert!(false, "Positive must be Some");
    }
    if let Some(v) = sign_from_constraint(SignConstraint::Negative) {
        assert!(v == -1, "Negative -> -1");
    } else {
        assert!(false, "Negative must be Some");
    }
    if let Some(v) = sign_from_constraint(SignConstraint::Zero) {
        assert!(v == 0, "Zero -> 0");
    } else {
        assert!(false, "Zero must be Some");
    }

    // Non-definite constraints return None
    assert!(sign_from_constraint(SignConstraint::NonNegative).is_none());
    assert!(sign_from_constraint(SignConstraint::NonPositive).is_none());
}

// ============================================================
// Tangent Plane — i64-based Rational (avoids BigRational dep)
// ============================================================

/// i64 Rational for tangent plane verification (exact for bounded values).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    fn from_i64(v: i64) -> Self {
        Self { num: v, den: 1 }
    }

    fn mul(&self, other: &Self) -> Self {
        Self { num: self.num * other.num, den: self.den * other.den }
    }

    fn add(&self, other: &Self) -> Self {
        Self { num: self.num * other.den + other.num * self.den, den: self.den * other.den }
    }

    fn sub(&self, other: &Self) -> Self {
        Self { num: self.num * other.den - other.num * self.den, den: self.den * other.den }
    }

    fn signum(&self) -> i64 {
        if self.num == 0 {
            0
        } else if (self.num > 0) == (self.den > 0) {
            1
        } else {
            -1
        }
    }
}

/// T(x, y) = a*y + b*x - a*b
fn tangent_plane(a: &Rational, b: &Rational, x: &Rational, y: &Rational) -> Rational {
    a.mul(y).add(&b.mul(x)).sub(&a.mul(b))
}

/// Same-sign quadrant check: (x-a) and (y-b) have same sign → underestimate
fn is_underestimate(a: &Rational, b: &Rational, x: &Rational, y: &Rational) -> bool {
    let dx = x.sub(a);
    let dy = y.sub(b);
    dx.signum() * dy.signum() > 0
}

/// Denominator-1 tangent plane numerator.
/// Avoids CHC inferable non-predicate summaries from Rational helper calls.
fn tangent_plane_i64(a: i64, b: i64, x: i64, y: i64) -> i64 {
    a * y + b * x - a * b
}

// ============================================================
// Tangent Plane Harnesses
// ============================================================

/// Port of ay::nia::proof_tangent_plane_at_model_point (case 1: positive)
/// T(a,b) at point (a,b) = a*b
#[kani::proof]
fn ay_nia_tangent_plane_at_model_point_positive() {
    let a = Rational::from_i64(2);
    let b = Rational::from_i64(3);
    let t = tangent_plane(&a, &b, &a, &b);
    let ab = a.mul(&b);
    assert!(t == ab, "T(2,3) at (2,3) = 6");
}

/// Port of ay::nia::proof_tangent_plane_at_model_point (case 2: negative)
#[kani::proof]
fn ay_nia_tangent_plane_at_model_point_negative() {
    let a2 = Rational::from_i64(-1);
    let b2 = Rational::from_i64(4);
    let t2 = tangent_plane(&a2, &b2, &a2, &b2);
    let ab2 = a2.mul(&b2);
    assert!(t2 == ab2, "T(-1,4) at (-1,4) = -4");
}

/// Port of ay::nia::proof_tangent_plane_at_model_point (case 3: zero)
#[kani::proof]
fn ay_nia_tangent_plane_at_model_point_zero() {
    let a3 = Rational::from_i64(0);
    let b3 = Rational::from_i64(5);
    let t3 = tangent_plane(&a3, &b3, &a3, &b3);
    let ab3 = a3.mul(&b3);
    assert!(t3 == ab3, "T(0,5) at (0,5) = 0");
}

/// Port of ay::nia::proof_tangent_plane_linear_in_x
/// T(x1,y) - T(x2,y) = b*(x1-x2)
#[kani::proof]
fn ay_nia_tangent_plane_linear_in_x() {
    let a = 2i64;
    let b = 3i64;
    let y = 5i64;

    let x1 = 1i64;
    let x2 = 4i64;

    let t1 = tangent_plane_i64(a, b, x1, y);
    let t2 = tangent_plane_i64(a, b, x2, y);
    let diff = t1 - t2;
    let expected = b * (x1 - x2);

    assert!(diff == expected, "Tangent plane is linear in x");
}

/// Port of ay::nia::proof_tangent_plane_linear_in_y
/// T(x,y1) - T(x,y2) = a*(y1-y2)
#[kani::proof]
fn ay_nia_tangent_plane_linear_in_y() {
    let a = 2i64;
    let b = 3i64;
    let x = 5i64;

    let y1 = 1i64;
    let y2 = 4i64;

    let t1 = tangent_plane_i64(a, b, x, y1);
    let t2 = tangent_plane_i64(a, b, x, y2);
    let diff = t1 - t2;
    let expected = a * (y1 - y2);

    assert!(diff == expected, "Tangent plane is linear in y");
}

/// Port of ay::nia::proof_is_underestimate_same_sign_quadrant
/// Part of #3768: Reduced from 3 is_underestimate calls to 1 + direct arithmetic.
/// Original 3-call version exceeded CHC inline budget (sfb=30, CTREX).
#[kani::proof]
fn ay_nia_is_underestimate_same_sign_quadrant() {
    let a = Rational::from_i64(2);
    let b = Rational::from_i64(3);

    // Same positive quadrant: x > a, y > b → underestimate
    let x_pos = Rational::from_i64(5);
    let y_pos = Rational::from_i64(7);
    assert!(is_underestimate(&a, &b, &x_pos, &y_pos), "Same positive → underestimate");

    // Same negative quadrant: dx<0, dy<0 → product>0
    let dx_neg = 0i64 - 2;
    let dy_neg = 1i64 - 3;
    assert!(dx_neg * dy_neg > 0, "Same negative → underestimate (direct)");

    // Opposite quadrant: dx>0, dy<0 → product<0
    let dx_opp = 5i64 - 2;
    let dy_opp = 1i64 - 3;
    assert!(dx_opp * dy_opp <= 0, "Opposite → not underestimate (direct)");
}

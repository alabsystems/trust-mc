// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! AY self-verification: CHC proof interpolation dependency marks
//!
//! These harnesses verify algebraic properties (commutativity, associativity,
//! idempotence) of the DependencyMark union operation used in ay-chc's
//! proof interpolation engine.
//!
//! Originally from ay/crates/ay-chc/src/proof_interpolation/mod.rs.
//! AY's CHC engine verifying its own correctness through trust_mc.

/// Dependency mark for Craig interpolation (from ay-chc)
///
/// Tracks whether a formula component came from partition A, B, both, or neither.
/// Union operation must be commutative, associative, and idempotent for
/// interpolant extraction correctness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DependencyMark {
    None,
    A,
    B,
    AB,
}

impl DependencyMark {
    fn union(self, other: Self) -> Self {
        use DependencyMark::{None, A, AB, B};
        match (self, other) {
            (None, x) | (x, None) => x,
            (A, A) => A,
            (B, B) => B,
            (AB, _) | (_, AB) => AB,
            (A, B) | (B, A) => AB,
        }
    }
}

fn any_dependency_mark() -> DependencyMark {
    let v: u8 = kani::any();
    kani::assume(v < 4);
    match v {
        0 => DependencyMark::None,
        1 => DependencyMark::A,
        2 => DependencyMark::B,
        _ => DependencyMark::AB,
    }
}

/// Union is commutative: a ∪ b = b ∪ a
// PROOF
#[kani::proof]
fn proof_dependency_mark_union_commutative() {
    let a = any_dependency_mark();
    let b = any_dependency_mark();
    assert_eq!(a.union(b), b.union(a));
}

/// Union is associative: (a ∪ b) ∪ c = a ∪ (b ∪ c)
// UNKNOWN
#[kani::proof]
fn proof_dependency_mark_union_associative() {
    let a = any_dependency_mark();
    let b = any_dependency_mark();
    let c = any_dependency_mark();
    assert_eq!(a.union(b).union(c), a.union(b.union(c)));
}

/// Union is idempotent: a ∪ a = a
// PROOF
#[kani::proof]
fn proof_dependency_mark_union_idempotent() {
    let a = any_dependency_mark();
    assert_eq!(a.union(a), a);
}

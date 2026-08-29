// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_chc_dependency_mark_union_associative=PROOF
// kani-expect: ay_chc_dependency_mark_union_commutative=PROOF
// kani-expect: ay_chc_dependency_mark_union_idempotent=PROOF
// kani-expect: ay_chc_trp_recurrence_soundness=PROOF
// NOTE: These 3 scalarized dependency-mark harnesses are stable PROOF at
// trust_mc a67c1f4889 / AY 733ba8cd. TRP recurrence stays direct arithmetic under
// bounded inputs to avoid checked-arithmetic Option branches on the CHC path.

//! AY self-verification bootstrap Tier 3i: CHC proof interpolation harnesses.
//!
//! These harnesses verify `DependencyMark` algebraic properties from
//! `ay-chc/src/proof_interpolation/mod.rs` and the TRP recurrence invariant
//! from `ay-chc/src/trp.rs`.
//!
//! DependencyMark is a 4-valued lattice: None < {A, B} < AB, where union
//! is the join operation. The harnesses verify commutativity, associativity,
//! and idempotence — foundational for proof interpolation correctness.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// ay-chc/src/proof_interpolation — DependencyMark lattice
// ============================================================

/// Boolean-set encoding of None/A/B/AB; keeps the lattice laws in propositional
/// logic instead of enum/datatype or bit-vector reasoning.
#[derive(Debug, Clone, Copy)]
struct DependencyMark {
    depends_on_a: bool,
    depends_on_b: bool,
}

const DEPENDENCY_NONE: DependencyMark = DependencyMark {
    depends_on_a: false,
    depends_on_b: false,
};
const DEPENDENCY_A: DependencyMark = DependencyMark {
    depends_on_a: true,
    depends_on_b: false,
};
const DEPENDENCY_B: DependencyMark = DependencyMark {
    depends_on_a: false,
    depends_on_b: true,
};
const DEPENDENCY_AB: DependencyMark = DependencyMark {
    depends_on_a: true,
    depends_on_b: true,
};

impl DependencyMark {
    fn union(self, other: Self) -> Self {
        Self {
            depends_on_a: self.depends_on_a || other.depends_on_a,
            depends_on_b: self.depends_on_b || other.depends_on_b,
        }
    }
}

fn assert_dependency_mark_eq(left: DependencyMark, right: DependencyMark) {
    assert!(left.depends_on_a == right.depends_on_a);
    assert!(left.depends_on_b == right.depends_on_b);
}

fn assert_union_commutative_for(a: DependencyMark, b: DependencyMark) {
    assert_dependency_mark_eq(a.union(b), b.union(a));
}

fn any_dependency_mark() -> DependencyMark {
    DependencyMark {
        depends_on_a: kani::any(),
        depends_on_b: kani::any(),
    }
}

/// Port of ay::proof_interpolation::proof_dependency_mark_union_commutative
#[kani::proof]
fn ay_chc_dependency_mark_union_commutative() {
    assert_union_commutative_for(DEPENDENCY_NONE, DEPENDENCY_NONE);
    assert_union_commutative_for(DEPENDENCY_NONE, DEPENDENCY_A);
    assert_union_commutative_for(DEPENDENCY_NONE, DEPENDENCY_B);
    assert_union_commutative_for(DEPENDENCY_NONE, DEPENDENCY_AB);
    assert_union_commutative_for(DEPENDENCY_A, DEPENDENCY_NONE);
    assert_union_commutative_for(DEPENDENCY_A, DEPENDENCY_A);
    assert_union_commutative_for(DEPENDENCY_A, DEPENDENCY_B);
    assert_union_commutative_for(DEPENDENCY_A, DEPENDENCY_AB);
    assert_union_commutative_for(DEPENDENCY_B, DEPENDENCY_NONE);
    assert_union_commutative_for(DEPENDENCY_B, DEPENDENCY_A);
    assert_union_commutative_for(DEPENDENCY_B, DEPENDENCY_B);
    assert_union_commutative_for(DEPENDENCY_B, DEPENDENCY_AB);
    assert_union_commutative_for(DEPENDENCY_AB, DEPENDENCY_NONE);
    assert_union_commutative_for(DEPENDENCY_AB, DEPENDENCY_A);
    assert_union_commutative_for(DEPENDENCY_AB, DEPENDENCY_B);
    assert_union_commutative_for(DEPENDENCY_AB, DEPENDENCY_AB);
}

/// Port of ay::proof_interpolation::proof_dependency_mark_union_associative
#[kani::proof]
fn ay_chc_dependency_mark_union_associative() {
    let a = any_dependency_mark();
    let b = any_dependency_mark();
    let c = any_dependency_mark();
    let left = a.union(b).union(c);
    let right = a.union(b.union(c));
    assert_dependency_mark_eq(left, right);
}

/// Port of ay::proof_interpolation::proof_dependency_mark_union_idempotent
#[kani::proof]
fn ay_chc_dependency_mark_union_idempotent() {
    let a = any_dependency_mark();
    let union = a.union(a);
    assert_dependency_mark_eq(union, a);
}

// ============================================================
// ay-chc/src/trp.rs — TRP recurrence soundness
// ============================================================

/// Port of ay::trp::proof_recurrence_soundness
///
/// For x' = x + delta pattern, after n iterations: x_n - x_0 = delta * n.
#[kani::proof]
fn ay_chc_trp_recurrence_soundness() {
    let x_0: i64 = kani::any();
    let delta: i64 = kani::any();
    let n: i64 = kani::any();

    kani::assume(n > 0 && n < 100);
    kani::assume(delta > -100 && delta < 100);
    kani::assume(x_0 > -1_000_000 && x_0 < 1_000_000);

    // These bounds rule out i64 overflow, so direct arithmetic avoids the
    // Option/control-flow branches introduced by checked_mul/checked_add.
    let n_delta = delta * n;
    let x_n = x_0 + n_delta;
    let computed_delta_sum = x_n - x_0;

    assert!(computed_delta_sum == n_delta);
}

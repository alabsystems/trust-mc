// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: Concrete Luby prefix/edge/boundaries and split xor-swap cases are CHC PROOF at ay 733ba8cd.

//! AY self-verification bootstrap Tier 3j: SAT solver pure-value harnesses.
//!
//! These harnesses are ported from `ay-sat/src/solver/verification.rs` and
//! `ay-sat/src/solver/restart.rs`. Only harnesses that use pure value
//! computation (no Solver struct state) are included here — solver-state
//! harnesses require the full Solver infrastructure.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// Literal type (shared across SAT harnesses)
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Literal(u32);

// ============================================================
// ay-sat/src/solver/verification.rs — XOR swap identity
// ============================================================

/// Port of ay::solver::proof_xor_swap_identity for the c == a case.
///
/// For any two literals a, b, and a third literal c (where c == a or c == b),
/// a ^ b ^ c gives the other literal.
#[kani::proof]
fn ay_sat_xor_swap_identity_c_is_a() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    kani::assume(a < 1000 && b < 1000);

    let lit_a = Literal(a);
    let lit_b = Literal(b);
    let lit_c = lit_a;

    let result = Literal(lit_a.0 ^ lit_b.0 ^ lit_c.0);
    assert_eq!(result, lit_b);
}

/// Port of ay::solver::proof_xor_swap_identity for the c == b case.
///
/// Splitting the two allowed c choices preserves the original property while
/// avoiding the boolean phi that leaves CHC with a hard XOR invariant.
#[kani::proof]
fn ay_sat_xor_swap_identity_c_is_b() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    kani::assume(a < 1000 && b < 1000);

    let lit_a = Literal(a);
    let lit_b = Literal(b);
    let lit_c = lit_b;

    let result = Literal(lit_a.0 ^ lit_b.0 ^ lit_c.0);
    assert_eq!(result, lit_a);
}

// ============================================================
// ay-sat/src/solver/restart.rs — Luby sequence
// ============================================================

/// Standalone mirror of ay's Luby sequence generator.
///
/// Kept as a `const fn` so the concrete prefix harness can evaluate the
/// recursive helper at compile time instead of forcing CHC to infer a
/// recursive relation for 7 fixed inputs.
const fn get_luby(i: u32) -> u32 {
    if i == 0 {
        return 1;
    }

    let mut k = 1u32;
    let mut p = 1u32;

    while p < i {
        k += 1;
        if k >= 32 {
            p = u32::MAX;
            break;
        }
        p = (1u32 << k) - 1;
    }

    if p == i {
        if k >= 32 {
            return 1u32 << 31;
        }
        1u32 << (k - 1)
    } else {
        let prev_p = if k > 32 { u32::MAX } else { (1u32 << (k - 1)) - 1 };
        get_luby(i - prev_p)
    }
}

const LUBY_1: u32 = get_luby(1);
const LUBY_2: u32 = get_luby(2);
const LUBY_3: u32 = get_luby(3);
const LUBY_4: u32 = get_luby(4);
const LUBY_5: u32 = get_luby(5);
const LUBY_6: u32 = get_luby(6);
const LUBY_7: u32 = get_luby(7);
const LUBY_ZERO: u32 = get_luby(0);
const LUBY_15: u32 = get_luby(15);
const LUBY_31: u32 = get_luby(31);

/// Port of ay::solver::proof_luby_values_concrete
///
/// Verify the first 7 values of the Luby sequence: 1, 1, 2, 1, 1, 2, 4
#[kani::proof]
fn ay_sat_luby_values_concrete() {
    assert_eq!(LUBY_1, 1);
    assert_eq!(LUBY_2, 1);
    assert_eq!(LUBY_3, 2);
    assert_eq!(LUBY_4, 1);
    assert_eq!(LUBY_5, 1);
    assert_eq!(LUBY_6, 2);
    assert_eq!(LUBY_7, 4);
}

/// Port of the explicit `i == 0` guard in ay::solver::get_luby.
///
/// The production path is 1-indexed, but the helper defines this safe edge
/// value and uses it to avoid shifting through the general recurrence.
#[kani::proof]
fn ay_sat_luby_zero_edge_case() {
    assert_eq!(LUBY_ZERO, 1);
}

/// Concrete power-boundary values of the Luby recurrence: 2^(k - 1).
#[kani::proof]
fn ay_sat_luby_power_boundaries_concrete() {
    assert_eq!(LUBY_1, 1);
    assert_eq!(LUBY_3, 2);
    assert_eq!(LUBY_7, 4);
    assert_eq!(LUBY_15, 8);
    assert_eq!(LUBY_31, 16);
}

/// Concrete recursive-tail values: 4, 5, and 6 map back to 1, 2, and 3.
///
/// This covers the `else { get_luby(i - prev_p) }` branch without forcing CHC
/// to synthesize an invariant for the recursive helper body at verification
/// time.
#[kani::proof]
fn ay_sat_luby_recursive_tail_concrete() {
    assert_eq!(LUBY_4, LUBY_1);
    assert_eq!(LUBY_5, LUBY_2);
    assert_eq!(LUBY_6, LUBY_3);
}

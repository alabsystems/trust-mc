// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A deliberately small, syntactic validity test for deferred inline checks.
//!
//! Every deferred check the walker records becomes its own CHC property at the
//! host (`emit_deferred_inline_check_errors`), and ay splits one harness's solve
//! budget across its properties. A check that holds WHATEVER the host state is
//! still solved like any other: measured on the 2026-09-23 walker branch, the
//! two locally valid checks of `a.checked_sub(b)` and `a.wrapping_shl(b)` in one
//! dyn body took 9.1 s and 12.6 s, and a harness with six of them ran out of
//! budget and reported UNKNOWN where it had been SUCCESSFUL.
//!
//! [`check_is_trivially_valid`] answers `true` only when the check is valid for
//! EVERY assignment of its free variables, by rules each of which is an exact
//! logical consequence:
//!
//! * `true`; a conjunction of valid checks;
//! * a disjunction `¬g₁ ∨ … ∨ ¬gₖ ∨ d₁ ∨ …` (the shape path weakening builds,
//!   `guard → check`) whose some `dⱼ` follows from the facts `g₁ … gₖ`;
//! * a literal that IS one of the facts, after normalising unsigned
//!   comparisons to `x <ᵤ y` or `¬(x <ᵤ y)` and removing double negation;
//! * a comparison of two bitvector constants, `K₁ = K₂` or `K₁ <ᵤ K₂` or
//!   either negated, that evaluates to true -- a constant divisor's
//!   `¬(8 = 0)`; a negated conjunction with such a conjunct that evaluates
//!   to false -- a constant divisor's `¬(s = MIN ∧ 8 = -1)`;
//! * `e <ᵤ K` for a constant `K` when an upper bound of `e` (from constants,
//!   `bvand` with a constant, zero-extension, `bvurem` by a constant, `bvlshr`
//!   by a constant) is below `K` -- `wrapping_shl`'s `(s & 7) < 8`,
//!   `(s >> 29) < 8` on a u32 `s`;
//! * `a -ᵤ b` does not underflow when `¬(a <ᵤ b)` is a fact (`checked_sub`);
//! * `a +ᵤ b` does not overflow when the bounds of `a` and `b` fit, or when
//!   `b ≤ 1` and `a <ᵤ y` is a fact for some `y` (`Step::forward_unchecked`).
//!
//! Anything else is "not known valid" and is emitted as before, so a missing
//! rule costs solver time and never a verdict. Dropping a valid check cannot
//! change a verdict: its violation is unsatisfiable in every state.

use ay_bindings::{Expr, ExprValue};

/// Recursion bound: path weakening nests one `Or` per branch or dispatch
/// level, so real checks are shallow; deeper ones are simply not simplified.
const MAX_DEPTH: usize = 32;

/// Is `check` (a MUST-HOLD condition, path condition included) valid for every
/// assignment of its free variables? `false` means "not shown", never
/// "invalid".
pub(in crate::codegen_ay::chc) fn check_is_trivially_valid(check: &Expr) -> bool {
    if !check.sort().is_bool() {
        return false;
    }
    prove(check, &mut Vec::new(), 0)
}

fn prove(goal: &Expr, facts: &mut Vec<Expr>, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    match goal.value() {
        ExprValue::BoolConst(value) => *value,
        ExprValue::And(parts) => parts.iter().all(|part| prove(part, facts, depth + 1)),
        ExprValue::Or(parts) => {
            // Assume every negated disjunct false (its operand a fact). If some
            // disjunct then follows, the assumptions (which include that
            // disjunct's own negation when it is negated) are contradictory,
            // so the disjunction holds in every state.
            let mark = facts.len();
            for part in parts {
                if let ExprValue::Not(inner) = part.value() {
                    add_fact(facts, inner, 0);
                }
            }
            let proved = parts.iter().any(|part| prove(part, facts, depth + 1));
            facts.truncate(mark);
            proved
        }
        ExprValue::Implies(antecedent, consequent) => {
            let mark = facts.len();
            add_fact(facts, antecedent, 0);
            let proved = prove(consequent, facts, depth + 1);
            facts.truncate(mark);
            proved
        }
        ExprValue::BvULt(lhs, rhs) => {
            literal_is_fact(goal, facts)
                || matches!((upper_bound(lhs), const_value(rhs)), (Some(ub), Some(k)) if ub < k)
        }
        ExprValue::BvSubNoUnderflowUnsigned(lhs, rhs) => {
            // a - b does not underflow iff b <= a iff ¬(a < b).
            literal_is_fact(&lhs.clone().bvult(rhs.clone()).not(), facts)
                || matches!((lower_bound(lhs), upper_bound(rhs)), (Some(lo), Some(hi)) if hi <= lo)
        }
        ExprValue::BvAddNoOverflowUnsigned(lhs, rhs) => {
            add_cannot_overflow(lhs, rhs, facts) || add_cannot_overflow(rhs, lhs, facts)
        }
        // ¬(a ∧ b ∧ …) holds when one conjunct is known false (a fact, or a
        // comparison of constants that evaluates to false), or when the same
        // conjunction, in any order, is known false (`checked_div`'s
        // `self == MIN && rhs == -1` guard against the MIN / -1 check).
        ExprValue::Not(inner) if matches!(inner.value(), ExprValue::And(_)) => {
            let ExprValue::And(parts) = inner.value() else { unreachable!() };
            literal_is_fact(goal, facts)
                || parts.iter().any(|part| {
                    literal_is_fact(&part.clone().not(), facts)
                        || constant_literal_value(part) == Some(false)
                })
                || facts.iter().any(|fact| negated_conjunction_matches(fact, parts))
        }
        _ => literal_is_fact(goal, facts) || constant_literal_value(goal) == Some(true),
    }
}

/// The truth value of `literal` when, after [`normalise`], it compares two
/// bitvector constants of one sort: `K₁ = K₂`, `K₁ <ᵤ K₂`, or the negation of
/// either. `None` for anything else. ay normalises a bitvector constant's
/// value modulo 2^width (`Expr::bitvec_const`), so comparing the stored
/// values is exact.
fn constant_literal_value(literal: &Expr) -> Option<bool> {
    fn constant_comparison(literal: &Expr) -> Option<bool> {
        match literal.value() {
            ExprValue::Eq(lhs, rhs) => constant_pair(lhs, rhs).map(|(a, b)| a == b),
            ExprValue::BvULt(lhs, rhs) => constant_pair(lhs, rhs).map(|(a, b)| a < b),
            _ => None,
        }
    }
    let normal = normalise(literal);
    match normal.value() {
        ExprValue::Not(positive) => constant_comparison(positive).map(|value| !value),
        _ => constant_comparison(&normal),
    }
}

/// Both operands as unsigned values, when both are bitvector constants of the
/// same sort (at most 128 bits wide).
fn constant_pair(lhs: &Expr, rhs: &Expr) -> Option<(u128, u128)> {
    if lhs.sort() != rhs.sort() || lhs.sort().bitvec_width().is_none() {
        return None;
    }
    Some((const_value(lhs)?, const_value(rhs)?))
}

/// Is `fact` `¬(q₁ ∧ …)` with the same conjuncts as `parts`, in any order?
fn negated_conjunction_matches(fact: &Expr, parts: &[Expr]) -> bool {
    let ExprValue::Not(inner) = fact.value() else { return false };
    let ExprValue::And(fact_parts) = inner.value() else { return false };
    fact_parts.len() == parts.len()
        && parts.iter().all(|part| fact_parts.contains(part))
        && fact_parts.iter().all(|part| parts.contains(part))
}

/// `a + b` cannot overflow: the bounds fit, or `b ≤ 1` and `a < y` for some `y`
/// (so `a ≤ MAX - 1`).
fn add_cannot_overflow(a: &Expr, b: &Expr, facts: &[Expr]) -> bool {
    let Some(width) = a.sort().bitvec_width() else { return false };
    let Some(max) = unsigned_max(width) else { return false };
    if let (Some(ua), Some(ub)) = (upper_bound(a), upper_bound(b))
        && ua.checked_add(ub).is_some_and(|sum| sum <= max)
    {
        return true;
    }
    upper_bound(b).is_some_and(|ub| ub <= 1)
        && facts.iter().any(|fact| {
            matches!(fact.value(), ExprValue::BvULt(lhs, _) if lhs == a && lhs.sort() == a.sort())
        })
}

/// Is the (normalised) literal one of the facts?
fn literal_is_fact(literal: &Expr, facts: &[Expr]) -> bool {
    let normal = normalise(literal);
    facts.iter().any(|fact| *fact == normal)
}

/// Record `fact` (known true) in normalised form, splitting conjunctions and
/// negated disjunctions.
fn add_fact(facts: &mut Vec<Expr>, fact: &Expr, depth: usize) {
    if depth > MAX_DEPTH || !fact.sort().is_bool() {
        return;
    }
    match fact.value() {
        ExprValue::And(parts) => {
            for part in parts {
                add_fact(facts, part, depth + 1);
            }
        }
        ExprValue::Not(inner) => match inner.value() {
            ExprValue::Not(positive) => add_fact(facts, positive, depth + 1),
            ExprValue::Or(parts) => {
                for part in parts {
                    add_fact(facts, &part.clone().not(), depth + 1);
                }
            }
            _ => facts.push(normalise(fact)),
        },
        // `x == false` / `x == true` on booleans (bool SwitchInt guards).
        ExprValue::Eq(lhs, rhs) if lhs.sort().is_bool() => match (lhs.value(), rhs.value()) {
            (_, ExprValue::BoolConst(true)) => add_fact(facts, lhs, depth + 1),
            (ExprValue::BoolConst(true), _) => add_fact(facts, rhs, depth + 1),
            (_, ExprValue::BoolConst(false)) => add_fact(facts, &lhs.clone().not(), depth + 1),
            (ExprValue::BoolConst(false), _) => add_fact(facts, &rhs.clone().not(), depth + 1),
            _ => facts.push(normalise(fact)),
        },
        _ => facts.push(normalise(fact)),
    }
}

/// Normalise unsigned comparisons to `x <ᵤ y` / `¬(x <ᵤ y)` and strip double
/// negation. Every rewrite is an equivalence.
fn normalise(literal: &Expr) -> Expr {
    match literal.value() {
        ExprValue::Not(inner) => match inner.value() {
            ExprValue::Not(positive) => normalise(positive),
            _ => negate_normal(normalise(inner)),
        },
        // a > b  ==  b < a
        ExprValue::BvUGt(lhs, rhs) => rhs.clone().bvult(lhs.clone()),
        // a >= b  ==  ¬(a < b)
        ExprValue::BvUGe(lhs, rhs) => lhs.clone().bvult(rhs.clone()).not(),
        // a <= b  ==  ¬(b < a)
        ExprValue::BvULe(lhs, rhs) => rhs.clone().bvult(lhs.clone()).not(),
        _ => literal.clone(),
    }
}

fn negate_normal(normal: Expr) -> Expr {
    match normal.value() {
        ExprValue::Not(positive) => positive.clone(),
        _ => normal.not(),
    }
}

fn const_value(expr: &Expr) -> Option<u128> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => u128::try_from(value.clone()).ok(),
        _ => None,
    }
}

fn unsigned_max(width: u32) -> Option<u128> {
    match width {
        0 => None,
        128 => Some(u128::MAX),
        w if w < 128 => Some((1u128 << w) - 1),
        _ => None,
    }
}

/// An upper bound of the unsigned value of `expr`, or `None` if its width is
/// over 128 bits or it is not a bitvector.
fn upper_bound(expr: &Expr) -> Option<u128> {
    let width = expr.sort().bitvec_width()?;
    let max = unsigned_max(width)?;
    let bound = match expr.value() {
        ExprValue::BitVecConst { .. } => const_value(expr)?,
        ExprValue::BvAnd(lhs, rhs) => match (upper_bound(lhs), upper_bound(rhs)) {
            (Some(a), Some(b)) => a.min(b),
            (Some(a), None) | (None, Some(a)) => a,
            (None, None) => max,
        },
        ExprValue::BvZeroExtend { expr: inner, .. } => upper_bound(inner).unwrap_or(max),
        ExprValue::BvURem(lhs, rhs) => {
            let lhs_bound = upper_bound(lhs).unwrap_or(max);
            match const_value(rhs) {
                Some(divisor) if divisor > 0 => lhs_bound.min(divisor - 1),
                // x % 0 == x in SMT-LIB, and x % y <= x otherwise.
                _ => lhs_bound,
            }
        }
        ExprValue::BvLShr(lhs, rhs) => {
            let lhs_bound = upper_bound(lhs).unwrap_or(max);
            match const_value(rhs) {
                // x <= U implies x >> k <= U >> k.
                Some(amount) if amount < u128::from(width) => lhs_bound >> amount,
                // bvlshr by the width or more is 0 in SMT-LIB.
                Some(_) => 0,
                None => lhs_bound,
            }
        }
        _ => max,
    };
    Some(bound.min(max))
}

/// A lower bound of the unsigned value of `expr` (constants only; 0 otherwise).
fn lower_bound(expr: &Expr) -> Option<u128> {
    expr.sort().bitvec_width()?;
    Some(const_value(expr).unwrap_or(0))
}

#[cfg(test)]
mod tests {
    use super::check_is_trivially_valid;
    use ay_bindings::{Expr, Sort};

    fn bv(name: &str, width: u32) -> Expr {
        Expr::var(name.to_string(), Sort::bitvec(width))
    }

    fn k(value: u128, width: u32) -> Expr {
        Expr::bitvec_const(value, width)
    }

    /// `wrapping_shl` on u8 with a u32 distance: `(s & 7) <u 8`.
    #[test]
    fn masked_shift_distance_is_valid() {
        let s = bv("s", 32);
        assert!(check_is_trivially_valid(&s.clone().bvand(k(7, 32)).bvult(k(8, 32))));
        assert!(check_is_trivially_valid(&k(31, 32).bvand(s.clone()).bvult(k(32, 32))));
        // The mask must actually bound the value.
        assert!(!check_is_trivially_valid(&s.clone().bvand(k(8, 32)).bvult(k(8, 32))));
        assert!(!check_is_trivially_valid(&s.bvult(k(8, 32))));
    }

    /// `checked_sub`: the Some-arm check weakened by its SwitchInt guard.
    #[test]
    fn guarded_unsigned_sub_is_valid_only_under_its_guard() {
        let a = bv("a", 32);
        let b = bv("b", 32);
        let lt = a.clone().bvult(b.clone());
        let no_underflow = a.clone().bvsub_no_underflow_unsigned(b.clone());
        // guard = ¬(a < b); weakened check = ¬guard ∨ check.
        let weakened = lt.clone().not().not().or(no_underflow.clone());
        assert!(check_is_trivially_valid(&weakened));
        // The same with the guard spelled a >= b, and through an outer path.
        let ge_guard = a.clone().bvuge(b.clone());
        assert!(check_is_trivially_valid(&ge_guard.clone().not().or(no_underflow.clone())));
        let outer = bv("p", 1).eq(k(1, 1));
        let nested = outer.not().or(ge_guard.not().or(no_underflow.clone()));
        assert!(check_is_trivially_valid(&nested));
        // Unguarded, or guarded the wrong way round, it is not valid.
        assert!(!check_is_trivially_valid(&no_underflow));
        assert!(!check_is_trivially_valid(&lt.not().or(no_underflow.clone())));
        let swapped = b.clone().bvult(a.clone()).not().not().or(no_underflow);
        assert!(!check_is_trivially_valid(&swapped));
    }

    /// `checked_div`: `rhs != 0 → rhs != 0`, and a bool `x == false` guard.
    #[test]
    fn guarded_divisor_check_is_valid() {
        let r = bv("r", 32);
        let nonzero = r.clone().eq(k(0, 32)).not();
        let is_zero = r.clone().eq(k(0, 32));
        assert!(check_is_trivially_valid(&is_zero.clone().or(nonzero.clone())));
        let bool_guard = is_zero.clone().eq(Expr::bool_const(false));
        assert!(check_is_trivially_valid(&bool_guard.not().or(nonzero.clone())));
        assert!(!check_is_trivially_valid(&nonzero));
        assert!(!check_is_trivially_valid(&is_zero.not().or(nonzero)));
    }

    /// `Step::forward_unchecked(start, 1)` under `start < end`.
    #[test]
    fn increment_below_a_strict_bound_is_valid() {
        let start = bv("start", 8);
        let end = bv("end", 8);
        let guard = start.clone().bvult(end.clone());
        let inc = start.clone().bvadd_no_overflow_unsigned(k(1, 8));
        assert!(check_is_trivially_valid(&guard.clone().not().or(inc.clone())));
        assert!(!check_is_trivially_valid(&inc));
        let by_two = start.clone().bvadd_no_overflow_unsigned(k(2, 8));
        assert!(!check_is_trivially_valid(&guard.clone().not().or(by_two)));
        // Bounds that fit need no guard: (x & 15) + 15 <= 255.
        let masked = start.bvand(k(15, 8)).bvadd_no_overflow_unsigned(k(15, 8));
        assert!(check_is_trivially_valid(&masked));
        let _ = end;
    }

    /// `checked_div` on a signed type: the MIN / -1 check under the guard that
    /// rules the pair out, in either conjunct order or one conjunct at a time.
    #[test]
    fn negated_conjunction_follows_from_its_guard() {
        let l = bv("l", 32);
        let r = bv("r", 32);
        let is_min = l.clone().eq(k(1u128 << 31, 32));
        let is_neg1 = r.clone().eq(k(u32::MAX as u128, 32));
        let check = is_neg1.clone().and(is_min.clone()).not();
        // guard ¬(l == MIN ∧ r == -1), conjuncts in the other order.
        let guard = is_min.clone().and(is_neg1.clone()).not();
        assert!(check_is_trivially_valid(&guard.clone().not().or(check.clone())));
        // guard l != MIN alone.
        assert!(check_is_trivially_valid(&is_min.clone().not().not().or(check.clone())));
        // no guard, or a guard on something else.
        assert!(!check_is_trivially_valid(&check));
        let other = r.clone().eq(k(0, 32)).not();
        assert!(!check_is_trivially_valid(&other.not().or(check)));
    }

    /// A constant divisor's checks: `¬(8 = 0)`, and the MIN / -1 check with a
    /// constant divisor `¬(s = MIN ∧ 8 = -1)`. Comparisons of two constants
    /// fold in every spelling, and only when they evaluate to true.
    #[test]
    fn constant_comparisons_fold() {
        let eight = k(8, 32);
        let zero = k(0, 32);
        assert!(check_is_trivially_valid(&eight.clone().eq(zero.clone()).not()));
        assert!(!check_is_trivially_valid(&eight.clone().eq(zero.clone())));
        assert!(check_is_trivially_valid(&eight.clone().eq(k(8, 32))));
        assert!(!check_is_trivially_valid(&eight.clone().eq(k(8, 32)).not()));
        // K1 < K2, K1 >= K2 (as ¬(K1 < K2)) and the other unsigned spellings.
        assert!(check_is_trivially_valid(&zero.clone().bvult(eight.clone())));
        assert!(!check_is_trivially_valid(&eight.clone().bvult(zero.clone())));
        assert!(check_is_trivially_valid(&eight.clone().bvult(zero.clone()).not()));
        assert!(!check_is_trivially_valid(&zero.clone().bvult(eight.clone()).not()));
        assert!(check_is_trivially_valid(&eight.clone().bvuge(k(8, 32))));
        assert!(check_is_trivially_valid(&eight.clone().bvugt(zero.clone())));
        assert!(!check_is_trivially_valid(&zero.clone().bvugt(eight.clone())));
        assert!(check_is_trivially_valid(&zero.clone().bvule(zero.clone())));
        // -1 is the all-ones value, so 8 = -1 is false and the pair is ruled out.
        let s = bv("s", 32);
        let is_min = s.clone().eq(k(1u128 << 31, 32));
        let divisor_is_neg1 = eight.clone().eq(k(u32::MAX as u128, 32));
        assert!(check_is_trivially_valid(&is_min.clone().and(divisor_is_neg1).not()));
        // A divisor that IS -1 leaves the check open.
        let neg1_is_neg1 = k(u32::MAX as u128, 32).eq(k(u32::MAX as u128, 32));
        assert!(!check_is_trivially_valid(&is_min.clone().and(neg1_is_neg1).not()));
        // Under a path guard, and never for a variable.
        let guarded = bv("p", 1).eq(k(1, 1)).not().or(eight.clone().eq(zero.clone()).not());
        assert!(check_is_trivially_valid(&guarded));
        assert!(!check_is_trivially_valid(&s.eq(zero).not()));
    }

    /// A right shift by a constant `k` bounds the value by `ub(lhs) >> k`
    /// (`x.unchecked_shl(s >> 29)` on u8), and by 0 once `k` reaches the width.
    #[test]
    fn logical_shift_right_by_a_constant_is_bounded() {
        let s = bv("s", 32);
        let shifted = |amount: u128| s.clone().bvlshr(k(amount, 32));
        // u32::MAX >> 29 == 7.
        assert!(check_is_trivially_valid(&shifted(29).bvult(k(8, 32))));
        assert!(!check_is_trivially_valid(&shifted(29).bvult(k(7, 32))));
        assert!(!check_is_trivially_valid(&shifted(28).bvult(k(8, 32))));
        // A masked operand shifts its own bound: (s & 0xFF) >> 4 <= 15.
        let masked = s.clone().bvand(k(0xFF, 32)).bvlshr(k(4, 32));
        assert!(check_is_trivially_valid(&masked.clone().bvult(k(16, 32))));
        assert!(!check_is_trivially_valid(&masked.bvult(k(15, 32))));
        // By 31 the bound is 1; by the width or more it is 0.
        assert!(check_is_trivially_valid(&shifted(31).bvult(k(2, 32))));
        assert!(!check_is_trivially_valid(&shifted(31).bvult(k(1, 32))));
        assert!(check_is_trivially_valid(&shifted(32).bvult(k(1, 32))));
        assert!(check_is_trivially_valid(&shifted(u32::MAX as u128).bvult(k(1, 32))));
        // A variable amount keeps the operand's bound.
        let by_var = s.clone().bvlshr(bv("t", 32));
        assert!(!check_is_trivially_valid(&by_var.bvult(k(8, 32))));
        // In an add on u8: (n >> 1) + (n >> 1) <= 254 fits, n + (n >> 1) need not.
        let narrow = bv("n", 8).bvlshr(k(1, 8));
        assert!(check_is_trivially_valid(
            &narrow.clone().bvadd_no_overflow_unsigned(narrow.clone())
        ));
        assert!(!check_is_trivially_valid(
            &bv("n", 8).bvlshr(k(0, 8)).bvadd_no_overflow_unsigned(narrow)
        ));
    }

    /// Conjunctions need every part; unrelated literals are never assumed.
    #[test]
    fn conjunction_and_unrelated_literals() {
        let a = bv("a", 8);
        let b = bv("b", 8);
        let shift_ok = a.clone().bvand(k(7, 8)).bvult(k(8, 8));
        let not_known = b.clone().bvult(k(8, 8));
        assert!(check_is_trivially_valid(&shift_ok.clone().and(Expr::bool_const(true))));
        assert!(!check_is_trivially_valid(&shift_ok.and(not_known.clone())));
        assert!(!check_is_trivially_valid(&Expr::bool_const(false)));
        assert!(!check_is_trivially_valid(&a.bvult(b).not().or(not_known)));
    }
}

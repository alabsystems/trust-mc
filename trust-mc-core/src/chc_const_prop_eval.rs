// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constant expression evaluation for CHC constant propagation. Part of #3371.

use std::collections::HashMap;

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;

use super::is_constant;
use crate::constraints::Constraints;

fn bitvec_modulus(width: u32) -> BigInt {
    BigInt::from(1u8) << (width as usize)
}

fn bitvec_to_signed(value: &BigInt, width: u32) -> BigInt {
    let sign_bit = BigInt::from(1u8) << ((width - 1) as usize);
    if value >= &sign_bit { value - bitvec_modulus(width) } else { value.clone() }
}

fn signed_trunc_div(dividend: &BigInt, divisor: &BigInt) -> BigInt {
    let zero = BigInt::from(0u8);
    let dividend_abs = if dividend < &zero { -dividend.clone() } else { dividend.clone() };
    let divisor_abs = if divisor < &zero { -divisor.clone() } else { divisor.clone() };
    let quotient = dividend_abs / divisor_abs;
    if (dividend < &zero) ^ (divisor < &zero) { -quotient } else { quotient }
}

fn signed_ashr(value: &BigInt, shift: u64, width: u32) -> BigInt {
    let zero = BigInt::from(0u8);
    if shift >= u64::from(width) {
        return if value < &zero { -BigInt::from(1u8) } else { zero };
    }

    let divisor = BigInt::from(1u8) << (shift as usize);
    if value >= &zero {
        value / divisor
    } else {
        -(((-value.clone()) + divisor.clone() - BigInt::from(1u8)) / divisor)
    }
}

/// Evaluates a BV binary operation when both operands are constants.
///
/// Returns `None` if either operand is not a `BitVecConst` or if the
/// operation isn't evaluable (e.g., division by zero).
///
/// Arithmetic operations return `Expr::bitvec_const` (normalized modulo 2^width).
/// Comparison operations return `Expr::bool_const`.
pub(super) fn eval_bv_binary_const(op: &ExprValue, a: &Expr, b: &Expr) -> Option<Expr> {
    let (va, wa) = match a.value() {
        ExprValue::BitVecConst { value, width } => (value, *width),
        _ => return None,
    };
    let (vb, wb) = match b.value() {
        ExprValue::BitVecConst { value, width } => (value, *width),
        _ => return None,
    };

    let zero = BigInt::from(0u8);
    match op {
        // Arithmetic (same-width operands, result same width).
        ExprValue::BvAdd(..) => Some(Expr::bitvec_const(va + vb, wa)),
        ExprValue::BvSub(..) => Some(Expr::bitvec_const(va - vb, wa)),
        ExprValue::BvMul(..) => Some(Expr::bitvec_const(va * vb, wa)),
        ExprValue::BvURem(..) if *vb != zero => Some(Expr::bitvec_const(va % vb, wa)),
        ExprValue::BvUDiv(..) if *vb != zero => Some(Expr::bitvec_const(va / vb, wa)),
        ExprValue::BvSDiv(..) if *vb != zero => {
            let signed_a = bitvec_to_signed(va, wa);
            let signed_b = bitvec_to_signed(vb, wb);
            Some(Expr::bitvec_const(signed_trunc_div(&signed_a, &signed_b), wa))
        }
        ExprValue::BvSRem(..) if *vb != zero => {
            let signed_a = bitvec_to_signed(va, wa);
            let signed_b = bitvec_to_signed(vb, wb);
            let quotient = signed_trunc_div(&signed_a, &signed_b);
            Some(Expr::bitvec_const(signed_a - (quotient * signed_b), wa))
        }

        // Bitwise (same-width operands).
        ExprValue::BvAnd(..) => Some(Expr::bitvec_const(va & vb, wa)),
        ExprValue::BvOr(..) => Some(Expr::bitvec_const(va | vb, wa)),
        ExprValue::BvXor(..) => Some(Expr::bitvec_const(va ^ vb, wa)),

        // Shifts. Shift amount is the unsigned value of vb.
        ExprValue::BvShl(..) => {
            let shift = u64::try_from(vb).unwrap_or(u64::from(wa));
            if shift >= u64::from(wa) {
                Some(Expr::bitvec_const(0u64, wa))
            } else {
                Some(Expr::bitvec_const(va << (shift as usize), wa))
            }
        }
        ExprValue::BvLShr(..) => {
            let shift = u64::try_from(vb).unwrap_or(u64::from(wa));
            if shift >= u64::from(wa) {
                Some(Expr::bitvec_const(0u64, wa))
            } else {
                Some(Expr::bitvec_const(va >> (shift as usize), wa))
            }
        }
        ExprValue::BvAShr(..) => {
            let shift = u64::try_from(vb).unwrap_or(u64::from(wa));
            let signed_a = bitvec_to_signed(va, wa);
            Some(Expr::bitvec_const(signed_ashr(&signed_a, shift, wa), wa))
        }

        // Unsigned comparisons (values already normalized to [0, 2^width)).
        ExprValue::BvULt(..) => Some(Expr::bool_const(va < vb)),
        ExprValue::BvULe(..) => Some(Expr::bool_const(va <= vb)),
        ExprValue::BvUGt(..) => Some(Expr::bool_const(va > vb)),
        ExprValue::BvUGe(..) => Some(Expr::bool_const(va >= vb)),
        ExprValue::BvSLt(..) => {
            let signed_a = bitvec_to_signed(va, wa);
            let signed_b = bitvec_to_signed(vb, wb);
            Some(Expr::bool_const(signed_a < signed_b))
        }
        ExprValue::BvSLe(..) => {
            let signed_a = bitvec_to_signed(va, wa);
            let signed_b = bitvec_to_signed(vb, wb);
            Some(Expr::bool_const(signed_a <= signed_b))
        }
        ExprValue::BvSGt(..) => {
            let signed_a = bitvec_to_signed(va, wa);
            let signed_b = bitvec_to_signed(vb, wb);
            Some(Expr::bool_const(signed_a > signed_b))
        }
        ExprValue::BvSGe(..) => {
            let signed_a = bitvec_to_signed(va, wa);
            let signed_b = bitvec_to_signed(vb, wb);
            Some(Expr::bool_const(signed_a >= signed_b))
        }

        // Concat: result width = wa + wb.
        ExprValue::BvConcat(..) => {
            let shifted = va << (wb as usize);
            Some(Expr::bitvec_const(shifted | vb, wa + wb))
        }

        // Overflow checks produce booleans.
        // bvadd_no_overflow_unsigned: (a + b) < 2^w — i.e., no carry.
        ExprValue::BvAddNoOverflowUnsigned(..) => {
            let sum = va + vb;
            let modulus = BigInt::from(1u8) << (wa as usize);
            Some(Expr::bool_const(sum < modulus))
        }
        // bvsub_no_underflow_unsigned: a >= b (unsigned).
        ExprValue::BvSubNoUnderflowUnsigned(..) => Some(Expr::bool_const(va >= vb)),

        _ => None,
    }
}

/// Evaluates `select(store(arr, idx, val), sel_idx)` using the McCarthy
/// store-select axiom, without requiring the array to be a `const_array`.
///
/// Uses structural equality for the matching case: `select(store(a, i, v), i) = v`.
/// Only requires constant indices for the recursion case (different indices).
pub(super) fn eval_select_store_const(array: &Expr, sel_index: &Expr) -> Option<Expr> {
    if let ExprValue::Store { array: inner_arr, index: store_idx, value: store_val } = array.value()
    {
        // Sound: select(store(a, i, v), i) = v for ALL i (McCarthy 1962).
        // Uses structural equality — works for variables, constants, and complex
        // index expressions alike.
        if sel_index == store_idx {
            return Some(store_val.clone());
        }
        // Only recurse when indices are provably different (both constant, not equal).
        if is_constant(sel_index) && is_constant(store_idx) {
            return eval_select_store_const(inner_arr, sel_index);
        }
    }
    None
}

/// Flattens `And(...)` conjunctions in constraints into a flat list.
///
/// Init rules combine all constraints into `And(And(...), ...)` via
/// `.reduce(Expr::and)`. This extracts leaf conjuncts so equality
/// matching can see `Eq` nodes buried inside `And` trees.
pub(super) fn flatten_conjunctions(constraints: &Constraints) -> Vec<Expr> {
    fn flatten_and(expr: &Expr, out: &mut Vec<Expr>) {
        if let ExprValue::And(children) = expr.value() {
            for child in children {
                flatten_and(child, out);
            }
        } else {
            out.push(expr.clone());
        }
    }
    let mut flat = Vec::new();
    for expr in constraints {
        flatten_and(expr, &mut flat);
    }
    flat
}

/// Returns `true` if the constraint list contains `false` as a top-level
/// conjunct or nested inside `And(...)` trees.
pub(super) fn has_false_conjunct(constraints: &Constraints) -> bool {
    constraints.iter().any(is_trivially_false)
}

/// Check if an expression is trivially false.
fn is_trivially_false(expr: &Expr) -> bool {
    match try_eval_to_bool(expr) {
        Some(false) => true,
        Some(true) => false,
        None => false,
    }
}

/// Strips trivially-true constraints from all rule bodies. Returns count.
pub(super) fn strip_trivially_true_constraints(vc: &mut crate::chc::ChcVc) -> usize {
    let mut total = 0;
    for rule in &mut vc.rules {
        let old: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        let n = old.len();
        let new: Vec<Expr> = old.into_iter().filter(|c| !is_trivially_true(c)).collect();
        total += n - new.len();
        rule.body.constraints = Constraints::Owned(new);
    }
    total
}

/// Check if an expression is trivially true.
pub(super) fn is_trivially_true(expr: &Expr) -> bool {
    matches!(try_eval_to_bool(expr), Some(true))
}

/// Attempt to evaluate an expression to a boolean constant.
///
/// Handles Bool connectives (And, Or, Not), Eq on constants,
/// and BV comparisons (BvULt, BvUGe, etc.) when both operands
/// are constant or reducible to constants. Returns `None` when
/// the expression cannot be fully evaluated.
pub fn try_eval_to_bool(expr: &Expr) -> Option<bool> {
    match expr.value() {
        ExprValue::BoolConst(b) => Some(*b),
        ExprValue::And(children) => {
            let mut all_true = true;
            for child in children {
                match try_eval_to_bool(child) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => all_true = false,
                }
            }
            if all_true { Some(true) } else { None }
        }
        ExprValue::Or(children) => {
            let mut all_false = true;
            for child in children {
                match try_eval_to_bool(child) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => all_false = false,
                }
            }
            if all_false { Some(false) } else { None }
        }
        ExprValue::Not(inner) => try_eval_to_bool(inner).map(|b| !b),
        ExprValue::Eq(a, b) if a == b => Some(true),
        ExprValue::Eq(a, b) => {
            if let (Some(lhs), Some(rhs)) = (try_eval_to_bool(a), try_eval_to_bool(b)) {
                return Some(lhs == rhs);
            }
            if let Some(value) = eval_const_array_store_eq(a, b) {
                return Some(value);
            }
            let ca = try_eval_to_const(a)?;
            let cb = try_eval_to_const(b)?;
            Some(ca == cb)
        }
        // BV comparisons: evaluate both operands, use eval_bv_binary_const.
        ExprValue::BvULt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b) => {
            let ca = try_eval_to_const(a)?;
            let cb = try_eval_to_const(b)?;
            let result = eval_bv_binary_const(expr.value(), &ca, &cb)?;
            match result.value() {
                ExprValue::BoolConst(b) => Some(*b),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Evaluates equality between a const array and a single store over the same
/// const array. This catches unreachable drop-check rules such as:
/// `const(true) == store(const(true), idx, false)`.
fn eval_const_array_store_eq(a: &Expr, b: &Expr) -> Option<bool> {
    eval_const_array_store_eq_ordered(a, b).or_else(|| eval_const_array_store_eq_ordered(b, a))
}

fn eval_const_array_store_eq_ordered(const_side: &Expr, store_side: &Expr) -> Option<bool> {
    let ExprValue::ConstArray { value: const_value, .. } = const_side.value() else {
        return None;
    };
    let ExprValue::Store { array, value: stored_value, .. } = store_side.value() else {
        return None;
    };
    let ExprValue::ConstArray { value: base_value, .. } = array.value() else {
        return None;
    };

    if base_value != const_value {
        return None;
    }
    if stored_value == const_value {
        return Some(true);
    }

    let const_eval = try_eval_to_const(const_value)?;
    let stored_eval = try_eval_to_const(stored_value)?;
    Some(const_eval == stored_eval)
}

/// Attempt to evaluate an expression to a constant (BitVecConst or BoolConst).
///
/// Recursively evaluates BV arithmetic, extract, extend, not, and neg
/// on constant operands. Returns `None` for non-constant expressions.
pub fn try_eval_to_const(expr: &Expr) -> Option<Expr> {
    match expr.value() {
        ExprValue::BitVecConst { .. } | ExprValue::BoolConst(_) => Some(expr.clone()),
        // BV binary ops: evaluate both sides, then fold.
        ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvMul(a, b)
        | ExprValue::BvUDiv(a, b)
        | ExprValue::BvSDiv(a, b)
        | ExprValue::BvURem(a, b)
        | ExprValue::BvSRem(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvXor(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvConcat(a, b) => {
            let ca = try_eval_to_const(a)?;
            let cb = try_eval_to_const(b)?;
            eval_bv_binary_const(expr.value(), &ca, &cb)
        }
        // BvExtract: shift right by `low`, mask to (high - low + 1) bits.
        ExprValue::BvExtract { expr: inner, high, low } => {
            let ci = try_eval_to_const(inner)?;
            if let ExprValue::BitVecConst { value, width } = ci.value() {
                if *low <= *high && *high < *width {
                    let result_width = high - low + 1;
                    let mask = (BigInt::from(1u8) << (result_width as usize)) - 1;
                    let extracted = (value >> (*low as usize)) & mask;
                    return Some(Expr::bitvec_const(extracted, result_width));
                }
            }
            None
        }
        // BvZeroExtend: same value, wider width.
        ExprValue::BvZeroExtend { expr: inner, extra_bits } => {
            let ci = try_eval_to_const(inner)?;
            if let ExprValue::BitVecConst { value, width } = ci.value() {
                Some(Expr::bitvec_const(value.clone(), width + extra_bits))
            } else {
                None
            }
        }
        // BvSignExtend: sign-extend by copying sign bit.
        ExprValue::BvSignExtend { expr: inner, extra_bits } => {
            let ci = try_eval_to_const(inner)?;
            if let ExprValue::BitVecConst { value, width } = ci.value() {
                let new_width = width + extra_bits;
                let signed = bitvec_to_signed(value, *width);
                Some(Expr::bitvec_const(signed, new_width))
            } else {
                None
            }
        }
        // BvNot: XOR with all-ones mask.
        ExprValue::BvNot(inner) => {
            let ci = try_eval_to_const(inner)?;
            if let ExprValue::BitVecConst { value, width } = ci.value() {
                let mask = (BigInt::from(1u8) << (*width as usize)) - 1;
                Some(Expr::bitvec_const(value ^ mask, *width))
            } else {
                None
            }
        }
        // BvNeg: two's complement negation = modular negation.
        ExprValue::BvNeg(inner) => {
            let ci = try_eval_to_const(inner)?;
            if let ExprValue::BitVecConst { value, width } = ci.value() {
                let modulus = bitvec_modulus(*width);
                Some(Expr::bitvec_const((modulus - value) % bitvec_modulus(*width), *width))
            } else {
                None
            }
        }
        // Comparisons + boolean structure fold to BoolConst via the bool
        // evaluator (exact raw-bits/width semantics live in
        // eval_bv_binary_const). Part of #55 piece 2: lets derived recursion
        // arguments like `Ite(n == 0, .., n - 1)` and switch discriminants
        // over comparisons evaluate all the way down.
        ExprValue::BvULt(..)
        | ExprValue::BvULe(..)
        | ExprValue::BvUGt(..)
        | ExprValue::BvUGe(..)
        | ExprValue::BvSLt(..)
        | ExprValue::BvSLe(..)
        | ExprValue::BvSGt(..)
        | ExprValue::BvSGe(..)
        | ExprValue::BvAddNoOverflowUnsigned(..)
        | ExprValue::BvSubNoUnderflowUnsigned(..)
        | ExprValue::And(..)
        | ExprValue::Or(..)
        | ExprValue::Not(..)
        | ExprValue::Eq(..) => try_eval_to_bool(expr).map(Expr::bool_const),
        // Ite: fold the condition exactly; only then fold the taken branch.
        ExprValue::Ite { cond, then_expr, else_expr } => {
            if try_eval_to_bool(cond)? {
                try_eval_to_const(then_expr)
            } else {
                try_eval_to_const(else_expr)
            }
        }
        // Positional tuple-field select over a literal constructor: the
        // checked-arithmetic lowering binds `CheckedSub(a, b)` as a tuple
        // DatatypeConstructor and reads `.0` via a `fld_N` selector — fold
        // structurally (same datatype, positional field) then evaluate the
        // selected argument. Part of #55 piece 2: without this, every derived
        // recursion argument in a debug (overflow-checked) build is opaque.
        ExprValue::DatatypeSelector { datatype_name, selector_name, expr: inner } => {
            let ExprValue::DatatypeConstructor { datatype_name: ctor_dt, args, .. } = inner.value()
            else {
                return None;
            };
            if ctor_dt != datatype_name {
                return None;
            }
            let idx: usize = selector_name.strip_prefix("fld_")?.parse().ok()?;
            try_eval_to_const(args.get(idx)?)
        }
        _ => None,
    }
}

/// Propagates constants to unconstrained `__out` head variables.
///
/// SOUNDNESS INVARIANT: `__out` suffix implies identity pass-through (created
/// via `StateVarManager::push_state_var_pair()`). When `X__out` is unconstrained
/// in a rule body, it is universally quantified, equivalent to `X__out == X`.
/// If `X` is known-constant, propagates that constant to `X__out`.
pub(super) fn propagate_to_unconstrained_out_vars(
    head_args: &[Expr],
    constraints: &Constraints,
    known: &mut HashMap<String, Expr>,
) {
    use std::collections::HashSet;

    // Collect all variable names mentioned in constraints via flattening.
    let flat = flatten_conjunctions(constraints);
    let mut constrained_vars: HashSet<String> = HashSet::new();
    for expr in &flat {
        if !collect_constraint_vars(expr, &mut constrained_vars, false) {
            // Unknown expression variant encountered — can't safely determine
            // which head vars are constrained. Abort to prevent unsound propagation.
            return;
        }
    }

    // For each head arg that's an unconstrained `__out` variable, check if
    // the base name (without `__out`) is in the known map.
    for arg in head_args {
        if let ExprValue::Var { name } = arg.value() {
            if let Some(base) = name.strip_suffix("__out") {
                if !constrained_vars.contains(name.as_str()) && !known.contains_key(name.as_str()) {
                    if let Some(constant) = known.get(base) {
                        known.insert(name.clone(), constant.clone());
                    }
                }
            }
        }
    }
}

/// Collects all variable names referenced in an expression tree.
///
/// Returns `true` if all sub-expressions were successfully traversed, `false`
/// if an unrecognized `ExprValue` variant was encountered. When `false`, the
/// caller should treat the collection as incomplete and avoid optimizations
/// that depend on knowing ALL constrained variables (soundness guard for
/// `#[non_exhaustive]` `ExprValue`).
///
/// `in_dt`: when `true`, variables are visited (for traversal completeness)
/// but NOT added to the constrained set. DatatypeConstructor/FuncApp set this
/// to `true` for their arguments — field args are value-defining, not
/// value-restricting (#3398 design).
///
/// Uses `ExprValue::children()` and `is_known_variant()` from ay_bindings
/// instead of manually enumerating every variant. Part of #3415.
fn collect_constraint_vars(
    expr: &Expr,
    out: &mut std::collections::HashSet<String>,
    in_dt: bool,
) -> bool {
    match expr.value() {
        ExprValue::Var { name } => {
            if !in_dt {
                out.insert(name.clone());
            }
            true
        }
        // DT/FuncApp args are value-defining, not value-restricting.
        // Recurse with in_dt=true so variables inside are visited for
        // traversal completeness but NOT added to the constrained set. (#3398)
        ExprValue::DatatypeConstructor { args, .. } | ExprValue::FuncApp { args, .. } => {
            args.iter().all(|a| collect_constraint_vars(a, out, true))
        }
        // All other known variants: recurse children generically.
        _ if expr.value().is_known_variant() => {
            expr.value().children().all(|c| collect_constraint_vars(c, out, in_dt))
        }
        // Unknown variant: conservative abort — can't safely determine
        // which variables are constrained.
        _ => false,
    }
}

#[cfg(test)]
#[path = "chc_const_prop_eval_tests.rs"]
mod tests;

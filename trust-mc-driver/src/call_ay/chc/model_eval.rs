// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Self-contained model evaluator used to validate counterexample witnesses.
//!
//! The acyclic error-derivation shortcut (`native_nullary`) trusts the embedded
//! `SmtContext::check_sat` to confirm a reachable `error`. That solver has known
//! soundness gaps on some bitvector shapes (e.g. it reports
//! `(not (= ((_ extract 31 0) (concat _ #x00000000)) #x0))` as SAT, which z3 and
//! the ay CLI both refute as UNSAT). Trusting it blindly turned genuinely-UNSAT
//! function-contract proofs into spurious `Genuine` counterexamples.
//!
//! [`constraints_are_constant_refuted`] targets the exact bitvector `concat`/
//! `extract` soundness gap in the embedded solver, which returns `Sat` for a
//! constraint set that is actually UNSAT (e.g.
//! `(= _a (concat _ #x00000000)) ∧ (= _b _a) ∧ (not (= ((_ extract 31 0) _b) #x0))`,
//! which z3 and the ay CLI both refute).
//!
//! The check is *model-free* — it does not trust the buggy solver's model at
//! all. It derives its own partial assignment by propagating `var = <constant>`
//! equalities to a fixpoint, then reports a refutation only if some constraint
//! provably folds to `false` under that assignment.
//!
//! This is sound in the critical direction: the propagated assignments are
//! *implied* by the constraints, so a genuinely-satisfiable set can never fold
//! any constraint to `false` (a satisfying model extends the propagation).
//! Therefore a genuine counterexample is never refuted — its fast exact-
//! derivation path is preserved — while the constant-foldable `concat`/`extract`
//! contradiction is caught and deferred to the full CHC portfolio.

use std::collections::HashMap;

use ay::chc::{ChcExpr, ChcOp, SmtValue};

/// Whether the accumulated constraints are provably contradictory by constant
/// propagation and folding — i.e. the embedded solver's `Sat` was spurious.
pub(super) fn constraints_are_constant_refuted(constraints: &[ChcExpr]) -> bool {
    // The only known `check_sat` soundness gap is `concat`/`extract`; skip the
    // work (and never reject) for constraint sets that cannot trip it.
    if !constraints.iter().any(uses_concat_or_extract) {
        return false;
    }

    // Derive a partial assignment from `var = <evaluable-expr>` equalities,
    // iterating to a fixpoint so equality chains propagate constants forward.
    let mut model: HashMap<String, SmtValue> = HashMap::new();
    loop {
        let mut changed = false;
        for c in constraints {
            let ChcExpr::Op(ChcOp::Eq, args) = c else { continue };
            if args.len() != 2 {
                continue;
            }
            for (lhs, rhs) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                let ChcExpr::Var(v) = lhs.as_ref() else { continue };
                if model.contains_key(&v.name) {
                    continue;
                }
                if let Some(val) = eval_chc(rhs, &model) {
                    model.insert(v.name.clone(), val);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // A constraint that folds to `false` under the implied assignment proves the
    // whole set unsatisfiable.
    constraints.iter().any(|c| matches!(eval_chc(c, &model), Some(SmtValue::Bool(false))))
}

/// Whether the expression tree contains a bitvector `concat` or `extract`.
fn uses_concat_or_extract(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::BvConcat | ChcOp::BvExtract(_, _), _) => true,
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|a| uses_concat_or_extract(a))
        }
        ChcExpr::ConstArray(_, inner) => uses_concat_or_extract(inner),
        _ => false,
    }
}

fn bv_mask(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
}

/// Whether this evaluator computes with bit-vectors of `width` bits: `1..=128`,
/// the widths a `u128` holds exactly. Anything wider is refused (`None`)
/// wherever it appears — as a literal, a model value, an operand or a result —
/// never computed modulo 2^128. ay-bindings prints every unsigned `u128`
/// multiplication-overflow flag as the high half of a 256-bit product,
/// `((_ extract 255 128) (bvmul ((_ zero_extend 128) a) ((_ zero_extend 128) b)))`;
/// computing that in a `u128` shifted right by 128 (a panic under overflow
/// checks, `v >> 0` without them) and let the vacuity witness certify an
/// infeasible derivation.
fn bv_width_supported(width: u32) -> bool {
    (1..=128).contains(&width)
}

/// Exact evaluation of `expr` under `assignment`, for a caller that holds a
/// TOTAL assignment and needs a yes/no it can rely on: the CHC vacuity witness
/// (`vacuity_witness`) accepts a derivation only when every constraint comes
/// back `Some(Bool(true))` here. `None` means "not evaluated exactly" — a
/// missing variable, an operator outside the supported fragment, a sort or
/// width mismatch, a bit-vector wider than 128 bits — and the caller must then
/// reject.
pub(super) fn eval_under(
    expr: &ChcExpr,
    assignment: &HashMap<String, SmtValue>,
) -> Option<SmtValue> {
    eval_chc(expr, assignment)
}

/// The value of a `width`-bit two's-complement bit-vector as a signed integer
/// (`width` in `1..=128`): sign-extend to 128 bits, then reinterpret.
fn bv_to_signed(value: u128, width: u32) -> Option<i128> {
    if width == 0 || width > 128 {
        return None;
    }
    let value = value & bv_mask(width);
    let negative = (value >> (width - 1)) & 1 == 1;
    let extended = if negative { value | !bv_mask(width) } else { value };
    Some(extended as i128)
}

/// Conservative evaluator: returns `Some(value)` only when the expression can be
/// concretely evaluated under `model`, and `None` for anything uncertain
/// (missing variable, uninterpreted function, unsupported operator, sort
/// mismatch). Correctness in the `Some` direction is what soundness relies on.
fn eval_chc(expr: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<SmtValue> {
    match expr {
        ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
        ChcExpr::Int(i) => Some(SmtValue::Int(*i)),
        ChcExpr::BitVec(v, w) if bv_width_supported(*w) => {
            Some(SmtValue::BitVec(*v & bv_mask(*w), *w))
        }
        ChcExpr::Var(v) => canonical_value(model.get(&v.name)?),
        // Every operator result passes the same width check as a literal, so a
        // bit-vector outside `1..=128` can never become an operand.
        ChcExpr::Op(op, args) => eval_chc_op(*op, args, model)
            .filter(|value| !matches!(value, SmtValue::BitVec(_, w) if !bv_width_supported(*w))),
        ChcExpr::ConstArray(_, inner) => {
            Some(SmtValue::ConstArray(Box::new(eval_chc(inner, model)?)))
        }
        _ => None,
    }
}

/// `value` in the one shape this evaluator computes with, or `None`: a
/// bit-vector masked to a width in `1..=128`, a Bool, an `i128` Int, or an
/// array (constant, or a default with point overrides at scalar indices, no
/// index listed twice with different elements). Everything else — BigInt,
/// Real, opaque solver placeholders, datatypes — is refused.
fn canonical_value(value: &SmtValue) -> Option<SmtValue> {
    match value {
        SmtValue::Bool(_) | SmtValue::Int(_) => Some(value.clone()),
        SmtValue::BitVec(v, w) if bv_width_supported(*w) => {
            Some(SmtValue::BitVec(v & bv_mask(*w), *w))
        }
        SmtValue::ConstArray(default) => {
            Some(SmtValue::ConstArray(Box::new(canonical_value(default)?)))
        }
        SmtValue::ArrayMap { default, entries } => {
            let default = canonical_value(default)?;
            let mut out: Vec<(SmtValue, SmtValue)> = Vec::with_capacity(entries.len());
            for (index, element) in entries {
                let index = canonical_value(index)?;
                if !is_scalar(&index) {
                    return None;
                }
                let element = canonical_value(element)?;
                match out.iter().find(|(seen, _)| *seen == index) {
                    Some((_, seen_element)) if *seen_element != element => return None,
                    Some(_) => {}
                    None => out.push((index, element)),
                }
            }
            Some(SmtValue::ArrayMap { default: Box::new(default), entries: out })
        }
        _ => None,
    }
}

fn is_scalar(value: &SmtValue) -> bool {
    matches!(value, SmtValue::Bool(_) | SmtValue::Int(_) | SmtValue::BitVec(..))
}

/// Two canonical scalars of the same sort (and width).
fn same_scalar_sort(a: &SmtValue, b: &SmtValue) -> bool {
    match (a, b) {
        (SmtValue::Bool(_), SmtValue::Bool(_)) | (SmtValue::Int(_), SmtValue::Int(_)) => true,
        (SmtValue::BitVec(_, x), SmtValue::BitVec(_, y)) => x == y,
        _ => false,
    }
}

/// The default and point overrides of a canonical array value.
fn array_parts(value: &SmtValue) -> Option<(&SmtValue, &[(SmtValue, SmtValue)])> {
    match value {
        SmtValue::ConstArray(default) => Some((default, &[])),
        SmtValue::ArrayMap { default, entries } => Some((default, entries)),
        _ => None,
    }
}

/// `(select array index)`: the override at `index`, else the default.
fn array_select(array: &SmtValue, index: &SmtValue) -> Option<SmtValue> {
    let (default, entries) = array_parts(array)?;
    if !is_scalar(index) || entries.iter().any(|(seen, _)| !same_scalar_sort(seen, index)) {
        return None;
    }
    let element = entries.iter().find(|(seen, _)| seen == index).map(|(_, e)| e);
    Some(element.unwrap_or(default).clone())
}

/// `(store array index element)`.
fn array_store(array: &SmtValue, index: SmtValue, element: SmtValue) -> Option<SmtValue> {
    let (default, entries) = array_parts(array)?;
    if !is_scalar(&index) || entries.iter().any(|(seen, _)| !same_scalar_sort(seen, &index)) {
        return None;
    }
    let mut out: Vec<(SmtValue, SmtValue)> =
        entries.iter().filter(|(seen, _)| *seen != index).cloned().collect();
    out.push((index, element));
    Some(SmtValue::ArrayMap { default: Box::new(default.clone()), entries: out })
}

/// Semantic equality of two canonical values: `Some(true)` / `Some(false)`
/// only when decided exactly, `None` otherwise.
///
/// Arrays are equal iff they agree at every index. Every index either array
/// overrides is compared directly. Outside those, both arrays read their
/// defaults, so equal defaults decide `true`; different defaults decide
/// `false` exactly when some index lies outside the overridden ones — always
/// for `Int` and wide bit-vectors, and checked by counting for `Bool` and
/// narrow bit-vectors; otherwise the answer is `None`.
fn values_equal(a: &SmtValue, b: &SmtValue) -> Option<bool> {
    if is_scalar(a) || is_scalar(b) {
        return (same_scalar_sort(a, b)).then(|| a == b);
    }
    let (default_a, entries_a) = array_parts(a)?;
    let (default_b, entries_b) = array_parts(b)?;
    let mut indices: Vec<&SmtValue> = Vec::with_capacity(entries_a.len() + entries_b.len());
    for (index, _) in entries_a.iter().chain(entries_b) {
        if !indices.contains(&index) {
            indices.push(index);
        }
    }
    for index in &indices {
        if !values_equal(&array_select(a, index)?, &array_select(b, index)?)? {
            return Some(false);
        }
    }
    if values_equal(default_a, default_b)? {
        return Some(true);
    }
    let domain_exceeds_overrides = match indices.first() {
        None | Some(SmtValue::Int(_)) => true,
        Some(SmtValue::BitVec(_, w)) if *w >= 64 => true,
        Some(SmtValue::BitVec(_, w)) => (indices.len() as u128) < (1u128 << w),
        Some(SmtValue::Bool(_)) => indices.len() < 2,
        Some(_) => false,
    };
    domain_exceeds_overrides.then_some(false)
}

fn eval_bool(expr: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<bool> {
    match eval_chc(expr, model)? {
        SmtValue::Bool(b) => Some(b),
        _ => None,
    }
}

/// Evaluate a bitvector operand, returning `(value, width)` with `width` in
/// `1..=128` (see [`bv_width_supported`]).
fn eval_bv(expr: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<(u128, u32)> {
    match eval_chc(expr, model)? {
        SmtValue::BitVec(v, w) if bv_width_supported(w) => Some((v & bv_mask(w), w)),
        _ => None,
    }
}

// i128-lockstep (ay rank 6 Phase 1): `ChcExpr::Int`/`SmtValue::Int` are i128-wide.
fn eval_int(expr: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<i128> {
    match eval_chc(expr, model)? {
        SmtValue::Int(i) => Some(i),
        _ => None,
    }
}

#[allow(clippy::too_many_lines)]
fn eval_chc_op(
    op: ChcOp,
    args: &[std::sync::Arc<ChcExpr>],
    model: &HashMap<String, SmtValue>,
) -> Option<SmtValue> {
    match op {
        ChcOp::Not if args.len() == 1 => Some(SmtValue::Bool(!eval_bool(&args[0], model)?)),
        ChcOp::And => {
            for a in args {
                if !eval_bool(a, model)? {
                    return Some(SmtValue::Bool(false));
                }
            }
            Some(SmtValue::Bool(true))
        }
        ChcOp::Or => {
            for a in args {
                if eval_bool(a, model)? {
                    return Some(SmtValue::Bool(true));
                }
            }
            Some(SmtValue::Bool(false))
        }
        ChcOp::Implies if args.len() == 2 => {
            Some(SmtValue::Bool(!eval_bool(&args[0], model)? || eval_bool(&args[1], model)?))
        }
        ChcOp::Iff if args.len() == 2 => {
            Some(SmtValue::Bool(eval_bool(&args[0], model)? == eval_bool(&args[1], model)?))
        }
        ChcOp::Eq if args.len() == 2 => eval_eq(&args[0], &args[1], model).map(SmtValue::Bool),
        ChcOp::Ne if args.len() == 2 => {
            eval_eq(&args[0], &args[1], model).map(|b| SmtValue::Bool(!b))
        }
        ChcOp::Ite if args.len() == 3 => {
            if eval_bool(&args[0], model)? {
                eval_chc(&args[1], model)
            } else {
                eval_chc(&args[2], model)
            }
        }
        // Integer arithmetic / comparison.
        ChcOp::Add | ChcOp::Sub | ChcOp::Mul if args.len() == 2 => {
            let (l, r) = (eval_int(&args[0], model)?, eval_int(&args[1], model)?);
            let v = match op {
                ChcOp::Add => l.checked_add(r)?,
                ChcOp::Sub => l.checked_sub(r)?,
                _ => l.checked_mul(r)?,
            };
            Some(SmtValue::Int(v))
        }
        ChcOp::Neg if args.len() == 1 => {
            Some(SmtValue::Int(eval_int(&args[0], model)?.checked_neg()?))
        }
        ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge if args.len() == 2 => {
            let (l, r) = (eval_int(&args[0], model)?, eval_int(&args[1], model)?);
            Some(SmtValue::Bool(match op {
                ChcOp::Lt => l < r,
                ChcOp::Le => l <= r,
                ChcOp::Gt => l > r,
                _ => l >= r,
            }))
        }
        // Bitvector arithmetic / bitwise (same-width operands).
        ChcOp::BvAdd | ChcOp::BvSub | ChcOp::BvMul | ChcOp::BvAnd | ChcOp::BvOr | ChcOp::BvXor
            if args.len() == 2 =>
        {
            let (lv, lw) = eval_bv(&args[0], model)?;
            let (rv, rw) = eval_bv(&args[1], model)?;
            if lw != rw {
                return None;
            }
            let v = match op {
                ChcOp::BvAdd => lv.wrapping_add(rv),
                ChcOp::BvSub => lv.wrapping_sub(rv),
                ChcOp::BvMul => lv.wrapping_mul(rv),
                ChcOp::BvAnd => lv & rv,
                ChcOp::BvOr => lv | rv,
                _ => lv ^ rv,
            };
            Some(SmtValue::BitVec(v & bv_mask(lw), lw))
        }
        ChcOp::BvNot if args.len() == 1 => {
            let (v, w) = eval_bv(&args[0], model)?;
            Some(SmtValue::BitVec((!v) & bv_mask(w), w))
        }
        ChcOp::BvNeg if args.len() == 1 => {
            let (v, w) = eval_bv(&args[0], model)?;
            Some(SmtValue::BitVec(v.wrapping_neg() & bv_mask(w), w))
        }
        // Unsigned bitvector comparisons (values are already masked, so raw u128
        // ordering matches unsigned bitvector ordering).
        ChcOp::BvULt | ChcOp::BvULe | ChcOp::BvUGt | ChcOp::BvUGe if args.len() == 2 => {
            let (lv, lw) = eval_bv(&args[0], model)?;
            let (rv, rw) = eval_bv(&args[1], model)?;
            if lw != rw {
                return None;
            }
            Some(SmtValue::Bool(match op {
                ChcOp::BvULt => lv < rv,
                ChcOp::BvULe => lv <= rv,
                ChcOp::BvUGt => lv > rv,
                _ => lv >= rv,
            }))
        }
        ChcOp::BvConcat if args.len() == 2 => {
            let (lv, lw) = eval_bv(&args[0], model)?;
            let (rv, rw) = eval_bv(&args[1], model)?;
            let width = lw.checked_add(rw)?;
            if width > 128 {
                return None;
            }
            Some(SmtValue::BitVec(((lv << rw) | rv) & bv_mask(width), width))
        }
        // `hi < w <= 128` keeps the shift below 128.
        ChcOp::BvExtract(hi, lo) if args.len() == 1 && hi >= lo => {
            let (v, w) = eval_bv(&args[0], model)?;
            if hi >= w {
                return None;
            }
            let width = hi - lo + 1;
            Some(SmtValue::BitVec((v >> lo) & bv_mask(width), width))
        }
        ChcOp::BvZeroExtend(n) if args.len() == 1 => {
            let (v, w) = eval_bv(&args[0], model)?;
            let width = w.checked_add(n)?;
            if !bv_width_supported(width) {
                return None;
            }
            Some(SmtValue::BitVec(v & bv_mask(w), width))
        }
        // The operators below follow the SMT-LIB 2.6 FixedSizeBitVectors theory
        // exactly, including its total definitions at the edges (division by
        // zero, shift amounts >= the width); each has a unit test at the edge.
        ChcOp::BvNand | ChcOp::BvNor | ChcOp::BvXnor if args.len() == 2 => {
            let (lv, lw) = eval_bv(&args[0], model)?;
            let (rv, rw) = eval_bv(&args[1], model)?;
            if lw != rw {
                return None;
            }
            let v = match op {
                ChcOp::BvNand => !(lv & rv),
                ChcOp::BvNor => !(lv | rv),
                _ => !(lv ^ rv),
            };
            Some(SmtValue::BitVec(v & bv_mask(lw), lw))
        }
        // `bvudiv s 0` is all ones and `bvurem s 0` is `s` (SMT-LIB definitions).
        ChcOp::BvUDiv | ChcOp::BvURem if args.len() == 2 => {
            let (lv, lw) = eval_bv(&args[0], model)?;
            let (rv, rw) = eval_bv(&args[1], model)?;
            if lw != rw || lw > 128 {
                return None;
            }
            let v = match (op, rv) {
                (ChcOp::BvUDiv, 0) => bv_mask(lw),
                (ChcOp::BvUDiv, _) => lv / rv,
                (_, 0) => lv,
                _ => lv % rv,
            };
            Some(SmtValue::BitVec(v & bv_mask(lw), lw))
        }
        // A shift by the width or more shifts every bit out: 0 for the logical
        // shifts, all copies of the sign bit for the arithmetic one.
        ChcOp::BvShl | ChcOp::BvLShr | ChcOp::BvAShr if args.len() == 2 => {
            let (lv, lw) = eval_bv(&args[0], model)?;
            let (rv, rw) = eval_bv(&args[1], model)?;
            if lw != rw || lw == 0 || lw > 128 {
                return None;
            }
            let out_of_range = rv >= u128::from(lw);
            let v = match op {
                ChcOp::BvShl if out_of_range => 0,
                ChcOp::BvShl => lv << rv,
                ChcOp::BvLShr if out_of_range => 0,
                ChcOp::BvLShr => lv >> rv,
                _ => {
                    let signed = bv_to_signed(lv, lw)?;
                    let shift = if out_of_range { 127 } else { rv as u32 };
                    (signed >> shift) as u128
                }
            };
            Some(SmtValue::BitVec(v & bv_mask(lw), lw))
        }
        ChcOp::BvSLt | ChcOp::BvSLe | ChcOp::BvSGt | ChcOp::BvSGe if args.len() == 2 => {
            let (lv, lw) = eval_bv(&args[0], model)?;
            let (rv, rw) = eval_bv(&args[1], model)?;
            if lw != rw {
                return None;
            }
            let (l, r) = (bv_to_signed(lv, lw)?, bv_to_signed(rv, rw)?);
            Some(SmtValue::Bool(match op {
                ChcOp::BvSLt => l < r,
                ChcOp::BvSLe => l <= r,
                ChcOp::BvSGt => l > r,
                _ => l >= r,
            }))
        }
        ChcOp::BvSignExtend(n) if args.len() == 1 => {
            let (v, w) = eval_bv(&args[0], model)?;
            let width = w.checked_add(n)?;
            if width > 128 {
                return None;
            }
            let extended = bv_to_signed(v, w)? as u128;
            Some(SmtValue::BitVec(extended & bv_mask(width), width))
        }
        // ay's parser keeps `concat` variadic; fold it left to right.
        ChcOp::BvConcat if args.len() > 2 => {
            let (mut acc, mut width) = eval_bv(&args[0], model)?;
            for arg in &args[1..] {
                let (v, w) = eval_bv(arg, model)?;
                width = width.checked_add(w)?;
                if width > 128 {
                    return None;
                }
                acc = ((acc << w) | v) & bv_mask(width);
            }
            Some(SmtValue::BitVec(acc, width))
        }
        ChcOp::Select if args.len() == 2 => {
            array_select(&eval_chc(&args[0], model)?, &eval_chc(&args[1], model)?)
        }
        ChcOp::Store if args.len() == 3 => array_store(
            &eval_chc(&args[0], model)?,
            eval_chc(&args[1], model)?,
            eval_chc(&args[2], model)?,
        ),
        _ => None,
    }
}

/// Structural equality of two operands under the model. Returns `None` when
/// either side cannot be concretely evaluated or their sorts differ.
fn eval_eq(a: &ChcExpr, b: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<bool> {
    values_equal(&eval_chc(a, model)?, &eval_chc(b, model)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay::chc::{ChcSort, ChcVar};
    use std::sync::Arc;

    fn bv(v: u128, w: u32) -> Arc<ChcExpr> {
        Arc::new(ChcExpr::BitVec(v, w))
    }
    fn var(name: &str) -> Arc<ChcExpr> {
        Arc::new(ChcExpr::Var(ChcVar::new(name, ChcSort::BitVec(64))))
    }
    fn op(o: ChcOp, args: Vec<Arc<ChcExpr>>) -> ChcExpr {
        ChcExpr::Op(o, args)
    }

    /// The exact shape of the `simple_ensures_pass` false positive: the low 32
    /// bits of `concat(_, #x00000000)` are 0, so asserting they are non-zero
    /// folds to `false`. The constraint set is refuted.
    #[test]
    fn refutes_bogus_concat_extract_low_bits() {
        // (not (= ((_ extract 31 0) (concat #x00000090 #x00000000)) #x00000000))
        let e = op(ChcOp::BvConcat, vec![bv(0x90, 32), bv(0, 32)]);
        let low = op(ChcOp::BvExtract(31, 0), vec![Arc::new(e)]);
        let ne = op(ChcOp::Ne, vec![Arc::new(low), bv(0, 32)]);
        assert!(constraints_are_constant_refuted(&[ne]));
    }

    /// The full `simple_ensures_pass` unsat-core shape: a variable-equality chain
    /// carries the concat value to the extract. Fixpoint propagation must fold it
    /// to a contradiction.
    #[test]
    fn refutes_concat_extract_through_equality_chain() {
        // a = concat(#x90, #x0); b = a; c = b; (not (= (extract 31 0) c) #x0)
        let a = var("a");
        let b = var("b");
        let c = var("c");
        let e = op(ChcOp::BvConcat, vec![bv(0x90, 32), bv(0, 32)]);
        let def_a = op(ChcOp::Eq, vec![a.clone(), Arc::new(e)]);
        let def_b = op(ChcOp::Eq, vec![b.clone(), a]);
        let def_c = op(ChcOp::Eq, vec![c.clone(), b]);
        let low = op(ChcOp::BvExtract(31, 0), vec![c]);
        let ne = op(ChcOp::Ne, vec![Arc::new(low), bv(0, 32)]);
        assert!(constraints_are_constant_refuted(&[def_a, def_b, def_c, ne]));
    }

    /// A genuinely-satisfiable concat/extract set is NOT refuted (the high half
    /// selected is `#x90`, matching the assertion).
    #[test]
    fn keeps_satisfiable_concat_extract() {
        let e = op(ChcOp::BvConcat, vec![bv(0x90, 32), bv(0, 32)]);
        let hi = op(ChcOp::BvExtract(63, 32), vec![Arc::new(e)]);
        let eq = op(ChcOp::Eq, vec![Arc::new(hi), bv(0x90, 32)]);
        assert!(!constraints_are_constant_refuted(&[eq]));
    }

    /// A satisfiable-but-undecidable concat/extract constraint (unbound variable)
    /// is NOT refuted — refutation requires a *provable* contradiction, so
    /// genuine counterexamples are preserved.
    #[test]
    fn keeps_undecidable_concat_extract() {
        // (not (= ((_ extract 31 0) x) #x0)) with x unconstrained — satisfiable.
        let low = op(ChcOp::BvExtract(31, 0), vec![var("x")]);
        let ne = op(ChcOp::Ne, vec![Arc::new(low), bv(0, 32)]);
        assert!(!constraints_are_constant_refuted(&[ne]));
    }

    fn eval_closed(e: ChcExpr) -> Option<SmtValue> {
        eval_under(&e, &HashMap::new())
    }

    fn bv_result(e: ChcExpr) -> (u128, u32) {
        match eval_closed(e) {
            Some(SmtValue::BitVec(v, w)) => (v, w),
            other => panic!("expected a bit-vector, got {other:?}"),
        }
    }

    fn bool_result(e: ChcExpr) -> bool {
        match eval_closed(e) {
            Some(SmtValue::Bool(b)) => b,
            other => panic!("expected a Bool, got {other:?}"),
        }
    }

    /// SMT-LIB: `bvudiv s #b0…0` is all ones, `bvurem s #b0…0` is `s`.
    #[test]
    fn unsigned_division_by_zero_follows_smtlib() {
        assert_eq!(bv_result(op(ChcOp::BvUDiv, vec![bv(7, 8), bv(0, 8)])), (0xff, 8));
        assert_eq!(bv_result(op(ChcOp::BvURem, vec![bv(7, 8), bv(0, 8)])), (7, 8));
        assert_eq!(bv_result(op(ChcOp::BvUDiv, vec![bv(7, 8), bv(2, 8)])), (3, 8));
        assert_eq!(bv_result(op(ChcOp::BvURem, vec![bv(7, 8), bv(2, 8)])), (1, 8));
    }

    #[test]
    fn shifts_by_the_width_or_more_follow_smtlib() {
        assert_eq!(bv_result(op(ChcOp::BvShl, vec![bv(0x81, 8), bv(1, 8)])), (0x02, 8));
        assert_eq!(bv_result(op(ChcOp::BvShl, vec![bv(0x81, 8), bv(8, 8)])), (0, 8));
        assert_eq!(bv_result(op(ChcOp::BvLShr, vec![bv(0x81, 8), bv(7, 8)])), (1, 8));
        assert_eq!(bv_result(op(ChcOp::BvLShr, vec![bv(0x81, 8), bv(200, 8)])), (0, 8));
        assert_eq!(bv_result(op(ChcOp::BvAShr, vec![bv(0x81, 8), bv(1, 8)])), (0xc0, 8));
        assert_eq!(bv_result(op(ChcOp::BvAShr, vec![bv(0x81, 8), bv(9, 8)])), (0xff, 8));
        assert_eq!(bv_result(op(ChcOp::BvAShr, vec![bv(0x41, 8), bv(9, 8)])), (0, 8));
        assert_eq!(
            bv_result(op(ChcOp::BvAShr, vec![bv(1u128 << 127, 128), bv(127, 128)])),
            (u128::MAX, 128)
        );
    }

    #[test]
    fn signed_comparisons_read_the_sign_bit() {
        // #x80 is -128, #x7f is 127.
        assert!(bool_result(op(ChcOp::BvSLt, vec![bv(0x80, 8), bv(0x7f, 8)])));
        assert!(!bool_result(op(ChcOp::BvSGt, vec![bv(0x80, 8), bv(0x7f, 8)])));
        assert!(bool_result(op(ChcOp::BvSLe, vec![bv(0xff, 8), bv(0xff, 8)])));
        assert!(bool_result(op(ChcOp::BvSGe, vec![bv(0, 8), bv(0xff, 8)])));
        // Width 1: #b1 is -1.
        assert!(bool_result(op(ChcOp::BvSLt, vec![bv(1, 1), bv(0, 1)])));
        // Width 128 and 127 at the extremes.
        assert!(bool_result(op(ChcOp::BvSLt, vec![bv(1u128 << 127, 128), bv(0, 128)])));
        assert!(bool_result(op(ChcOp::BvSLt, vec![bv(1u128 << 126, 127), bv(0, 127)])));
        // Mixed widths are not evaluated.
        assert_eq!(eval_closed(op(ChcOp::BvSLt, vec![bv(0, 8), bv(0, 16)])), None);
    }

    #[test]
    fn sign_extension_copies_the_sign_bit() {
        assert_eq!(bv_result(op(ChcOp::BvSignExtend(8), vec![bv(0x80, 8)])), (0xff80, 16));
        assert_eq!(bv_result(op(ChcOp::BvSignExtend(8), vec![bv(0x7f, 8)])), (0x007f, 16));
        assert_eq!(bv_result(op(ChcOp::BvSignExtend(0), vec![bv(0x80, 8)])), (0x80, 8));
        assert_eq!(eval_closed(op(ChcOp::BvSignExtend(8), vec![bv(1, 128)])), None);
    }

    #[test]
    fn negated_bitwise_operators_stay_within_the_width() {
        assert_eq!(bv_result(op(ChcOp::BvNand, vec![bv(0x0f, 8), bv(0x3c, 8)])), (0xf3, 8));
        assert_eq!(bv_result(op(ChcOp::BvNor, vec![bv(0x0f, 8), bv(0x30, 8)])), (0xc0, 8));
        assert_eq!(bv_result(op(ChcOp::BvXnor, vec![bv(0x0f, 8), bv(0x3c, 8)])), (0xcc, 8));
    }

    #[test]
    fn variadic_concat_folds_left_to_right() {
        assert_eq!(
            bv_result(op(ChcOp::BvConcat, vec![bv(0x1, 4), bv(0x2, 4), bv(0x3, 8)])),
            (0x1203, 16)
        );
        assert_eq!(eval_closed(op(ChcOp::BvConcat, vec![bv(0, 64), bv(0, 64), bv(0, 8)])), None);
    }

    fn arr_var(name: &str) -> Arc<ChcExpr> {
        Arc::new(ChcExpr::Var(ChcVar::new(
            name,
            ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(8))),
        )))
    }

    fn const_arr(v: u128) -> Arc<ChcExpr> {
        Arc::new(ChcExpr::ConstArray(ChcSort::BitVec(8), bv(v, 8)))
    }

    #[test]
    fn select_reads_the_latest_store_then_the_default() {
        let stored = Arc::new(op(ChcOp::Store, vec![const_arr(7), bv(1, 8), bv(9, 8)]));
        let restored = Arc::new(op(ChcOp::Store, vec![stored.clone(), bv(1, 8), bv(4, 8)]));
        assert_eq!(bv_result(op(ChcOp::Select, vec![stored.clone(), bv(1, 8)])), (9, 8));
        assert_eq!(bv_result(op(ChcOp::Select, vec![stored, bv(2, 8)])), (7, 8));
        assert_eq!(bv_result(op(ChcOp::Select, vec![restored, bv(1, 8)])), (4, 8));
    }

    #[test]
    fn array_equality_is_extensional() {
        let a = Arc::new(op(ChcOp::Store, vec![const_arr(0), bv(3, 8), bv(0, 8)]));
        // Storing the default over a constant array changes nothing.
        assert!(bool_result(op(ChcOp::Eq, vec![a.clone(), const_arr(0)])));
        let b = Arc::new(op(ChcOp::Store, vec![const_arr(0), bv(3, 8), bv(1, 8)]));
        assert!(!bool_result(op(ChcOp::Eq, vec![b, const_arr(0)])));
        // Different defaults over an 8-bit index: some index is not overridden.
        assert!(!bool_result(op(ChcOp::Eq, vec![const_arr(0), const_arr(1)])));
    }

    #[test]
    fn different_defaults_over_a_fully_overridden_domain_are_not_decided() {
        let bool_arr = |d: u128| Arc::new(ChcExpr::ConstArray(ChcSort::Bool, bv(d, 8)));
        let t = Arc::new(ChcExpr::Bool(true));
        let f = Arc::new(ChcExpr::Bool(false));
        let a = Arc::new(op(ChcOp::Store, vec![bool_arr(0), t.clone(), bv(5, 8)]));
        let a = Arc::new(op(ChcOp::Store, vec![a, f.clone(), bv(6, 8)]));
        let b = Arc::new(op(ChcOp::Store, vec![bool_arr(1), t, bv(5, 8)]));
        let b = Arc::new(op(ChcOp::Store, vec![b, f, bv(6, 8)]));
        // Equal at both Bool indices, so the arrays ARE equal although their
        // defaults differ; the evaluator must not answer `false`.
        assert_ne!(eval_closed(op(ChcOp::Eq, vec![a, b])), Some(SmtValue::Bool(false)));
    }

    #[test]
    fn array_variables_read_their_model_value() {
        let model = HashMap::from([(
            "a".to_string(),
            SmtValue::ArrayMap {
                default: Box::new(SmtValue::BitVec(0, 8)),
                entries: vec![(SmtValue::BitVec(2, 8), SmtValue::BitVec(5, 8))],
            },
        )]);
        let read = op(ChcOp::Select, vec![arr_var("a"), bv(2, 8)]);
        assert_eq!(eval_under(&read, &model), Some(SmtValue::BitVec(5, 8)));
        // An index listed twice with different elements is ambiguous: refused.
        let ambiguous = HashMap::from([(
            "a".to_string(),
            SmtValue::ArrayMap {
                default: Box::new(SmtValue::BitVec(0, 8)),
                entries: vec![
                    (SmtValue::BitVec(2, 8), SmtValue::BitVec(5, 8)),
                    (SmtValue::BitVec(2, 8), SmtValue::BitVec(6, 8)),
                ],
            },
        )]);
        assert_eq!(eval_under(&read, &ambiguous), None);
        // An opaque solver placeholder is never evaluated.
        let opaque = HashMap::from([("a".to_string(), SmtValue::Opaque("@arr1".into()))]);
        assert_eq!(eval_under(&read, &opaque), None);
    }

    /// ay-bindings' unsigned `u128` multiplication-overflow flag, the exact
    /// shape it prints (`BvMulNoOverflowUnsigned` at width 128):
    /// `(= ((_ extract 255 128) (bvmul ((_ zero_extend 128) a) ((_ zero_extend 128) b))) #x0…0)`.
    /// The 256-bit product is outside the fragment this evaluator computes, so
    /// the flag is `None` — never `Some(true)`, the value a product computed
    /// modulo 2^128 and a masked `v >> 128` gave for `a = b = 2^64` (whose
    /// product 2^128 DOES overflow), and never a shift-overflow panic.
    #[test]
    fn the_u128_multiplication_overflow_flag_is_not_evaluated() {
        let two_64 = 1u128 << 64;
        let widened = |v: u128| Arc::new(op(ChcOp::BvZeroExtend(128), vec![bv(v, 128)]));
        for (a, b) in [(two_64, two_64), (3, 3), (0, 0), (u128::MAX, u128::MAX)] {
            let product = Arc::new(op(ChcOp::BvMul, vec![widened(a), widened(b)]));
            let high = Arc::new(op(ChcOp::BvExtract(255, 128), vec![product]));
            let no_overflow = Arc::new(op(ChcOp::Eq, vec![high, bv(0, 128)]));
            assert_eq!(eval_closed((*no_overflow).clone()), None, "a={a:#x} b={b:#x}");
            assert_eq!(eval_closed(op(ChcOp::Not, vec![no_overflow])), None, "a={a:#x} b={b:#x}");
        }
        // The same term read from a model rather than built from literals.
        let model = HashMap::from([
            ("a".to_string(), SmtValue::BitVec(two_64, 128)),
            ("b".to_string(), SmtValue::BitVec(two_64, 128)),
        ]);
        let wide_var = |name: &str| {
            Arc::new(op(
                ChcOp::BvZeroExtend(128),
                vec![Arc::new(ChcExpr::Var(ChcVar::new(name, ChcSort::BitVec(128))))],
            ))
        };
        let product = Arc::new(op(ChcOp::BvMul, vec![wide_var("a"), wide_var("b")]));
        let high = Arc::new(op(ChcOp::BvExtract(255, 128), vec![product]));
        assert_eq!(eval_under(&op(ChcOp::Eq, vec![high, bv(0, 128)]), &model), None);
    }

    /// Every way a bit-vector outside `1..=128` bits could arise is refused:
    /// a literal, `zero_extend` past 128, arithmetic and bitwise operators on
    /// such a value, `extract` with an index at or past the operand's width,
    /// and a zero-width operand of `concat`. Widths up to 128 still evaluate.
    #[test]
    fn bit_vectors_outside_one_to_128_bits_are_not_evaluated() {
        assert_eq!(eval_closed(ChcExpr::BitVec(0, 256)), None);
        assert_eq!(eval_closed(ChcExpr::BitVec(0, 129)), None);
        assert_eq!(eval_closed(ChcExpr::BitVec(0, 0)), None);
        assert_eq!(eval_closed(op(ChcOp::BvZeroExtend(128), vec![bv(1, 128)])), None);
        assert_eq!(eval_closed(op(ChcOp::BvZeroExtend(1), vec![bv(1, 128)])), None);
        assert_eq!(eval_closed(op(ChcOp::BvZeroExtend(65), vec![bv(1, 64)])), None);
        for wide_op in [
            ChcOp::BvAdd,
            ChcOp::BvSub,
            ChcOp::BvMul,
            ChcOp::BvAnd,
            ChcOp::BvOr,
            ChcOp::BvXor,
            ChcOp::BvNand,
            ChcOp::BvNor,
            ChcOp::BvXnor,
            ChcOp::BvULt,
            ChcOp::BvSLt,
            ChcOp::BvUDiv,
            ChcOp::BvShl,
        ] {
            assert_eq!(eval_closed(op(wide_op, vec![bv(1, 256), bv(1, 256)])), None, "{wide_op:?}");
        }
        assert_eq!(eval_closed(op(ChcOp::BvNot, vec![bv(0, 129)])), None);
        assert_eq!(eval_closed(op(ChcOp::BvNeg, vec![bv(1, 200)])), None);
        assert_eq!(eval_closed(op(ChcOp::Eq, vec![bv(1, 256), bv(1, 256)])), None);
        assert_eq!(eval_closed(op(ChcOp::BvExtract(255, 128), vec![bv(1, 128)])), None);
        assert_eq!(eval_closed(op(ChcOp::BvExtract(8, 0), vec![bv(1, 8)])), None);
        assert_eq!(eval_closed(op(ChcOp::BvExtract(130, 129), vec![bv(1, 128)])), None);
        assert_eq!(eval_closed(op(ChcOp::BvConcat, vec![bv(0, 0), bv(1, 128)])), None);
        let model = HashMap::from([("w".to_string(), SmtValue::BitVec(1, 256))]);
        let w = Arc::new(ChcExpr::Var(ChcVar::new("w", ChcSort::BitVec(256))));
        assert_eq!(eval_under(&op(ChcOp::BvExtract(7, 0), vec![w]), &model), None);
        // The supported edges still evaluate exactly.
        assert_eq!(
            bv_result(op(ChcOp::BvZeroExtend(64), vec![bv(u128::from(u64::MAX), 64)])),
            (u128::from(u64::MAX), 128)
        );
        assert_eq!(bv_result(op(ChcOp::BvExtract(127, 64), vec![bv(3u128 << 64, 128)])), (3, 64));
        assert_eq!(bv_result(op(ChcOp::BvExtract(127, 127), vec![bv(1u128 << 127, 128)])), (1, 1));
        assert_eq!(
            bv_result(op(ChcOp::BvMul, vec![bv(u128::MAX, 128), bv(2, 128)])),
            (u128::MAX - 1, 128)
        );
    }

    #[test]
    fn a_variable_outside_the_assignment_is_not_evaluated() {
        assert_eq!(eval_closed(op(ChcOp::BvAdd, vec![var("nowhere"), bv(1, 64)])), None);
    }

    /// Constraints WITHOUT concat/extract are never refuted by this guard, even
    /// when unsatisfiable — the embedded solver is reliable there and the fast
    /// path is preserved.
    #[test]
    fn skips_constraints_without_concat_extract() {
        // x = 7 and x = 8 is unsat, but has no concat/extract → not our concern.
        let x = var("x");
        let e7 = op(ChcOp::Eq, vec![x.clone(), bv(7, 64)]);
        let e8 = op(ChcOp::Eq, vec![x, bv(8, 64)]);
        assert!(!constraints_are_constant_refuted(&[e7, e8]));
    }
}

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

/// Conservative evaluator: returns `Some(value)` only when the expression can be
/// concretely evaluated under `model`, and `None` for anything uncertain
/// (missing variable, uninterpreted function, unsupported operator, sort
/// mismatch). Correctness in the `Some` direction is what soundness relies on.
fn eval_chc(expr: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<SmtValue> {
    match expr {
        ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
        ChcExpr::Int(i) => Some(SmtValue::Int(*i)),
        ChcExpr::BitVec(v, w) => Some(SmtValue::BitVec(*v & bv_mask(*w), *w)),
        ChcExpr::Var(v) => match model.get(&v.name)? {
            val @ (SmtValue::Bool(_) | SmtValue::Int(_) | SmtValue::BitVec(..)) => {
                Some(val.clone())
            }
            _ => None,
        },
        ChcExpr::Op(op, args) => eval_chc_op(*op, args, model),
        _ => None,
    }
}

fn eval_bool(expr: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<bool> {
    match eval_chc(expr, model)? {
        SmtValue::Bool(b) => Some(b),
        _ => None,
    }
}

/// Evaluate a bitvector operand, returning `(value, width)`.
fn eval_bv(expr: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<(u128, u32)> {
    match eval_chc(expr, model)? {
        SmtValue::BitVec(v, w) => Some((v & bv_mask(w), w)),
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
        ChcOp::BvExtract(hi, lo) if args.len() == 1 && hi >= lo => {
            let (v, _w) = eval_bv(&args[0], model)?;
            let width = hi - lo + 1;
            Some(SmtValue::BitVec((v >> lo) & bv_mask(width), width))
        }
        ChcOp::BvZeroExtend(n) if args.len() == 1 => {
            let (v, w) = eval_bv(&args[0], model)?;
            Some(SmtValue::BitVec(v & bv_mask(w), w.checked_add(n)?))
        }
        _ => None,
    }
}

/// Structural equality of two operands under the model. Returns `None` when
/// either side cannot be concretely evaluated or their sorts differ.
fn eval_eq(a: &ChcExpr, b: &ChcExpr, model: &HashMap<String, SmtValue>) -> Option<bool> {
    match (eval_chc(a, model)?, eval_chc(b, model)?) {
        (SmtValue::Bool(x), SmtValue::Bool(y)) => Some(x == y),
        (SmtValue::Int(x), SmtValue::Int(y)) => Some(x == y),
        (SmtValue::BitVec(xv, xw), SmtValue::BitVec(yv, yw)) if xw == yw => Some(xv == yv),
        _ => None,
    }
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

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constructor-guard collection for CHC rule generation.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, SortInner};
use tracing::debug;

use crate::codegen_ay::types::CtorFieldExt;

/// Collect `((_ is Constructor) container)` guards for every DatatypeSelector
/// on a multi-constructor datatype found in `exprs`.
///
/// Z3 PDR requires these guards to treat accessor functions as interpreted
/// (Part of #3207). Without them, nested accessors like `(fld_val (value x))`
/// are treated as uninterpreted, causing UNKNOWN instead of PROOF/CTREX.
pub(in crate::codegen_ay) fn collect_constructor_guards(exprs: &[Expr]) -> Vec<Expr> {
    let mut guards = Vec::new();
    // Deduplicate by container pointer identity + constructor name to avoid
    // emitting redundant guards when the same variable is accessed multiple
    // times in one block. We use the raw pointer of the container's ExprValue
    // Arc as a cheap identity key.
    let mut seen: HashSet<(usize, String)> = HashSet::new();
    for expr in exprs {
        collect_guards_recursive(expr, &mut guards, &mut seen);
    }
    if !guards.is_empty() {
        debug!(
            "constructor_guard: emitted {} guard(s) from {} constraints",
            guards.len(),
            exprs.len()
        );
    }
    guards
}

/// Recursively walk an expression tree, collecting constructor tester guards
/// for every DatatypeSelector node whose container is a multi-constructor datatype.
fn collect_guards_recursive(
    expr: &Expr,
    guards: &mut Vec<Expr>,
    seen: &mut HashSet<(usize, String)>,
) {
    match expr.value() {
        ExprValue::DatatypeSelector { datatype_name, selector_name, expr: container } => {
            // Check if the container is a multi-constructor datatype.
            if let SortInner::Datatype(dt) = container.sort().inner() {
                if dt.constructors.len() > 1 {
                    // Find which constructor owns this selector.
                    if let Some(cons) = dt.constructors.iter().find(|c| c.has_field(selector_name))
                    {
                        // Skip guard when container is a known DT constant (#3896).
                        // If the container is a DatatypeConstructor, the variant is
                        // statically known. Emitting a guard for a mismatched
                        // constructor (e.g., `((_ is Some) None)`) makes the rule
                        // body vacuously false, producing a false PROOF. When the
                        // constructor matches, the guard is trivially true and adds
                        // no information. Either way, skip.
                        let container_is_known_constant =
                            matches!(container.value(), ExprValue::DatatypeConstructor { .. });
                        if !container_is_known_constant {
                            let guard =
                                literal_constructor_guard(container, datatype_name, &cons.name)
                                    .unwrap_or_else(|| {
                                        container.clone().is_constructor(
                                            datatype_name.clone(),
                                            cons.name.clone(),
                                        )
                                    });
                            // Skip guards that are semantically constant. A
                            // constant-TRUE guard adds no information; a
                            // constant-FALSE guard (e.g. `((_ is B_Foo) …)` on a
                            // value statically known to be `A_Foo`) would inject
                            // a vacuously-false constraint into the rule body,
                            // making a genuinely-reachable block/assertion
                            // unreachable → false PROOF. `simplify_bool_ite` can
                            // yield `not(not(false))`, which is a `Not` node, not
                            // a bare `BoolConst`, so peel nested negations before
                            // deciding. Part of the multi-variant-flattened enum
                            // downcast-guard fix.
                            if peel_bool_const(&guard).is_some() {
                                collect_guards_recursive(container, guards, seen);
                                return;
                            }
                            // Dedup by container identity (pointer) + constructor name.
                            // This correctly handles multiple variables of the same type
                            // (different containers get different guards) while avoiding
                            // duplicates for the same container accessed via different
                            // fields.
                            let container_ptr = std::ptr::from_ref(container.value()) as usize;
                            let key = (container_ptr, cons.name.clone());
                            if seen.insert(key) {
                                debug!(
                                    "constructor_guard: adding ((_ is {}) ...) for selector {} on {}",
                                    cons.name, selector_name, datatype_name
                                );
                                guards.push(guard);
                            }
                        }
                    }
                }
            }
            // Recurse into the container expression (may have nested selectors).
            collect_guards_recursive(container, guards, seen);
        }
        // For all other variants, recurse into sub-expressions.
        ExprValue::Not(e)
        | ExprValue::BvNeg(e)
        | ExprValue::BvNot(e)
        | ExprValue::IntNeg(e)
        | ExprValue::IntToReal(e)
        | ExprValue::RealToInt(e)
        | ExprValue::IsInt(e)
        | ExprValue::RealNeg(e)
        | ExprValue::BvNegNoOverflow(e)
        | ExprValue::BvZeroExtend { expr: e, .. }
        | ExprValue::BvSignExtend { expr: e, .. }
        | ExprValue::BvExtract { expr: e, .. }
        | ExprValue::ConstArray { value: e, .. } => {
            collect_guards_recursive(e, guards, seen);
        }
        ExprValue::And(es) | ExprValue::Or(es) | ExprValue::Distinct(es) => {
            for e in es {
                collect_guards_recursive(e, guards, seen);
            }
        }
        ExprValue::Eq(a, b)
        | ExprValue::Xor(a, b)
        | ExprValue::Implies(a, b)
        | ExprValue::BvAdd(a, b)
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
        | ExprValue::BvULt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::BvConcat(a, b)
        | ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvAddNoOverflowSigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b)
        | ExprValue::BvSubNoOverflowSigned(a, b)
        | ExprValue::BvMulNoOverflowUnsigned(a, b)
        | ExprValue::BvMulNoOverflowSigned(a, b)
        | ExprValue::BvSdivNoOverflow(a, b)
        | ExprValue::IntAdd(a, b)
        | ExprValue::IntSub(a, b)
        | ExprValue::IntMul(a, b)
        | ExprValue::IntDiv(a, b)
        | ExprValue::IntMod(a, b)
        | ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b)
        | ExprValue::RealAdd(a, b)
        | ExprValue::RealSub(a, b)
        | ExprValue::RealMul(a, b)
        | ExprValue::RealDiv(a, b)
        | ExprValue::RealLt(a, b)
        | ExprValue::RealLe(a, b)
        | ExprValue::RealGt(a, b)
        | ExprValue::RealGe(a, b) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            collect_guards_recursive(cond, guards, seen);
            // Part of #3886: When the ITE condition is a DatatypeTester
            // `((_ is C) container)`, the then-branch is already guarded
            // by the tester — selectors inside it are only evaluated when
            // the tester holds. Emitting standalone top-level guards for
            // those selectors is redundant at best, and produces vacuously
            // false constraints when the tester evaluates to false at
            // runtime. Example: `(ite ((_ is Some) (fld_data x)) (value
            // (fld_data x)) #x0...)` — the `value` selector is safe
            // inside the then-branch, but a standalone guard `((_ is Some)
            // (fld_data x))` injected into the rule body kills the rule
            // when x.data is None, causing false PROOF.
            if !matches!(cond.value(), ExprValue::DatatypeTester { .. }) {
                collect_guards_recursive(then_expr, guards, seen);
            }
            collect_guards_recursive(else_expr, guards, seen);
        }
        ExprValue::Select { array, index } => {
            collect_guards_recursive(array, guards, seen);
            collect_guards_recursive(index, guards, seen);
        }
        ExprValue::Store { array, index, value } => {
            collect_guards_recursive(array, guards, seen);
            collect_guards_recursive(index, guards, seen);
            collect_guards_recursive(value, guards, seen);
        }
        ExprValue::DatatypeConstructor { args, .. } => {
            for arg in args {
                collect_guards_recursive(arg, guards, seen);
            }
        }
        ExprValue::DatatypeTester { expr: e, .. } => {
            collect_guards_recursive(e, guards, seen);
        }
        ExprValue::FuncApp { args, .. } => {
            for arg in args {
                collect_guards_recursive(arg, guards, seen);
            }
        }
        ExprValue::Forall { body, .. } | ExprValue::Exists { body, .. } => {
            collect_guards_recursive(body, guards, seen);
        }
        // Leaf nodes: no sub-expressions to recurse into.
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_)
        | ExprValue::Var { .. } => {}
        // Sort conversions: recurse into sub-expression (soundness-critical).
        // Bv2Int/Int2Bv wrap DatatypeSelector in production CHC encoding.
        ExprValue::Bv2Int(e) | ExprValue::Int2Bv(e, _) => {
            collect_guards_recursive(e, guards, seen);
        }
        // FP unary operations: recurse into sub-expression.
        ExprValue::FpAbs(e)
        | ExprValue::FpNeg(e)
        | ExprValue::FpIsNaN(e)
        | ExprValue::FpIsInfinite(e)
        | ExprValue::FpIsZero(e)
        | ExprValue::FpIsNormal(e)
        | ExprValue::FpIsSubnormal(e)
        | ExprValue::FpIsPositive(e)
        | ExprValue::FpIsNegative(e)
        | ExprValue::FpToReal(e) => {
            collect_guards_recursive(e, guards, seen);
        }
        // FP operations with RoundingMode + single expression.
        ExprValue::FpSqrt(_, e)
        | ExprValue::FpRoundToIntegral(_, e)
        | ExprValue::FpToSbv(_, e, _)
        | ExprValue::FpToUbv(_, e, _)
        | ExprValue::BvToFp(_, e, _, _)
        | ExprValue::BvToFpUnsigned(_, e, _, _)
        | ExprValue::FpToFp(_, e, _, _) => {
            collect_guards_recursive(e, guards, seen);
        }
        // FP binary operations (plain two-expr).
        ExprValue::FpRem(a, b)
        | ExprValue::FpMin(a, b)
        | ExprValue::FpMax(a, b)
        | ExprValue::FpEq(a, b)
        | ExprValue::FpLt(a, b)
        | ExprValue::FpLe(a, b)
        | ExprValue::FpGt(a, b)
        | ExprValue::FpGe(a, b) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
        }
        // FP binary operations with RoundingMode.
        ExprValue::FpAdd(_, a, b)
        | ExprValue::FpSub(_, a, b)
        | ExprValue::FpMul(_, a, b)
        | ExprValue::FpDiv(_, a, b) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
        }
        // FP ternary operations.
        ExprValue::FpFromBvs(a, b, c) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
            collect_guards_recursive(c, guards, seen);
        }
        ExprValue::FpFma(_, a, b, c) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
            collect_guards_recursive(c, guards, seen);
        }
        // FP leaf constants: no sub-expressions.
        ExprValue::FpPlusInfinity { .. }
        | ExprValue::FpMinusInfinity { .. }
        | ExprValue::FpNaN { .. }
        | ExprValue::FpPlusZero { .. }
        | ExprValue::FpMinusZero { .. } => {}
        // String unary operations.
        ExprValue::StrLen(e)
        | ExprValue::StrToInt(e)
        | ExprValue::StrFromInt(e)
        | ExprValue::StrToRe(e) => {
            collect_guards_recursive(e, guards, seen);
        }
        // String binary operations.
        ExprValue::StrConcat(a, b)
        | ExprValue::StrAt(a, b)
        | ExprValue::StrContains(a, b)
        | ExprValue::StrPrefixOf(a, b)
        | ExprValue::StrSuffixOf(a, b)
        | ExprValue::StrInRe(a, b) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
        }
        // String ternary operations.
        ExprValue::StrSubstr(a, b, c)
        | ExprValue::StrIndexOf(a, b, c)
        | ExprValue::StrReplace(a, b, c)
        | ExprValue::StrReplaceAll(a, b, c) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
            collect_guards_recursive(c, guards, seen);
        }
        // Regex operations.
        ExprValue::ReStar(e) | ExprValue::RePlus(e) => {
            collect_guards_recursive(e, guards, seen);
        }
        ExprValue::ReUnion(a, b) | ExprValue::ReConcat(a, b) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
        }
        // Sequence leaf: no sub-expressions.
        ExprValue::SeqEmpty(_) => {}
        // Sequence unary operations.
        ExprValue::SeqUnit(e) | ExprValue::SeqLen(e) => {
            collect_guards_recursive(e, guards, seen);
        }
        // Sequence binary operations.
        ExprValue::SeqConcat(a, b)
        | ExprValue::SeqNth(a, b)
        | ExprValue::SeqContains(a, b)
        | ExprValue::SeqPrefixOf(a, b)
        | ExprValue::SeqSuffixOf(a, b) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
        }
        // Sequence ternary operations.
        ExprValue::SeqExtract(a, b, c)
        | ExprValue::SeqIndexOf(a, b, c)
        | ExprValue::SeqReplace(a, b, c) => {
            collect_guards_recursive(a, guards, seen);
            collect_guards_recursive(b, guards, seen);
            collect_guards_recursive(c, guards, seen);
        }
        // Catch-all for future ExprValue variants (#[non_exhaustive]).
        // All 146 known variants are handled explicitly above.
        // If AY adds new variants with Expr fields, this will silently skip them.
        // Prefer adding explicit arms above when new variants are observed.
        _ => {
            debug!("constructor_guard: unhandled ExprValue variant in guard collection");
        }
    }
}

/// Fold a guard expression to a boolean constant when it is semantically
/// constant, peeling nested `Not` negations. `simplify_bool_ite` can emit
/// `not(not(false))` (a `Not` node wrapping a `BoolConst`) for a statically
/// decided constructor test; a bare `matches!(_, BoolConst(_))` check misses it.
fn peel_bool_const(expr: &Expr) -> Option<bool> {
    match expr.value() {
        ExprValue::BoolConst(b) => Some(*b),
        ExprValue::Not(inner) => peel_bool_const(inner).map(|b| !b),
        _ => None,
    }
}

fn literal_constructor_guard(container: &Expr, dt_name: &str, cons_name: &str) -> Option<Expr> {
    // Avoid `((_ is C) (ite cond (A ...) (B ...)))` guards; PDR struggles
    // with the datatype tester, while the equivalent scalar condition is direct.
    match container.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_guard = literal_constructor_branch_guard(then_expr, dt_name, cons_name)?;
            let else_guard = literal_constructor_branch_guard(else_expr, dt_name, cons_name)?;
            Some(simplify_bool_ite(cond.clone(), then_guard, else_guard))
        }
        _ => None,
    }
}

fn literal_constructor_branch_guard(expr: &Expr, dt_name: &str, cons_name: &str) -> Option<Expr> {
    match expr.value() {
        ExprValue::DatatypeConstructor { datatype_name, constructor_name, .. } => {
            (datatype_name == dt_name).then(|| Expr::bool_const(constructor_name == cons_name))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_guard = literal_constructor_branch_guard(then_expr, dt_name, cons_name)?;
            let else_guard = literal_constructor_branch_guard(else_expr, dt_name, cons_name)?;
            Some(simplify_bool_ite(cond.clone(), then_guard, else_guard))
        }
        _ => None,
    }
}

fn simplify_bool_ite(cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr {
    match (bool_const_value(&then_expr), bool_const_value(&else_expr)) {
        (Some(true), Some(false)) => cond,
        (Some(false), Some(true)) => cond.not(),
        (Some(true), Some(true)) => Expr::bool_const(true),
        (Some(false), Some(false)) => Expr::bool_const(false),
        _ => Expr::ite(cond, then_expr, else_expr),
    }
}

fn bool_const_value(expr: &Expr) -> Option<bool> {
    match expr.value() {
        ExprValue::BoolConst(value) => Some(*value),
        _ => None,
    }
}

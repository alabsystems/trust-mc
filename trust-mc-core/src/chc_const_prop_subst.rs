// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Expression-level variable substitution for CHC constant propagation.
//!
//! Recursively replaces `Var(name)` references with constant values in
//! expression trees. Also performs targeted constant folding for `Eq` and `Not`.
//!
//! ## Soundness
//!
//! Known compound variants are handled generically via `children()` +
//! `rebuild_with_children()` — new `ExprValue` variants are automatically
//! traversed. The catch-all `_ => expr.clone()` only fires for unknown
//! `#[non_exhaustive]` variants, where variables are left un-substituted
//! (sound: explicit equality constraints still bind them).
//!
//! Special-case constant folding is preserved for: Not, BvExtract, BV binary
//! ops, Eq, And/Or (short-circuit), ITE, Select/Store, DT selector
//! (beta-reduction), and quantifiers (scope filtering).

use std::collections::HashMap;

use ay_bindings::{Expr, ExprValue, SortInner, rebuild_with_children};
use num_bigint::BigInt;

use super::eval::{eval_bv_binary_const, eval_select_store_const};
use super::is_scalar_constant;

/// Substitutes known-constant variables in an expression tree.
///
/// Also performs targeted constant folding:
/// - `(= const1 const2)` → `true`/`false`
/// - `(not true)` → `false`, `(not false)` → `true`
///
/// Returns the original expression (cloned) if no substitutions apply.
pub(super) fn substitute_vars(expr: &Expr, known: &HashMap<String, Expr>) -> Expr {
    if known.is_empty() {
        return expr.clone();
    }
    substitute_vars_inner(expr, known)
}

/// Handles leaves and unary operations; delegates compound operations.
fn substitute_vars_inner(expr: &Expr, known: &HashMap<String, Expr>) -> Expr {
    match expr.value() {
        // Leaf: variable — substitute if known.
        ExprValue::Var { name } => known.get(name).cloned().unwrap_or_else(|| expr.clone()),

        // Leaf: constants — no substitution.
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_) => expr.clone(),

        // Unary boolean (with constant folding).
        ExprValue::Not(e) => {
            let inner = substitute_vars_inner(e, known);
            match inner.value() {
                ExprValue::BoolConst(b) => Expr::bool_const(!b),
                _ => match super::eval::try_eval_to_bool(&inner) {
                    Some(b) => Expr::bool_const(!b),
                    None => inner.not(),
                },
            }
        }

        // Unary BV/Int/Real operations.
        ExprValue::BvNeg(e) => substitute_vars_inner(e, known).bvneg(),
        ExprValue::BvNot(e) => substitute_vars_inner(e, known).bvnot(),
        ExprValue::IntNeg(e) => substitute_vars_inner(e, known).int_neg(),
        ExprValue::RealNeg(e) => substitute_vars_inner(e, known).real_neg(),
        ExprValue::BvNegNoOverflow(e) => substitute_vars_inner(e, known).bvneg_no_overflow(),
        ExprValue::IntToReal(e) => substitute_vars_inner(e, known).int_to_real(),
        ExprValue::RealToInt(e) => substitute_vars_inner(e, known).real_to_int(),
        ExprValue::IsInt(e) => substitute_vars_inner(e, known).is_int(),
        ExprValue::Bv2Int(e) => substitute_vars_inner(e, known).bv2int(),

        // Unary with extra fields.
        ExprValue::Int2Bv(e, width) => substitute_vars_inner(e, known).int2bv(*width),
        ExprValue::BvZeroExtend { expr: e, extra_bits } => {
            substitute_vars_inner(e, known).zero_extend(*extra_bits)
        }
        ExprValue::BvSignExtend { expr: e, extra_bits } => {
            substitute_vars_inner(e, known).sign_extend(*extra_bits)
        }
        ExprValue::BvExtract { expr: e, high, low } => {
            let inner = substitute_vars_inner(e, known);
            if let ExprValue::BitVecConst { value, .. } = inner.value() {
                if inner.sort().bitvec_width().is_some_and(|width| *low <= *high && *high < width) {
                    let result_width = high - low + 1;
                    let mask = (BigInt::from(1u8) << (result_width as usize)) - 1;
                    let extracted = (value >> (*low as usize)) & mask;
                    return Expr::bitvec_const(extracted, result_width);
                }
                return expr.clone();
            }
            // Part of #4187: const-prop can substitute a BV input with an
            // incompatible sort (for example Array<BV64, Bool> from a memory
            // equality) or a narrower BV. Rebuilding extract on that term
            // panics in ay-bindings; keep the original, well-typed expression
            // instead of emitting malformed SMT.
            if !inner.sort().is_bitvec()
                || inner.sort().bitvec_width().is_none_or(|width| *low > *high || *high >= width)
            {
                return expr.clone();
            }
            inner.extract(*high, *low)
        }
        ExprValue::ConstArray { index_sort, value } => {
            Expr::const_array(index_sort.clone(), substitute_vars_inner(value, known))
        }

        // Binary and compound operations.
        _ => substitute_vars_compound(expr, known),
    }
}

/// Handles BV binary operations with constant folding.
///
/// Returns `Some(result)` if the expression is a BV binary op. Substitutes
/// children, tries `eval_bv_binary_const` for constant folding, then uses
/// `rebuild_with_children` for reconstruction. Part of #3415.
fn substitute_vars_bv_binary(expr: &Expr, known: &HashMap<String, Expr>) -> Option<Expr> {
    let (a, b) = match expr.value() {
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
        | ExprValue::BvSdivNoOverflow(a, b) => (a, b),
        _ => return None,
    };

    let new_a = substitute_vars_inner(a, known);
    let new_b = substitute_vars_inner(b, known);

    // Evaluate BV operations on constant arguments.
    if let Some(folded) = eval_bv_binary_const(expr.value(), &new_a, &new_b) {
        return Some(folded);
    }

    Some(rebuild_with_children(expr, vec![new_a, new_b]))
}

/// Handles Eq, n-ary, and structured operations. Delegates Int/Real/logic
/// binary and DT/quantifier operations to separate functions.
fn substitute_vars_compound(expr: &Expr, known: &HashMap<String, Expr>) -> Expr {
    if let Some(result) = substitute_vars_bv_binary(expr, known) {
        return result;
    }

    match expr.value() {
        ExprValue::Eq(a, b) => {
            let new_a = substitute_vars_inner(a, known);
            let new_b = substitute_vars_inner(b, known);
            if is_scalar_constant(&new_a) && is_scalar_constant(&new_b) {
                // Scalar constants: structural PartialEq is complete (both directions).
                Expr::bool_const(new_a == new_b)
            } else if new_a == new_b {
                // Non-scalar structural identity: identical AST ⇒ identical semantics.
                // Only fold to true — structural inequality doesn't imply semantic
                // inequality for Store/ConstArray (different store orderings can be
                // semantically equivalent), so we never fold to false here.
                Expr::bool_const(true)
            } else {
                new_a.eq(new_b)
            }
        }
        ExprValue::And(exprs) => fold_and(exprs, known),
        ExprValue::Or(exprs) => fold_or(exprs, known),
        ExprValue::Distinct(exprs) => {
            Expr::distinct(exprs.iter().map(|e| substitute_vars_inner(e, known)).collect())
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let new_cond = substitute_vars_inner(cond, known);
            let new_then = substitute_vars_inner(then_expr, known);
            let new_else = substitute_vars_inner(else_expr, known);
            match new_cond.value() {
                ExprValue::BoolConst(true) => new_then,
                ExprValue::BoolConst(false) => new_else,
                _ if new_then == new_else => new_then,
                // Try evaluating BV comparisons/expressions to bool.
                _ => match super::eval::try_eval_to_bool(&new_cond) {
                    Some(true) => new_then,
                    Some(false) => new_else,
                    None => Expr::ite(new_cond, new_then, new_else),
                },
            }
        }
        ExprValue::Select { array, index } => fold_select(array, index, known),
        ExprValue::Store { array, index, value } => fold_store(array, index, value, known),
        // DT, quantifier, function — keep special-case handling.
        _ => substitute_vars_dt_quant(expr, known),
    }
}

/// And with constant folding: short-circuits on `false`, filters `true`.
fn fold_and(exprs: &[Expr], known: &HashMap<String, Expr>) -> Expr {
    let mut filtered = Vec::new();
    for e in exprs {
        let sub = substitute_vars_inner(e, known);
        match sub.value() {
            ExprValue::BoolConst(false) => return Expr::bool_const(false),
            ExprValue::BoolConst(true) => continue,
            _ => match super::eval::try_eval_to_bool(&sub) {
                Some(false) => return Expr::bool_const(false),
                Some(true) => continue,
                None => filtered.push(sub),
            },
        }
    }
    if filtered.is_empty() {
        return Expr::bool_const(true);
    }
    if filtered.len() == 1 {
        return filtered.into_iter().next().expect("invariant: len==1");
    }
    Expr::and_many(filtered)
}

/// Or with constant folding: short-circuits on `true`, filters `false`.
fn fold_or(exprs: &[Expr], known: &HashMap<String, Expr>) -> Expr {
    let mut filtered = Vec::new();
    for e in exprs {
        let sub = substitute_vars_inner(e, known);
        match sub.value() {
            ExprValue::BoolConst(true) => return Expr::bool_const(true),
            ExprValue::BoolConst(false) => continue,
            _ => match super::eval::try_eval_to_bool(&sub) {
                Some(true) => return Expr::bool_const(true),
                Some(false) => continue,
                None => filtered.push(sub),
            },
        }
    }
    if filtered.is_empty() {
        return Expr::bool_const(false);
    }
    if filtered.len() == 1 {
        return filtered.into_iter().next().expect("invariant: len==1");
    }
    Expr::or_many(filtered)
}

/// Select with const_array and store folding.
fn fold_select(array: &Expr, index: &Expr, known: &HashMap<String, Expr>) -> Expr {
    let new_array = substitute_vars_inner(array, known);
    let new_index = substitute_vars_inner(index, known);
    // Part of #4187: const-prop can substitute either side of select(...) with
    // a different array/index sort. Rebuilding select on those children panics
    // in ay-bindings; keep the original, well-typed select instead.
    if new_array.sort() != array.sort() || new_index.sort() != index.sort() {
        return array.clone().select(index.clone());
    }
    if let ExprValue::ConstArray { value, .. } = new_array.value() {
        return value.clone();
    }
    if let Some(result) = eval_select_store_const(&new_array, &new_index) {
        return result;
    }
    new_array.select(new_index)
}

/// Store with const_array identity folding.
///
/// Sort guard: if const-prop substitutes the value with a different sort
/// (e.g., DT variable replaced by BV constant from a cross-sort equality),
/// fall back to the original expression to avoid a sort mismatch panic in
/// `Expr::store`. Mirrors the sort guard in `fold_dt_constructor`. Part of #3991.
fn fold_store(array: &Expr, index: &Expr, value: &Expr, known: &HashMap<String, Expr>) -> Expr {
    let new_array = substitute_vars_inner(array, known);
    let new_index = substitute_vars_inner(index, known);
    let new_value = substitute_vars_inner(value, known);
    // store(const_array(v), _, v) → const_array(v) — storing same value is a no-op.
    if let ExprValue::ConstArray { value: arr_val, .. } = new_array.value() {
        if *arr_val == new_value {
            return new_array;
        }
    }
    // store(a, i, select(a, i)) → a — writing a cell to its current value is a no-op.
    if let ExprValue::Select { array: selected_array, index: selected_index } = new_value.value() {
        if *selected_array == new_array && *selected_index == new_index {
            return new_array;
        }
    }
    // Sort guard: the array element sort must match the value sort.
    // Const-prop can replace enum/struct-typed variables with their BV
    // encodings, producing a sort mismatch that would panic in Expr::store.
    if let Some(arr_sort) = new_array.sort().array_sort() {
        if arr_sort.element_sort != *new_value.sort() {
            return new_array.store(new_index, value.clone());
        }
    }
    // store(store(a, i, old), i, new) → store(a, i, new). The later write
    // completely overwrites the inner write at the same structural index.
    if let ExprValue::Store { array: inner_array, index: inner_index, .. } = new_array.value() {
        if *inner_index == new_index {
            return inner_array.clone().store(new_index, new_value);
        }
    }
    new_array.store(new_index, new_value)
}

/// Fold a DatatypeConstructor after substitution, but only keep substituted
/// args whose sorts still match the constructor field sorts.
///
/// Const-prop can replace enum-typed fields with their BV encodings. Rebuilding
/// the constructor with those BV terms produces malformed SMT like
/// `(Wrapper_mk (_ BitVec 10))` when the field expects a datatype. Fall back to
/// the original field expression for mismatched positions so the constructor
/// stays well-typed while still preserving any safe substitutions in sibling
/// fields. Part of #3768.
fn fold_dt_constructor(
    expr: &Expr,
    datatype_name: &str,
    constructor_name: &str,
    args: &[Expr],
    known: &HashMap<String, Expr>,
) -> Expr {
    let new_args: Vec<Expr> = args.iter().map(|arg| substitute_vars_inner(arg, known)).collect();
    let SortInner::Datatype(dt) = expr.sort().inner() else {
        return expr.clone();
    };
    let Some(ctor) = dt.constructors.iter().find(|ctor| ctor.name == *constructor_name) else {
        return expr.clone();
    };
    if ctor.fields.len() != args.len() {
        return expr.clone();
    }

    let adjusted_args: Vec<Expr> = args
        .iter()
        .zip(new_args)
        .zip(&ctor.fields)
        .map(
            |((original_arg, new_arg), field)| {
                if *new_arg.sort() == field.sort { new_arg } else { original_arg.clone() }
            },
        )
        .collect();

    if adjusted_args == args {
        return expr.clone();
    }

    Expr::datatype_constructor(
        datatype_name.to_owned(),
        constructor_name.to_owned(),
        adjusted_args,
        expr.sort().clone(),
    )
}

/// Fold a DatatypeSelector after substitution: beta-reduce if the inner is a
/// matching DatatypeConstructor, otherwise fall back to `try_field_select`
/// (which tolerates sort mismatches from BV-encoded enums). Part of #3348, #3768.
fn fold_dt_selector(expr: &Expr, datatype_name: &str, selector_name: &str, inner: &Expr) -> Expr {
    // Beta-reduction: sel_i(C(a_0, ..., a_n)) → a_i
    if let ExprValue::DatatypeConstructor { constructor_name: ctor_name, args, .. } = inner.value()
    {
        if let SortInner::Datatype(dt) = inner.sort().inner() {
            if let Some(ctor) = dt.constructors.iter().find(|c| c.name == *ctor_name) {
                if let Some(idx) = ctor.fields.iter().position(|f| f.name == *selector_name) {
                    if let Some(arg) = args.get(idx) {
                        return arg.clone();
                    }
                }
            }
        }
    }
    match inner.clone().try_field_select(
        datatype_name.to_owned(),
        selector_name.to_owned(),
        expr.sort().clone(),
    ) {
        Ok(sel) => sel,
        Err(_) => expr.clone(),
    }
}

/// Handles datatype, function application, and quantifier operations.
fn substitute_vars_dt_quant(expr: &Expr, known: &HashMap<String, Expr>) -> Expr {
    match expr.value() {
        ExprValue::DatatypeConstructor { datatype_name, constructor_name, args } => {
            fold_dt_constructor(expr, datatype_name, constructor_name, args, known)
        }
        ExprValue::DatatypeSelector { datatype_name, selector_name, expr: e } => {
            let inner = substitute_vars_inner(e, known);
            fold_dt_selector(expr, datatype_name, selector_name, &inner)
        }
        ExprValue::DatatypeTester { datatype_name, constructor_name, expr: e } => {
            let inner = substitute_vars_inner(e, known);
            // After substitution, the inner may no longer be a Datatype sort
            // (e.g., BV-encoded enum replaced by a constant). Part of #3768.
            match inner.try_is_constructor(datatype_name.clone(), constructor_name.clone()) {
                Ok(tester) => tester,
                Err(_) => expr.clone(),
            }
        }
        ExprValue::FuncApp { name, args } => {
            let new_args: Vec<Expr> =
                args.iter().map(|e| substitute_vars_inner(e, known)).collect();
            Expr::func_app_with_sort(name.clone(), new_args, expr.sort().clone())
        }
        ExprValue::Forall { vars, body, triggers } => {
            let filtered = filter_bound_vars(known, vars);
            let new_body = substitute_vars_inner(body, &filtered);
            let new_triggers: Vec<Vec<Expr>> = triggers
                .iter()
                .map(|group| group.iter().map(|e| substitute_vars_inner(e, &filtered)).collect())
                .collect();
            Expr::forall_with_triggers(vars.clone(), new_body, new_triggers)
        }
        ExprValue::Exists { vars, body, triggers } => {
            let filtered = filter_bound_vars(known, vars);
            let new_body = substitute_vars_inner(body, &filtered);
            let new_triggers: Vec<Vec<Expr>> = triggers
                .iter()
                .map(|group| group.iter().map(|e| substitute_vars_inner(e, &filtered)).collect())
                .collect();
            Expr::exists_with_triggers(vars.clone(), new_body, new_triggers)
        }

        // All other known variants: generic recurse + reconstruct via
        // children() + rebuild_with_children(). Covers Int/Real/FP/string/etc.
        // New ExprValue variants are automatically handled. Part of #3415.
        _ if expr.value().is_known_variant() => {
            let new_children: Vec<Expr> =
                expr.value().children().map(|c| substitute_vars_inner(c, known)).collect();
            rebuild_with_children(expr, new_children)
        }
        // Unknown variants: return unchanged (sound — equality constraints
        // still bind the variable, just reduces optimization effectiveness).
        _ => expr.clone(),
    }
}

/// Removes bound variable names from the substitution map to avoid
/// capturing quantifier-bound variables.
fn filter_bound_vars(
    known: &HashMap<String, Expr>,
    vars: &[(String, ay_bindings::Sort)],
) -> HashMap<String, Expr> {
    let mut filtered = known.clone();
    for (var_name, _) in vars {
        filtered.remove(var_name);
    }
    filtered
}

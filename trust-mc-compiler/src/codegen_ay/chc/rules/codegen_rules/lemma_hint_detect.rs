// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC loop modification detection for lemma hint injection.
//!
//! Scans emitted CHC rules for state variable accumulation patterns,
//! handling MIR checked-arithmetic indirection through temporaries.
//!
//! Extracted from lemma_hint.rs for file-size compliance.
//! Part of #3258.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};
use tracing::debug;

use super::lemma_hint::{IncrSource, LoopModification};
use trust_mc_core::chc::Rule;

/// An intermediate arithmetic operation found in constraints.
/// `tmp_fld0__out = A + B` where A may be a state var and B another.
/// Part of #2267: Arc<str> fields (O(1) clone) instead of String (O(n) clone).
#[derive(Debug)]
struct ArithOp {
    /// The output variable name (e.g., `_fn_9_fld0`)
    out_var_base: Arc<str>,
    /// The input variable name (base of the add/sub, e.g., the state var being accumulated)
    input_var: Arc<str>,
    /// The source being added/subtracted
    source: IncrSource,
    /// Whether this is add or sub
    is_sub: bool,
}

/// Result of analyzing one side of an equality constraint.
/// Part of #2267: Arc<str> variants (O(1) clone) instead of String (O(n) clone).
enum EqResult {
    /// Simple alias: `X__out = Y` where both sides are variables
    Alias { base_name: Arc<str>, source: Arc<str> },
    /// Arithmetic: `T__out = A +/- B`
    Arith(ArithOp),
    /// Direct modification: `X__out = X + Y` (no indirection)
    Direct(Arc<str>, LoopModification),
}

/// Result of scanning rules for state variable modification patterns.
/// Part of #2267: Arc<str> keys throughout (O(1) clone, eliminates
/// the String→Arc<str> conversion that was in detect_all_modifications).
pub(super) struct ModificationResult {
    /// Variables with detected accumulator patterns (sum += i, i += 1, etc.)
    pub modifications: HashMap<Arc<str>, LoopModification>,
    /// For each variable, the set of other variables it is compared against
    /// (via Lt, Le, Gt, Ge) in any rule constraint. Used to identify loop
    /// bound variables for `counter <= bound` hints: only variables that the
    /// counter is compared against in the loop guard get bound hints.
    pub comparison_targets: HashMap<Arc<str>, HashSet<Arc<str>>>,
}

/// Scan all rules in the VC for state variable accumulation patterns.
///
/// Handles MIR checked-arithmetic indirection:
/// 1. Collect all `X__out = Y` aliases (simple variable assignments)
/// 2. Collect all `T__out = A +/- B` arithmetic operations
/// 3. Resolve: if `X__out = T_fld0` and `T_fld0__out = X + Y`, then X += Y
///
/// Also collects `comparison_targets`: for each variable, the set of other
/// variables it is compared against (Lt, Le, Gt, Ge) in any constraint.
/// This identifies loop guard comparisons (e.g., `counter < bound`) so that
/// bound hints are emitted only for the actual loop bound variable.
///
/// Uses the `__out` suffix convention to match input/output state var pairs.
///
/// Note: A single variable may have multiple aliases from different rules
/// (e.g., `_4__out = _1` from initialization and `_4__out = _9_fld0` from
/// the loop body). All aliases are collected so that indirect resolution
/// can match through any of them.
///
/// Part of #2267: Arc<str> used throughout (O(1) clone). Eliminates the
/// String→Arc<str> conversion that was previously done at the end.
pub(super) fn detect_all_modifications(rules: &[Rule]) -> ModificationResult {
    let mut aliases: HashMap<Arc<str>, Vec<Arc<str>>> = HashMap::new();
    let mut arith_ops: Vec<ArithOp> = Vec::new();
    let mut modifications: HashMap<Arc<str>, LoopModification> = HashMap::new();
    let mut comparison_targets: HashMap<Arc<str>, HashSet<Arc<str>>> = HashMap::new();

    for rule in rules {
        for constraint in &rule.body.constraints {
            collect_comparison_vars(constraint, &mut comparison_targets);
            let ExprValue::Eq(lhs, rhs) = constraint.value() else {
                continue;
            };
            if let Some(result) = try_extract_eq(lhs, rhs) {
                process_eq_result(result, &mut aliases, &mut arith_ops, &mut modifications);
            } else if let Some(result) = try_extract_eq(rhs, lhs) {
                process_eq_result(result, &mut aliases, &mut arith_ops, &mut modifications);
            }
        }
    }

    debug!(
        alias_count = aliases.len(),
        arith_op_count = arith_ops.len(),
        direct_count = modifications.len(),
        comparison_var_count = comparison_targets.len(),
        "lemma_hint: phase 1+2 complete"
    );

    // Phase 3: Resolve indirect patterns through aliases.
    // If X__out = T and T__out = X + Y, then X is incremented by Y.
    resolve_indirect_modifications(&aliases, &arith_ops, &mut modifications);

    ModificationResult { modifications, comparison_targets }
}

/// Recursively scan an expression for comparison sub-expressions with bare
/// `Var` operands. Records both directions: if `A < B` is found, A→B and
/// B→A are recorded. Handles comparisons nested inside Eq, Ite, Not, etc.
fn collect_comparison_vars(expr: &Expr, targets: &mut HashMap<Arc<str>, HashSet<Arc<str>>>) {
    match expr.value() {
        // Int ordered comparisons
        ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b) => {
            record_comparison_pair(a, b, targets);
        }
        // BV ordered comparisons (unsigned and signed)
        ExprValue::BvULt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b) => {
            record_comparison_pair(a, b, targets);
        }
        // Recurse into wrappers that may contain nested comparisons
        ExprValue::Eq(a, b) => {
            collect_comparison_vars(a, targets);
            collect_comparison_vars(b, targets);
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            collect_comparison_vars(cond, targets);
            collect_comparison_vars(then_expr, targets);
            collect_comparison_vars(else_expr, targets);
        }
        ExprValue::Not(inner) => {
            collect_comparison_vars(inner, targets);
        }
        ExprValue::And(es) | ExprValue::Or(es) => {
            for e in es {
                collect_comparison_vars(e, targets);
            }
        }
        _ => {}
    }
}

/// Record a comparison pair if both operands are bare variables.
/// Part of #2267: create Arc<str> once per name, share via Arc::clone.
/// Eliminates up to 4 String allocations per call (was .to_owned() x4).
fn record_comparison_pair(a: &Expr, b: &Expr, targets: &mut HashMap<Arc<str>, HashSet<Arc<str>>>) {
    if let (ExprValue::Var { name: a_name }, ExprValue::Var { name: b_name }) =
        (a.value(), b.value())
    {
        let a_arc: Arc<str> = Arc::from(a_name.as_str());
        let b_arc: Arc<str> = Arc::from(b_name.as_str());
        insert_comparison(&a_arc, Arc::clone(&b_arc), targets);
        insert_comparison(&b_arc, a_arc, targets);
    }
}

/// Insert a directed comparison edge using Arc<str> for O(1) key cloning.
/// Part of #2267: accepts Arc<str> by reference (key) and by value (value).
/// Key is cloned (O(1)) only when creating a new map entry.
fn insert_comparison(
    key: &Arc<str>,
    value: Arc<str>,
    targets: &mut HashMap<Arc<str>, HashSet<Arc<str>>>,
) {
    if let Some(set) = targets.get_mut(&**key) {
        if !set.contains(&*value) {
            set.insert(value);
        }
    } else {
        let mut set = HashSet::new();
        set.insert(value);
        targets.insert(Arc::clone(key), set);
    }
}

/// Resolve indirect modification patterns through alias chains.
///
/// When MIR emits `sum__out = _tmp_fld0` (alias) and `_tmp_fld0__out = sum + i`
/// (arith op), this resolves to `sum += i`.
///
/// A variable may have multiple aliases from different rules (initialization
/// vs loop body). All aliases are checked for each arith op.
fn resolve_indirect_modifications(
    aliases: &HashMap<Arc<str>, Vec<Arc<str>>>,
    arith_ops: &[ArithOp],
    modifications: &mut HashMap<Arc<str>, LoopModification>,
) {
    for op in arith_ops {
        for (alias_base, alias_sources) in aliases {
            for alias_source in alias_sources {
                if alias_source == &op.out_var_base && alias_base == &op.input_var {
                    let modification = if op.is_sub {
                        LoopModification::DecrementBy(op.source.clone_source())
                    } else {
                        LoopModification::IncrementBy(op.source.clone_source())
                    };
                    insert_by_priority(modifications, Arc::clone(alias_base), modification);
                }
            }
        }
    }
}

/// Try to extract a modification pattern from an equality constraint.
///
/// Given `out_candidate = rhs`, checks if `out_candidate` is a `__out` variable
/// and classifies the rhs as alias, arithmetic, or direct modification.
/// Part of #2267: creates Arc<str> from base_name once, shares downstream.
fn try_extract_eq(out_candidate: &Expr, rhs: &Expr) -> Option<EqResult> {
    let ExprValue::Var { name: out_name } = out_candidate.value() else {
        return None;
    };
    let base_name_str = out_name.strip_suffix("__out")?;
    let base_name: Arc<str> = Arc::from(base_name_str);

    match rhs.value() {
        ExprValue::Var { name: source_name } => {
            Some(EqResult::Alias { base_name, source: Arc::from(source_name.as_str()) })
        }
        ExprValue::IntAdd(a, b) | ExprValue::BvAdd(a, b) => {
            let is_int = matches!(rhs.value(), ExprValue::IntAdd(..));
            try_extract_add(base_name, a, b, is_int)
        }
        ExprValue::IntSub(a, b) | ExprValue::BvSub(a, b) => {
            let is_int = matches!(rhs.value(), ExprValue::IntSub(..));
            try_extract_sub(base_name, a, b, is_int)
        }
        _ => None,
    }
}

/// Extract addition pattern: `base__out = A + B`.
///
/// Checks for direct match (`base__out = base + Y`) first, then falls back
/// to recording as an indirect arithmetic operation for alias resolution.
fn try_extract_add(base_name: Arc<str>, a: &Expr, b: &Expr, is_int: bool) -> Option<EqResult> {
    // Direct match: X__out = X + Y (commutative)
    if is_var_named(a, &base_name) {
        if let Some(source) = classify_source(b, is_int) {
            return Some(EqResult::Direct(base_name, LoopModification::IncrementBy(source)));
        }
    }
    if is_var_named(b, &base_name) {
        if let Some(source) = classify_source(a, is_int) {
            return Some(EqResult::Direct(base_name, LoopModification::IncrementBy(source)));
        }
    }
    // Indirect: record for alias resolution
    try_extract_arith_op(base_name, a, b, is_int, false)
}

/// Extract subtraction pattern: `base__out = A - B`.
fn try_extract_sub(base_name: Arc<str>, a: &Expr, b: &Expr, is_int: bool) -> Option<EqResult> {
    // Direct match: X__out = X - Y
    if is_var_named(a, &base_name) {
        if let Some(source) = classify_source(b, is_int) {
            return Some(EqResult::Direct(base_name, LoopModification::DecrementBy(source)));
        }
    }
    // Indirect: record for alias resolution
    try_extract_arith_op(base_name, a, b, is_int, true)
}

/// Record an arithmetic operation for later alias resolution.
fn try_extract_arith_op(
    base_name: Arc<str>,
    a: &Expr,
    b: &Expr,
    is_int: bool,
    is_sub: bool,
) -> Option<EqResult> {
    if let ExprValue::Var { name: a_name } = a.value() {
        if let Some(source) = classify_source(b, is_int) {
            return Some(EqResult::Arith(ArithOp {
                out_var_base: base_name,
                input_var: Arc::from(a_name.as_str()),
                source,
                is_sub,
            }));
        }
    }
    if !is_sub {
        // Addition is commutative — try b as input var too
        if let ExprValue::Var { name: b_name } = b.value() {
            if let Some(source) = classify_source(a, is_int) {
                return Some(EqResult::Arith(ArithOp {
                    out_var_base: base_name,
                    input_var: Arc::from(b_name.as_str()),
                    source,
                    is_sub: false,
                }));
            }
        }
    }
    None
}

fn process_eq_result(
    result: EqResult,
    aliases: &mut HashMap<Arc<str>, Vec<Arc<str>>>,
    arith_ops: &mut Vec<ArithOp>,
    modifications: &mut HashMap<Arc<str>, LoopModification>,
) {
    match result {
        EqResult::Alias { base_name, source } => {
            let sources = aliases.entry(base_name).or_default();
            if !sources.contains(&source) {
                sources.push(source);
            }
        }
        EqResult::Arith(op) => {
            arith_ops.push(op);
        }
        EqResult::Direct(base_name, modification) => {
            insert_by_priority(modifications, base_name, modification);
        }
    }
}

/// Insert a modification for `key`, replacing the existing entry only if the
/// new modification has higher priority. Ensures deterministic selection when
/// multiple rules produce different modification patterns for the same variable
/// (e.g., initialization alias vs loop body accumulator).
/// Part of #3343: replaces non-deterministic `or_insert` first-wins semantics.
fn insert_by_priority(
    modifications: &mut HashMap<Arc<str>, LoopModification>,
    key: Arc<str>,
    new_mod: LoopModification,
) {
    match modifications.entry(key) {
        std::collections::hash_map::Entry::Vacant(e) => {
            e.insert(new_mod);
        }
        std::collections::hash_map::Entry::Occupied(mut e) => {
            if new_mod.priority() > e.get().priority() {
                e.insert(new_mod);
            }
        }
    }
}

/// Check if an expression is a `Var` with the given name.
fn is_var_named(expr: &Expr, name: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name: n } if n == name)
}

/// Classify an expression as an increment source.
/// Handles Int constants, BV constants, Bv2Int-wrapped constants/vars,
/// and bare variables.
/// Part of #2267: Variable case uses Arc::from(&str) (1 alloc) not Arc::from(clone()) (2 allocs).
fn classify_source(expr: &Expr, _is_int: bool) -> Option<IncrSource> {
    match expr.value() {
        ExprValue::IntConst(v) => {
            let val: i64 = v.try_into().ok()?;
            Some(IncrSource::Constant(val))
        }
        ExprValue::BitVecConst { value: v, .. } => {
            let val: i64 = v.try_into().ok()?;
            Some(IncrSource::Constant(val))
        }
        // Int-lift wraps BV constants/vars in Bv2Int. Unwrap and recurse.
        ExprValue::Bv2Int(inner) => classify_source(inner, _is_int),
        ExprValue::Var { name } => Some(IncrSource::Variable(Arc::from(name.as_str()))),
        _ => None,
    }
}

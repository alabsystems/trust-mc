// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Normalize free-variable array bases in store chains to `const_array`.
//!
//! The MIR encoder creates free universally-quantified array variables
//! (`__chc_array_N`) as bases for local array initialization:
//!
//! ```text
//! (= arr__out (store (store __chc_array_2 #x0 val0) #x1 val1))
//! ```
//!
//! The scalarizer rejects these because the store chain base is neither the
//! relation input variable nor `const_array(...)`. However, since `__chc_array_N`
//! is a universally quantified free variable NOT appearing in any relation,
//! the uninitialized array positions are unconstrained — semantically equivalent
//! to `const_array(default)` for scalarization purposes.
//!
//! This pass replaces such free-variable bases with `const_array` expressions,
//! enabling the scalarizer to decompose the store chains into per-index scalar
//! equalities.
//!
//! Runs before scalarization in the translation and emit pipelines. The early
//! pass ensures scalarization sees initialized lanes before later rewrites erase
//! the array selects needed to recover them.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};

use crate::chc::ChcVc;

/// Normalize free-variable array bases in store chains.
///
/// For each constraint containing a store chain whose innermost base is a
/// declared Array-sorted var NOT appearing in any relation argument, replace
/// that base with `const_array(index_sort, default_elem)`.
///
/// Returns the number of store chain bases normalized.
pub(super) fn normalize_free_array_bases(vc: &mut ChcVc) -> usize {
    // Step 1: Collect essential vars — those appearing in any relation app.
    let mut essential: HashSet<String> = HashSet::new();
    for rule in &vc.rules {
        collect_relation_vars(&rule.head, &mut essential);
        if let Some(ref rel) = rule.body.relation {
            collect_relation_vars(rel, &mut essential);
        }
    }

    // Step 2: Identify declared Array-sorted vars that are NOT essential.
    let mut free_array_vars: HashSet<String> = HashSet::new();
    for v in vc.vars() {
        if v.sort.is_array() && !essential.contains(&*v.name) {
            free_array_vars.insert(v.name.to_string());
        }
    }

    if free_array_vars.is_empty() {
        return 0;
    }

    // Step 3: Rewrite store chain bases in all rule constraints.
    let mut total_normalized = 0;
    for rule in &mut vc.rules {
        let old_constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        let mut rule_normalized = 0;
        let mut new_constraints = Vec::with_capacity(old_constraints.len());
        for constraint in &old_constraints {
            let (rewritten, count) = rewrite_free_bases_in_expr(constraint, &free_array_vars);
            rule_normalized += count;
            new_constraints.push(rewritten);
        }
        if rule_normalized > 0 {
            rule.body.constraints = crate::constraints::Constraints::Owned(new_constraints);
            total_normalized += rule_normalized;
        }
    }

    total_normalized
}

/// Rewrite an expression, replacing free-var Array bases in store chains
/// with `const_array` expressions.
///
/// Returns the rewritten expression and the number of replacements made.
fn rewrite_free_bases_in_expr(expr: &Expr, free_vars: &HashSet<String>) -> (Expr, usize) {
    match expr.value() {
        ExprValue::Store { array, index, value } => {
            // Check if the innermost base of this store chain is a free var.
            if let Some((base_name, base_sort)) = find_store_chain_base(expr) {
                if free_vars.contains(&base_name) {
                    if let Some(arr_sort) = base_sort.array_sort() {
                        let default_elem = make_default_value(&arr_sort.element_sort, &base_name);
                        let const_arr =
                            Expr::const_array(arr_sort.index_sort.clone(), default_elem);
                        return (rebuild_store_chain_with_base(expr, &const_arr), 1);
                    }
                }
            }
            // Not a free-base chain — recurse into children.
            let (new_array, c1) = rewrite_free_bases_in_expr(array, free_vars);
            let (new_index, c2) = rewrite_free_bases_in_expr(index, free_vars);
            let (new_value, c3) = rewrite_free_bases_in_expr(value, free_vars);
            if c1 + c2 + c3 > 0 {
                (new_array.store(new_index, new_value), c1 + c2 + c3)
            } else {
                (expr.clone(), 0)
            }
        }
        ExprValue::Eq(lhs, rhs) => {
            let (new_lhs, c1) = rewrite_free_bases_in_expr(lhs, free_vars);
            let (new_rhs, c2) = rewrite_free_bases_in_expr(rhs, free_vars);
            if c1 + c2 > 0 { (new_lhs.eq(new_rhs), c1 + c2) } else { (expr.clone(), 0) }
        }
        ExprValue::Select { array, index } => {
            let (new_array, c1) = rewrite_free_bases_in_expr(array, free_vars);
            let (new_index, c2) = rewrite_free_bases_in_expr(index, free_vars);
            if c1 + c2 > 0 { (new_array.select(new_index), c1 + c2) } else { (expr.clone(), 0) }
        }
        _ => {
            let children: Vec<&Expr> = expr.children().collect();
            if children.is_empty() {
                return (expr.clone(), 0);
            }
            let mut any_changed = false;
            let mut total_count = 0;
            let mut new_children = Vec::with_capacity(children.len());
            for child in &children {
                let (rewritten, count) = rewrite_free_bases_in_expr(child, free_vars);
                if count > 0 {
                    any_changed = true;
                    total_count += count;
                }
                new_children.push(rewritten);
            }
            if any_changed {
                (ay_bindings::rebuild_with_children(expr, new_children), total_count)
            } else {
                (expr.clone(), 0)
            }
        }
    }
}

/// Find the innermost base of a store chain.
/// Returns `(var_name, var_sort)` if the base is a `Var`.
fn find_store_chain_base(expr: &Expr) -> Option<(String, Sort)> {
    match expr.value() {
        ExprValue::Var { name } => Some((name.clone(), expr.sort().clone())),
        ExprValue::Store { array, .. } => find_store_chain_base(array),
        _ => None,
    }
}

/// Rebuild a store chain replacing the innermost base.
fn rebuild_store_chain_with_base(expr: &Expr, new_base: &Expr) -> Expr {
    match expr.value() {
        ExprValue::Var { .. } => new_base.clone(),
        ExprValue::Store { array, index, value } => {
            let rebuilt_array = rebuild_store_chain_with_base(array, new_base);
            rebuilt_array.store(index.clone(), value.clone())
        }
        _ => expr.clone(),
    }
}

/// Create a default zero-value expression for a sort.
///
/// For scalarization purposes, the specific default value doesn't matter
/// because only the stored positions are accessed. We use zero for
/// deterministic output.
fn make_default_value(sort: &Sort, suffix: &str) -> Expr {
    if let Some(width) = sort.bitvec_width() {
        Expr::bitvec_const(0u128, width)
    } else if sort.is_bool() {
        Expr::bool_const(false)
    } else if sort.is_int() {
        Expr::int_const(0)
    } else {
        // For complex sorts (datatypes, nested arrays), use a fresh
        // unconstrained variable. This is safe because scalarized
        // indices only access stored positions.
        Expr::var(&format!("__default_elem_{suffix}"), sort.clone())
    }
}

/// Collect variable names from a relation application's arguments.
fn collect_relation_vars(app: &crate::chc::RelationApp, out: &mut HashSet<String>) {
    for arg in app.args.iter() {
        collect_vars_recursive(arg, out);
    }
}

/// Recursively collect variable names from an expression.
fn collect_vars_recursive(expr: &Expr, out: &mut HashSet<String>) {
    match expr.value() {
        ExprValue::Var { name } => {
            out.insert(name.clone());
        }
        _ => {
            for child in expr.children() {
                collect_vars_recursive(child, out);
            }
        }
    }
}

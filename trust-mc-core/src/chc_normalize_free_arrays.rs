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
//! "Free" is judged per rule, by every occurrence. A var that no relation
//! application names can still be bound inside its rule: fragment composition
//! frames an array forward with `(= a__mid_bb4 a)` and then stores into
//! `a__mid_bb4`. Its unstored lanes are `a`'s, so a `const_array(0)` base
//! would zero them. That is an under-approximation, and it hid real failures:
//! `a=[1,2]; while i<2 { a[0]+=1 }; assert!(a[1]==0)` was proved once
//! the scalarizer kept the loop head's column whole. A base is therefore
//! replaced only in a rule where it occurs solely as the innermost base of
//! store chains. Measured over the 1134 CHC corpus units (2026-09-25), what
//! still qualifies is only the encoder's fresh aggregate bases, whose chains
//! store every lane of the array, and the memory type and per-allocation
//! region arrays that `prune_vc_unused_type_arrays` dropped from the relations
//! because nothing reads them.
//!
//! Runs before scalarization in the translation and emit pipelines. The early
//! pass ensures scalarization sees initialized lanes before later rewrites erase
//! the array selects needed to recover them.

use std::collections::{BTreeSet, HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort};

use crate::chc::ChcVc;

/// Normalize free-variable array bases in store chains.
///
/// A base is replaced in a rule only when that rule leaves it unconstrained:
/// it is a declared Array-sorted var that no relation application names (in
/// any rule), and EVERY occurrence of it in the rule's constraints is the
/// innermost base of a store chain. Any other occurrence — an equality such
/// as the frame identity `(= a__mid_bb4 a)`, a `select`, an argument to an
/// `ite` — ties its unstored lanes to something, and replacing the base with
/// `const_array(0)` would force those lanes to zero: an UNDER-approximation
/// of the rule's states, which hides reachable errors.
///
/// Returns the number of store chain bases normalized and the names of the
/// vars replaced.
pub(super) fn normalize_free_array_bases(vc: &mut ChcVc) -> (usize, BTreeSet<String>) {
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
        return (0, BTreeSet::new());
    }

    // Step 3: Per rule, rewrite the store chain bases that rule leaves
    // unconstrained.
    let mut total_normalized = 0;
    let mut names: BTreeSet<String> = BTreeSet::new();
    for rule in &mut vc.rules {
        let mut uses: HashMap<String, BaseUses> = HashMap::new();
        for constraint in rule.body.constraints.iter() {
            count_uses(constraint, &free_array_vars, false, &mut uses);
        }
        let replaceable: HashSet<String> = uses
            .into_iter()
            .filter(|(_, u)| u.as_base > 0 && u.as_base == u.total)
            .map(|(name, _)| name)
            .collect();
        if replaceable.is_empty() {
            continue;
        }
        let mut rule_normalized = 0;
        let mut new_constraints = Vec::with_capacity(rule.body.constraints.len());
        for constraint in rule.body.constraints.iter() {
            let (rewritten, count) = rewrite_free_bases_in_expr(constraint, &replaceable);
            rule_normalized += count;
            new_constraints.push(rewritten);
        }
        if rule_normalized == 0 {
            continue;
        }
        // All or nothing: a base replaced in one place and left raw in
        // another would decouple the two, so a rule where any replaced name
        // survives the rewrite keeps its original constraints.
        let mut survivors: HashSet<String> = HashSet::new();
        for c in &new_constraints {
            collect_vars_recursive(c, &mut survivors);
        }
        if survivors.iter().any(|name| replaceable.contains(name)) {
            continue;
        }
        rule.body.constraints = crate::constraints::Constraints::Owned(new_constraints);
        total_normalized += rule_normalized;
        names.extend(replaceable);
    }

    (total_normalized, names)
}

/// How often a candidate var occurs in one rule, and how many of those
/// occurrences are the innermost base of a store chain.
#[derive(Default)]
struct BaseUses {
    total: usize,
    as_base: usize,
}

/// Count occurrences of `candidates` in `expr`. `at_base` is true when `expr`
/// is the innermost base of a store chain.
fn count_uses(
    expr: &Expr,
    candidates: &HashSet<String>,
    at_base: bool,
    uses: &mut HashMap<String, BaseUses>,
) {
    match expr.value() {
        ExprValue::Var { name } => {
            if candidates.contains(name) {
                let entry = uses.entry(name.clone()).or_default();
                entry.total += 1;
                if at_base {
                    entry.as_base += 1;
                }
            }
        }
        ExprValue::Store { .. } => {
            let mut cur = expr;
            while let ExprValue::Store { array, index, value } = cur.value() {
                count_uses(index, candidates, false, uses);
                count_uses(value, candidates, false, uses);
                cur = array;
            }
            count_uses(cur, candidates, true, uses);
        }
        _ => {
            for child in expr.children() {
                count_uses(child, candidates, false, uses);
            }
        }
    }
}

/// Rewrite an expression, replacing the `replace` vars that are store chain
/// bases with `const_array` expressions. Every store chain is rebuilt with its
/// indices and values rewritten too, so the replacement reaches every base
/// occurrence [`count_uses`] counted.
///
/// Returns the rewritten expression and the number of replacements made.
fn rewrite_free_bases_in_expr(expr: &Expr, replace: &HashSet<String>) -> (Expr, usize) {
    match expr.value() {
        ExprValue::Store { .. } => {
            let mut spine: Vec<(&Expr, &Expr)> = Vec::new();
            let mut cur = expr;
            while let ExprValue::Store { array, index, value } = cur.value() {
                spine.push((index, value));
                cur = array;
            }
            let (mut rebuilt, mut count) = match cur.value() {
                ExprValue::Var { name } if replace.contains(name) => {
                    match cur.sort().array_sort() {
                        Some(arr_sort) => {
                            let default_elem = make_default_value(&arr_sort.element_sort, name);
                            (Expr::const_array(arr_sort.index_sort.clone(), default_elem), 1)
                        }
                        None => (cur.clone(), 0),
                    }
                }
                _ => rewrite_free_bases_in_expr(cur, replace),
            };
            for (index, value) in spine.into_iter().rev() {
                let (new_index, c1) = rewrite_free_bases_in_expr(index, replace);
                let (new_value, c2) = rewrite_free_bases_in_expr(value, replace);
                count += c1 + c2;
                rebuilt = rebuilt.store(new_index, new_value);
            }
            if count > 0 { (rebuilt, count) } else { (expr.clone(), 0) }
        }
        ExprValue::Eq(lhs, rhs) => {
            let (new_lhs, c1) = rewrite_free_bases_in_expr(lhs, replace);
            let (new_rhs, c2) = rewrite_free_bases_in_expr(rhs, replace);
            if c1 + c2 > 0 { (new_lhs.eq(new_rhs), c1 + c2) } else { (expr.clone(), 0) }
        }
        ExprValue::Select { array, index } => {
            let (new_array, c1) = rewrite_free_bases_in_expr(array, replace);
            let (new_index, c2) = rewrite_free_bases_in_expr(index, replace);
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
                let (rewritten, count) = rewrite_free_bases_in_expr(child, replace);
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

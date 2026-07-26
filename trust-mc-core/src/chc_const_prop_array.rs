// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Intra-block array store-select resolution for CHC constant propagation.
//!
//! After scalar constant propagation converges (Phase 1), values may still
//! be "stuck" behind type-indexed memory arrays. For example:
//!
//! ```text
//! Constraint 1: (= mem' (store mem addr #x04))
//! Constraint 2: (= _7 (select mem' addr))
//! ```
//!
//! Phase 1 cannot resolve `_7` because `mem'` is an array (not a scalar
//! constant) and `store(mem, addr, #x04)` is never added to the scalar
//! `known` map.
//!
//! This module bridges the gap:
//! - **Phase 2** tracks array store definitions in a side map.
//! - **Phase 3** resolves `select` operations through tracked stores
//!   using the McCarthy store-select axiom: `select(store(a, i, v), i) = v`.
//!
//! Part of #3371. Design: designs/2026-03-07-nonnull-dangling-phase2-param-pruning.md

use std::collections::HashMap;

use ay_bindings::{Expr, ExprValue};

use super::eval::eval_select_store_const;
use super::is_constant;
use super::subst::substitute_vars;

/// Resolves scalar constants that flow through array store/select patterns.
///
/// Scans flattened constraints for store definitions (Phase 2), then resolves
/// select operations through those stores (Phase 3). Only adds values to
/// `known` that are provably constant (soundness guard).
pub(super) fn resolve_array_store_selects(flat: &[Expr], known: &mut HashMap<String, Expr>) {
    // Phase 2: Track array store definitions.
    // For constraints matching (= arr_var (store base idx val)),
    // build a map of arr_var → store expression. Unlike scalar constants,
    // array expressions are tracked even when not fully constant —
    // they're resolved via store-select axiom in Phase 3.
    let mut array_stores: HashMap<String, Expr> = HashMap::new();
    let mut array_aliases: Vec<(String, String)> = Vec::new();
    for expr in flat {
        if let ExprValue::Eq(lhs, rhs) = expr.value() {
            // (= Var StoreExpr)
            if let ExprValue::Var { name } = lhs.value() {
                let sub_rhs = substitute_vars(rhs, known);
                if matches!(sub_rhs.value(), ExprValue::Store { .. }) {
                    array_stores.insert(name.clone(), sub_rhs);
                }
            }
            // (= StoreExpr Var)
            if let ExprValue::Var { name } = rhs.value() {
                let sub_lhs = substitute_vars(lhs, known);
                if matches!(sub_lhs.value(), ExprValue::Store { .. }) {
                    array_stores.insert(name.clone(), sub_lhs);
                }
            }
            if let (ExprValue::Var { name: lhs_name }, ExprValue::Var { name: rhs_name }) =
                (lhs.value(), rhs.value())
            {
                if lhs.sort().array_sort().is_some() && lhs.sort() == rhs.sort() {
                    array_aliases.push((lhs_name.clone(), rhs_name.clone()));
                }
            }
        }
    }
    if array_stores.is_empty() {
        return;
    }
    propagate_store_aliases(&mut array_stores, &array_aliases);

    // Phase 3: Resolve select-from-stored-array patterns.
    // For constraints matching (= scalar_var (select arr_var idx)),
    // if arr_var has a known store and the indices match (McCarthy axiom),
    // resolve to the stored value. Only adds to `known` if the resolved
    // value is a constant (soundness guard).
    let mut changed = true;
    while changed {
        changed = false;
        for expr in flat {
            if let ExprValue::Eq(lhs, rhs) = expr.value() {
                if let Some((name, val)) = resolve_select_from_store(lhs, rhs, known, &array_stores)
                    .or_else(|| resolve_select_from_store(rhs, lhs, known, &array_stores))
                {
                    known.insert(name, val);
                    changed = true;
                }
            }
        }
    }
}

/// Copies tracked store definitions across array-only Var = Var aliases.
///
/// This keeps the store/select optimization narrow: aliases do not enter the
/// scalar `known` map, and only variables with the same array sort can inherit
/// a tracked store definition.
fn propagate_store_aliases(
    array_stores: &mut HashMap<String, Expr>,
    array_aliases: &[(String, String)],
) {
    let mut changed = true;
    while changed {
        changed = false;
        for (lhs, rhs) in array_aliases {
            match (array_stores.get(lhs).cloned(), array_stores.get(rhs).cloned()) {
                (Some(store), None) => {
                    array_stores.insert(rhs.clone(), store);
                    changed = true;
                }
                (None, Some(store)) => {
                    array_stores.insert(lhs.clone(), store);
                    changed = true;
                }
                _ => {}
            }
        }
    }
}

/// Resolves `(= var_side (select arr_var idx))` through array store tracking.
///
/// If `var_side` is an unknown Var and `select_side` resolves to a select from
/// a tracked array store where the index matches, returns the variable name
/// and resolved constant value. Uses the McCarthy store-select axiom:
/// `select(store(a, i, v), i) = v`.
fn resolve_select_from_store(
    var_side: &Expr,
    select_side: &Expr,
    known: &HashMap<String, Expr>,
    array_stores: &HashMap<String, Expr>,
) -> Option<(String, Expr)> {
    let name = match var_side.value() {
        ExprValue::Var { name } if !known.contains_key(name) => name,
        _ => return None,
    };
    let sub = substitute_vars(select_side, known);
    if let ExprValue::Select { array, index } = sub.value() {
        if let ExprValue::Var { name: arr_name } = array.value() {
            if let Some(store_expr) = array_stores.get(arr_name) {
                // Re-substitute store with latest known constants
                // to handle cascading (e.g., stored value resolved
                // after a prior Phase 3 iteration).
                let store_subst = substitute_vars(store_expr, known);
                // Part of #3416: Expand nested array store variables before
                // eval_select_store_const. Without this, chained stores like
                // mem'' = store(mem', j, v2) where mem' = store(mem, i, v1)
                // fail to resolve select(mem'', i) because the inner Var
                // "mem'" is not structurally a Store expression.
                let expanded = expand_array_stores(store_subst, array_stores, known);
                if let Some(val) = eval_select_store_const(&expanded, index) {
                    if is_constant(&val) {
                        return Some((name.clone(), val));
                    }
                }
            }
        }
    }
    None
}

/// Recursively expand array store variables in a store expression.
///
/// Replaces Var nodes that are tracked in `array_stores` with their
/// corresponding store expressions, enabling `eval_select_store_const`
/// to resolve through chained stores.
///
/// Bounds recursion to 8 levels to prevent infinite loops from cyclic
/// constraints (which shouldn't occur in well-formed CHC, but defensive).
fn expand_array_stores(
    expr: Expr,
    array_stores: &HashMap<String, Expr>,
    known: &HashMap<String, Expr>,
) -> Expr {
    expand_array_stores_bounded(expr, array_stores, known, 8)
}

fn expand_array_stores_bounded(
    expr: Expr,
    array_stores: &HashMap<String, Expr>,
    known: &HashMap<String, Expr>,
    depth: usize,
) -> Expr {
    if depth == 0 {
        return expr;
    }
    if let ExprValue::Store { array, index, value } = expr.value() {
        // If the inner array is a Var with a known store, expand it.
        if let ExprValue::Var { name } = array.value() {
            if let Some(inner_store) = array_stores.get(name) {
                let inner_subst = substitute_vars(inner_store, known);
                let expanded_inner =
                    expand_array_stores_bounded(inner_subst, array_stores, known, depth - 1);
                return expanded_inner.store(index.clone(), value.clone());
            }
        }
        // Recurse into the inner array even if it's not a direct Var lookup.
        let expanded_inner =
            expand_array_stores_bounded(array.clone(), array_stores, known, depth - 1);
        return expanded_inner.store(index.clone(), value.clone());
    }
    expr
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ay_bindings::{Expr, Sort};

    use super::resolve_array_store_selects;

    #[test]
    fn test_select_from_stored_array_resolves_constant() {
        // Phase 1 has already resolved _1 = #x04 (scalar constant).
        // Constraints encode: mem' = store(mem, addr, _1), _7 = select(mem', addr).
        // Phase 2-3 should resolve _7 = #x04 via McCarthy store-select axiom.
        let bv64 = Sort::bitvec(64);
        let arr_sort = Sort::array(bv64.clone(), bv64.clone());

        let mem = Expr::var("mem", arr_sort.clone());
        let mem_prime = Expr::var("mem_prime", arr_sort);
        let addr = Expr::var("addr", bv64.clone());
        let var_1 = Expr::var("_1", bv64.clone());
        let var_7 = Expr::var("_7", bv64);

        // (= mem_prime (store mem addr _1))
        let c1 = mem_prime.clone().eq(mem.store(addr.clone(), var_1));
        // (= _7 (select mem_prime addr))
        let c2 = var_7.eq(mem_prime.select(addr));

        let mut known: HashMap<String, Expr> = HashMap::new();
        known.insert("_1".into(), Expr::bitvec_const(4i64, 64));

        resolve_array_store_selects(&[c1, c2], &mut known);

        assert!(known.contains_key("_7"), "_7 should be resolved via store-select");
        assert_eq!(known["_7"], Expr::bitvec_const(4i64, 64));
    }

    #[test]
    fn test_select_from_array_alias_resolves_tracked_store() {
        let bv64 = Sort::bitvec(64);
        let arr_sort = Sort::array(bv64.clone(), bv64.clone());

        let mem = Expr::var("mem", arr_sort.clone());
        let mem_prime = Expr::var("mem_prime", arr_sort.clone());
        let mem_alias = Expr::var("mem_alias", arr_sort);
        let addr = Expr::var("addr", bv64.clone());
        let stored = Expr::bitvec_const(4i64, 64);
        let var_7 = Expr::var("_7", bv64);

        // mem_prime = store(mem, addr, 4)
        let c_store = mem_prime.clone().eq(mem.store(addr.clone(), stored.clone()));
        // mem_alias = mem_prime
        let c_alias = mem_alias.clone().eq(mem_prime);
        // _7 = select(mem_alias, addr)
        let c_select = var_7.eq(mem_alias.select(addr));

        let mut known: HashMap<String, Expr> = HashMap::new();
        resolve_array_store_selects(&[c_store, c_alias, c_select], &mut known);

        assert!(
            known.contains_key("_7"),
            "_7 should resolve when the tracked store flows through an array alias"
        );
        assert_eq!(known["_7"], stored);
    }

    /// Part of #3416: select(store(a, i, v), j) where i != j must NOT resolve.
    /// If mismatched indices incorrectly resolve, error rules are eliminated → false PROOFs.
    #[test]
    fn test_mismatched_index_does_not_resolve() {
        let bv64 = Sort::bitvec(64);
        let arr_sort = Sort::array(bv64.clone(), bv64.clone());

        let mem = Expr::var("mem", arr_sort.clone());
        let mem_prime = Expr::var("mem_prime", arr_sort);
        let addr_i = Expr::bitvec_const(10i64, 64);
        let addr_j = Expr::bitvec_const(20i64, 64);
        let val = Expr::bitvec_const(0xFFi64, 64);
        let var_7 = Expr::var("_7", bv64);

        // mem' = store(mem, 10, 0xFF)
        let c1 = mem_prime.clone().eq(mem.store(addr_i, val));
        // _7 = select(mem', 20)  — different index
        let c2 = var_7.eq(mem_prime.select(addr_j));

        let mut known: HashMap<String, Expr> = HashMap::new();
        resolve_array_store_selects(&[c1, c2], &mut known);

        assert!(
            !known.contains_key("_7"),
            "_7 must NOT resolve when select index differs from store index"
        );
    }

    /// Part of #3416: select(store(store(a, i, v1), j, v2), i) should resolve to v1.
    /// Chained stores require recursive resolution through eval_select_store_const.
    #[test]
    fn test_chained_stores_resolves_correct_value() {
        let bv64 = Sort::bitvec(64);
        let arr_sort = Sort::array(bv64.clone(), bv64.clone());

        let mem = Expr::var("mem", arr_sort.clone());
        let mem_prime = Expr::var("mem_prime", arr_sort.clone());
        let mem_dprime = Expr::var("mem_dprime", arr_sort);
        let addr_i = Expr::bitvec_const(10i64, 64);
        let addr_j = Expr::bitvec_const(20i64, 64);
        let v1 = Expr::bitvec_const(0xAAi64, 64);
        let v2 = Expr::bitvec_const(0xBBi64, 64);
        let var_out = Expr::var("_out", bv64);

        // mem' = store(mem, 10, 0xAA)
        let c1 = mem_prime.clone().eq(mem.store(addr_i.clone(), v1));
        // mem'' = store(mem', 20, 0xBB)
        let c2 = mem_dprime.clone().eq(mem_prime.store(addr_j, v2));
        // _out = select(mem'', 10) — should resolve to 0xAA (inner store value)
        let c3 = var_out.eq(mem_dprime.select(addr_i));

        let mut known: HashMap<String, Expr> = HashMap::new();
        resolve_array_store_selects(&[c1, c2, c3], &mut known);

        assert!(known.contains_key("_out"), "_out should resolve through chained stores");
        assert_eq!(known["_out"], Expr::bitvec_const(0xAAi64, 64));
    }

    /// Part of #3416: Resolution must work when the select constraint appears
    /// before the store constraint in the flat list. The fixed-point loop
    /// (Phase 3) iterates until convergence, so ordering should not matter.
    #[test]
    fn test_select_before_store_order_independent() {
        let bv64 = Sort::bitvec(64);
        let arr_sort = Sort::array(bv64.clone(), bv64.clone());

        let mem = Expr::var("mem", arr_sort.clone());
        let mem_prime = Expr::var("mem_prime", arr_sort);
        let addr = Expr::var("addr", bv64.clone());
        let var_1 = Expr::var("_1", bv64.clone());
        let var_7 = Expr::var("_7", bv64);

        // Note: select constraint BEFORE store constraint
        // _7 = select(mem', addr)
        let c_select = var_7.eq(mem_prime.clone().select(addr.clone()));
        // mem' = store(mem, addr, _1)
        let c_store = mem_prime.eq(mem.store(addr, var_1));

        let mut known: HashMap<String, Expr> = HashMap::new();
        known.insert("_1".into(), Expr::bitvec_const(42i64, 64));

        // Constraint order: select first, then store
        resolve_array_store_selects(&[c_select, c_store], &mut known);

        assert!(known.contains_key("_7"), "_7 should resolve regardless of constraint order");
        assert_eq!(known["_7"], Expr::bitvec_const(42i64, 64));
    }

    /// Part of #3416: When the stored value is not constant after substitution,
    /// the is_constant() guard (line 114) must prevent adding it to `known`.
    /// If this guard fails, non-constants would be propagated as constants → unsound.
    #[test]
    fn test_non_constant_value_not_propagated() {
        let bv64 = Sort::bitvec(64);
        let arr_sort = Sort::array(bv64.clone(), bv64.clone());

        let mem = Expr::var("mem", arr_sort.clone());
        let mem_prime = Expr::var("mem_prime", arr_sort);
        let addr = Expr::bitvec_const(10i64, 64);
        // symbolic_val is NOT in `known` — it's an unresolved variable
        let symbolic_val = Expr::var("symbolic_val", bv64.clone());
        let var_7 = Expr::var("_7", bv64);

        // mem' = store(mem, 10, symbolic_val)
        let c1 = mem_prime.clone().eq(mem.store(addr.clone(), symbolic_val));
        // _7 = select(mem', 10)
        let c2 = var_7.eq(mem_prime.select(addr));

        let mut known: HashMap<String, Expr> = HashMap::new();
        // Note: symbolic_val is NOT added to known — it remains symbolic
        resolve_array_store_selects(&[c1, c2], &mut known);

        assert!(!known.contains_key("_7"), "_7 must NOT resolve when stored value is not constant");
    }

    /// Part of #3416: Multiple stores to same array with different variable names.
    /// mem' = store(mem, i, v1), mem'' = store(mem', j, v2).
    /// select(mem'', j) should resolve to v2 (direct match).
    /// select(mem'', i) should resolve to v1 (chained — see test_chained_stores).
    /// This tests the direct match case (select from the outer store).
    #[test]
    fn test_nested_store_chain_direct_match() {
        let bv64 = Sort::bitvec(64);
        let arr_sort = Sort::array(bv64.clone(), bv64.clone());

        let mem = Expr::var("mem", arr_sort.clone());
        let mem_prime = Expr::var("mem_prime", arr_sort.clone());
        let mem_dprime = Expr::var("mem_dprime", arr_sort);
        let addr_i = Expr::bitvec_const(10i64, 64);
        let addr_j = Expr::bitvec_const(20i64, 64);
        let v1 = Expr::bitvec_const(0xAAi64, 64);
        let v2 = Expr::bitvec_const(0xBBi64, 64);
        let var_direct = Expr::var("_direct", bv64);

        // mem' = store(mem, 10, 0xAA)
        let c1 = mem_prime.clone().eq(mem.store(addr_i, v1));
        // mem'' = store(mem', 20, 0xBB)
        let c2 = mem_dprime.clone().eq(mem_prime.store(addr_j.clone(), v2));
        // _direct = select(mem'', 20) — direct match on outer store
        let c3 = var_direct.eq(mem_dprime.select(addr_j));

        let mut known: HashMap<String, Expr> = HashMap::new();
        resolve_array_store_selects(&[c1, c2, c3], &mut known);

        assert!(
            known.contains_key("_direct"),
            "_direct should resolve via direct match on outer store"
        );
        assert_eq!(known["_direct"], Expr::bitvec_const(0xBBi64, 64));
    }
}

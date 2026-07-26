// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_const_array_store_contradiction_drops_query_rule() {
    // Models drop-check noise from CHC memory validity arrays:
    // const(true) == store(const(true), idx, false) is unsatisfiable for any idx.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::nullary("error"));

    let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));
    let freed =
        all_valid.clone().store(Expr::var("obj_id", Sort::bitvec(32)), Expr::bool_const(false));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![all_valid.eq(freed)]),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    assert_error_rule_dropped(&vc, "unsatisfiable const-array/store equality");
}

#[test]
fn test_const_array_store_same_value_keeps_rule() {
    // Storing the const-array default value is a no-op, so the equality is true,
    // not false. The rule should remain and the tautological constraint is stripped.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::nullary("error"));

    let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));
    let unchanged =
        all_valid.clone().store(Expr::var("obj_id", Sort::bitvec(32)), Expr::bool_const(true));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![all_valid.eq(unchanged)]),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    let error_rule = vc
        .rules
        .iter()
        .find(|rule| rule.head.name.as_str() == "error")
        .expect("tautological const-array/store equality should not eliminate the rule");
    assert!(
        error_rule.body.constraints.is_empty(),
        "tautological const-array/store equality should be stripped"
    );
}

#[test]
fn test_store_select_same_cell_folds_to_array() {
    // Rewriting an array cell to its current value is a semantic no-op:
    // store(a, i, select(a, i)) = a. Scalarization cleanup can expose this
    // pattern after index constants are substituted.
    let idx_sort = Sort::bitvec(32);
    let arr_sort = Sort::array(idx_sort.clone(), Sort::bool());
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", idx_sort);
    let store_expr = arr.clone().store(idx.clone(), arr.clone().select(idx));

    let mut known = HashMap::new();
    known.insert("idx".to_string(), Expr::bitvec_const(7i64, 32));

    let result = substitute_vars(&store_expr, &known);

    assert_eq!(result, arr, "redundant store/select write should fold back to the array");
}

#[test]
fn test_nested_store_same_cell_drops_overwritten_write() {
    // A later store to the same cell dominates the earlier write:
    // store(store(a, i, old), i, new) = store(a, i, new).
    let idx_sort = Sort::bitvec(32);
    let arr_sort = Sort::array(idx_sort.clone(), Sort::bool());
    let arr = Expr::var("arr", arr_sort);
    let idx = Expr::var("idx", idx_sort);
    let store_expr = arr
        .clone()
        .store(idx.clone(), Expr::bool_const(false))
        .store(idx.clone(), Expr::bool_const(true));

    let mut known = HashMap::new();
    known.insert("idx".to_string(), Expr::bitvec_const(7i64, 32));

    let result = substitute_vars(&store_expr, &known);
    let expected = arr.store(Expr::bitvec_const(7i64, 32), Expr::bool_const(true));

    assert_eq!(result, expected, "overwritten same-index store should be removed");
}

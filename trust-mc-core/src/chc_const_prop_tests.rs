// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC constant propagation.

use std::collections::HashMap;

use ay_bindings::{Expr, Sort};

use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

use super::propagate_constants;
use super::subst::substitute_vars;

#[path = "chc_const_prop_array_store_tests.rs"]
mod array_store_tests;
#[path = "chc_const_prop_rule_preservation_tests.rs"]
mod rule_preservation_tests;

/// Helper: creates a BV64 constant.
fn bv64(val: i64) -> Expr {
    Expr::bitvec_const(val, 64)
}

/// Helper: creates a BV64 variable.
fn bv64_var(name: &str) -> Expr {
    Expr::var(name, Sort::bitvec(64))
}

/// Helper: creates a Bool variable.
fn bool_var(name: &str) -> Expr {
    Expr::var(name, Sort::bool())
}

/// Helper: finds relation by name, panicking with a descriptive message on failure.
fn find_relation<'a>(vc: &'a ChcVc, name: &str) -> &'a RelationDecl {
    vc.relations
        .iter()
        .find(|r| r.name == name)
        .unwrap_or_else(|| panic!("relation {name} not found in VC"))
}

fn assert_error_rule_dropped(vc: &ChcVc, reason: &str) {
    assert!(
        vc.rules.iter().all(|r| r.head.name.as_str() != "error"),
        "{reason}: false-body error rule should be dropped"
    );
}

#[test]
fn test_single_constant_position_removed() {
    // R(x, y) where y is always #x4 across all rules targeting R.
    // After propagation, R should have arity 1.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("R", vec![Sort::bitvec(64), Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → R(x=0, y=4)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("R", vec![bv64(0), bv64(4)]),
    ));

    // R(x, y) → R(x+1, y=4) with constraint x_out = x + 1
    let x = bv64_var("x");
    let y = bv64_var("y");
    let x_out = bv64_var("x_out");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("R", vec![x.clone(), y])),
            vec![x_out.clone().eq(x.bvadd(bv64(1)))],
        ),
        RelationApp::new("R", vec![x_out, bv64(4)]),
    ));

    let stripped = propagate_constants(&mut vc);
    assert!(stripped > 0, "should strip at least one position");

    // R should now have arity 1 (only x, y removed).
    let r_decl = find_relation(&vc, "R");
    assert_eq!(r_decl.arity(), 1, "R should have arity 1 after removing constant y");
}

#[test]
fn test_identity_chain_propagation() {
    // Simulates the test_nonnull_dangling pattern:
    // bb0: _9 = #x4, bb1: _14 = _9, bb2: _10 = _14
    // After propagation, all three positions should collapse.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("bb2", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(_9=#x4)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(4)]),
    ));

    // bb0(_9) with constraint _14 = _9 → bb1(_14)
    let v9 = bv64_var("_9");
    let v14 = bv64_var("_14");
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![v9.clone()])), vec![v14.clone().eq(v9)]),
        RelationApp::new("bb1", vec![v14]),
    ));

    // bb1(_14) with constraint _10 = _14 → bb2(_10)
    let v14_b = bv64_var("_14");
    let v10 = bv64_var("_10");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![v14_b.clone()])),
            vec![v10.clone().eq(v14_b)],
        ),
        RelationApp::new("bb2", vec![v10]),
    ));

    // bb2(_10) with _10 == 0 → error
    let v10_b = bv64_var("_10");
    let is_zero = bool_var("_is_zero");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb2", vec![v10_b.clone()])),
            vec![is_zero.eq(v10_b.eq(bv64(0)))],
        ),
        RelationApp::nullary("error"),
    ));

    let stripped = propagate_constants(&mut vc);

    // All three relations should have their constant position removed.
    assert!(stripped >= 3, "should strip at least 3 positions, got {stripped}");
    for name in &["bb0", "bb1", "bb2"] {
        let decl = find_relation(&vc, name);
        assert_eq!(decl.arity(), 0, "relation {name} should have arity 0 after chain propagation");
    }
}

#[test]
fn test_non_constant_position_preserved() {
    // R(x, y) where x varies across rules — should not be removed.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("R", vec![Sort::bitvec(64), Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("R", vec![bv64(0), bv64(4)]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("R", vec![bv64(1), bv64(4)]),
    ));

    let stripped = propagate_constants(&mut vc);

    let r_decl = find_relation(&vc, "R");
    assert_eq!(r_decl.arity(), 1, "R should have arity 1 (x kept, y removed)");
    assert_eq!(stripped, 1);
}

#[test]
fn test_no_constants_is_noop() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("R", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = bv64_var("x");
    let y = bv64_var("y");

    vc.add_rule(Rule::new(RuleBody::new(None, vec![]), RelationApp::new("R", vec![x])));
    vc.add_rule(Rule::new(RuleBody::new(None, vec![]), RelationApp::new("R", vec![y])));

    let stripped = propagate_constants(&mut vc);
    assert_eq!(stripped, 0);
}

#[test]
fn test_empty_vc_is_noop() {
    let mut vc = ChcVc::new();
    let stripped = propagate_constants(&mut vc);
    assert_eq!(stripped, 0);
}

#[test]
fn test_mixed_constant_and_variable_head_args() {
    // R(x, y) where one rule has y=4 and another has y as variable.
    // y should NOT be removed.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("S", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("R", vec![Sort::bitvec(64), Sort::bitvec(64)]));

    let y = bv64_var("y");

    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![]),
        RelationApp::new("R", vec![bv64(0), bv64(4)]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("S", vec![y.clone()])), vec![]),
        RelationApp::new("R", vec![bv64(0), y]),
    ));

    let stripped = propagate_constants(&mut vc);

    let r_decl = find_relation(&vc, "R");
    assert_eq!(r_decl.arity(), 1, "R: only constant x removed, variable y kept");
    assert_eq!(stripped, 1);
}

#[test]
fn test_body_constraint_resolved_constant() {
    // Simulates the real CHC encoding pattern:
    // bb17 → bb10 where bb10's head arg is `_9__out` (a variable),
    // but the body has `(= _9__out #x4)`. The pass should resolve
    // `_9__out` through body constraints to detect the constant.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(_9__out) with body constraint (= _9__out #x4)
    let v9_out = bv64_var("_9__out");
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![v9_out.clone().eq(bv64(4))]),
        RelationApp::new("bb0", vec![v9_out]),
    ));

    let stripped = propagate_constants(&mut vc);
    assert!(stripped > 0, "should strip the constant position resolved through body constraint");
    let decl = find_relation(&vc, "bb0");
    assert_eq!(
        decl.arity(),
        0,
        "bb0 should have arity 0 after resolving body-constrained constant"
    );
}

#[test]
fn test_expression_level_constant_substitution() {
    // Models the test_nonnull_dangling assertion pattern:
    // bb0 passes _20 = #x4, and the error rule has constraint (= _20 #x0).
    // After propagation, (= _20 #x0) should become (= #x4 #x0) → false.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(_20 = #x4)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(4)]),
    ));

    // bb0(_20) with constraint (= _20 #x0) → error
    let v20 = bv64_var("_20");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![v20.clone()])),
            vec![v20.eq(bv64(0))], // Should become (= #x4 #x0) = false
        ),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    // The error rule's constraint (= _20 #x0) folds to (= #x4 #x0) -> false,
    // making the rule inert.
    assert_error_rule_dropped(&vc, "error rule after substituting _20 -> #x4");
}

#[test]
fn test_expression_substitution_in_nested_expr() {
    // Verifies substitution in nested expressions: (= _4 (= _20 #x0))
    // where _20 → #x4. After substitution: (= _4 false).
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(_20 = #x4)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(4)]),
    ));

    // bb0(_20) with constraint _4 = (_20 == #x0) → error
    let v20 = bv64_var("_20");
    let v4 = bool_var("_4");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![v20.clone()])),
            vec![
                v4.clone().eq(v20.eq(bv64(0))), // _4 = (_20 == 0) → _4 = false
                v4.not().not(),                 // (not (not _4))
            ],
        ),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    // After propagation, _20 → #x4 and _4 → false (via expression evaluation).
    // The constraint `_4 = (_20 == 0)` folds to `false = false` → `true`.
    // The constraint `(not (not _4))` folds to `(not (not false))` -> `false`.
    assert_error_rule_dropped(&vc, "error rule when nested expression folds false");
}

/// Helper: creates an Array(BV32, Bool) variable.
fn array_bv32_bool_var(name: &str) -> Expr {
    Expr::var(name, Sort::array(Sort::bitvec(32), Sort::bool()))
}

#[test]
fn test_const_array_position_removed() {
    // Models the obj_valid pattern: entry sets obj_valid = const_array(true),
    // and a self-loop passes it through unchanged while x varies.
    // The const_array(true) position should be detected as constant and removed,
    // but x (varying across rules) should be kept.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new(
        "bb0",
        vec![Sort::bitvec(64), Sort::array(Sort::bitvec(32), Sort::bool())],
    ));
    vc.add_relation(RelationDecl::nullary("error"));

    let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));

    // entry → bb0(x=0, obj_valid=const_array(true))
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(0), all_valid]),
    ));

    // bb0(x, obj_valid) → bb0(x+1, obj_valid) — self-loop with identity obj_valid.
    // x varies (0 from entry, x+1 from loop), obj_valid always const_array(true).
    let x = bv64_var("x");
    let ov = array_bv32_bool_var("obj_valid");
    let x_out = bv64_var("x_out");
    let ov_out = array_bv32_bool_var("obj_valid__out");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), ov.clone()])),
            vec![x_out.clone().eq(x.bvadd(bv64(1))), ov_out.clone().eq(ov)],
        ),
        RelationApp::new("bb0", vec![x_out, ov_out]),
    ));

    let stripped = propagate_constants(&mut vc);
    assert!(stripped > 0, "should strip const_array position");

    // bb0 should have obj_valid position removed but keep x.
    let bb0 = find_relation(&vc, "bb0");
    assert_eq!(bb0.arity(), 1, "bb0: obj_valid position should be removed, leaving only x");
}

#[test]
fn test_select_const_array_folds_to_value() {
    // Models the error rule pattern: error rule checks not(select(obj_valid, addr))
    // where obj_valid = const_array(true). After propagation:
    // select(const_array(true), addr) → true, not(true) → false.
    // The error rule constraint should contain BoolConst(false).
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::array(Sort::bitvec(32), Sort::bool())]));
    vc.add_relation(RelationDecl::nullary("error"));

    let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));

    // entry → bb0(obj_valid=const_array(true))
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![all_valid]),
    ));

    // bb0(obj_valid) with not(select(obj_valid, addr)) → error
    let ov = array_bv32_bool_var("obj_valid");
    let addr = Expr::var("addr", Sort::bitvec(32));
    let check = ov.clone().select(addr); // select(obj_valid, addr)
    let violation = check.not(); // not(select(obj_valid, addr))
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![ov])), vec![violation]),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    // The error rule had not(select(const_array(true), addr)) -> not(true) -> false.
    assert_error_rule_dropped(&vc, "error rule when const-array select folds false");
}

#[test]
fn test_const_array_not_propagated_when_stored() {
    // When a rule stores false into obj_valid (deallocation), the position
    // is NOT constant and should NOT be removed.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::array(Sort::bitvec(32), Sort::bool())]));
    vc.add_relation(RelationDecl::nullary("error"));

    let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));

    // Rule 1: entry → bb0(obj_valid=const_array(true))
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![all_valid.clone()]),
    ));

    // Rule 2: entry → bb0(obj_valid=store(const_array(true), id, false))
    // Simulates deallocation — obj_valid at position 0 is NOT the same constant.
    let freed = all_valid.store(Expr::bitvec_const(1, 32), Expr::bool_const(false));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![freed]),
    ));

    let stripped = propagate_constants(&mut vc);
    assert_eq!(stripped, 0, "obj_valid position should NOT be removed when values differ");

    let bb0 = find_relation(&vc, "bb0");
    assert_eq!(bb0.arity(), 1, "bb0 should retain obj_valid when it varies across rules");
}

#[test]
fn test_init_rule_and_flattening() {
    // Models the real entry rule pattern: Rule::init combines all constraints
    // into a single And(...) expression. Without And-flattening,
    // propagate_through_equalities can't see the nested Eq constraints.
    //
    // Entry rule: And(Eq(obj_valid, const_array(true)), Eq(_3, false))
    // → bb0(obj_valid_out, _3_out)
    // where obj_valid_out and _3_out are resolved through the And's Eq children.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new(
        "bb0",
        vec![Sort::array(Sort::bitvec(32), Sort::bool()), Sort::bool()],
    ));
    vc.add_relation(RelationDecl::nullary("error"));

    let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));
    let ov_out = array_bv32_bool_var("obj_valid__out");
    let v3_out = bool_var("_3__out");

    // Simulate Rule::init: constraints combined with And.
    let combined = ov_out.clone().eq(all_valid).and(v3_out.clone().eq(Expr::bool_const(false)));
    vc.add_rule(Rule::init(combined, RelationApp::new("bb0", vec![ov_out, v3_out])));

    // Error rule: bb0(obj_valid, _3) with not(select(obj_valid, addr)) → error
    let ov = array_bv32_bool_var("obj_valid");
    let v3 = bool_var("_3");
    let addr = Expr::var("addr", Sort::bitvec(32));
    let violation = ov.clone().select(addr).not();
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![ov, v3])), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = propagate_constants(&mut vc);
    assert!(stripped > 0, "should propagate constants from And-wrapped init rule constraints");

    // bb0 should have both positions removed (both are constant).
    let bb0 = find_relation(&vc, "bb0");
    assert_eq!(bb0.arity(), 0, "bb0: both obj_valid and _3 should be propagated from init rule");

    // Error rule had not(select(const_array(true), addr)) -> not(true) -> false.
    assert_error_rule_dropped(&vc, "error rule after And-flattened constant propagation");
}

#[test]
fn test_bvashr_constrained_var_not_propagated() {
    // Regression test for #3398: BvAShr was not handled by collect_constraint_vars,
    // causing variables inside BvAShr to be falsely classified as "unconstrained".
    //
    // x__out appears inside BvAShr(x__out, #x1) — it IS constrained.
    // Even though base var x is constant #x4, x__out must NOT be propagated.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(x=#x4)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(4)]),
    ));

    // bb0(x) → bb1(x__out) with constraint: shift_result = bvashr(x__out, #x1).
    // x__out is constrained by the BvAShr — must not be falsely propagated.
    let x = bv64_var("x");
    let x_out = bv64_var("x__out");
    let shift_result = bv64_var("shift_result");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x])),
            vec![shift_result.eq(x_out.clone().bvashr(bv64(1)))],
        ),
        RelationApp::new("bb1", vec![x_out]),
    ));

    propagate_constants(&mut vc);

    // bb0 should be stripped (x is constant #x4), but bb1 must keep its position
    // because x__out is constrained by BvAShr, not an identity pass-through.
    let bb0 = find_relation(&vc, "bb0");
    assert_eq!(bb0.arity(), 0, "bb0: constant x should be stripped");
    let bb1 = find_relation(&vc, "bb1");
    assert_eq!(bb1.arity(), 1, "bb1: x__out is constrained by BvAShr, must not be propagated");
}

#[test]
fn test_datatype_constructor_arg_propagated() {
    // Updated for #3405: DatatypeConstructor arguments are value-defining, not
    // value-restricting. A variable appearing only as a DT field is unconstrained
    // — the constructor wraps the value but does not restrict what the variable
    // can be. When the base variable (x) is a known constant, the __out variable
    // (x__out) should be propagated through DT constructors.
    //
    // Originally from #3398 (expected arity=1), corrected after #3405 showed
    // that blocking propagation through DT constructors caused -14 PROOF
    // regression on iterator harnesses.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(x=#x10)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(16)]),
    ));

    // bb0(x) → bb1(x__out) with constraint:
    // wrapped = DatatypeConstructor("Option", "Some", [x__out], option_sort).
    // x__out is NOT constrained by the constructor — it freely receives
    // propagated constants (wrapped_var is unconstrained, so the Eq is
    // trivially satisfiable for any x__out).
    let x = bv64_var("x");
    let x_out = bv64_var("x__out");
    let option_sort = Sort::enum_type(
        "Option",
        vec![("Some", vec![("val", Sort::bitvec(64))]), ("None", vec![] as Vec<(&str, Sort)>)],
    );
    let wrapped =
        Expr::datatype_constructor("Option", "Some", vec![x_out.clone()], option_sort.clone());
    let wrapped_var = Expr::var("wrapped", option_sort);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x])), vec![wrapped_var.eq(wrapped)]),
        RelationApp::new("bb1", vec![x_out]),
    ));

    propagate_constants(&mut vc);

    // bb1 arity drops to 0: x__out is unconstrained by DT constructor and gets
    // propagated to the known constant value of x (#x10).
    let bb1 = find_relation(&vc, "bb1");
    assert_eq!(
        bb1.arity(),
        0,
        "bb1: x__out inside DatatypeConstructor is unconstrained, should be propagated"
    );
}

#[test]
fn test_dt_arg_constrained_outside_dt() {
    // #3398: x__out appears both inside DatatypeConstructor AND in an Eq
    // constraint outside DT context. The Eq makes x__out genuinely constrained,
    // so propagation should NOT happen.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(x=#x10)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(16)]),
    ));

    // bb0(x) → bb1(x__out) with TWO constraints:
    // 1. wrapped = DatatypeConstructor("Some", [x__out]) — DT context
    // 2. Eq(x__out, other_var) — non-DT context, genuinely constraining
    let x = bv64_var("x");
    let x_out = bv64_var("x__out");
    let other_var = bv64_var("other");
    let option_sort = Sort::enum_type(
        "Option",
        vec![("Some", vec![("val", Sort::bitvec(64))]), ("None", vec![] as Vec<(&str, Sort)>)],
    );
    let wrapped =
        Expr::datatype_constructor("Option", "Some", vec![x_out.clone()], option_sort.clone());
    let wrapped_var = Expr::var("wrapped", option_sort);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x])),
            vec![wrapped_var.eq(wrapped), x_out.clone().eq(other_var)],
        ),
        RelationApp::new("bb1", vec![x_out]),
    ));

    propagate_constants(&mut vc);

    // bb1 arity stays 1: x__out is constrained by the Eq (non-DT context).
    let bb1 = find_relation(&vc, "bb1");
    assert_eq!(
        bb1.arity(),
        1,
        "bb1: x__out appears in Eq outside DT context, must not be propagated"
    );
}

#[test]
fn test_dt_constructor_falls_back_on_bv_encoded_enum_arg() {
    // #3768: const-prop can substitute an enum-typed field with its BV encoding.
    // Rebuilding the outer constructor with that BV term would produce malformed
    // SMT (`Wrapper_mk ((_ BitVec 10))`) even though the field expects Bound_u8.
    let bound_sort = Sort::enum_type(
        "Bound_u8",
        vec![
            ("Included", vec![("value", Sort::bitvec(8))]),
            ("Excluded", vec![("value", Sort::bitvec(8))]),
            ("Unbounded", vec![] as Vec<(&str, Sort)>),
        ],
    );
    let wrapper_sort = Sort::struct_type("Wrapper_Bound_u8", [("fld_0", bound_sort.clone())]);

    let inner = Expr::var("inner", bound_sort);
    let wrapper = Expr::datatype_constructor(
        "Wrapper_Bound_u8",
        "Wrapper_Bound_u8_mk",
        vec![inner],
        wrapper_sort,
    );

    let mut known = HashMap::new();
    known.insert("inner".to_string(), Expr::bitvec_const(0i64, 10));

    let result = substitute_vars(&wrapper, &known);

    assert_eq!(
        result, wrapper,
        "DatatypeConstructor must keep the original field when substitution changes the field sort"
    );
}

#[test]
fn test_dt_constructor_keeps_safe_matching_arg_substitutions() {
    let option_sort = Sort::enum_type(
        "Option_u64",
        vec![("Some", vec![("value", Sort::bitvec(64))]), ("None", vec![] as Vec<(&str, Sort)>)],
    );
    let wrapper_sort = Sort::struct_type("Wrapper_Option_u64", [("fld_0", option_sort.clone())]);

    let inner = Expr::var("inner", option_sort.clone());
    let wrapper = Expr::datatype_constructor(
        "Wrapper_Option_u64",
        "Wrapper_Option_u64_mk",
        vec![inner],
        wrapper_sort.clone(),
    );
    let some = Expr::datatype_constructor(
        "Option_u64",
        "Some",
        vec![Expr::bitvec_const(7i64, 64)],
        option_sort,
    );

    let mut known = HashMap::new();
    known.insert("inner".to_string(), some.clone());

    let result = substitute_vars(&wrapper, &known);
    let expected = Expr::datatype_constructor(
        "Wrapper_Option_u64",
        "Wrapper_Option_u64_mk",
        vec![some],
        wrapper_sort,
    );

    assert_eq!(
        result, expected,
        "DatatypeConstructor should still substitute args whose sorts match the field sort"
    );
}

#[test]
fn test_dt_selector_beta_reduction_matches_constructor_name() {
    // #3489: DatatypeSelector beta-reduction must match on constructor_name,
    // not iterate all constructors. With two constructors that share field names
    // at different indices, the old code could return the wrong arg.
    //
    // Enum E:
    //   A(x: BV64, y: BV64)  — field "x" at index 0
    //   B(y: BV64, x: BV64)  — field "x" at index 1
    //
    // sel_x(B(10, 20)) should return 20 (index 1 in B), not 10 (index 0 in A).
    let e_sort = Sort::enum_type(
        "E",
        vec![
            ("A", vec![("x", Sort::bitvec(64)), ("y", Sort::bitvec(64))]),
            ("B", vec![("y", Sort::bitvec(64)), ("x", Sort::bitvec(64))]),
        ],
    );

    // known = { "v" => B(10, 20) }
    let b_ctor = Expr::datatype_constructor(
        "E",
        "B",
        vec![Expr::bitvec_const(10i64, 64), Expr::bitvec_const(20i64, 64)],
        e_sort.clone(),
    );
    let mut known = HashMap::new();
    known.insert("v".to_string(), b_ctor);

    // Expression: sel_x(v)  — DatatypeSelector selecting "x" from Var("v")
    let v = Expr::var("v", e_sort);
    let selector = v.field_select("E", "x", Sort::bitvec(64));

    let result = substitute_vars(&selector, &known);

    // With fix: matches B constructor, finds "x" at index 1, returns 20.
    // Without fix: iterates constructors, finds "x" at index 0 in A, returns 10.
    assert_eq!(
        result,
        Expr::bitvec_const(20i64, 64),
        "DatatypeSelector beta-reduction must use constructor_name to find correct field index"
    );
}

#[test]
fn test_store_eq_identical_folded_to_true() {
    // #3500: Eq(Store(...), Store(...)) with structurally identical ASTs
    // folds to true. Identical AST ⇒ identical semantics, always sound.
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::bool());
    let base = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));
    let store_a = base.clone().store(Expr::bitvec_const(0i64, 32), Expr::bool_const(false));
    let store_b = base.store(Expr::bitvec_const(0i64, 32), Expr::bool_const(false));

    let mut known = HashMap::new();
    known.insert("a".to_string(), store_a);
    known.insert("b".to_string(), store_b);

    let a_var = Expr::var("a", arr_sort.clone());
    let b_var = Expr::var("b", arr_sort);
    let eq_expr = a_var.eq(b_var);

    let result = substitute_vars(&eq_expr, &known);

    assert!(
        matches!(result.value(), ay_bindings::ExprValue::BoolConst(true)),
        "Eq on structurally identical Store expressions should fold to true"
    );
}

#[test]
fn test_store_eq_different_not_folded() {
    // #3479/#3500: Eq(Store(...), Store(...)) with different structure must
    // NOT be folded — structural inequality doesn't imply semantic inequality.
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::bool());
    let base = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));
    let store_a = base.clone().store(Expr::bitvec_const(0i64, 32), Expr::bool_const(false));
    let store_b = base.store(Expr::bitvec_const(1i64, 32), Expr::bool_const(false));

    let mut known = HashMap::new();
    known.insert("a".to_string(), store_a);
    known.insert("b".to_string(), store_b);

    let a_var = Expr::var("a", arr_sort.clone());
    let b_var = Expr::var("b", arr_sort);
    let eq_expr = a_var.eq(b_var);

    let result = substitute_vars(&eq_expr, &known);

    assert!(
        !matches!(result.value(), ay_bindings::ExprValue::BoolConst(_)),
        "Eq on structurally different Store expressions must not be folded to bool"
    );
}

#[test]
fn test_out_var_invariant_unconstrained_propagated() {
    // #3478: Document the __out naming invariant and its soundness implications.
    //
    // When X__out is unconstrained in the rule body AND X is a known constant,
    // propagate_to_unconstrained_out_vars() assumes X__out == X (identity
    // pass-through) and propagates the constant.
    //
    // This test verifies the propagation behavior and documents that correctness
    // depends on the invariant: __out variables are ONLY created via
    // push_state_var_pair(in_name, in_name + "__out", sort).
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(x=#x7)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(7)]),
    ));

    // bb0(x) → bb1(x__out) with NO constraints on x__out.
    // The __out invariant says: unconstrained x__out is identity of x.
    // Therefore x__out should receive the constant value #x7.
    let x = bv64_var("x");
    let x_out = bv64_var("x__out");
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x])), vec![]),
        RelationApp::new("bb1", vec![x_out]),
    ));

    // bb1(x__out) ∧ x__out != #x7 → error()
    // If propagation works correctly, x__out becomes #x7, the Eq(#x7, #x7)
    // in the Not folds to true, Not(true) folds to false, and the error rule
    // is eliminated.
    let y = bv64_var("y");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![y.clone()])),
            vec![Expr::not(y.eq(bv64(7)))],
        ),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    // bb1 arity drops to 0: x__out was propagated to constant #x7.
    let bb1 = find_relation(&vc, "bb1");
    assert_eq!(
        bb1.arity(),
        0,
        "bb1: unconstrained x__out should be propagated via __out identity invariant"
    );

    assert_error_rule_dropped(&vc, "error rule after __out identity propagation");
}

#[test]
fn test_out_var_constrained_not_propagated() {
    // #3478: Counterpart to the above — when x__out IS constrained (appears in
    // a body constraint that references a non-constant variable), propagation
    // via the __out identity assumption must NOT happen.
    //
    // Note: constraints like `x__out = x + 1` where `x` is constant will still
    // resolve via arithmetic folding — that's correct constant propagation through
    // the constraint itself, not the __out identity assumption. To test the identity
    // assumption guard, we constrain x__out with a non-resolvable variable.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64), Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb0(x=#x7, y=symbolic)
    // y is symbolic (non-constant) across rules, so it blocks propagation.
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv64(7), bv64_var("init_y")]),
    ));

    // bb0(x, y) → bb1(x__out) with constraint: x__out = y.
    // x__out is constrained by the Eq with non-constant y — the __out identity
    // assumption must NOT apply.
    let x = bv64_var("x");
    let y = bv64_var("y");
    let x_out = bv64_var("x__out");
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x, y.clone()])), vec![x_out.clone().eq(y)]),
        RelationApp::new("bb1", vec![x_out]),
    ));

    propagate_constants(&mut vc);

    // bb1 arity stays 1: x__out is constrained by an Eq with non-constant y,
    // so neither the __out identity assumption nor arithmetic folding applies.
    let bb1 = find_relation(&vc, "bb1");
    assert_eq!(bb1.arity(), 1, "bb1: x__out constrained by non-constant y must NOT be propagated");
}

#[test]
fn test_ite_constant_condition_folding() {
    // #3479: Ite with constant condition should be folded.
    // Ite(true, then, else) → then
    // Ite(false, then, else) → else
    let mut known = HashMap::new();
    known.insert("c".to_string(), Expr::bool_const(true));

    let c = Expr::var("c", Sort::bool());
    let then_val = Expr::bitvec_const(42i64, 64);
    let else_val = Expr::bitvec_const(99i64, 64);
    let ite_expr = Expr::ite(c, then_val.clone(), else_val.clone());

    let result = substitute_vars(&ite_expr, &known);
    assert_eq!(result, then_val, "Ite(true, 42, 99) should fold to 42");

    // Test false condition.
    let mut known_false = HashMap::new();
    known_false.insert("c".to_string(), Expr::bool_const(false));
    let c2 = Expr::var("c", Sort::bool());
    let ite_false = Expr::ite(c2, Expr::bitvec_const(42i64, 64), else_val.clone());

    let result_false = substitute_vars(&ite_false, &known_false);
    assert_eq!(result_false, else_val, "Ite(false, 42, 99) should fold to 99");
}

#[test]
fn test_store_cross_sort_const_prop_does_not_panic() {
    // #3991: Const-prop can substitute a DT-sorted variable with a BV constant
    // from a cross-sort equality (e.g., RawWaker var = BV64 fn-ptr identity).
    // Without the sort guard in fold_store, rebuilding
    // store(Array<BV64, RawWaker>, idx, BV64) panics with "Mismatch element sort".
    let raw_waker_sort =
        Sort::struct_type("RawWaker", [("data", Sort::bitvec(64)), ("vtable", Sort::bitvec(64))]);
    let arr_sort = Sort::array(Sort::bitvec(64), raw_waker_sort.clone());

    let arr = Expr::var("mem_RawWaker", arr_sort);
    let idx = Expr::bitvec_const(1i64, 64);
    let val = Expr::var("waker_val", raw_waker_sort);
    let store_expr = arr.store(idx, val);

    // Simulate cross-sort pollution: const-prop maps the DT variable to BV64.
    let mut known = HashMap::new();
    known.insert("waker_val".to_string(), Expr::bitvec_const(0xDEADBEEFu64 as i64, 64));

    // Must not panic — sort guard falls back to original value expression.
    let result = substitute_vars(&store_expr, &known);

    // The result should still be a Store with the original (unsubstituted) value,
    // since the substituted value has the wrong sort.
    assert!(
        matches!(result.value(), ay_bindings::ExprValue::Store { .. }),
        "fold_store sort guard should produce a Store, not panic"
    );
}

#[test]
fn test_extract_cross_sort_const_prop_does_not_panic() {
    // Part of #4187: const-prop can substitute a BV-valued local used by
    // extract(...) with a memory array expression. Rebuilding extract on the
    // substituted term panics in ay-bindings; keep the original extract.
    let wide = Expr::var("wide", Sort::bitvec(128));
    let original = wide.clone().extract(63, 0);

    let mut known = HashMap::new();
    known.insert("wide".to_string(), Expr::const_array(Sort::bitvec(64), Expr::bool_const(false)));

    let result = substitute_vars(&original, &known);
    assert_eq!(result, original, "cross-sort extract substitution must fall back");
}

#[test]
fn test_select_cross_sort_const_prop_does_not_panic() {
    // Part of #4187: const-prop can substitute an Array<BV64, Bool> variable
    // with an array using a different index sort. Rebuilding select(...) on
    // those children panics in ay-bindings; keep the original select.
    let arr = Expr::var("arr", Sort::array(Sort::bitvec(64), Sort::bool()));
    let idx = Expr::bitvec_const(1i64, 64);
    let original = arr.clone().select(idx.clone());

    let mut known = HashMap::new();
    known.insert("arr".to_string(), Expr::const_array(Sort::bool(), Expr::bool_const(false)));

    let result = substitute_vars(&original, &known);
    assert_eq!(result, original, "cross-sort select substitution must fall back");
}

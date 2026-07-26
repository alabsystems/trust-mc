// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_false_body_rules_are_eliminated_except_error_heads() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::nullary("dead"));
    vc.add_relation(RelationDecl::nullary("error"));

    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![Expr::bool_const(false)]),
        RelationApp::nullary("dead"),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![Expr::bool_const(false)]),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    assert!(
        vc.rules.iter().all(|rule| rule.head.name.as_str() != "dead"),
        "non-query false-bodied rule should still be eliminated"
    );
    // Task #76 (refined at the v41 gate): only the CANONICAL discharge shape
    // — no body relation, literal-false constraint, as emitted by
    // `replace_with_unsat_error_obligation` — is retained. A relation-bodied
    // error rule whose constraints evaluate to false is an infeasible edge
    // and is eliminated as before (retaining those sent the solver into
    // re-deriving infeasibility: offset-bytes-overflow 272ms -> 59.8s).
    assert!(
        vc.rules.iter().all(|rule| rule.head.name.as_str() != "error"),
        "relation-bodied false error rule is an infeasible edge — eliminated"
    );

    // The canonical discharge obligation itself must survive.
    let mut vc2 = ChcVc::new();
    vc2.add_relation(RelationDecl::nullary("error"));
    vc2.add_rule(Rule::new(
        RuleBody::new(None, vec![Expr::bool_const(false)]),
        RelationApp::nullary("error"),
    ));
    propagate_constants(&mut vc2);
    assert!(
        vc2.rules.iter().any(|rule| rule.head.name.as_str() == "error"),
        "canonical (=> false error) discharge obligation must be RETAINED"
    );
}

#[test]
fn test_false_body_custom_query_target_is_eliminated() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::nullary("violation"));
    vc.query = crate::chc::ChcQuery::new().with_target("violation");

    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![Expr::bool_const(false)]),
        RelationApp::nullary("violation"),
    ));

    propagate_constants(&mut vc);

    assert!(
        vc.rules.iter().all(|rule| rule.head.name.as_str() != "violation"),
        "custom query-target false-bodied rule should be eliminated"
    );
}

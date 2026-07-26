// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::chc::{
    ChcProperty, ChcQuery, ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl,
};
use crate::violation::PropertyKind;
use ay_bindings::{Expr, Sort};

#[test]
fn test_prune_dead_identity_scalars_removes_identity_only_pair() {
    let mut vc = ChcVc::new();
    for name in ["dead", "dead__out", "live", "live__out"] {
        vc.add_var(VarDecl::new(name, Sort::int()));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int(), Sort::int()]));

    let dead = Expr::var("dead", Sort::int());
    let dead_out = Expr::var("dead__out", Sort::int());
    let live = Expr::var("live", Sort::int());
    let live_out = Expr::var("live__out", Sort::int());

    let init = Rule::new(
        RuleBody::new(
            None,
            vec![
                Expr::eq(dead_out.clone(), Expr::int_const(0)),
                Expr::eq(live_out.clone(), Expr::int_const(0)),
            ],
        ),
        RelationApp::new("bb0", vec![dead_out.clone(), live_out.clone()]),
    );
    vc.add_rule(init);

    let step = Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![dead.clone(), live.clone()])),
            vec![
                Expr::eq(dead_out.clone(), dead),
                Expr::eq(live_out.clone(), live.int_add(Expr::int_const(1))),
            ],
        ),
        RelationApp::new("bb1", vec![dead_out, live_out]),
    );
    vc.add_rule(step);

    assert_eq!(vc.prune_dead_identity_scalars(), 1);
    assert_eq!(vc.relations[0].arity(), 1);
    assert_eq!(vc.relations[1].arity(), 1);
    assert_eq!(vc.rules[0].head.args.len(), 1);
    assert_eq!(vc.rules[1].body.relation.as_ref().expect("bb0").args.len(), 1);
    assert_eq!(vc.rules[1].head.args.len(), 1);
}

#[test]
fn test_prune_dead_identity_scalars_removes_init_select_write_only_array() {
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
    let int_sort = Sort::int();
    let mut vc = ChcVc::new();
    for (name, sort) in [
        ("obj_size", arr_sort.clone()),
        ("obj_size__out", arr_sort.clone()),
        ("live", int_sort.clone()),
        ("live__out", int_sort.clone()),
    ] {
        vc.add_var(VarDecl::new(name, sort));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort.clone(), int_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort.clone(), int_sort.clone()]));

    let obj_size = Expr::var("obj_size", arr_sort.clone());
    let obj_size_out = Expr::var("obj_size__out", arr_sort.clone());
    let live = Expr::var("live", int_sort.clone());
    let live_out = Expr::var("live__out", int_sort.clone());
    let obj_zero = Expr::bitvec_const(0i64, 32);
    let obj_one = Expr::bitvec_const(1i64, 32);
    let size_8 = Expr::bitvec_const(8i64, 32);
    let size_16 = Expr::bitvec_const(16i64, 32);

    vc.add_rule(Rule::new(
        RuleBody::new(
            None,
            vec![
                obj_size.clone().select(obj_zero).eq(size_8.clone()),
                live.clone().eq(Expr::int_const(0)),
            ],
        ),
        RelationApp::new("bb0", vec![obj_size.clone(), live.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![obj_size.clone(), live.clone()])),
            vec![
                obj_size_out.clone().eq(obj_size.store(obj_one, size_16)),
                live_out.clone().eq(live.int_add(Expr::int_const(1))),
            ],
        ),
        RelationApp::new("bb1", vec![obj_size_out, live_out]),
    ));

    assert_eq!(vc.prune_dead_identity_scalars(), 1);
    assert_eq!(vc.relations[0].arity(), 1);
    assert_eq!(vc.relations[1].arity(), 1);
    assert_eq!(vc.rules[0].head.args.len(), 1);
    assert_eq!(vc.rules[1].body.relation.as_ref().expect("bb0").args.len(), 1);
    assert_eq!(vc.rules[1].head.args.len(), 1);
}

#[test]
fn test_prune_dead_identity_scalars_keeps_noninit_array_select_guard() {
    let arr_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
    let mut vc = ChcVc::new();
    for name in ["arr", "arr__out"] {
        vc.add_var(VarDecl::new(name, arr_sort.clone()));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort.clone()]));

    let arr = Expr::var("arr", arr_sort.clone());
    let arr_out = Expr::var("arr__out", arr_sort);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![arr.clone()])),
            vec![
                arr.clone().select(Expr::bitvec_const(0i64, 32)).eq(Expr::bitvec_const(8i64, 32)),
                arr_out.clone().eq(arr),
            ],
        ),
        RelationApp::new("bb1", vec![arr_out]),
    ));

    assert_eq!(vc.prune_dead_identity_scalars(), 0);
    assert_eq!(vc.relations[0].arity(), 1);
    assert_eq!(vc.relations[1].arity(), 1);
}

#[test]
fn test_prune_dead_vars_removes_false_conjunct_rules() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("stale_safety", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::nullary("dead"));
    vc.query = crate::chc::ChcQuery::new().with_target("error");

    let x = Expr::var("x", Sort::int());
    let stale_safety = Expr::var("stale_safety", Sort::int());
    let impossible_safety_check =
        Expr::and_many(vec![stale_safety.int_gt(Expr::int_const(0)), Expr::bool_const(false)]);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![impossible_safety_check],
        ),
        RelationApp::nullary("error"),
    ));

    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![Expr::bool_const(false)]),
        RelationApp::nullary("dead"),
    ));

    let live_guard = x.clone().int_gt(Expr::int_const(0));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![live_guard]),
        RelationApp::new("bb0", vec![x]),
    ));

    let stripped = vc.prune_dead_vars_and_constraints();

    assert!(stripped >= 2, "false-premise rules should be stripped");
    assert_eq!(vc.rules.len(), 1, "only the transition should remain");
    assert!(vc.rules.iter().all(|rule| rule.head.name != "error"));
    assert!(vc.rules.iter().all(|rule| rule.head.name != "dead"));
    assert!(
        vc.vars().iter().all(|var| &*var.name != "stale_safety"),
        "vars referenced only by a dropped query rule should be removed"
    );
}

/// Builds the shared VC shape for the per-property error-head protection
/// tests: `true → bb4(x)`, a guarded error rule
/// `bb4(x) ∧ i < 8 ∧ j > i → error_p2` whose guard vars are rule-local
/// (in no relation signature), and the BSEM-18 bridge `error_p2 → error`.
fn per_property_guard_vc() -> ChcVc {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("__kani_any_inline_i", Sort::int()));
    vc.add_var(VarDecl::new("__kani_any_inline_j", Sort::int()));
    vc.add_relation(RelationDecl::new("bb4", vec![Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error_p2"));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = ChcQuery::new().with_target("error");

    let x = Expr::var("x", Sort::int());
    let fresh_i = Expr::var("__kani_any_inline_i", Sort::int());
    let fresh_j = Expr::var("__kani_any_inline_j", Sort::int());

    vc.add_rule(Rule::new(RuleBody::new(None, vec![]), RelationApp::new("bb4", vec![x.clone()])));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb4", vec![x])),
            vec![fresh_i.clone().int_lt(Expr::int_const(8)), fresh_j.int_gt(fresh_i)],
        ),
        RelationApp::nullary("error_p2"),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("error_p2")), vec![]),
        RelationApp::nullary("error"),
    ));
    vc
}

fn assert_per_property_guard_survives(vc: &ChcVc) {
    let error_rule = vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "error_p2")
        .expect("error_p2 rule must survive");
    assert_eq!(
        error_rule.body.constraints.len(),
        2,
        "per-property error rule must keep its full ¬safety guard; stripping \
         it fabricates an unconditional `bb4 → error_p2` counterexample edge"
    );
    assert!(
        vc.vars().iter().any(|var| &*var.name == "__kani_any_inline_i"),
        "guard vars must keep their declare-var entries"
    );
    assert!(
        vc.vars().iter().any(|var| &*var.name == "__kani_any_inline_j"),
        "guard vars must keep their declare-var entries"
    );
}

/// STAGE 1 regression test (#4278 generalization, BSEM-18): a rule headed by
/// a per-property `error_p{N}` relation registered in `vc.properties` keeps
/// its guard even though the guard vars appear in no relation signature
/// (Rotate/bitreverse spurious-FP cluster).
#[test]
fn test_prune_dead_vars_keeps_per_property_error_rule_guard() {
    let mut vc = per_property_guard_vc();
    vc.add_property(ChcProperty {
        id: 2,
        kind: PropertyKind::MemorySafety,
        bb: 4,
        relation: "error_p2".to_owned(),
        message: None,
        location: None,
        approximation_dependent: None,
    });

    vc.prune_dead_vars_and_constraints();

    assert_per_property_guard_survives(&vc);
}

/// STAGE 1: same as above, but with NO `properties` metadata — the protected
/// head must be discovered structurally from the constraint-free nullary
/// bridge rule `error_p2 → error` (covers hand-built / ingested VCs).
#[test]
fn test_prune_dead_vars_keeps_error_rule_guard_via_bridge_shape() {
    let mut vc = per_property_guard_vc();

    vc.prune_dead_vars_and_constraints();

    assert_per_property_guard_survives(&vc);
}

/// STAGE 2 regression test (transitive liveness closure): a 3-hop `__mid_bb`
/// equality chain inside a transition rule that feeds an error rule must
/// survive whole. `fragment_compose` emits such chains for loop frame
/// composition; the historical one-hop keep rule kept only the chain ends
/// (`m1 = x` via the essential var `x`, `m3 = m2` via the essential head arg
/// `m3`) and cut the interior hop `m2 = m1`, leaving the loop head entered
/// with havocked state (ctlz/cttz fabricated-counterexample cluster).
#[test]
fn test_prune_dead_vars_keeps_mid_equality_chain_feeding_error_rule() {
    let mut vc = ChcVc::new();
    for name in ["x", "y", "__mid_bb1", "__mid_bb2", "__mid_bb3"] {
        vc.add_var(VarDecl::new(name, Sort::int()));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error_p0"));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = ChcQuery::new().with_target("error");
    vc.add_property(ChcProperty {
        id: 0,
        kind: PropertyKind::Assertion,
        bb: 1,
        relation: "error_p0".to_owned(),
        message: None,
        location: None,
        approximation_dependent: None,
    });

    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let m1 = Expr::var("__mid_bb1", Sort::int());
    let m2 = Expr::var("__mid_bb2", Sort::int());
    let m3 = Expr::var("__mid_bb3", Sort::int());

    // init: x = 5 → bb0(x)
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![Expr::eq(x.clone(), Expr::int_const(5))]),
        RelationApp::new("bb0", vec![x.clone()]),
    ));
    // transition with the 3-hop chain:
    // bb0(x) ∧ m1 = x ∧ m2 = m1 ∧ m3 = m2 → bb1(m3)
    // Only x (body app) and m3 (head app) are relation-app vars; m1 and m2
    // are interior hops.
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![Expr::eq(m1.clone(), x), Expr::eq(m2.clone(), m1), Expr::eq(m3.clone(), m2)],
        ),
        RelationApp::new("bb1", vec![m3]),
    ));
    // error rule: bb1(y) ∧ y > 9 → error_p0, bridged into error.
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![y.clone()])),
            vec![y.int_gt(Expr::int_const(9))],
        ),
        RelationApp::nullary("error_p0"),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("error_p0")), vec![]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.prune_dead_vars_and_constraints();

    assert_eq!(stripped, 0, "nothing here is dead — the chain is live");
    let transition =
        vc.rules.iter().find(|rule| rule.head.name == "bb1").expect("transition rule must survive");
    assert_eq!(
        transition.body.constraints.len(),
        3,
        "all three equality hops must survive; cutting an interior hop \
         havocs the successor block's entry state"
    );
    for name in ["__mid_bb1", "__mid_bb2", "__mid_bb3"] {
        assert!(
            vc.vars().iter().any(|var| &*var.name == name),
            "chain var {name} must keep its declare-var entry"
        );
    }
}

/// STAGE 2: the pass still performs its job — a chain of definitional dead
/// equalities (`stale_out = stale_mid + 2`, `stale_mid = stale_base + 1`)
/// fully disconnected from every relation app is stripped (one hop per
/// round), together with the declare-var entries.
#[test]
fn test_prune_dead_vars_strips_definitional_dead_equality_chain() {
    let mut vc = ChcVc::new();
    for name in ["x", "stale_base", "stale_mid", "stale_out"] {
        vc.add_var(VarDecl::new(name, Sort::int()));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));

    let x = Expr::var("x", Sort::int());
    let stale_base = Expr::var("stale_base", Sort::int());
    let stale_mid = Expr::var("stale_mid", Sort::int());
    let stale_out = Expr::var("stale_out", Sort::int());

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![
                x.clone().int_gt(Expr::int_const(0)),
                Expr::eq(stale_mid.clone(), stale_base.int_add(Expr::int_const(1))),
                Expr::eq(stale_out, stale_mid.int_add(Expr::int_const(2))),
            ],
        ),
        RelationApp::new("bb1", vec![x]),
    ));

    let stripped = vc.prune_dead_vars_and_constraints();

    assert_eq!(stripped, 2, "both dead definitional equalities must go");
    assert_eq!(vc.rules[0].body.constraints.len(), 1, "the live guard stays");
    for name in ["stale_base", "stale_mid", "stale_out"] {
        assert!(
            vc.vars().iter().all(|var| &*var.name != name),
            "stripped var {name} must lose its declare-var entry"
        );
    }
    assert!(vc.vars().iter().any(|var| &*var.name == "x"));
}

/// STAGE 2 (task-#57 guard): a disconnected but NON-definitional cluster —
/// here mutually-contradictory inequalities, i.e. a possibly-UNSAT cluster —
/// must be KEPT. Deleting it would weaken the rule (a vacuous rule would
/// start firing), which is exactly the missed-bug surface that sank the
/// previous attempt at this fix.
#[test]
fn test_prune_dead_vars_keeps_disconnected_unsat_cluster() {
    let mut vc = ChcVc::new();
    for name in ["x", "stale_a", "stale_b"] {
        vc.add_var(VarDecl::new(name, Sort::int()));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));

    let x = Expr::var("x", Sort::int());
    let stale_a = Expr::var("stale_a", Sort::int());
    let stale_b = Expr::var("stale_b", Sort::int());

    // stale_a > stale_b ∧ stale_b > stale_a is UNSAT: the rule is vacuous
    // and must STAY vacuous.
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![stale_a.clone().int_gt(stale_b.clone()), stale_b.int_gt(stale_a)],
        ),
        RelationApp::new("bb1", vec![x]),
    ));

    let stripped = vc.prune_dead_vars_and_constraints();

    assert_eq!(stripped, 0, "non-definitional disconnected constraints must be kept");
    assert_eq!(vc.rules[0].body.constraints.len(), 2);
}

#[test]
fn test_prune_dead_vars_deduplicates_rules_after_cleanup() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));

    let x = Expr::var("x", Sort::int());
    let live_guard = x.clone().int_gt(Expr::int_const(0));
    let from = RelationApp::new("bb0", vec![x.clone()]);
    let to = RelationApp::new("bb1", vec![x.clone()]);

    vc.add_rule(Rule::new(RuleBody::new(Some(from.clone()), vec![live_guard.clone()]), to.clone()));
    vc.add_rule(Rule::new(RuleBody::new(Some(from), vec![live_guard.clone()]), to));

    let stripped = vc.prune_dead_vars_and_constraints();

    assert_eq!(stripped, 1, "duplicate rule body should be stripped");
    assert_eq!(vc.rules.len(), 1, "duplicate Horn rule should be removed");
    let constraints: Vec<_> = vc.rules[0].body.constraints.iter().cloned().collect();
    assert_eq!(constraints, vec![live_guard]);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Part of #40: fragment-composition `__mid_bbN` array alias chains must not
//! defeat scalarization. Before the collapse pre-pass, a frame rule like
//! `bb1(mem) ∧ (= mem__mid_bb2 mem) → bb2(mem__mid_bb2)` left a whole-array
//! mention (`mem__mid_bb2`) that the residual fail-closed check treated as an
//! unconstrained free array, banning `mem` from scalarization in EVERY rule —
//! dragging Array-sorted params into all loop predicates (the ArrayParamLimit
//! PDR-stall class).

use super::super::collapse_mid_aliases::collapse_mid_aliases;
use super::super::rewrite::scalarize_vc;
use super::{arr_sort, bv32_sort, bv64_const, obj_size_sort};
use ay_bindings::Expr;
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

/// Two-rule VC: rule 0 does const-index work on `mem` (scalarizable);
/// rule 1 is a pure frame chain threading `mem` through a `__mid_bb2` alias.
fn build_mid_chain_vc(frame_constraints: Vec<Expr>, frame_head_arg: Expr) -> ChcVc {
    let mem_in = Expr::var("mem", arr_sort());
    let mem_out = Expr::var("mem__out", arr_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());
    let addr = bv64_const(0x10);

    let mut vc = ChcVc::new();
    for (name, sort) in [
        ("mem", arr_sort()),
        ("mem__out", arr_sort()),
        ("mem__mid_bb2", arr_sort()),
        ("x", bv32_sort()),
        ("x__out", bv32_sort()),
    ] {
        vc.add_var(VarDecl::new(name, sort));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb2", vec![arr_sort()]));

    // Rule 0: bb0(mem, x) ∧ mem__out = store(mem, 0x10, x) ∧ x__out = select(mem, 0x10)
    //         → bb1(mem__out, x__out)
    let store_constraint = mem_out.clone().eq(mem_in.clone().store(addr.clone(), x.clone()));
    let select_constraint = x_out.clone().eq(mem_in.clone().select(addr));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![mem_in.clone(), x.clone()])),
            vec![store_constraint, select_constraint],
        ),
        RelationApp::new("bb1", vec![mem_out, x_out]),
    ));

    // Rule 1: bb1(mem, x) ∧ <frame_constraints> → bb2(<frame_head_arg>)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![mem_in, x])), frame_constraints),
        RelationApp::new("bb2", vec![frame_head_arg]),
    ));
    vc
}

fn mid_identity() -> Expr {
    Expr::var("mem__mid_bb2", arr_sort()).eq(Expr::var("mem", arr_sort()))
}

#[test]
fn collapse_substitutes_mid_alias_and_drops_identity() {
    let mut vc = build_mid_chain_vc(vec![mid_identity()], Expr::var("mem__mid_bb2", arr_sort()));
    collapse_mid_aliases(&mut vc);

    let frame_rule = &vc.rules[1];
    // Identity conjunct dropped as tautological after substitution.
    assert_eq!(frame_rule.body.constraints.iter().count(), 0);
    // Head arg substituted to the canonical name.
    let head_arg = &frame_rule.head.args[0];
    assert_eq!(
        format!("{head_arg:?}").contains("mem__mid_bb2"),
        false,
        "mid alias must be substituted out of the head args"
    );
}

#[test]
fn mid_alias_chain_no_longer_bans_scalarization() {
    let mut vc = build_mid_chain_vc(vec![mid_identity()], Expr::var("mem__mid_bb2", arr_sort()));
    scalarize_vc(&mut vc);

    // Success criterion (#40): no relation keeps an Array-sorted parameter.
    for rel in &vc.relations {
        for sort in &rel.arg_sorts {
            assert!(
                !sort.is_array(),
                "relation {} still carries an Array-sorted param after scalarization",
                rel.name
            );
        }
    }
}

#[test]
fn non_identity_mid_definition_fails_closed() {
    // The mid var has a REAL definition (a store), so the rule must be left
    // untouched and the residual ban must keep `mem` un-scalarized (sound).
    let mem_in = Expr::var("mem", arr_sort());
    let mid = Expr::var("mem__mid_bb2", arr_sort());
    let store_def =
        mid.clone().eq(mem_in.clone().store(bv64_const(0x20), Expr::bitvec_const(7u64, 32)));
    let mut vc =
        build_mid_chain_vc(vec![store_def, mid_identity()], Expr::var("mem__mid_bb2", arr_sort()));
    let with_guard = vc.rules[1].body.constraints.iter().count();
    collapse_mid_aliases(&mut vc);
    assert_eq!(
        vc.rules[1].body.constraints.iter().count(),
        with_guard,
        "rule with a non-identity mid definition must be left untouched"
    );

    scalarize_vc(&mut vc);
    let bb2 = vc.relations.iter().find(|r| r.name == "bb2").expect("bb2 exists");
    assert!(
        bb2.arg_sorts.iter().any(|s| s.is_array()),
        "fail-closed: mem must stay un-scalarized when the mid var has a real definition"
    );
}

// ---------------------------------------------------------------------------
// Per-variable guard: one rule, one MODIFIED array and one FRAMED array
// ---------------------------------------------------------------------------

/// Everything the rule still spells, as one debug string: constraints, head
/// args and body-relation args. Used to assert that a name is GONE, which is
/// the property the residual-mention ban in `scalarize_vc` actually tests.
fn rule_text(vc: &ChcVc, rule_idx: usize) -> String {
    let rule = &vc.rules[rule_idx];
    let mut text = String::new();
    for constraint in rule.body.constraints.iter() {
        text.push_str(&format!("{constraint:?}"));
    }
    for arg in rule.head.args.iter() {
        text.push_str(&format!("{arg:?}"));
    }
    if let Some(body_rel) = &rule.body.relation {
        for arg in body_rel.args.iter() {
            text.push_str(&format!("{arg:?}"));
        }
    }
    text
}

/// Sorts of one relation's parameters, by name.
fn relation_sorts<'a>(vc: &'a ChcVc, name: &str) -> &'a [ay_bindings::Sort] {
    &vc.relations.iter().find(|r| r.name == name).expect("relation exists").arg_sorts
}

/// The shape fragment composition actually emits for a loop body that writes
/// memory: a NON-identity definition for the modified state var
/// (`mem__mid_bb2 = store(mem, ..)`) beside an identity frame constraint for the
/// var the block leaves alone (`sz__mid_bb2 = sz`).
///
/// `mem` must stay un-scalarized (its mid carries a real definition), and `sz`
/// must NOT be dragged down with it — the per-rule guard used to abandon this
/// whole rule, leaving `sz__mid_bb2` to trip the residual check.
fn build_modified_and_framed_vc() -> ChcVc {
    let mem = Expr::var("mem", arr_sort());
    let mem_out = Expr::var("mem__out", arr_sort());
    let sz = Expr::var("sz", obj_size_sort());
    let sz_out = Expr::var("sz__out", obj_size_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());

    let mut vc = ChcVc::new();
    for (name, sort) in [
        ("mem", arr_sort()),
        ("mem__out", arr_sort()),
        ("mem__mid_bb2", arr_sort()),
        ("sz", obj_size_sort()),
        ("sz__out", obj_size_sort()),
        ("sz__mid_bb2", obj_size_sort()),
        ("x", bv32_sort()),
        ("x__out", bv32_sort()),
    ] {
        vc.add_var(VarDecl::new(name, sort));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), obj_size_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), obj_size_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb2", vec![arr_sort(), obj_size_sort()]));

    // Rule 0: constant-index work on BOTH arrays, so both are candidates.
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![mem.clone(), sz.clone(), x.clone()])),
            vec![
                mem_out.clone().eq(mem.clone().store(bv64_const(0x10), x.clone())),
                x_out.clone().eq(mem.clone().select(bv64_const(0x10))),
                sz_out.clone().eq(sz
                    .clone()
                    .store(Expr::bitvec_const(1u64, 32), Expr::bitvec_const(4u64, 32))),
            ],
        ),
        RelationApp::new("bb1", vec![mem_out, sz_out, x_out]),
    ));

    // Rule 1: mem is MODIFIED (impure mid), sz is FRAMED (pure mid alias).
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![mem.clone(), sz.clone(), x.clone()])),
            vec![
                Expr::var("mem__mid_bb2", arr_sort()).eq(mem.store(bv64_const(0x20), x)),
                Expr::var("sz__mid_bb2", obj_size_sort()).eq(sz),
            ],
        ),
        RelationApp::new(
            "bb2",
            vec![Expr::var("mem__mid_bb2", arr_sort()), Expr::var("sz__mid_bb2", obj_size_sort())],
        ),
    ));
    vc
}

#[test]
fn framed_alias_collapses_even_though_another_mid_var_is_stored_to() {
    let mut vc = build_modified_and_framed_vc();
    collapse_mid_aliases(&mut vc);

    let text = rule_text(&vc, 1);
    assert!(
        !text.contains("sz__mid_bb2"),
        "the FRAMED array's pure alias must be substituted out even though          mem__mid_bb2 has a real definition; rule still reads: {text}"
    );
    assert!(
        text.contains("mem__mid_bb2"),
        "the MODIFIED array's mid var carries a non-identity definition and must          be withheld (fail-closed), not substituted; rule reads: {text}"
    );
    // The identity conjunct is gone; the store definition is kept.
    assert_eq!(
        vc.rules[1].body.constraints.iter().count(),
        1,
        "only the sz identity may be dropped"
    );
}

#[test]
fn only_the_withheld_array_keeps_an_array_param_after_scalarization() {
    let mut vc = build_modified_and_framed_vc();
    scalarize_vc(&mut vc);

    // SHAPE: which sorts survive in which predicate. `sz` is
    // (Array BV32 BV32) and must be scalarized away everywhere; `mem` is
    // (Array BV64 BV32) and must survive, un-scalarized and sound.
    for rel in ["bb0", "bb1", "bb2"] {
        let sorts = relation_sorts(&vc, rel);
        assert!(
            !sorts.contains(&obj_size_sort()),
            "relation {rel} must not keep the framed (Array BV32 BV32) param: {sorts:?}"
        );
        assert!(
            sorts.contains(&arr_sort()),
            "relation {rel} must keep the withheld (Array BV64 BV32) param: {sorts:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Chains whose ROOT is the withheld variable
// ---------------------------------------------------------------------------

/// `a__mid_bb2 = a__mid_bb1` (pure) on top of `a__mid_bb1 = store(a, ..)`
/// (impure). The alias collapses onto the withheld root; the root stays.
#[test]
fn alias_onto_a_stored_mid_root_collapses_to_the_root_and_terminates() {
    let a = Expr::var("a", arr_sort());
    let mid1 = Expr::var("a__mid_bb1", arr_sort());
    let mid2 = Expr::var("a__mid_bb2", arr_sort());
    let x = Expr::var("x", bv32_sort());

    let mut vc = ChcVc::new();
    for (name, sort) in [
        ("a", arr_sort()),
        ("a__mid_bb1", arr_sort()),
        ("a__mid_bb2", arr_sort()),
        ("x", bv32_sort()),
    ] {
        vc.add_var(VarDecl::new(name, sort));
    }
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb2", vec![arr_sort()]));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![a.clone(), x.clone()])),
            vec![mid1.clone().eq(a.store(bv64_const(0x10), x)), mid2.eq(mid1)],
        ),
        RelationApp::new("bb2", vec![Expr::var("a__mid_bb2", arr_sort())]),
    ));

    collapse_mid_aliases(&mut vc);

    let text = rule_text(&vc, 0);
    assert!(!text.contains("a__mid_bb2"), "the pure alias must be eliminated: {text}");
    assert!(
        text.contains("a__mid_bb1"),
        "the stored-to root must be withheld, not substituted: {text}"
    );
    assert_eq!(
        vc.rules[0].body.constraints.iter().count(),
        1,
        "the alias identity is dropped, the store definition is kept"
    );
}

// ---------------------------------------------------------------------------
// A withheld root landing in a relation column (prusti/Selection_sort, row 72)
// ---------------------------------------------------------------------------

/// Every relation application agrees with its declaration, sort by sort. This
/// is the property AY's CHC parser enforces; violating it is a `ChcParseError`
/// before any solver runs.
fn assert_relation_apps_sort_consistent(vc: &ChcVc) {
    let apps = vc
        .rules
        .iter()
        .flat_map(|rule| std::iter::once(&rule.head).chain(rule.body.relation.as_ref()));
    for app in apps {
        let sorts = relation_sorts(vc, app.name.as_str());
        let arg_sorts: Vec<ay_bindings::Sort> = app.args.iter().map(|a| a.sort().clone()).collect();
        assert_eq!(
            arg_sorts, sorts,
            "application of {} disagrees with its declaration after scalarization",
            app.name
        );
    }
}

/// The Selection_sort shape. The entry block initialises the whole array with
/// constant-index stores (`let mut array = [9, 4, ...]`), so its fragment-composed
/// rule defines a stored-to mid var and frames it forward through a pure alias
/// into the loop head's column. The loop itself indexes the array SYMBOLICALLY
/// (`array[j]`), so the state array can never be scalarized.
///
/// `collapse_mid_aliases` substitutes the pure alias onto the withheld root, so
/// the head now names `a__mid_bb0` — itself a constant-index candidate (every
/// lane it has is overwritten, so it needs nothing from `a`). Expanding that
/// recognised NAME alone widened the entry head to two bv32 lanes while the
/// loop's own applications kept `a` whole, and the declaration took the head's
/// sorts: "Predicate 'main__bb8' expected argument sort (_ BitVec 32), got
/// (Array (_ BitVec 64) (_ BitVec 32))".
fn build_withheld_root_in_loop_column_vc() -> ChcVc {
    let a = Expr::var("a", arr_sort());
    let a_out = Expr::var("a__out", arr_sort());
    let mid0 = Expr::var("a__mid_bb0", arr_sort());
    let mid6 = Expr::var("a__mid_bb6", arr_sort());
    let i = Expr::var("i", super::bv64_sort());
    let i_out = Expr::var("i__out", super::bv64_sort());

    let mut vc = ChcVc::new();
    for (name, sort) in [
        ("a", arr_sort()),
        ("a__out", arr_sort()),
        ("a__mid_bb0", arr_sort()),
        ("a__mid_bb6", arr_sort()),
        ("i", super::bv64_sort()),
        ("i__out", super::bv64_sort()),
        ("first", super::bv32_sort()),
    ] {
        vc.add_var(VarDecl::new(name, sort));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), super::bv64_sort()]));
    vc.add_relation(RelationDecl::new("bb8", vec![arr_sort(), super::bv64_sort()]));

    // Entry: bb0(a, i) ∧ a__mid_bb0 = store(store(K(0), 0, 9), 1, 4)
    //        ∧ first = select(a__mid_bb0, 0) ∧ a__mid_bb6 = a__mid_bb0
    //        → bb8(a__mid_bb6, i)
    // (`let mut array = [9, 4]` after free-base normalisation, read once at a
    // constant index by the composed fragment, which gives the stored-to mid
    // var lanes of its own)
    let init = Expr::const_array(super::bv64_sort(), Expr::bitvec_const(0u64, 32))
        .store(bv64_const(0), Expr::bitvec_const(9u64, 32))
        .store(bv64_const(1), Expr::bitvec_const(4u64, 32));
    let first = Expr::var("first", super::bv32_sort());
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![a.clone(), i.clone()])),
            vec![
                mid0.clone().eq(init),
                first.eq(mid0.clone().select(bv64_const(0))),
                mid6.clone().eq(mid0),
            ],
        ),
        RelationApp::new("bb8", vec![mid6, i.clone()]),
    ));

    // Loop: bb8(a, i) ∧ a__out = store(a, i, select(a, i + 1)) ∧ i__out = i + 1
    //       → bb8(a__out, i__out)       (symbolic index: `a` is unscalarizable)
    let next = i.clone().bvadd(bv64_const(1));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb8", vec![a.clone(), i.clone()])),
            vec![
                a_out.clone().eq(a.clone().store(i.clone(), a.select(next.clone()))),
                i_out.clone().eq(next),
            ],
        ),
        RelationApp::new("bb8", vec![a_out, i_out]),
    ));
    vc
}

#[test]
fn a_withheld_root_in_a_disputed_column_is_not_expanded() {
    let mut vc = build_withheld_root_in_loop_column_vc();
    scalarize_vc(&mut vc);

    // The program must stay well-sorted: every application of bb8 carries the
    // same column sorts as its declaration.
    assert_relation_apps_sort_consistent(&vc);

    // SHAPE: the loop head keeps the whole array (the column is disputed, so
    // nothing in it is scalarized), and the entry head carries the stored-to
    // array itself, not two free-standing lanes.
    assert_eq!(relation_sorts(&vc, "bb8"), &[arr_sort(), super::bv64_sort()]);
    let entry_head = &vc.rules[0].head;
    assert!(
        format!("{:?}", entry_head.args[0]).contains("a__mid_bb0"),
        "the entry head must still bind the stored-to array whole: {:?}",
        entry_head.args
    );
    // The store definition survives un-scalarized (fail closed, not dropped).
    let entry_text = rule_text(&vc, 0);
    assert!(
        entry_text.contains("a__mid_bb0") && !entry_text.contains("a__mid_bb0_at_"),
        "the stored-to array must keep its whole-array definition: {entry_text}"
    );
}

/// The complement: two DIFFERENT scalarizable arrays share a column (the entry
/// edge hands the loop head `p__out`, the loop names its own `q`), and their
/// lane layouts are identical. Each application contributes the same lanes in
/// the same order, so the column must still scalarize — a disputed-column
/// refusal is only for layouts that differ.
#[test]
fn distinct_arrays_with_identical_lanes_still_share_a_scalarized_column() {
    let p = Expr::var("p", arr_sort());
    let p_out = Expr::var("p__out", arr_sort());
    let q = Expr::var("q", arr_sort());
    let q_out = Expr::var("q__out", arr_sort());
    let r = Expr::var("r", bv32_sort());
    let s = Expr::var("s", bv32_sort());

    let mut vc = ChcVc::new();
    for (name, sort) in [
        ("p", arr_sort()),
        ("p__out", arr_sort()),
        ("q", arr_sort()),
        ("q__out", arr_sort()),
        ("r", bv32_sort()),
        ("s", bv32_sort()),
    ] {
        vc.add_var(VarDecl::new(name, sort));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort()]));

    // bb0(p) ∧ p__out = store(p, 0, 5) ∧ r = select(p, 0) → bb1(p__out)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![p.clone()])),
            vec![
                p_out.clone().eq(p.clone().store(bv64_const(0), Expr::bitvec_const(5u64, 32))),
                r.eq(p.select(bv64_const(0))),
            ],
        ),
        RelationApp::new("bb1", vec![p_out]),
    ));
    // bb1(q) ∧ q__out = store(q, 0, 6) ∧ s = select(q, 0) → bb1(q__out)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![q.clone()])),
            vec![
                q_out.clone().eq(q.clone().store(bv64_const(0), Expr::bitvec_const(6u64, 32))),
                s.eq(q.select(bv64_const(0))),
            ],
        ),
        RelationApp::new("bb1", vec![q_out]),
    ));

    scalarize_vc(&mut vc);

    assert_relation_apps_sort_consistent(&vc);
    assert!(
        relation_sorts(&vc, "bb1").iter().all(|sort| !sort.is_array()),
        "identical lane layouts must not block scalarization: {:?}",
        relation_sorts(&vc, "bb1")
    );
}

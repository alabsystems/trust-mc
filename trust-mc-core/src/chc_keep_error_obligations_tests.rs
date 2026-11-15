// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Keep-error-obligations mode: the pruning passes must not erase the last
//! error obligation of a VC that registered properties once the lost-checks
//! recovery asked them not to.

use super::*;
use ay_bindings::Sort;

fn property(id: u32) -> ChcProperty {
    ChcProperty {
        id,
        kind: PropertyKind::Assertion,
        bb: 0,
        relation: format!("error_p{id}"),
        message: None,
        location: None,
        approximation_dependent: None,
        discharged_at_encode: None,
    }
}

/// `f__bb0` runs; the only check site sits in `f__bb_dead`, which no rule
/// derives (or whose guard folded to `false`, with `false_guard`).
fn vc_with_one_check(keep: bool, false_guard: bool) -> ChcVc {
    let x = Expr::var("x", Sort::bitvec(8));
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("f__bb0", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("f__bb_dead", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::nullary("error_p0"));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::init(
        x.clone().eq(Expr::bitvec_const(1u8, 8)),
        RelationApp::new("f__bb0", vec![x.clone()]),
    ));
    let (body, constraints) = if false_guard {
        ("f__bb0", vec![x.clone().eq(Expr::bitvec_const(1u8, 8)), Expr::bool_const(false)])
    } else {
        ("f__bb_dead", Vec::new())
    };
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new(body, vec![x.clone()])), constraints),
        RelationApp::new("error_p0", Vec::new()),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("error_p0", Vec::new())), Vec::new()),
        RelationApp::new("error", Vec::new()),
    ));
    vc.query = ChcQuery::new().with_target("error");
    vc.properties.push(property(0));
    vc.keep_error_obligations = keep;
    vc
}

fn error_obligations(vc: &ChcVc) -> usize {
    vc.rules.iter().filter(|rule| rule_is_error_obligation(rule)).count()
}

#[test]
fn orphan_prune_erases_every_error_obligation_by_default() {
    let mut vc = vc_with_one_check(false, false);
    let before = vc.clone();
    vc.prune_orphan_block_rules();
    assert_eq!(error_obligations(&vc), 0);
    assert!(passes_lost_every_error_obligation(&before, &vc));
}

#[test]
fn orphan_prune_keeps_error_obligations_in_keep_mode() {
    let mut vc = vc_with_one_check(true, false);
    let before = vc.clone();
    vc.prune_orphan_block_rules();
    assert_eq!(error_obligations(&vc), 2, "check edge and bridge survive");
    assert!(vc.relations.iter().any(|rel| rel.name == "f__bb_dead"), "body relation stays declared");
    assert!(!passes_lost_every_error_obligation(&before, &vc));
}

#[test]
fn false_guard_elimination_erases_the_check_but_accounts_for_it_by_default() {
    // The folds-to-false class belongs to the out-of-band record, not to this
    // recovery: `eliminate_trivially_false_rules` deletes the rule AND marks the
    // property `discharged_at_encode`, and emission then emits the canonical
    // `false => error` obligation. So the obligation is gone yet nothing is lost,
    // and the detector must NOT ask for a keep-mode re-encode here — pinning live
    // `error_p{id}` rules would defeat that gate and make the solver re-derive an
    // infeasibility. Contrast `orphan_prune_erases_every_error_obligation_by_default`,
    // where nobody accounts for the check and the recovery is the only answer.
    let mut vc = vc_with_one_check(false, true);
    let before = vc.clone();
    vc.eliminate_trivially_false_rules();
    vc.prune_orphan_block_rules();
    assert_eq!(error_obligations(&vc), 0);
    assert_eq!(
        vc.properties[0].discharged_at_encode,
        Some("violation_folds_to_false"),
        "the erased check is recorded, not lost"
    );
    assert!(!passes_lost_every_error_obligation(&before, &vc));
}

#[test]
fn false_guard_elimination_pins_the_check_in_keep_mode() {
    let mut vc = vc_with_one_check(true, true);
    vc.eliminate_trivially_false_rules();
    vc.prune_orphan_block_rules();
    let check = vc
        .rules
        .iter()
        .find(|rule| rule.head.name.as_str() == "error_p0")
        .expect("check obligation kept");
    assert_eq!(
        check.body.relation.as_ref().map(|app| app.name.as_str()),
        Some("f__bb0"),
        "the body relation is kept"
    );
    assert_eq!(check.body.constraints.len(), 1);
    assert_eq!(check.body.constraints.first(), Some(&Expr::bool_const(false)));
    assert_eq!(error_obligations(&vc), 2);
}

#[test]
fn lost_obligation_detector_exempts_certified_keep_mode_and_unregistered() {
    let before = vc_with_one_check(false, false);
    let mut after = before.clone();
    after.rules.retain(|rule| !rule_is_error_obligation(rule));
    assert!(passes_lost_every_error_obligation(&before, &after));

    let mut certified = after.clone();
    certified.trivially_safe_discharged = true;
    assert!(!passes_lost_every_error_obligation(&before, &certified));

    let mut kept = after.clone();
    kept.keep_error_obligations = true;
    assert!(!passes_lost_every_error_obligation(&before, &kept));

    let mut unregistered = after.clone();
    unregistered.properties.clear();
    assert!(!passes_lost_every_error_obligation(&before, &unregistered));

    let mut nothing_before = before.clone();
    nothing_before.rules.retain(|rule| !rule_is_error_obligation(rule));
    assert!(!passes_lost_every_error_obligation(&nothing_before, &after));
}

#[test]
fn lost_obligation_detector_exempts_a_vc_discharged_at_encode() {
    // Main's out-of-band mechanism (`mark_property_discharged_at_encode`, recorded
    // by `eliminate_trivially_false_rules`) owns the folds-to-false class: emission
    // sees every property accounted for and emits the canonical `false => error`
    // obligation instead. That shape must NOT be re-encoded in keep mode.
    let before = vc_with_one_check(false, true);
    let mut after = vc_with_one_check(false, true);
    after.rules.retain(|rule| !crate::chc::rule_is_error_obligation(rule));
    assert_eq!(error_obligations(&after), 0);
    assert!(passes_lost_every_error_obligation(&before, &after));
    for property in after.properties.clone() {
        after.mark_property_discharged_at_encode(property.id, "violation_folds_to_false");
    }
    assert!(
        !passes_lost_every_error_obligation(&before, &after),
        "every property accounted for at encode time is not a lost check"
    );
}

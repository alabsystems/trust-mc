// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(clippy::unwrap_used, clippy::panic)]
use super::common::*;
use crate::codegen_ay::emit_chc;

const SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]
mod kani {
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(c: bool, _: &str) { let _ = c; }
}
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CELLS: [AtomicU32; 2] = [AtomicU32::new(11), AtomicU32::new(23)];
pub fn slice_safe() {
    let s: &[AtomicU32] = &CELLS;
    let t = s;
    t[1].store(39, SeqCst);
    kani::assert(CELLS[1].load(SeqCst) == 39, "written cell");
    kani::assert(CELLS[0].load(SeqCst) == 11, "neighbor");
}
pub fn slice_bug() {
    let s: &[AtomicU32] = &CELLS;
    s[1].store(39, SeqCst);
    kani::assert(CELLS[1].load(SeqCst) == 23, "stale cell");
}
pub fn choice_safe(c: bool) {
    let r = if c { &CELLS[0] } else { &CELLS[1] };
    r.store(39, SeqCst);
    kani::assert(c || CELLS[1].load(SeqCst) == 39, "false arm");
    kani::assert(!c || CELLS[1].load(SeqCst) == 23, "true arm neighbor");
    kani::assert(!c || CELLS[0].load(SeqCst) == 39, "true arm");
    kani::assert(c || CELLS[0].load(SeqCst) == 11, "false arm neighbor");
}
pub fn choice_bug(c: bool) {
    let r = if c { &CELLS[0] } else { &CELLS[1] };
    r.store(39, SeqCst);
    kani::assert(c || CELLS[1].load(SeqCst) == 23, "stale false arm");
}
pub fn symbolic_safe(i: usize) {
    if i < 2 {
        CELLS[i].store(39, SeqCst);
        kani::assert(CELLS[i].load(SeqCst) == 39, "selected");
        kani::assert(i == 0 || CELLS[0].load(SeqCst) == 11, "neighbor");
    }
}
pub fn symbolic_bug(i: usize) {
    if i < 2 {
        CELLS[i].store(39, SeqCst);
        kani::assert(CELLS[i].load(SeqCst) != 39, "wrong selected");
    }
}
pub fn iter_safe() {
    for cell in CELLS.iter() { cell.store(39, SeqCst); }
    kani::assert(CELLS[1].load(SeqCst) == 39, "last cell");
    kani::assert(CELLS[0].load(SeqCst) == 39, "first cell");
}
pub fn iter_bug() {
    for cell in CELLS.iter() { cell.store(39, SeqCst); }
    kani::assert(CELLS[1].load(SeqCst) == 23, "stale last cell");
}

pub fn aliases_cross_view_safe() {
    let s: &[AtomicU32] = &CELLS;
    let t = s;
    let r = &t[1];
    kani::assert(std::ptr::eq(r, &CELLS[1]), "same storage");
    r.store(39, SeqCst);
    kani::assert(unsafe { *CELLS[1].as_ptr() } == 39, "scalar view");
    kani::assert(CELLS[0].load(SeqCst) == 11, "neighbor");
}
pub fn sequential_rmw_safe() {
    let s: &[AtomicU32] = &CELLS;
    s[1].store(39, SeqCst);
    let old = CELLS[1].fetch_add(2, SeqCst);
    s[0].store(57, SeqCst);
    kani::assert(old == 39, "old RMW value");
    kani::assert(CELLS[1].load(SeqCst) == 41, "later state");
    kani::assert(unsafe { *CELLS[1].as_ptr() } == 41, "later scalar view");
    kani::assert(CELLS[0].load(SeqCst) == 57, "other store");
}
pub fn sequential_rmw_bug() {
    let s: &[AtomicU32] = &CELLS;
    s[1].store(39, SeqCst);
    let old = CELLS[1].fetch_add(2, SeqCst);
    kani::assert(old == 23, "stale old RMW");
}
pub fn cursor_snapshot_safe() {
    let mut it = CELLS.iter();
    match it.next() {
        Some(first) => {
            match it.next() {
                Some(second) => {
                    first.store(39, SeqCst);
                    second.store(57, SeqCst);
                    kani::assert(std::ptr::eq(first, &CELLS[0]), "first identity after next");
                    kani::assert(std::ptr::eq(second, &CELLS[1]), "second identity");
                }
                None => kani::assert(false, "second exists"),
            }
        }
        None => kani::assert(false, "first exists"),
    }
    match it.next() { None => (), Some(_) => kani::assert(false, "exhausted") }
    kani::assert(CELLS[0].load(SeqCst) == 39, "snapshot cell");
    kani::assert(CELLS[1].load(SeqCst) == 57, "second cell");
}
pub fn early_break_safe() {
    let mut count = 0;
    for cell in CELLS.iter() {
        cell.store(39, SeqCst);
        count += 1;
        break;
    }
    kani::assert(count == 1, "one side effect");
    kani::assert(CELLS[0].load(SeqCst) == 39, "first cell");
    kani::assert(CELLS[1].load(SeqCst) == 23, "unvisited neighbor");
}
pub fn early_break_bug() {
    for cell in CELLS.iter() { cell.store(39, SeqCst); break; }
    kani::assert(CELLS[1].load(SeqCst) == 39, "unvisited cell is not written");
}
pub fn conditional_write_safe(c: bool) {
    let r = if c { &CELLS[0] } else { &CELLS[1] };
    if c { r.store(39, SeqCst); }
    kani::assert(CELLS[1].load(SeqCst) == 23, "never written");
    kani::assert(c || CELLS[0].load(SeqCst) == 11, "no write on false arm");
}
pub fn conditional_write_bug(c: bool) {
    if c { CELLS[1].store(39, SeqCst); }
    kani::assert(CELLS[1].load(SeqCst) == 39, "missing write on false path");
}
pub fn two_objects_safe(c: bool) {
    static OTHER: [AtomicU32; 2] = [AtomicU32::new(5), AtomicU32::new(7)];
    let r = if c { &CELLS[1] } else { &OTHER[1] };
    r.store(39, SeqCst);
    kani::assert(!c || OTHER[1].load(SeqCst) == 7, "other allocation untouched");
    kani::assert(c || CELLS[1].load(SeqCst) == 23, "first allocation untouched");
    kani::assert(c || OTHER[1].load(SeqCst) == 39, "other allocation written");
    kani::assert(!c || CELLS[1].load(SeqCst) == 39, "first allocation written");
}
pub fn oob_bug(i: usize) {
    CELLS[i].store(39, SeqCst);
    kani::assert(true, "bounds error remains");
}
pub fn iter_skip_safe(c: bool) {
    let mut count = 0usize;
    for cell in CELLS.iter() {
        if count == 0 || c { cell.store(39, SeqCst); }
        count += 1;
    }
    kani::assert(count == 2, "all iterations");
    kani::assert(CELLS[0].load(SeqCst) == 39, "first written");
    kani::assert(c || CELLS[1].load(SeqCst) == 23, "second skipped");
    kani::assert(!c || CELLS[1].load(SeqCst) == 39, "second written");
}

pub fn guard_mixed_producer(c: bool) {
    let mut it = CELLS.iter();
    let candidate = if c { it.next() } else { Some(&CELLS[1]) };
    if let Some(cell) = candidate { cell.store(39, SeqCst); }
    kani::assert(c || CELLS[1].load(SeqCst) == 39, "mixed producer remains guarded");
}
pub fn guard_opaque_receiver() {
    let cell = std::hint::black_box(&CELLS[1]);
    cell.store(39, SeqCst);
    kani::assert(CELLS[1].load(SeqCst) == 39, "opaque producer remains guarded");
}
"#;

fn check(name: &str, expected: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = instance.body().unwrap();
        if let Ok(dir) = std::env::var("TRUST_MC_ARRAY_ADDRESS_EVIDENCE") {
            std::fs::create_dir_all(&dir).unwrap();
            let chc = ChcCtx::new(
                ctx.tcx,
                &body,
                name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let mut facts = String::new();
            for (i, d) in body.locals().iter().enumerate() {
                if let TyKind::RigidTy(RigidTy::Adt(def, args)) = d.ty.kind() {
                    facts.push_str(&format!(
                        "ADT crate={} name={} args={args:?}\n",
                        def.krate().name,
                        def.name()
                    ));
                }
                facts.push_str(&format!(
                    "{i}: {} item={:?} next={:?}\n",
                    d.ty,
                    chc.borrowed_slice_item_ty(d.ty),
                    chc.borrowed_static_next_sources(i)
                ));
            }
            std::fs::write(std::path::Path::new(&dir).join(format!("{name}.facts")), facts)
                .unwrap();
        }
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        if let Ok(dir) = std::env::var("TRUST_MC_ARRAY_ADDRESS_EVIDENCE") {
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}.raw.smt2")),
                emit_chc(&vc).to_string(),
            )
            .unwrap();
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}.properties")),
                format!("{:#?}", vc.properties),
            )
            .unwrap();
        }
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        super::super::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = emit_chc(&vc).to_string();
        if let Ok(dir) = std::env::var("TRUST_MC_ARRAY_ADDRESS_EVIDENCE") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), &smt).unwrap();
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}.mir")),
                format!("{body:#?}"),
            )
            .unwrap();
        }
        let problem = ay_chc::ChcParser::parse(&smt).unwrap();
        let mut config = ay_chc::AdaptiveConfig::with_budget(
            std::time::Duration::from_secs(z3_test_timeout_secs_or(30)),
            false,
        );
        config.strict_proofs = true;
        let outcome = ay_chc::AdaptivePortfolio::new(problem, config).solve();
        if let Ok(dir) = std::env::var("TRUST_MC_ARRAY_ADDRESS_EVIDENCE") {
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}.verdict")),
                format!("{outcome:?}"),
            )
            .unwrap();
        }
        verdict = Some(match outcome {
            ay_chc::VerifiedChcResult::Safe(_) => "unsat".to_string(),
            ay_chc::VerifiedChcResult::Unsafe(_) => "sat".to_string(),
            unknown => {
                eprintln!("{name}: {unknown:?}");
                "unknown".to_string()
            }
        });
    });
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(name)
        .unwrap_or_default();
    if expected == "guarded" {
        assert!(
            reasons.contains_key("payload_value_fact_producer_mix")
                || reasons.contains_key("payload_value_fact_address_reader")
                || reasons.contains_key("enum_ref_payload_escapes"),
            "{name}: mixed-producer guard was lost: {reasons:?}"
        );
        return;
    }
    if expected == "static_store_unrouted" {
        assert!(
            reasons.contains_key(expected),
            "{name}: unknown producer lost its fallback: {reasons:?}"
        );
        return;
    }
    assert_eq!(verdict.as_deref(), Some(expected), "{name}: {reasons:?}");
    if expected == "unsat" {
        assert!(reasons.is_empty(), "{name}: exact safe probe lost semantics: {reasons:?}");
    }
}
#[test]
fn slice_safe() {
    check("slice_safe", "unsat");
}
#[test]
fn slice_bug() {
    check("slice_bug", "sat");
}
#[test]
fn choice_safe() {
    check("choice_safe", "unsat");
}
#[test]
fn choice_bug() {
    check("choice_bug", "sat");
}
#[test]
fn symbolic_safe() {
    check("symbolic_safe", "unsat");
}
#[test]
fn symbolic_bug() {
    check("symbolic_bug", "sat");
}
#[test]
fn iter_safe() {
    check("iter_safe", "unsat");
}
#[test]
fn iter_bug() {
    check("iter_bug", "sat");
}

#[test]
fn aliases_cross_view_safe() {
    check("aliases_cross_view_safe", "unsat");
}
#[test]
fn sequential_rmw_safe() {
    check("sequential_rmw_safe", "unsat");
}
#[test]
fn sequential_rmw_bug() {
    check("sequential_rmw_bug", "sat");
}
#[test]
fn cursor_snapshot_safe() {
    check("cursor_snapshot_safe", "unsat");
}
#[test]
fn early_break_safe() {
    check("early_break_safe", "unsat");
}
#[test]
fn early_break_bug() {
    check("early_break_bug", "sat");
}
#[test]
fn conditional_write_safe() {
    check("conditional_write_safe", "unsat");
}
#[test]
fn conditional_write_bug() {
    check("conditional_write_bug", "sat");
}
#[test]
fn two_objects_safe() {
    check("two_objects_safe", "unsat");
}
#[test]
fn oob_bug() {
    check("oob_bug", "sat");
}
#[test]
fn iter_skip_safe() {
    check("iter_skip_safe", "unsat");
}

#[test]
fn mixed_producer_keeps_guard() {
    check("guard_mixed_producer", "guarded");
}
#[test]
fn opaque_receiver_keeps_guard() {
    check("guard_opaque_receiver", "static_store_unrouted");
}

// These execute the transformed Horn systems. They detect a dropped catch-all
// and the invalid inference that a cursor reset bounds the total executions.
#[test]
fn cursor_partition_retains_outside_values() {
    use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};
    let mut vc = ChcVc::new();
    let sort = ay_bindings::Sort::bitvec(64);
    let pc = Expr::var("cursor", sort.clone());
    vc.add_var(VarDecl::new("cursor", sort.clone()));
    vc.add_relation(RelationDecl::new("cycle", vec![sort]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = trust_mc_core::chc::ChcQuery::new().with_target("error");
    vc.add_rule(Rule::init(
        Expr::bool_const(true),
        RelationApp::new("cycle", vec![Expr::bitvec_const(3u128, 64)]),
    ));
    let body = RelationApp::new("cycle", vec![pc.clone()]);
    vc.add_rule(Rule::new(RuleBody::new(Some(body.clone()), vec![]), body.clone()));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(body), vec![pc.eq(Expr::bitvec_const(3u128, 64))]),
        RelationApp::nullary("error"),
    ));
    super::super::decl::static_iterator_partition::partition_cursor(&mut vc, "cursor", 2);
    let result =
        run_z3_on_smt2_with_timeout(&emit_chc(&vc).to_string(), z3_test_timeout_secs_or(30))
            .unwrap();
    assert_eq!(result, "sat", "outside cursor value must remain reachable");
}

#[test]
fn cursor_partition_preserves_resets() {
    use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};
    let mut vc = ChcVc::new();
    let word = ay_bindings::Sort::bitvec(64);
    let byte = ay_bindings::Sort::bitvec(8);
    let pc = Expr::var("cursor", word.clone());
    let count = Expr::var("count", byte.clone());
    vc.add_var(VarDecl::new("cursor", word.clone()));
    vc.add_var(VarDecl::new("count", byte.clone()));
    vc.add_relation(RelationDecl::new("cycle", vec![word, byte]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = trust_mc_core::chc::ChcQuery::new().with_target("error");
    vc.add_rule(Rule::init(
        Expr::bool_const(true),
        RelationApp::new(
            "cycle",
            vec![Expr::bitvec_const(0u128, 64), Expr::bitvec_const(0u128, 8)],
        ),
    ));
    let body = RelationApp::new("cycle", vec![pc, count.clone()]);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(body.clone()), vec![]),
        RelationApp::new(
            "cycle",
            vec![Expr::bitvec_const(0u128, 64), count.clone().bvadd(Expr::bitvec_const(1u128, 8))],
        ),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(body), vec![count.eq(Expr::bitvec_const(2u128, 8))]),
        RelationApp::nullary("error"),
    ));
    super::super::decl::static_iterator_partition::partition_cursor(&mut vc, "cursor", 2);
    let result =
        run_z3_on_smt2_with_timeout(&emit_chc(&vc).to_string(), z3_test_timeout_secs_or(30))
            .unwrap();
    assert_eq!(result, "sat", "reset must not discard later executions");
}

#[test]
fn cursor_partition_retains_discharged_checks() {
    use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};
    let mut vc = ChcVc::new();
    let sort = ay_bindings::Sort::bitvec(64);
    let pc = Expr::var("cursor", sort.clone());
    vc.add_var(VarDecl::new("cursor", sort.clone()));
    vc.add_relation(RelationDecl::new("cycle", vec![sort]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = trust_mc_core::chc::ChcQuery::new().with_target("error");
    vc.add_rule(Rule::init(
        Expr::bool_const(true),
        RelationApp::new("cycle", vec![Expr::bitvec_const(0u128, 64)]),
    ));
    let body = RelationApp::new("cycle", vec![pc.clone()]);
    vc.add_rule(Rule::new(RuleBody::new(Some(body.clone()), vec![]), body.clone()));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(body),
            vec![
                pc.clone().eq(Expr::bitvec_const(0u128, 64)),
                pc.eq(Expr::bitvec_const(1u128, 64)),
            ],
        ),
        RelationApp::nullary("error"),
    ));
    super::super::decl::static_iterator_partition::partition_cursor(&mut vc, "cursor", 2);
    assert!(
        vc.rules.iter().any(trust_mc_core::chc::rule_is_error_obligation),
        "an infeasible check must remain an obligation"
    );
    let result =
        run_z3_on_smt2_with_timeout(&emit_chc(&vc).to_string(), z3_test_timeout_secs_or(30))
            .unwrap();
    assert_eq!(result, "unsat", "contradictory check must be discharged");
}

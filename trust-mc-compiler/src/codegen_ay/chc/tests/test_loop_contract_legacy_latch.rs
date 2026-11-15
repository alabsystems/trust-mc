// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Design 5 (docs/chc-hole-fix-designs-2026-09-24.md, "Legacy loop-contract
//! latch"): the CHC prescan that books every legacy loop-contract latch of a
//! harness body fail-closed (`loop_modifies_frame::prescan_loop_contract_legacy_latches`).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::loop_modifies_frame::{
    LOOP_CONTRACT_LEGACY_LATCH, count_legacy_loop_contract_latches,
    prescan_loop_contract_legacy_latches,
};

/// Register calls at every `_transformed` role the loop-contract transform
/// emits. As in real code, one invariant closure means one register instance.
const REGISTER_ROLES_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

#[inline(never)]
#[kanitool::fn_marker = "kani_register_loop_contract"]
fn kani_register_loop_contract<F: Fn() -> bool>(f: &F, transformed: usize) -> bool {
    transformed != 0 && f()
}

fn rule_pair(captured: u8) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    let base = kani_register_loop_contract(r, 2);
    let latch = kani_register_loop_contract(r, 1);
    base & latch
}

fn fresh_borrow_rule_pair() -> bool {
    let inv = || true;
    let base = kani_register_loop_contract(&inv, 2);
    let latch = kani_register_loop_contract(&inv, 1);
    base & latch
}

fn lone_latch(captured: u8) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    kani_register_loop_contract(r, 1)
}

fn base_of_another_loop(captured: u8) -> bool {
    let inv_a = || captured == 7;
    let inv_b = || captured == 8;
    let a = &inv_a;
    let b = &inv_b;
    let base = kani_register_loop_contract(a, 2);
    let latch = kani_register_loop_contract(b, 1);
    base & latch
}

fn legacy_latch(captured: u8) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    kani_register_loop_contract(r, 5)
}

fn two_legacy_latches(captured: u8) -> bool {
    let inv_a = || captured == 7;
    let inv_b = || captured == 8;
    let a = &inv_a;
    let b = &inv_b;
    let first = kani_register_loop_contract(a, 5);
    let second = kani_register_loop_contract(b, 5);
    first & second
}

fn nested_legacy(captured: u8) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    kani_register_loop_contract(r, 4)
}

fn untransformed(captured: u8) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    kani_register_loop_contract(r, 0)
}

fn dynamic_role(captured: u8, role: usize) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    kani_register_loop_contract(r, role)
}

fn unknown_role(captured: u8) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    kani_register_loop_contract(r, 9)
}

#[kanitool::should_panic]
fn should_panic_legacy(captured: u8) -> bool {
    let inv = || captured == 7;
    let r = &inv;
    kani_register_loop_contract(r, 5)
}
"#;

fn legacy_latches(tcx: TyCtxt<'_>, suffix: &str) -> usize {
    let instance = find_instance_by_suffix(tcx, suffix);
    count_legacy_loop_contract_latches(&instance.body().expect("body"))
}

/// Which register calls are legacy latches. A rule loop's latch is paired
/// with its base breadcrumb by the register callee (one instance per invariant
/// closure), not by the closure operand; a latch whose loop has no
/// base, the reachable-state latch (role 5), and any role the transform does
/// not emit are legacy. Role 0 belongs to the untransformed-breadcrumb gate
/// and role 4 to the nested-legacy prescan, so neither is counted twice.
#[test]
fn legacy_latch_count_follows_the_register_roles() {
    with_test_ay_ctx_for_source(REGISTER_ROLES_SOURCE, |ctx| {
        let tcx = ctx.tcx;
        assert_eq!(legacy_latches(tcx, "rule_pair"), 0, "a paired rule latch is not legacy");
        assert_eq!(
            legacy_latches(tcx, "fresh_borrow_rule_pair"),
            0,
            "the pairing must not depend on the closure operand's local"
        );
        assert_eq!(legacy_latches(tcx, "lone_latch"), 1, "a latch with no base is legacy");
        assert_eq!(
            legacy_latches(tcx, "base_of_another_loop"),
            1,
            "a base breadcrumb pairs only with the latch of its own invariant closure"
        );
        assert_eq!(legacy_latches(tcx, "legacy_latch"), 1, "role 5 is a legacy latch");
        assert_eq!(legacy_latches(tcx, "two_legacy_latches"), 2, "one per legacy latch");
        assert_eq!(legacy_latches(tcx, "nested_legacy"), 0, "role 4 has its own prescan");
        assert_eq!(legacy_latches(tcx, "untransformed"), 0, "role 0 has its own gate");
        assert_eq!(legacy_latches(tcx, "dynamic_role"), 1, "a non-constant role fails closed");
        assert_eq!(legacy_latches(tcx, "unknown_role"), 1, "an unknown role fails closed");
    });
}

/// The prescan books one unblessed reason per legacy latch. With no harness
/// instance to prove the harness is not `should_panic`, the event stays
/// UNACCOUNTED, so no counterexample of the harness can be certified; for a
/// known non-`should_panic` instance it is accounted with no freed variable.
#[test]
fn prescan_books_each_legacy_latch_fail_closed() {
    assert_eq!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness(LOOP_CONTRACT_LEGACY_LATCH),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::FailClose,
        "the legacy-latch reason must never be blessed"
    );
    with_test_ay_ctx_for_source(REGISTER_ROLES_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "two_legacy_latches");
        let body = instance.body().expect("body");

        let mut unknown_harness =
            ChcCtx::new(ctx.tcx, &body, "two_legacy_latches", ChcConfig::default());
        unknown_harness.current_instance = None;
        prescan_loop_contract_legacy_latches(&mut unknown_harness);
        assert_eq!(unknown_harness.sound_fallback_count(), 2);
        assert_eq!(
            unknown_harness.vc.accounted_approximations, 0,
            "without a harness instance the booking must stay unaccounted"
        );

        let mut plain_harness =
            ChcCtx::new(ctx.tcx, &body, "two_legacy_latches", ChcConfig::default());
        plain_harness.current_instance = Some(instance);
        prescan_loop_contract_legacy_latches(&mut plain_harness);
        assert_eq!(plain_harness.sound_fallback_count(), 2);
        assert_eq!(
            plain_harness.vc.accounted_approximations, 2,
            "a non-should_panic harness accounts each event with no freed variable"
        );
        assert!(plain_harness.vc.approximated_vars.is_empty());

        // Under `should_panic` a certified panic IS the success, so the
        // booking must stay unaccounted there (the driver's V6 gate then
        // refuses the uncertified panic).
        let should_panic = find_instance_by_suffix(ctx.tcx, "should_panic_legacy");
        let should_panic_body = should_panic.body().expect("body");
        let mut panic_harness =
            ChcCtx::new(ctx.tcx, &should_panic_body, "should_panic_legacy", ChcConfig::default());
        panic_harness.current_instance = Some(should_panic);
        prescan_loop_contract_legacy_latches(&mut panic_harness);
        assert_eq!(panic_harness.sound_fallback_count(), 1);
        assert_eq!(
            panic_harness.vc.accounted_approximations, 0,
            "a should_panic harness must not account the legacy latch"
        );

        let paired = find_instance_by_suffix(ctx.tcx, "rule_pair");
        let paired_body = paired.body().expect("body");
        let mut rule_harness =
            ChcCtx::new(ctx.tcx, &paired_body, "rule_pair", ChcConfig::default());
        rule_harness.current_instance = Some(paired);
        prescan_loop_contract_legacy_latches(&mut rule_harness);
        assert_eq!(rule_harness.sound_fallback_count(), 0, "a rule loop books nothing");
    });
}

/// Design 5 backstop: loop contracts the harness body reaches OUTSIDE itself
/// (`loop_contract_scan::prescan_loop_contracts_beyond_body`), through
/// non-local generic code, through a fn pointer, and not at all.
const BEYOND_BODY_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

#[inline(never)]
#[kanitool::fn_marker = "kani_register_loop_contract"]
fn kani_register_loop_contract<F: Fn() -> bool>(f: &F, transformed: usize) -> bool {
    transformed != 0 && f()
}

fn contracted(n: u32) -> u32 {
    let inv = || n < 100;
    if kani_register_loop_contract(&inv, 1) { n } else { 0 }
}

struct MyIter(u32);

impl Iterator for MyIter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.0 == 0 {
            return None;
        }
        self.0 = 0;
        Some(contracted(1))
    }
}

fn harness_generic() -> usize {
    MyIter(1).count()
}

#[kanitool::should_panic]
fn harness_generic_should_panic() -> usize {
    MyIter(1).count()
}

fn harness_fn_pointer() -> u32 {
    let f: fn(u32) -> u32 = contracted;
    f(1)
}

fn harness_own_loop(n: u32) -> bool {
    let inv = || n < 100;
    kani_register_loop_contract(&inv, 1)
}

fn harness_unrelated() -> u32 {
    let v = [1u32, 2];
    v[0].wrapping_add(v[1])
}
"#;

/// Abstracts every function whose path contains one of the fragments.
struct NamedBoundary(&'static [&'static str]);

impl crate::kani_middle::reachability::AbstractionBoundary for NamedBoundary {
    fn has_explicit_stub(&self, path: &str) -> bool {
        self.0.iter().any(|fragment| path.contains(fragment))
    }

    fn has_handler_backed_abstraction(&self, _path: &str) -> bool {
        false
    }

    fn record_unstubbed_abstraction(&self, _path: &str) {}
}

/// The collector's universe for `root`, as a per-harness codegen installs it.
fn universe_of(
    tcx: TyCtxt<'_>,
    root: rustc_public::mir::mono::Instance,
    boundary: &NamedBoundary,
) -> crate::kani_middle::dyn_universe::DynUniverse {
    let mut transformer = crate::kani_middle::transform::BodyTransformation::new_for_tests();
    let (_items, graph) = crate::kani_middle::reachability::collect_reachable_items(
        tcx,
        &mut transformer,
        &[rustc_public::mir::mono::MonoItem::Fn(root)],
        boundary,
    );
    graph.dyn_universe
}

fn beyond_body_bookings(tcx: TyCtxt<'_>, harness: &str, boundary: &NamedBoundary) -> usize {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::loop_contract_scan::count_loop_contracts_beyond_body;
    let instance = find_instance_by_suffix(tcx, harness);
    let body = instance.body().expect("body");
    let universe = universe_of(tcx, instance, boundary);
    let reach = universe.loop_contract_reach().expect("the collector computes the reach");
    let config = ChcConfig { loop_contracts: true, ..ChcConfig::default() };
    let mut chc_ctx = ChcCtx::new(tcx, &body, harness, config);
    chc_ctx.current_instance = Some(instance);
    count_loop_contracts_beyond_body(&chc_ctx, Some(&reach))
}

/// A live call that reaches a loop contract through non-local generic code
/// is counted whether the graph answers (nothing abstracted) or the raw-body
/// scan must (the collector abstracted `Iterator::count`); a loop contract
/// reachable through a fn pointer is counted once; the body's own register
/// call and a body that reaches no loop contract count nothing.
#[test]
fn beyond_body_count_follows_generic_code_fn_pointers_and_abstracted_calls() {
    with_test_ay_ctx_for_source(BEYOND_BODY_SOURCE, |ctx| {
        let tcx = ctx.tcx;
        let none = NamedBoundary(&[]);
        let count_abstracted = NamedBoundary(&["Iterator::count"]);
        assert_eq!(beyond_body_bookings(tcx, "harness_generic", &none), 1, "graph yes");
        assert_eq!(
            beyond_body_bookings(tcx, "harness_generic", &count_abstracted),
            1,
            "the graph cannot see past `count`; the raw-body scan must"
        );
        assert_eq!(beyond_body_bookings(tcx, "harness_fn_pointer", &none), 1, "address taken");
        assert_eq!(beyond_body_bookings(tcx, "harness_own_loop", &none), 0, "the body's own loop");
        assert_eq!(beyond_body_bookings(tcx, "harness_unrelated", &none), 0);
    });
}

/// The booking is unblessed; accounted with no freed variable for a plain
/// harness, unaccounted under `should_panic`; with no call graph installed it
/// fails closed; with `-Z loop-contracts` off it books nothing.
#[test]
fn beyond_body_prescan_books_fail_closed() {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::loop_contract_scan::{
        LOOP_CONTRACT_BEYOND_BODY, prescan_loop_contracts_beyond_body,
    };
    assert_eq!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness(LOOP_CONTRACT_BEYOND_BODY),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::FailClose,
        "the beyond-body reason must never be blessed"
    );
    with_test_ay_ctx_for_source(BEYOND_BODY_SOURCE, |ctx| {
        let tcx = ctx.tcx;
        let none = NamedBoundary(&[]);
        let on = ChcConfig { loop_contracts: true, ..ChcConfig::default() };

        let plain = find_instance_by_suffix(tcx, "harness_generic");
        let plain_body = plain.body().expect("body");
        {
            let _guard = crate::kani_middle::dyn_universe::HarnessUniverseGuard::install(
                std::sync::Arc::new(universe_of(tcx, plain, &none)),
            );
            let mut harness = ChcCtx::new(tcx, &plain_body, "harness_generic", on);
            harness.current_instance = Some(plain);
            prescan_loop_contracts_beyond_body(&mut harness);
            assert_eq!(harness.sound_fallback_count(), 1);
            assert_eq!(harness.vc.accounted_approximations, 1, "accounted, no freed variable");
            assert!(harness.vc.approximated_vars.is_empty());

            let mut off = ChcCtx::new(tcx, &plain_body, "harness_generic", ChcConfig::default());
            off.current_instance = Some(plain);
            prescan_loop_contracts_beyond_body(&mut off);
            assert_eq!(off.sound_fallback_count(), 0, "no -Z loop-contracts, no booking");
        }

        let panicky = find_instance_by_suffix(tcx, "harness_generic_should_panic");
        let panicky_body = panicky.body().expect("body");
        {
            let _guard = crate::kani_middle::dyn_universe::HarnessUniverseGuard::install(
                std::sync::Arc::new(universe_of(tcx, panicky, &none)),
            );
            let mut harness = ChcCtx::new(tcx, &panicky_body, "harness_generic_should_panic", on);
            harness.current_instance = Some(panicky);
            prescan_loop_contracts_beyond_body(&mut harness);
            assert_eq!(harness.sound_fallback_count(), 1);
            assert_eq!(
                harness.vc.accounted_approximations, 0,
                "a should_panic harness must not account it"
            );
        }

        // No universe installed: a body encoded outside a per-harness codegen.
        let unrelated = find_instance_by_suffix(tcx, "harness_unrelated");
        let unrelated_body = unrelated.body().expect("body");
        let mut harness = ChcCtx::new(tcx, &unrelated_body, "harness_unrelated", on);
        harness.current_instance = Some(unrelated);
        prescan_loop_contracts_beyond_body(&mut harness);
        assert_eq!(harness.sound_fallback_count(), 1, "no call graph: fail closed");
    });
}

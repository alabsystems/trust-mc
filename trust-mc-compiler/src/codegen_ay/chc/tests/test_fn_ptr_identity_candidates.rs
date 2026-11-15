// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Design 3 of `docs/chc-hole-fix-designs-2026-09-24.md`: fn-pointer identity
//! and candidate completeness (`call/fn_ptr_targets.rs`,
//! `dyn_dispatch_scope.rs`, `kani_middle/dyn_universe.rs`). The driver
//! measurements are in `tools/soundness-duals/walker_fn_ptr_target_dual.rs` and
//! `walker_dispatch_candidates_dual.rs`.
//!
//! The solver probes come in pairs that differ only in the asserted
//! predicate, so the safe probe's `unsat` shows nothing else in the program
//! can fail, and the bug probe's `sat` is then its assertion. Before design 3
//! each bug probe here was `unsat` (a false proof) and each fail-closed probe
//! recorded no reason.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

/// Spelled out rather than imported, so this file compiles, and fails, against
/// an encoder that never records them.
const CANDIDATES_INCOMPLETE: &str = "fn_ptr_candidates_incomplete";
const TARGET_UNWALKABLE: &str = "fn_ptr_target_unwalkable";
const INDIRECT_CALL_HAVOCKED: &str = "nested_indirect_call_havocked";
const DYN_CANDIDATES_INCOMPLETE: &str = "dyn_dispatch_candidates_incomplete";
const DYN_CANDIDATE_UNWALKABLE: &str = "dyn_dispatch_candidate_unwalkable";
const DYN_PRINCIPAL_MISMATCH: &str = "dyn_dispatch_principal_mismatch";
const INVALID_FN_PTR: &str = "invalid function pointer";

const PROBE: &str = r#"
    #![allow(dead_code)]

    mod m1 {
        pub fn op2(a: u8, b: u8) -> u8 { a.wrapping_add(b) }
    }
    mod m2 {
        pub fn op2(a: u8, b: u8) -> u8 { unsafe { a.unchecked_add(b) } }
    }
    fn add_safe(a: u8, b: u8) -> u8 { a.wrapping_add(b) }
    fn add_ub(a: u8, b: u8) -> u8 { unsafe { a.unchecked_add(b) } }
    fn big_ub(a: u8, b: u8) -> u8 {
        let mut r = a;
        if b == 1 { r ^= 1; }
        if b == 2 { r ^= 2; }
        if b == 3 { r ^= 3; }
        if b == 4 { r ^= 4; }
        if b == 5 { r ^= 5; }
        if b == 6 { r ^= 6; }
        if b == 7 { r ^= 7; }
        if b == 8 { r ^= 8; }
        if b == 9 { r ^= 9; }
        if b == 10 { r ^= 10; }
        if b == 11 { r ^= 11; }
        if b == 12 { r ^= 12; }
        if b == 13 { r ^= 13; }
        if b == 14 { r ^= 14; }
        unsafe { r.unchecked_add(b) }
    }
    static S_UB: fn(u8, u8) -> u8 = add_ub;

    pub trait Op { fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8; }
    pub struct A;
    pub struct B;
    impl Op for A { fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8 { f(a, b) } }
    impl Op for B { fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8 { f(a, b) } }
    fn pick(c: bool) -> Box<dyn Op> { if c { Box::new(A) } else { Box::new(B) } }

    // --- D1: identity per instance, not per trimmed name ---------------------
    pub fn probe_samename_distinct_safe() -> bool {
        let p1: fn(u8, u8) -> u8 = m1::op2;
        let p2: fn(u8, u8) -> u8 = m2::op2;
        assert!(p1 != p2);
        true
    }
    pub fn probe_samename_distinct_bug() -> bool {
        let p1: fn(u8, u8) -> u8 = m1::op2;
        let p2: fn(u8, u8) -> u8 = m2::op2;
        assert!(p1 == p2);
        true
    }
    // The walker's fn-pointer arm runs `m2::op2`, not the decoy `m1::op2`.
    pub fn probe_samename_in_dyn_bug(c: bool, a: u8, b: u8) -> u8 {
        let decoy: fn(u8, u8) -> u8 = m1::op2;
        let r0 = decoy(0, 0);
        let f: fn(u8, u8) -> u8 = m2::op2;
        r0 ^ pick(c).op(f, a, b)
    }

    // --- Completeness: a symbolic choice on the host -------------------------
    pub fn probe_host_symbolic_bug(c: bool, a: u8, b: u8) -> u8 {
        let f: fn(u8, u8) -> u8 = if c { add_safe } else { add_ub };
        f(a, b)
    }
    pub fn probe_host_symbolic_safe(c: bool, a: u8, b: u8) -> u8 {
        if a >= 100 || b >= 100 { return 0; }
        let f: fn(u8, u8) -> u8 = if c { add_safe } else { add_ub };
        f(a, b)
    }

    // --- Fail closed: a static pointer, a target too large ------------------
    pub fn probe_static_in_dyn(c: bool, a: u8, b: u8) -> u8 {
        let f = S_UB;
        pick(c).op(f, a, b)
    }
    pub fn probe_too_large_in_dyn(c: bool, a: u8, b: u8) -> u8 {
        let f: fn(u8, u8) -> u8 = big_ub;
        pick(c).op(f, a, b)
    }

    // --- Completeness from the harness universe -------------------------------
    #[inline(never)]
    fn choose(c: bool) -> fn(u8, u8) -> u8 { if c { add_safe } else { add_ub } }
    // The pointer is a call's result: only the universe knows its targets.
    pub fn probe_returned_in_dyn_bug(c: bool, a: u8, b: u8) -> u8 {
        let f = choose(c);
        pick(c).op(f, a, b)
    }
    // The same, in a harness where a static holds a fn pointer: the encoder
    // does not read that value as an id, so the universe proves nothing.
    pub fn probe_returned_in_dyn_with_static(c: bool, a: u8, b: u8) -> u8 {
        let s = S_UB;
        let f = if c { choose(c) } else { s };
        pick(c).op(f, a, b)
    }

    // --- dyn: candidates and principal ---------------------------------------
    pub trait Op2 { fn op2(&self, a: u8, b: u8) -> u8; }
    pub struct Small;
    pub struct SmallUb;
    pub struct Big;
    impl Op2 for Small { fn op2(&self, a: u8, b: u8) -> u8 { a.wrapping_add(b) } }
    impl Op2 for SmallUb { fn op2(&self, a: u8, b: u8) -> u8 { unsafe { a.unchecked_add(b) } } }
    // Over the walker's inline budget on its own (the relaxed CHC budget is
    // 40 effective blocks).
    impl Op2 for Big {
        fn op2(&self, a: u8, b: u8) -> u8 {
            let mut r = a;
            if b == 1 { r ^= 1; }
            if b == 2 { r ^= 2; }
            if b == 3 { r ^= 3; }
            if b == 4 { r ^= 4; }
            if b == 5 { r ^= 5; }
            if b == 6 { r ^= 6; }
            if b == 7 { r ^= 7; }
            if b == 8 { r ^= 8; }
            if b == 9 { r ^= 9; }
            if b == 10 { r ^= 10; }
            if b == 11 { r ^= 11; }
            if b == 12 { r ^= 12; }
            if b == 13 { r ^= 13; }
            if b == 14 { r ^= 14; }
            if b == 15 { r ^= 15; }
            if b == 16 { r ^= 16; }
            if b == 17 { r ^= 17; }
            if b == 18 { r ^= 18; }
            if b == 19 { r ^= 19; }
            if b == 20 { r ^= 20; }
            if b == 21 { r ^= 21; }
            if b == 22 { r ^= 22; }
            if b == 23 { r ^= 23; }
            if b == 24 { r ^= 24; }
            if b == 25 { r ^= 25; }
            if b == 26 { r ^= 26; }
            if b == 27 { r ^= 27; }
            if b == 28 { r ^= 28; }
            if b == 29 { r ^= 29; }
            if b == 30 { r ^= 30; }
            if b == 31 { r ^= 31; }
            if b == 32 { r ^= 32; }
            unsafe { r.unchecked_add(b) }
        }
    }

    // `Big` is a runtime type here and cannot be walked.
    pub fn probe_dyn_big_runtime(c: bool, a: u8, b: u8) -> u8 {
        let o: Box<dyn Op2> = if c { Box::new(Small) } else { Box::new(Big) };
        o.op2(a, b)
    }
    // `Big` is a candidate but never a runtime type here.
    pub fn probe_dyn_big_not_runtime(c: bool, a: u8, b: u8) -> u8 {
        let o: Box<dyn Op2> = if c { Box::new(Small) } else { Box::new(SmallUb) };
        o.op2(a, b)
    }

    pub trait MyFn: Fn(u8, u8) -> u8 {}
    impl<T: Fn(u8, u8) -> u8> MyFn for T {}
    pub fn probe_subtrait_bug(a: u8, b: u8) -> u8 {
        let f: Box<dyn MyFn> = Box::new(|x: u8, y: u8| x.wrapping_add(y));
        let d: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| x.wrapping_mul(y));
        let r = f(a, b);
        assert!(r == a.wrapping_mul(b));
        d(0, 0)
    }
    pub fn probe_subtrait_safe(a: u8, b: u8) -> u8 {
        let f: Box<dyn MyFn> = Box::new(|x: u8, y: u8| x.wrapping_add(y));
        let d: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| x.wrapping_mul(y));
        let r = f(a, b);
        assert!(r == a.wrapping_add(b));
        d(0, 0)
    }
    fn sub_item(x: u8, y: u8) -> u8 { x.wrapping_sub(y) }
    pub fn probe_closure_and_fn_item_bug(c: bool, a: u8, b: u8) -> u8 {
        if b == 0 { return 0; }
        let c1 = |x: u8, y: u8| x.wrapping_add(y);
        let f: &dyn Fn(u8, u8) -> u8 = if c { &c1 } else { &sub_item };
        let r = f(a, b);
        assert!(r == a.wrapping_add(b));
        r
    }
"#;

/// How the probe is encoded: with or without the reachability collector's
/// dyn-coercion universe (a per-harness codegen always has it).
#[derive(Clone, Copy, PartialEq)]
enum Universe {
    Collected,
    Absent,
}

/// Encode `fn_name` from the probe crate at the driver's track level; return
/// its translation-drop site reasons, the messages of its registered
/// properties and, when `solve` is set, the solver verdict on its CHC.
fn encode_probe(
    fn_name: &str,
    universe: Universe,
    solve: bool,
) -> (BTreeMap<String, usize>, Vec<String>, Option<(String, String)>) {
    encode_probe_in(PROBE, fn_name, universe, solve)
}

/// [`encode_probe`] over the crate `source`.
fn encode_probe_in(
    source: &str,
    fn_name: &str,
    universe: Universe,
    solve: bool,
) -> (BTreeMap<String, usize>, Vec<String>, Option<(String, String)>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let ran = AtomicBool::new(false);
    let mut verdict = None;
    let mut messages = Vec::new();
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let _universe_guard = (universe == Universe::Collected)
            .then(|| install_harness_dyn_universe(ctx.tcx, instance));
        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, config);
        messages = vc.properties.iter().filter_map(|p| p.message.clone()).collect();
        if solve {
            let smt = emit_chc(&vc).to_string();
            let result =
                run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(Z3_TEST_TIMEOUT_SECS))
                    .unwrap_or_else(|e| panic!("{fn_name}: AY execution failed: {e}. SMT:\n{smt}"));
            verdict = Some((result, smt));
        }
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and {fn_name} was encoded");
    let sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (sites, messages, verdict)
}

/// Assert the solver verdict of an [`encode_probe`] run, showing the CHC when
/// it differs.
fn assert_verdict(fn_name: &str, verdict: Option<(String, String)>, expected: &str, why: &str) {
    let (result, smt) = verdict.unwrap_or_else(|| panic!("{fn_name}: the probe was not solved"));
    assert_eq!(result, expected, "{fn_name}: {why}. SMT:\n{smt}");
}

fn has(sites: &BTreeMap<String, usize>, reason: &str) -> bool {
    sites.get(reason).is_some_and(|count| *count > 0)
}

/// D1: `m1::op2` and `m2::op2` are two functions, so their pointers differ.
/// They used to share the trimmed-name id `op2`: `p1 != p2` failed.
#[test]
fn test_samename_fn_ptrs_have_distinct_identities() {
    let (_, _, verdict) = encode_probe("probe_samename_distinct_safe", Universe::Absent, true);
    assert_verdict(
        "probe_samename_distinct_safe",
        verdict,
        "unsat",
        "two same-named functions must get two identities",
    );
    let (_, _, verdict) = encode_probe("probe_samename_distinct_bug", Universe::Absent, true);
    assert_verdict("probe_samename_distinct_bug", verdict, "sat", "the pointers are not equal");
}

/// D1 through the walker: a call through `m2::op2` inside a walked dyn method
/// runs `m2::op2`, whose `unchecked_add` can overflow. With one id for both,
/// the decoy `m1::op2` was walked instead.
#[test]
fn test_samename_target_in_dyn_walk_is_the_named_function() {
    let (sites, _, verdict) = encode_probe("probe_samename_in_dyn_bug", Universe::Collected, true);
    assert_verdict(
        "probe_samename_in_dyn_bug",
        verdict,
        "sat",
        "the overflow in m2::op2 must be reachable",
    );
    assert!(
        !has(&sites, CANDIDATES_INCOMPLETE),
        "an exact id is a complete candidate set: {sites:?}"
    );
}

/// A symbolic choice between two reified functions on the host is dispatched
/// over both, under `pointer == id`, with the obligation `pointer ∈ ids` as
/// its default arm. The first reification used to be walked alone.
#[test]
fn test_host_symbolic_fn_ptr_dispatches_every_target() {
    let (sites, messages, verdict) =
        encode_probe("probe_host_symbolic_bug", Universe::Collected, true);
    assert_verdict(
        "probe_host_symbolic_bug",
        verdict,
        "sat",
        "the add_ub arm's overflow must be reachable",
    );
    assert!(
        messages.iter().any(|m| m == INVALID_FN_PTR),
        "the default arm is a checked obligation: {messages:?}"
    );
    assert!(!has(&sites, CANDIDATES_INCOMPLETE), "a closed local is complete: {sites:?}");
    let (_, _, verdict) = encode_probe("probe_host_symbolic_safe", Universe::Collected, true);
    assert_verdict(
        "probe_host_symbolic_safe",
        verdict,
        "unsat",
        "with small operands neither target overflows and the obligation holds",
    );
}

/// A pointer read from a static inside a walked dyn method: its value is not
/// known, so the call fails closed. With no target reified in the host it
/// used to be havocked as the blessed `nested_call_overapprox`.
#[test]
fn test_static_fn_ptr_in_dyn_walk_fails_closed() {
    let (sites, _, _) = encode_probe("probe_static_in_dyn", Universe::Collected, false);
    assert!(
        has(&sites, CANDIDATES_INCOMPLETE) || has(&sites, INDIRECT_CALL_HAVOCKED),
        "a pointer from a static has an unknown target: {sites:?}"
    );
}

/// A lone exact target over the inline budget fails closed. Its walk used to
/// return None with nothing recorded.
#[test]
fn test_lone_target_too_large_fails_closed() {
    let (sites, _, _) = encode_probe("probe_too_large_in_dyn", Universe::Collected, false);
    assert!(
        has(&sites, TARGET_UNWALKABLE),
        "an unwalked exact target drops its obligations: {sites:?}"
    );
}

/// A dyn candidate that cannot be walked fails closed when it is a runtime
/// type of the receiver, and costs nothing when the harness never unsizes it.
#[test]
fn test_unwalkable_dyn_candidate_fails_closed_only_as_a_runtime_type() {
    let (sites, _, _) = encode_probe("probe_dyn_big_runtime", Universe::Collected, false);
    assert!(
        has(&sites, DYN_CANDIDATE_UNWALKABLE),
        "Big is a runtime type and was not walked: {sites:?}"
    );
    let (sites, _, _) = encode_probe("probe_dyn_big_not_runtime", Universe::Collected, false);
    assert!(
        !has(&sites, DYN_CANDIDATE_UNWALKABLE) && !has(&sites, DYN_CANDIDATES_INCOMPLETE),
        "Big is never unsized here, and the arms cover Small and SmallUb: {sites:?}"
    );
}

/// With no universe (a body encoded outside a per-harness codegen), a dyn
/// merge cannot show its arms cover every runtime type.
#[test]
fn test_dyn_merge_without_universe_fails_closed() {
    let (sites, _, _) = encode_probe("probe_dyn_big_not_runtime", Universe::Absent, false);
    assert!(has(&sites, DYN_CANDIDATES_INCOMPLETE), "no universe, no completeness: {sites:?}");
}

/// `Box<dyn MyFn>` with `trait MyFn: Fn(..)`: the call dispatches over
/// `MyFn`'s candidates, whose list the stored vtable id indexes. The `Fn` list
/// held only the `wrapping_mul` closure, which was walked in place of the
/// real one and proved `r == a.wrapping_mul(b)`.
#[test]
fn test_subtrait_receiver_dispatches_over_its_principal() {
    let (sites, _, verdict) = encode_probe("probe_subtrait_bug", Universe::Collected, true);
    assert_verdict(
        "probe_subtrait_bug",
        verdict,
        "sat",
        "the called closure adds, so r == a * b can fail",
    );
    assert!(!has(&sites, DYN_PRINCIPAL_MISMATCH), "MyFn has Fn as a supertrait: {sites:?}");
    let (_, _, verdict) = encode_probe("probe_subtrait_safe", Universe::Collected, true);
    assert_verdict("probe_subtrait_safe", verdict, "unsat", "the called closure adds");
}

/// A closure and a function item behind one `&dyn Fn`: both are candidates.
/// The closure lane used to drop the fn item and walk the closure alone.
#[test]
fn test_closure_and_fn_item_behind_dyn_fn_are_both_candidates() {
    let (_, _, verdict) = encode_probe("probe_closure_and_fn_item_bug", Universe::Collected, true);
    assert_verdict(
        "probe_closure_and_fn_item_bug",
        verdict,
        "sat",
        "the fn item subtracts, so r == a + b can fail",
    );
}

/// A pointer returned by a call has no local value domain, but the harness's
/// reachability universe lists every function it reifies at that type: the
/// set is complete, dispatched with the "invalid function pointer" obligation.
#[test]
fn test_returned_fn_ptr_is_complete_by_the_universe() {
    let (sites, messages, verdict) =
        encode_probe("probe_returned_in_dyn_bug", Universe::Collected, true);
    assert_verdict(
        "probe_returned_in_dyn_bug",
        verdict,
        "sat",
        "the add_ub target's overflow must be reachable",
    );
    assert!(!has(&sites, CANDIDATES_INCOMPLETE), "the universe completes the set: {sites:?}");
    assert!(
        messages.iter().any(|m| m == INVALID_FN_PTR),
        "the default arm is a checked obligation: {messages:?}"
    );
}

/// A static that holds a fn pointer disables the universe for fn pointers:
/// its value is not read as an id, so a pointer that may come from it has an
/// unknown target.
#[test]
fn test_fn_ptr_in_a_static_disables_the_universe() {
    let (sites, _, _) =
        encode_probe("probe_returned_in_dyn_with_static", Universe::Collected, false);
    assert!(
        has(&sites, CANDIDATES_INCOMPLETE) || has(&sites, INDIRECT_CALL_HAVOCKED),
        "a pointer that may come from a static has an unknown target: {sites:?}"
    );
}

/// The review of design 3 (2026-09-26): `dyn` -> `dyn` unsizes, a
/// `kani::assume` in a body reached through a fn pointer or `dyn`, fn pointers
/// held by a constant or static, and fn pointers read back through another
/// type.
const REVIEW_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    pub trait Sup { fn m(&self, a: u8, b: u8) -> u8; }
    pub trait Sub: Sup {}
    pub struct UA;
    pub struct UB;
    pub struct UC;
    impl Sup for UA { fn m(&self, a: u8, b: u8) -> u8 { a.wrapping_add(b) } }
    impl Sup for UB { fn m(&self, a: u8, b: u8) -> u8 { unsafe { a.unchecked_add(b) } } }
    impl Sup for UC { fn m(&self, a: u8, b: u8) -> u8 { a.wrapping_mul(b) } }
    impl Sub for UB {}
    impl Sub for UC {}

    // --- trait upcasting: UB/UC reach `dyn Sup` only through `dyn Sub` -------
    pub fn probe_upcast_bug(c: bool, a: u8, b: u8) -> u8 {
        let o: Box<dyn Sup> = if c { Box::new(UA) } else { let s: Box<dyn Sub> = Box::new(UB); s };
        o.m(a, b)
    }
    pub fn probe_upcast_safe(c: bool, a: u8, b: u8) -> u8 {
        let o: Box<dyn Sup> = if c { Box::new(UA) } else { let s: Box<dyn Sub> = Box::new(UC); s };
        let r = o.m(a, b);
        assert!(r == a.wrapping_add(b) || r == a.wrapping_mul(b));
        r
    }
    #[inline(never)]
    fn upcast_box(s: Box<dyn Sub>) -> Box<dyn Sup> { s }
    pub fn probe_upcast_in_callee_bug(c: bool, a: u8, b: u8) -> u8 {
        let o: Box<dyn Sup> = if c { Box::new(UA) } else { upcast_box(Box::new(UB)) };
        o.m(a, b)
    }

    // A `dyn Sub` whose runtime types no coercion records (a transmute): the
    // upcast's target has unknown runtime types, so the lone direct `UA` is
    // not its sole runtime type.
    pub fn probe_upcast_unknown_source(a: u8, b: u8, raw: (usize, usize)) -> u8 {
        let direct: Box<dyn Sup> = Box::new(UA);
        let r0 = direct.m(a, b);
        let s: Box<dyn Sub> = unsafe { core::mem::transmute(raw) };
        let o: Box<dyn Sup> = s;
        r0 ^ o.m(a, b)
    }

    // --- dropping an auto trait keeps the principal --------------------------
    pub trait Tr3 { fn t(&self, a: u8, b: u8) -> u8; }
    impl Tr3 for UA { fn t(&self, a: u8, b: u8) -> u8 { a.wrapping_add(b) } }
    impl Tr3 for UB { fn t(&self, a: u8, b: u8) -> u8 { unsafe { a.unchecked_add(b) } } }
    pub fn probe_drop_send_bug(c: bool, a: u8, b: u8) -> u8 {
        let o: Box<dyn Tr3> =
            if c { Box::new(UA) } else { let s: Box<dyn Tr3 + Send> = Box::new(UB); s };
        o.t(a, b)
    }
    pub fn probe_drop_send_safe(c: bool, a: u8, b: u8) -> u8 {
        if a >= 100 || b >= 100 { return 0; }
        let o: Box<dyn Tr3> =
            if c { Box::new(UA) } else { let s: Box<dyn Tr3 + Send> = Box::new(UB); s };
        o.t(a, b)
    }

    // --- the Fn family: a closure boxed as `dyn MyFn`, upcast to `dyn Fn` ----
    pub trait MyFn: Fn(u8, u8) -> u8 {}
    impl<T: Fn(u8, u8) -> u8> MyFn for T {}
    pub fn probe_upcast_fn_only_bug(a: u8, b: u8) -> u8 {
        let safe: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| x.wrapping_add(y));
        let r0 = safe(a, 1);
        let g: Box<dyn MyFn> = Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) });
        let f: Box<dyn Fn(u8, u8) -> u8> = g;
        r0 ^ f(a, b)
    }

    // --- an assume in a body reached through a fn pointer or dyn -------------
    fn assume_small(a: u8, b: u8) -> u8 { kani::assume(a < 10); a.wrapping_add(b) }
    fn assume_small2(a: u8, b: u8) -> u8 { kani::assume(a < 10); a.wrapping_sub(b) }
    pub fn probe_assume_fnptr_safe(a: u8, b: u8) -> u8 {
        let f: fn(u8, u8) -> u8 = assume_small;
        let r = f(a, b);
        assert!(a < 10);
        r
    }
    pub fn probe_assume_fnptr_bug(a: u8, b: u8) -> u8 {
        let f: fn(u8, u8) -> u8 = assume_small;
        let r = f(a, b);
        assert!(a < 9);
        r
    }
    pub fn probe_assume_fnptr_multi_safe(c: bool, a: u8, b: u8) -> u8 {
        let f: fn(u8, u8) -> u8 = if c { assume_small } else { assume_small2 };
        let r = f(a, b);
        assert!(a < 10);
        r
    }
    pub trait Asm { fn m(&self, a: u8) -> u8; }
    impl Asm for UA { fn m(&self, a: u8) -> u8 { kani::assume(a < 10); a } }
    impl Asm for UB { fn m(&self, a: u8) -> u8 { kani::assume(a < 10); a.wrapping_add(1) } }
    pub fn probe_assume_dyn_safe(c: bool, a: u8) -> u8 {
        let o: Box<dyn Asm> = if c { Box::new(UA) } else { Box::new(UB) };
        let r = o.m(a);
        assert!(a < 10);
        r
    }

    // --- a fn pointer held by a const or static is the function's identity ---
    fn add_safe(a: u8, b: u8) -> u8 { a.wrapping_add(b) }
    fn add_other(a: u8, b: u8) -> u8 { a.wrapping_sub(b) }
    static SF: fn(u8, u8) -> u8 = add_safe;
    const CF: fn(u8, u8) -> u8 = add_safe;
    pub fn probe_static_eq_reified_safe() -> bool {
        let f: fn(u8, u8) -> u8 = add_safe;
        assert!(SF == f);
        true
    }
    pub fn probe_static_eq_reified_bug() -> bool {
        let f: fn(u8, u8) -> u8 = add_other;
        assert!(SF == f);
        true
    }
    pub fn probe_const_eq_reified_safe() -> bool {
        let f: fn(u8, u8) -> u8 = add_safe;
        assert!(CF == f);
        true
    }

    // --- a fn pointer read back through another type -------------------------
    #[inline(never)]
    fn launder(p: *const ()) -> *const () { p }
    pub fn probe_fnptr_void_ptr_callback(a: u8, b: u8) -> u8 {
        let f: fn(u8, u8) -> u8 = add_safe;
        let p = launder(f as *const ());
        let slot: *const *const () = &p;
        let g = unsafe { *(slot as *const fn(u8, u8) -> u8) };
        g(a, b)
    }
"#;

/// Trait upcasting: `UB` reaches `dyn Sup` only through a `dyn Sub`, and the
/// coercion site used to store the id of the pseudo-candidate `dyn Sub` in
/// `Sup`'s list. The dispatch dropped that candidate silently, the arms for
/// `UA` and `UB` "covered" the universe, and the default arm stood for `UB`:
/// its overflow verified clean. The id is now mapped from `Sub`'s list.
#[test]
fn test_upcast_maps_the_source_vtable_id() {
    let (sites, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_upcast_bug", Universe::Collected, true);
    assert_verdict(
        "probe_upcast_bug",
        verdict,
        "sat",
        "UB's overflow is reached through the upcast",
    );
    assert!(
        !has(&sites, DYN_CANDIDATES_INCOMPLETE) && !has(&sites, DYN_CANDIDATE_UNWALKABLE),
        "the mapped id names a walked arm: {sites:?}"
    );
    let (sites, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_upcast_safe", Universe::Collected, true);
    assert_verdict(
        "probe_upcast_safe",
        verdict,
        "unsat",
        "the upcast object is a UC, which multiplies",
    );
    assert!(!has(&sites, "dyn_to_dyn_vtable_unmapped"), "the source id is known: {sites:?}");
}

/// An upcast inside a walked callee: its id is derived there too (or fails
/// closed), never copied from `Sub`'s list into `Sup`'s, where it named `UA`.
#[test]
fn test_upcast_in_a_walked_callee_is_not_a_copied_id() {
    let (sites, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_upcast_in_callee_bug", Universe::Collected, true);
    let (result, smt) = verdict.expect("solved");
    let failed_closed = has(&sites, "dyn_to_dyn_vtable_unmapped")
        || has(&sites, DYN_CANDIDATES_INCOMPLETE)
        || has(&sites, DYN_CANDIDATE_UNWALKABLE);
    assert!(
        result == "sat" || failed_closed,
        "UB's overflow is reachable, or the dispatch fails closed: {result} {sites:?}\n{smt}"
    );
}

/// An upcast from a trait object whose runtime types the collector never saw
/// (built by a transmute here, by a stub in general): the target principal's
/// runtime types are unknown, so no merge over it is complete and the type
/// the body coerces directly is not walked as the sole runtime type.
#[test]
fn test_upcast_from_an_unrecorded_source_fails_closed() {
    let (sites, _, _) =
        encode_probe_in(REVIEW_PROBE, "probe_upcast_unknown_source", Universe::Collected, false);
    assert!(
        has(&sites, DYN_CANDIDATES_INCOMPLETE) || has(&sites, "dyn_to_dyn_vtable_unmapped"),
        "the upcast object's runtime type is unknown: {sites:?}"
    );
}

/// Dropping an auto trait keeps the principal: the id is the source's.
#[test]
fn test_auto_trait_drop_copies_the_source_vtable_id() {
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_drop_send_bug", Universe::Collected, true);
    assert_verdict("probe_drop_send_bug", verdict, "sat", "UB's overflow survives the cast");
    let (sites, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_drop_send_safe", Universe::Collected, true);
    assert_verdict("probe_drop_send_safe", verdict, "unsat", "small operands never overflow");
    assert!(!has(&sites, DYN_CANDIDATES_INCOMPLETE), "both runtime types are walked: {sites:?}");
}

/// A closure boxed as `dyn MyFn` and upcast to `dyn Fn` is a runtime type of
/// `dyn Fn` (the universe closes over upcasts): the lone closure coerced to
/// `dyn Fn` directly is no longer walked unconditionally.
#[test]
fn test_fn_family_upcast_is_a_runtime_type() {
    let (sites, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_upcast_fn_only_bug", Universe::Collected, true);
    let (result, smt) = verdict.expect("solved");
    let failed_closed = has(&sites, "dyn_to_dyn_vtable_unmapped")
        || has(&sites, DYN_CANDIDATES_INCOMPLETE)
        || has(&sites, "fn_trait_dispatch_unguarded_candidate");
    assert!(
        result == "sat" || failed_closed,
        "the upcast closure's overflow is reachable, or the call fails closed: \
         {result} {sites:?}\n{smt}"
    );
}

/// A `kani::assume` in a body reached through a fn pointer constrains the
/// caller's path, as it does through a direct call. The fn-pointer emit
/// dropped it and left the pruned leaf as a free value.
#[test]
fn test_callee_assume_through_a_fn_pointer_holds_for_the_caller() {
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_assume_fnptr_safe", Universe::Collected, true);
    assert_verdict("probe_assume_fnptr_safe", verdict, "unsat", "the callee assumed a < 10");
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_assume_fnptr_bug", Universe::Collected, true);
    assert_verdict("probe_assume_fnptr_bug", verdict, "sat", "a == 9 satisfies the assume");
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_assume_fnptr_multi_safe", Universe::Collected, true);
    assert_verdict(
        "probe_assume_fnptr_multi_safe",
        verdict,
        "unsat",
        "both targets assume a < 10, each under its own pointer guard",
    );
}

/// The same through a multi-impl `dyn` dispatch.
#[test]
fn test_callee_assume_through_dyn_holds_for_the_caller() {
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_assume_dyn_safe", Universe::Collected, true);
    assert_verdict("probe_assume_dyn_safe", verdict, "unsat", "both impls assume a < 10");
}

/// A fn pointer a static or const holds is the function's identity: `SF ==
/// f` holds for the same function (it compared a hash with a minted id and
/// failed) and fails for another.
#[test]
fn test_static_and_const_fn_ptrs_are_the_function_identity() {
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_static_eq_reified_safe", Universe::Absent, true);
    assert_verdict("probe_static_eq_reified_safe", verdict, "unsat", "SF holds add_safe");
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_static_eq_reified_bug", Universe::Absent, true);
    assert_verdict("probe_static_eq_reified_bug", verdict, "sat", "SF is not add_other");
    let (_, _, verdict) =
        encode_probe_in(REVIEW_PROBE, "probe_const_eq_reified_safe", Universe::Absent, true);
    assert_verdict("probe_const_eq_reified_safe", verdict, "unsat", "CF holds add_safe");
}

/// A fn pointer read back through another type is completed by the universe,
/// and its "invalid function pointer" obligation is uncertified: it reads a
/// freed variable recorded as a sound havoc, so a violation is never Genuine.
#[test]
fn test_universe_completed_obligation_is_uncertified() {
    let (sites, messages, _) =
        encode_probe_in(REVIEW_PROBE, "probe_fnptr_void_ptr_callback", Universe::Collected, false);
    if messages.iter().any(|m| m == INVALID_FN_PTR) {
        assert!(
            has(&sites, "fn_ptr_obligation_value_uncertified"),
            "an obligation over a loaded pointer must not certify: {sites:?}"
        );
    } else {
        assert!(
            has(&sites, CANDIDATES_INCOMPLETE) || has(&sites, INDIRECT_CALL_HAVOCKED),
            "no obligation: the call must fail closed instead: {sites:?} {messages:?}"
        );
    }
}

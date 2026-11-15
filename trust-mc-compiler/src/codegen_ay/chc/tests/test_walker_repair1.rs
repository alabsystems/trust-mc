// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Repair round 1 of fix/chc-walker-fail-closed (walker fail-closed review 6;
//! docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed: repair round
//! 1"): (1) an array slice view's length scoped to its path and its write,
//! (2, 3) SwitchInt discriminants compared at their type's width and a
//! havocked fieldless enum constrained to its discriminants, (4) loops the
//! walker abandons under a declared unwind bound, (5) the host-assumed replay
//! raise bounded by where it helps and what it costs, (7) a constant-length
//! reduction replayed to its length, (8) `ManuallyDrop::deref` as the
//! identity it is. Every probe asserts the shape it is about.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

use crate::codegen_ay::chc::call::inline_body::{
    InlineReturn, extract_inline_assume_guard, translate_inline_body,
};
use ay_bindings::{Expr, ExprValue, rebuild_with_children};
use rustc_public::mir::{Body, TerminatorKind};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicBool, Ordering};
use trust_mc_core::chc_const_prop::eval::try_eval_to_const;

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    use std::cmp::Ordering;

    // (1) The array arm is walked first (`otherwise` of `switchInt(c)`).
    pub fn probe_join_len(c: bool, v: &[u8]) -> usize {
        let arr = [1u8, 2, 3, 4];
        let s: &[u8] = if c { &arr } else { v };
        s.len()
    }
    // (1) Only one arm writes the slice local; the other reads the value it
    // had before the SwitchInt.
    pub fn probe_join_len_one_arm(c: bool, v: &[u8]) -> usize {
        let arr = [1u8, 2, 3, 4];
        let mut s: &[u8] = v;
        if c {
            s = &arr;
        }
        s.len()
    }
    // (1) One path writes the slice local twice.
    pub fn probe_len_reassign(v: &[u8]) -> usize {
        let arr = [1u8, 2, 3, 4];
        let mut n = 0usize;
        let mut k = 0u8;
        while k < 2 {
            let s: &[u8] = if k == 0 { &arr } else { v };
            n = s.len();
            k += 1;
        }
        n
    }

    // (2, 3) `Ordering` is `#[repr(i8)]`: `Less` is -1, SwitchInt case 255.
    pub fn probe_ordering_match(o: Ordering) -> u8 {
        match o {
            Ordering::Less => 1,
            Ordering::Equal => 2,
            Ordering::Greater => 3,
        }
    }
    pub fn probe_less_arm(o: Ordering) -> u8 {
        match o {
            Ordering::Less => 10,
            _ => 20,
        }
    }

    // (2) A fieldless enum from a callee the walker havocs (float
    // arithmetic), and one from a callee that forges it.
    #[derive(Clone, Copy)]
    pub enum E3 { A, B, C }
    #[inline(never)]
    fn classify(x: f32) -> E3 {
        if x < 0.0 { E3::A } else if x == 0.0 { E3::B } else { E3::C }
    }
    #[inline(never)]
    fn forge(x: f32) -> E3 {
        let b = (x * 2.0) as u8;
        unsafe { std::mem::transmute::<u8, E3>(b) }
    }
    pub fn probe_classify_match(x: f32) -> u8 {
        match classify(x * 2.0) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }
    pub fn probe_forge_match(x: f32) -> u8 {
        match forge(x) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }

    // (4) An obligation-free loop, and a branchy one.
    pub fn probe_while_count(n: u8) -> u8 {
        let mut i = 0u8;
        let mut acc = 0u8;
        while i < n {
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }
    pub fn probe_branchy(n: u8, m: u8) -> u8 {
        let mut acc: u8 = 0;
        let mut i: u8 = 0;
        while i < n {
            if acc & 1 == 0 { acc = acc.wrapping_add(m); } else { acc = acc.wrapping_mul(3); }
            if acc & 2 == 0 { acc = acc.wrapping_add(1); } else { acc = acc.wrapping_sub(m); }
            i = i.wrapping_add(1);
        }
        acc
    }
    // (4) More than 16 effective blocks around an obligation-free loop.
    #[inline(never)]
    fn big_loop(n: u8, k: u8) -> u8 {
        let mut acc: u8 = 0;
        let mut i: u8 = 0;
        while i < n {
            acc = acc.wrapping_add(i);
            i = i.wrapping_add(1);
        }
        if k == 1 { acc = acc.wrapping_add(3); }
        if k == 2 { acc = acc.wrapping_mul(5); }
        if k == 3 { acc = acc.wrapping_sub(7); }
        if k == 4 { acc = acc.wrapping_add(11); }
        if k == 5 { acc = acc.wrapping_mul(13); }
        if k == 6 { acc = acc.wrapping_sub(17); }
        if k == 7 { acc = acc.wrapping_add(19); }
        if k == 8 { acc = acc.wrapping_mul(23); }
        if k == 9 { acc = acc.wrapping_sub(29); }
        acc
    }
    pub fn probe_big_host(n: u8, k: u8) -> u8 {
        big_loop(n, k)
    }

    // (5) Walked loops under the host's `kani::assume(n <= 10)`: one with no
    // obligation, one whose accumulator feeds an index and an obligation.
    #[inline(never)]
    pub fn probe_free_callee(x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i = 0u8;
        while i < n {
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }
    pub fn probe_free_host(x: u8, n: u8) -> u8 {
        kani::assume(n <= 10);
        probe_free_callee(x, n)
    }
    #[inline(never)]
    pub fn probe_feedback_callee(x: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = x;
        let mut j = 0u8;
        while j < n {
            let k = (acc as i8) % 4;
            acc = acc.wrapping_add(table[k as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
    pub fn probe_feedback_host(x: u8, n: u8) -> u8 {
        kani::assume(n <= 10);
        probe_feedback_callee(x, n)
    }

    // (7) `sum` over nine elements, the ninth past the old replay bound.
    pub fn probe_sum9_ok() {
        let mut a = [0u8; 9];
        a[0] = 200;
        a[8] = 40;
        let s: u8 = a.iter().sum();
        assert!(s == 240);
    }

    // (8) A capacity read through `ManuallyDrop`'s `Deref`.
    pub fn probe_md_cap_ok() {
        let mut v: Vec<u16> = Vec::with_capacity(3);
        v.push(1);
        let v = std::mem::ManuallyDrop::new(v);
        let cap = v.capacity();
        assert!(cap == 3);
    }
"#;

fn with_probe(test: impl for<'tcx> FnOnce(TyCtxt<'tcx>) + Send) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(PROBE, |ctx| {
        test(ctx.tcx);
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and the test body ran");
}

fn arg_params(body: &Body) -> Vec<Expr> {
    (1..=body.arg_locals().len())
        .map(|local| {
            let sort =
                ChcCtx::translate_ty(body.locals()[local].ty).expect("argument type translates");
            Expr::var(format!("arg{local}"), sort)
        })
        .collect()
}

struct Walked {
    result: Option<InlineReturn>,
    reasons: BTreeMap<String, usize>,
}

fn walk_with(tcx: TyCtxt<'_>, fn_name: &str, config: ChcConfig) -> Walked {
    let ctx_name = format!("walker_repair1__{fn_name}");
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let params = arg_params(&body);
    let mut chc_ctx = ChcCtx::new(tcx, &body, ctx_name.as_str(), config);
    chc_ctx.declare_block_relations();
    chc_ctx.mark_inline_field_reads(&body, &params, 0);
    let result =
        translate_inline_body(&mut chc_ctx, &body, &params, 0, &HashMap::new(), Some(instance), 0);
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(&ctx_name)
        .unwrap_or_default();
    Walked { result, reasons }
}

fn walk(tcx: TyCtxt<'_>, fn_name: &str) -> Walked {
    walk_with(tcx, fn_name, ChcConfig::default())
}

fn walk_from_host(tcx: TyCtxt<'_>, host_fn: &str, callee_fn: &str) -> Walked {
    let ctx_name = format!("walker_repair1__{host_fn}");
    let host = find_instance_by_suffix(tcx, host_fn).body().expect("host body");
    let callee = find_instance_by_suffix(tcx, callee_fn);
    let callee_body = callee.body().expect("callee body");
    let call_bb = host
        .blocks
        .iter()
        .position(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return false;
            };
            matches!(
                func.ty(host.locals()).map(|ty| ty.kind()),
                Ok(rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)))
                    if def.name().ends_with(callee_fn)
            )
        })
        .expect("the host calls the callee");
    let params = arg_params(&callee_body);
    let mut chc_ctx = ChcCtx::new(tcx, &host, ctx_name.as_str(), ChcConfig::default());
    chc_ctx.declare_block_relations();
    chc_ctx.mark_inline_field_reads(&callee_body, &params, 0);
    let result = translate_inline_body(
        &mut chc_ctx,
        &callee_body,
        &params,
        call_bb,
        &HashMap::new(),
        Some(callee),
        0,
    );
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(&ctx_name)
        .unwrap_or_default();
    Walked { result, reasons }
}

fn vars_of(expr: &Expr) -> Vec<String> {
    let mut names = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(node.value())) {
            continue;
        }
        if let ExprValue::Var { name } = node.value() {
            names.push(name.to_string());
        }
        stack.extend(node.value().children());
    }
    names
}

fn substitute(expr: &Expr, values: &HashMap<String, Expr>) -> Expr {
    if let ExprValue::Var { name } = expr.value() {
        return values.get(name.as_str()).cloned().unwrap_or_else(|| expr.clone());
    }
    let children: Vec<Expr> = expr.value().children().map(|c| substitute(c, values)).collect();
    if children.is_empty() { expr.clone() } else { rebuild_with_children(expr, children) }
}

fn fold_deep(expr: &Expr) -> Expr {
    let children: Vec<Expr> = expr.value().children().map(fold_deep).collect();
    let rebuilt =
        if children.is_empty() { expr.clone() } else { rebuild_with_children(expr, children) };
    try_eval_to_const(&rebuilt).unwrap_or(rebuilt)
}

fn eval_with(expr: &Expr, values: &[(&str, Expr)]) -> Option<Expr> {
    let values: HashMap<String, Expr> =
        values.iter().map(|(name, value)| ((*name).to_string(), value.clone())).collect();
    try_eval_to_const(&fold_deep(&substitute(expr, &values)))
}

fn as_u128(expr: Option<Expr>) -> Option<u128> {
    match expr?.value() {
        ExprValue::BitVecConst { value, .. } => u128::try_from(value.clone()).ok(),
        _ => None,
    }
}

fn as_bool(expr: Option<Expr>) -> Option<bool> {
    match expr?.value() {
        ExprValue::BoolConst(b) => Some(*b),
        _ => None,
    }
}

/// The bitvector width of the variable `name` in `expr`.
fn var_width(expr: &Expr, name: &str) -> Option<u32> {
    let mut seen = HashSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(node.value())) {
            continue;
        }
        if let ExprValue::Var { name: var } = node.value()
            && var.as_str() == name
        {
            return node.sort().bitvec_width();
        }
        stack.extend(node.value().children());
    }
    None
}

/// A `&[u8]` fat pointer of length `len` (the metadata is the high half).
fn slice_of_len(len: u128) -> Expr {
    Expr::bitvec_const((len << 64) | 0x1000, 128)
}

/// The deferred checks reading an uncertified reach-check variable.
fn reach_checks(walked: &InlineReturn) -> Vec<Option<String>> {
    walked
        .deferred_checks
        .iter()
        .filter(|c| vars_of(&c.check).iter().any(|n| n.starts_with("__walker_uncertified_reach")))
        .map(|c| c.message.clone())
        .collect()
}

/// The largest constant `K` of an exit test `K < n` in `expr`: the last
/// loop pass the walk replayed.
fn deepest_replayed_pass(expr: &Expr) -> Option<u128> {
    let mut deepest = None;
    let mut seen = HashSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(node.value())) {
            continue;
        }
        if let ExprValue::BvULt(lhs, _) = node.value()
            && let Some(k) = as_u128(try_eval_to_const(lhs))
        {
            deepest = Some(deepest.map_or(k, |d: u128| d.max(k)));
        }
        stack.extend(node.value().children());
    }
    deepest
}

fn chc_verdict(tcx: TyCtxt<'_>, name: &str) -> String {
    let instance = find_instance_by_suffix(tcx, name);
    let body = instance.body().expect("function body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name, ChcConfig::default());
    let smt = crate::codegen_ay::emit_chc(&vc).to_string();
    run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
        .unwrap_or_else(|err| format!("error:{err}"))
}

// ---------------------------------------------------------------------------
// (1) An array slice view's length
// ---------------------------------------------------------------------------

/// `s = if c { &arr } else { v }; s.len()`: the array arm is walked first and
/// records `len(s) = 4`; the `v` arm must read `v`'s own length. Before,
/// the side table was not restored between arms and the `v` arm read 4
/// (walker fail-closed review 6, finding 1, `c3_len_in_walk_bug`).
#[test]
fn test_slice_view_len_does_not_leak_into_the_other_arm() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_join_len").result.expect("the walk finishes");
        let at = |c: bool, len: u128| {
            as_u128(eval_with(
                &walked.value,
                &[("arg1", Expr::bool_const(c)), ("arg2", slice_of_len(len))],
            ))
        };
        assert_eq!(at(true, 2), Some(4), "the array arm reads the array's length");
        assert_eq!(at(false, 2), Some(2), "the `v` arm reads `v`'s length");
        assert_eq!(at(false, 7), Some(7), "the `v` arm reads `v`'s length");

        // The arm that does not write `s` reads the entry it had at the
        // SwitchInt, not the array arm's (`switchint.rs`, the per-arm
        // restore of the side tables).
        let one_arm = walk(tcx, "probe_join_len_one_arm").result.expect("the walk finishes");
        let at = |c: bool, len: u128| {
            as_u128(eval_with(
                &one_arm.value,
                &[("arg1", Expr::bool_const(c)), ("arg2", slice_of_len(len))],
            ))
        };
        assert_eq!(at(true, 2), Some(4), "the writing arm reads the array's length");
        assert_eq!(at(false, 2), Some(2), "the other arm reads `v`'s length");
    });
}

/// One path writes the slice local twice: the array view on the first loop
/// iteration, `v` on the second. The second write replaces the first's
/// length (`statement_metadata::clear_inline_subslice_metadata_for_write`).
#[test]
fn test_slice_view_len_is_replaced_by_a_later_write() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_len_reassign").result.expect("the walk finishes");
        let n = as_u128(eval_with(&walked.value, &[("arg1", slice_of_len(2))]));
        assert_eq!(n, Some(2), "the last write is `v`, of length 2");
    });
}

// ---------------------------------------------------------------------------
// (2, 3) Negative discriminants and havocked fieldless enums
// ---------------------------------------------------------------------------

/// An exhaustive `match` on `Ordering`: `Less` (-1, case 255) selects its
/// arm, and the exhaustive `otherwise` arm's "unreachable code" obligation
/// holds for every valid value. Before, the walker compared the
/// sign-extended discriminant `0xFF..FF` with `255`, `Less` took the
/// `otherwise` arm, and the obligation failed (review 6, finding 2).
#[test]
fn test_negative_discriminant_selects_its_case() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_ordering_match").result.expect("the walk finishes");
        for (bits, expected) in [(0xFFu128, 1u128), (0, 2), (1, 3)] {
            let o = Expr::bitvec_const(bits, 8);
            assert_eq!(
                as_u128(eval_with(&walked.value, &[("arg1", o.clone())])),
                Some(expected),
                "discriminant bits {bits:#x}"
            );
            for check in &walked.deferred_checks {
                assert_eq!(
                    as_bool(eval_with(&check.check, &[("arg1", o.clone())])),
                    Some(true),
                    "check {:?} holds for the valid discriminant {bits:#x}",
                    check.message
                );
            }
        }
    });
}

/// An explicit `Less` arm with the rest `_`: `Less` yields 10. Before, the
/// arm was never selected and the result was always 20 (review 6,
/// finding 3, `o1_less_value_bug`).
#[test]
fn test_explicit_negative_arm_is_selected() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_less_arm").result.expect("the walk finishes");
        let at = |bits: u128| {
            as_u128(eval_with(&walked.value, &[("arg1", Expr::bitvec_const(bits, 8))]))
        };
        assert_eq!(at(0xFF), Some(10), "`Less` selects its arm");
        assert_eq!(at(0), Some(20));
        assert_eq!(at(1), Some(20));
    });
}

/// The havoc of a fieldless enum returned by a callee the walker gives up on
/// is assumed to hold one of the enum's discriminants when the callee cannot
/// forge another (no transmute anywhere it reaches); a callee that
/// transmutes gets no such assumption. Before, the havoc ranged over every
/// bit pattern and the exhaustive `otherwise` arm failed on values no
/// execution produces (review 6, finding 2, `a6_havocked_enum_safe`).
#[test]
fn test_havocked_fieldless_enum_is_valid_unless_the_callee_can_forge_one() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_classify_match");
        let result = walked.result.expect("the walk finishes");
        assert!(
            walked.reasons.contains_key("nested_call_overapprox"),
            "the float callee is havocked, reasons = {:?}",
            walked.reasons
        );
        let guard = extract_inline_assume_guard(&result.value)
            .expect("the havoc's validity is an assumption on the path");
        let havoc = vars_of(&guard)
            .into_iter()
            .find(|name| name.contains("__nested_call_overapprox"))
            .expect("the assumption reads the havoc");
        let width = var_width(&guard, &havoc).expect("the havoc is a bitvector");
        let holds = |bits: u128| {
            as_bool(eval_with(&guard, &[(havoc.as_str(), Expr::bitvec_const(bits, width))]))
        };
        assert_eq!(holds(1), Some(true), "a valid discriminant is admitted");
        assert_eq!(holds(7), Some(false), "an invalid one is not");

        let forged = walk(tcx, "probe_forge_match").result.expect("the walk finishes");
        let forged_guard = extract_inline_assume_guard(&forged.value);
        assert!(
            forged_guard
                .as_ref()
                .is_none_or(|g| !vars_of(g).iter().any(|n| n.contains("__nested_call_overapprox"))),
            "a callee that transmutes gets no validity assumption: {forged_guard:?}"
        );
    });
}

// ---------------------------------------------------------------------------
// (4) Loops the walker abandons under a declared unwind bound
// ---------------------------------------------------------------------------

fn unwind(u: u32) -> ChcConfig {
    ChcConfig { recursive_unwind_depth: u, unwinding_assertions: true, ..ChcConfig::default() }
}

/// Under `unwind(40)` a `while i < n` loop outruns the walker's replay
/// ceiling (33 passes since repair round 5): the abandoned arm's region holds
/// the loop, which can fail Kani's unwinding assertion, so it is a reach
/// check. Without a declared bound the same arm is the value havoc. Before,
/// the region scan counted no loop and the arm was always the havoc (review
/// 6, finding 4).
#[test]
fn test_abandoned_loop_under_a_declared_unwind_is_an_obligation() {
    with_probe(|tcx| {
        let bounded = walk_with(tcx, "probe_while_count", unwind(40));
        let bounded = bounded.result.expect("the walk finishes");
        let checks = reach_checks(&bounded);
        assert!(
            checks.iter().flatten().any(|m| m.contains("unwinding assertion loop")),
            "the abandoned loop can fail its unwinding assertion: {checks:?}"
        );
        let unbounded = walk(tcx, "probe_while_count").result.expect("the walk finishes");
        assert!(reach_checks(&unbounded).is_empty(), "no bound, no unwinding assertion");
    });
}

/// Two branches per pass under `unwind(6)`: the SwitchInt depth limit
/// abandons the loop on 2048 paths. Each abandoned edge records one freed
/// reach variable, and the merges join its per-path checks into one, so the
/// checks stay a handful. Before the merge key there were 2048 checks, and
/// the solver could not parse the result.
#[test]
fn test_abandoned_arm_checks_are_joined_per_edge() {
    with_probe(|tcx| {
        let walked = walk_with(tcx, "probe_branchy", unwind(6));
        let result = walked.result.expect("the walk finishes");
        let checks = reach_checks(&result);
        assert!(!checks.is_empty(), "the depth limit abandons the loop");
        assert!(checks.len() <= 8, "one check per abandoned edge, got {}", checks.len());
        let recorded = walked.reasons.get("walker_bailed_arm_obligation_uncertified").copied();
        assert!(
            recorded.is_some_and(|n| n <= 8),
            "one freed reach variable per edge, recorded {recorded:?}"
        );
    });
}

/// A callee the walker cannot enter (more than 16 effective blocks) with a
/// loop: under a declared unwind bound its havoc drops the loop's unwinding
/// assertion, a sighting; without one it keeps the blessing.
#[test]
fn test_havocked_callee_with_a_loop_under_a_declared_unwind_is_a_sighting() {
    with_probe(|tcx| {
        let bounded = walk_with(tcx, "probe_big_host", unwind(3));
        assert!(
            bounded.reasons.contains_key("walker_nested_call_lost_effect"),
            "the havocked loop can fail its unwinding assertion, reasons = {:?}",
            bounded.reasons
        );
        let unbounded = walk(tcx, "probe_big_host");
        assert!(
            unbounded.reasons.contains_key("nested_call_overapprox")
                && !unbounded.reasons.contains_key("walker_nested_call_lost_effect"),
            "without a bound the havoc keeps its blessing, reasons = {:?}",
            unbounded.reasons
        );
    });
}

// ---------------------------------------------------------------------------
// (5) The host-assumed replay raise
// ---------------------------------------------------------------------------

/// The host's `kani::assume(n <= 10)` raises a walked loop's replay only
/// where the abandoned region can carry an obligation: an obligation-free
/// loop keeps the built-in replay (its arm past the replay is the sound
/// value havoc). Before, every walked loop under a host assume was raised to
/// 17 passes (review 6, finding 5, `rj_dep_safe20`).
#[test]
fn test_assumed_bound_does_not_raise_an_obligation_free_loop() {
    with_probe(|tcx| {
        let walked = walk_from_host(tcx, "probe_free_host", "probe_free_callee");
        let result = walked.result.expect("the walk finishes");
        let deepest = deepest_replayed_pass(&result.value);
        assert!(
            deepest.is_some_and(|k| k <= 6),
            "the built-in replay, not the raised one (deepest pass {deepest:?})"
        );
    });
}

/// A loop whose accumulator feeds an index and an obligation, under the
/// host's `kani::assume(n <= 10)`: the raised walk's written-out terms pass
/// the ceiling, so the walk falls back to the built-in replay. Before, the
/// raised walk was kept and its terms did not compile in 155 s
/// (`g2_signed_rem_index_bug`).
#[test]
fn test_raised_replay_falls_back_when_its_terms_explode() {
    with_probe(|tcx| {
        let walked = walk_from_host(tcx, "probe_feedback_host", "probe_feedback_callee");
        let result = walked.result.expect("the walk finishes");
        let deepest = deepest_replayed_pass(&result.value);
        assert!(
            deepest.is_some_and(|k| k <= 6),
            "the raised walk was discarded (deepest pass {deepest:?})"
        );
    });
}

// ---------------------------------------------------------------------------
// (7, 8) Statement-path shapes
// ---------------------------------------------------------------------------

/// `sum` over a nine-element array: the chain is replayed to the array's
/// length, so the ninth element is exact and `s == 240` proves. Before, the
/// ninth step was past the replay bound of 8 and its reach check failed the
/// harness (review 6, finding 7, `f3_sum_ninth_safe`).
#[test]
fn test_constant_length_sum_is_replayed_to_its_length() {
    with_probe(|tcx| {
        let verdict = chc_verdict(tcx, "probe_sum9_ok");
        assert_eq!(verdict, "unsat", "the nine-element sum is exact");
    });
}

/// `ManuallyDrop::new(v).capacity()` reads the wrapped Vec's capacity: the
/// `Deref` result refers where its argument does. Before, `deref` was a
/// havoc stub and the capacity an unconstrained value, certified Genuine
/// (review 6, finding 8, `m1_manuallydrop_cap_safe`).
#[test]
fn test_manually_drop_capacity_reads_the_wrapped_vec() {
    with_probe(|tcx| {
        let verdict = chc_verdict(tcx, "probe_md_cap_ok");
        assert_eq!(verdict, "unsat", "the capacity is the Vec's");
    });
}

/// Under `unwind(20)` the same loop is replayed to Kani's bound, not
/// abandoned at 17 passes: the declared fuel ceiling is 32 and the SwitchInt
/// depth limit follows it (repair round 5, `walker_declared_replay_dual.rs`
/// `d4`), so the walk records the pass past the bound exactly and leaves no
/// abandoned-arm reach check.
#[test]
fn test_declared_unwind_above_seventeen_is_replayed() {
    with_probe(|tcx| {
        let walked = walk_with(tcx, "probe_while_count", unwind(20));
        let result = walked.result.expect("the walk finishes");
        let checks = reach_checks(&result);
        assert!(
            !checks.iter().flatten().any(|m| m.contains("unwinding assertion loop")),
            "the loop is replayed, not abandoned: {checks:?}"
        );
        assert!(
            !walked.reasons.contains_key("walker_bailed_arm_obligation_uncertified"),
            "no abandoned arm: {:?}",
            walked.reasons
        );
    });
}

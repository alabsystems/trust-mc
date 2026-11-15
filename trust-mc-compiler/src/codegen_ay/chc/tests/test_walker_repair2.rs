// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Repair round 2 of fix/chc-walker-fail-closed (walker fail-closed review 6
//! round 2; docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed:
//! repair round 2"): (1) Kani's unwinding assertion on a reduction's std loop
//! under a declared unwind, (2) no validity assumption on a havocked enum a
//! callee can pass on, (3) a walked body's argument locals read no caller's
//! slice-length entry, (4) a collection write through `ManuallyDrop::deref_mut`
//! fails closed, (6) an oversized declared-unwind walk fails closed, (7) the
//! host-assumed raise only where it can reach the loop's exit. Every probe
//! asserts the shape it is about. (5) is `straightline_proof.rs`'s
//! `saturation_applies_each_firing_once`, (8) is
//! `codegen_function/integration_bmc_reduce_unwind_tests.rs`.

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

    #[inline(never)]
    fn sink<T>(_v: T) {}

    // (1) Reductions under a declared unwind.
    pub fn probe_sum5() {
        let a: [u8; 5] = [1, 1, 1, 1, 1];
        let s: u8 = a.iter().sum();
        sink(s);
    }
    // `fold` with a closure that checks nothing, so the only obligation the
    // reduction can carry is the loop's unwinding assertion.
    pub fn probe_into_fold4() {
        let a: [u8; 4] = [1, 1, 1, 1];
        let s = IntoIterator::into_iter(a).fold(0u8, |acc, x| acc.wrapping_add(x));
        sink(s);
    }
    // `try_fold` takes `&mut self`: the count is bounded through the borrow.
    pub fn probe_try_fold2() -> bool {
        let arr = [(1u8, 2u8), (2, 2)];
        let result = arr.iter().try_fold((), |_acc, _i| Some(()));
        result.is_some()
    }
    pub fn probe_map_fold5() {
        let a: [u8; 5] = [1, 1, 1, 1, 1];
        let s = a.iter().map(|x| *x as u16).fold(0u16, |acc, x| acc.wrapping_add(x));
        sink(s);
    }

    // (2) A fieldless enum from a float helper the walker havocs, which
    // returns its argument on one path: by value, and through a reference.
    #[derive(Clone, Copy)]
    pub enum E3 { A, B, C }
    #[inline(never)]
    fn pass_f(e: E3, x: f32) -> E3 {
        if x < 0.0 { e } else { E3::A }
    }
    #[inline(never)]
    fn get_f(e: &E3, x: f32) -> E3 {
        if x < 0.0 { *e } else { E3::A }
    }
    pub fn probe_pass_match(e: E3, x: f32) -> u8 {
        match pass_f(e, x * 2.0) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }
    pub fn probe_ref_match(e: E3, x: f32) -> u8 {
        match get_f(&e, x * 2.0) {
            E3::A => 1,
            E3::B => 2,
            E3::C => 3,
        }
    }

    // (3) A walked body whose argument is a slice.
    pub fn probe_arg_len(c: bool, v: &[u8]) -> usize {
        v.len()
    }

    // (4) Collection writes through `ManuallyDrop::deref_mut`, and a
    // `deref_mut` that only exposes the buffer.
    pub fn probe_md_push_cap() {
        let mut md = std::mem::ManuallyDrop::new(Vec::<u8>::with_capacity(1));
        md.push(1);
        md.push(2);
        assert!(md.capacity() == 1);
    }
    pub fn probe_md_ptr_cap() {
        let mut v: Vec<u16> = Vec::with_capacity(3);
        v.push(1);
        let mut v = std::mem::ManuallyDrop::new(v);
        let cap = v.capacity();
        let p = v.as_mut_ptr() as *mut u8;
        sink(p);
        sink(cap * 2);
    }

    // (6) A loop whose accumulator feeds its own index: every replayed pass
    // doubles the written-out term.
    pub fn probe_feedback(x: u8, n: u8) -> u8 {
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

    // (7) A walked loop whose region carries an obligation, under the
    // host's assumed bound on its trip count.
    #[inline(never)]
    pub fn probe_raise_callee(a: u8, n: u8) -> u8 {
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let t = (acc & 0x7f) + 129;
            acc = t.wrapping_add(j);
            j = j.wrapping_add(1);
        }
        acc
    }
    pub fn probe_raise_host10(a: u8, n: u8) -> u8 {
        kani::assume(n <= 10);
        probe_raise_callee(a, n)
    }
    pub fn probe_raise_host19(a: u8, n: u8) -> u8 {
        kani::assume(n <= 19);
        probe_raise_callee(a, n)
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
    let ctx_name = format!("walker_repair2__{fn_name}");
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
    let ctx_name = format!("walker_repair2__{host_fn}");
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

fn unwind(u: u32) -> ChcConfig {
    ChcConfig { recursive_unwind_depth: u, unwinding_assertions: true, ..ChcConfig::default() }
}

/// The CHC verdict of `name` as a harness under `config` ("sat": an error is
/// reachable), and the translation-drop reasons its encoding recorded.
fn chc_verdict_with(
    tcx: TyCtxt<'_>,
    name: &str,
    config: ChcConfig,
) -> (String, BTreeMap<String, usize>) {
    let instance = find_instance_by_suffix(tcx, name);
    let body = instance.body().expect("function body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name, config);
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(name)
        .unwrap_or_default();
    let smt = crate::codegen_ay::emit_chc(&vc).to_string();
    let verdict = run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
        .unwrap_or_else(|err| format!("error:{err}"));
    (verdict, reasons)
}

// ---------------------------------------------------------------------------
// (1) Kani's unwinding assertion on a reduction's std loop
// ---------------------------------------------------------------------------

/// `sum` over five elements of a slice iterator: Kani's `fold` loop fails its
/// unwinding assertion once more than `U` remain, so under `unwind(4)` an
/// error is reachable and under `unwind(5)` none is. Before, the replay was
/// raised to the array's length whatever the declared bound, and nothing
/// stated the failure (review 6 round 2, finding 1, `r2_slice_sum_n5_u4`).
#[test]
fn test_slice_sum_states_the_fold_unwinding_assertion() {
    with_probe(|tcx| {
        assert_eq!(chc_verdict_with(tcx, "probe_sum5", unwind(4)).0, "sat", "N = 5 > U = 4");
        assert_eq!(chc_verdict_with(tcx, "probe_sum5", unwind(5)).0, "unsat", "N = 5 = U");
    });
}

/// `fold` over an `array::IntoIter` of four: its loop tests before its body
/// and fails once `U` elements remain, so `unwind(4)` fails and `unwind(5)`
/// does not (measured on Kani: `intofold_n4_u4` FAILED).
#[test]
fn test_array_into_iter_fold_fails_at_the_bound() {
    with_probe(|tcx| {
        assert_eq!(chc_verdict_with(tcx, "probe_into_fold4", unwind(4)).0, "sat", "N = U = 4");
        assert_eq!(chc_verdict_with(tcx, "probe_into_fold4", unwind(5)).0, "unsat", "N = 4 < U");
    });
}

/// `fold` over a `map` of a slice iterator, which the precise chain does not
/// fold: the element count is bounded by the array's length through the
/// adapter, so `unwind(5)` needs no check and `unwind(4)` keeps the
/// fail-closed one.
#[test]
fn test_adapter_fold_is_bounded_through_the_adapter() {
    with_probe(|tcx| {
        let (bounded, _) = chc_verdict_with(tcx, "probe_map_fold5", unwind(5));
        assert_eq!(bounded, "unsat", "five elements through `map` stay within unwind(5)");
        let (past, reasons) = chc_verdict_with(tcx, "probe_map_fold5", unwind(4));
        assert_eq!(past, "sat", "five elements can pass unwind(4)");
        assert!(
            reasons.contains_key("iter_reduce_unwind_uncertified"),
            "the check is the uncertified one, reasons = {reasons:?}"
        );
    });
}

/// `try_fold` over two elements under `unwind(3)` (Kani's `Iterator/try_fold.rs`):
/// the receiver is a `&mut` borrow of the slice iterator, and the count is
/// bounded through it, so no check fires; under `unwind(2)` the check stays.
/// Before, the borrow ended the trace, the count was unknown, and the
/// fail-closed check failed a program Kani proves.
#[test]
fn test_try_fold_count_is_bounded_through_the_borrow() {
    with_probe(|tcx| {
        let (bounded, reasons) = chc_verdict_with(tcx, "probe_try_fold2", unwind(3));
        assert_eq!(bounded, "unsat", "two elements stay within unwind(3), reasons = {reasons:?}");
        let (past, _) = chc_verdict_with(tcx, "probe_try_fold2", unwind(2));
        assert_eq!(past, "sat", "two elements can reach unwind(2)");
    });
}

// ---------------------------------------------------------------------------
// (2) A havocked enum the callee can pass on
// ---------------------------------------------------------------------------

/// The havoc of a callee that returns its `E3` argument on one path is
/// assumed to be a valid discriminant OR that argument: a forged argument
/// (7) reaches the exhaustive arm, a valid one does not. Before, the
/// assumption was validity alone, which pruned the forged execution
/// (review 6 round 2, finding 2, `f1_forged_by_value_bug`).
#[test]
fn test_havocked_enum_keeps_a_by_value_argument() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_pass_match").result.expect("the walk finishes");
        let guard = extract_inline_assume_guard(&walked.value)
            .expect("the havoc's possible values are an assumption on the path");
        let havoc = vars_of(&guard)
            .into_iter()
            .find(|name| name.contains("__nested_call_overapprox"))
            .expect("the assumption reads the havoc");
        let width = var_width(&guard, &havoc).expect("the havoc is a bitvector");
        let arg_width = var_width(&guard, "arg1").expect("the assumption reads the argument");
        let holds = |h: u128, e: u128| {
            as_bool(eval_with(
                &guard,
                &[
                    (havoc.as_str(), Expr::bitvec_const(h, width)),
                    ("arg1", Expr::bitvec_const(e, arg_width)),
                ],
            ))
        };
        assert_eq!(holds(1, 0), Some(true), "a valid discriminant is admitted");
        assert_eq!(holds(7, 7), Some(true), "the forged argument passed on is admitted");
        assert_eq!(holds(7, 1), Some(false), "a value neither valid nor the argument is not");
    });
}

/// A callee that reads the enum through a reference gets no assumption at
/// all: the value behind it may be forged.
#[test]
fn test_havocked_enum_behind_a_reference_is_not_assumed_valid() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_ref_match").result.expect("the walk finishes");
        let guard = extract_inline_assume_guard(&walked.value);
        assert!(
            guard
                .as_ref()
                .is_none_or(|g| !vars_of(g).iter().any(|n| n.contains("__nested_call_overapprox"))),
            "no validity assumption through `&E3`: {guard:?}"
        );
    });
}

// ---------------------------------------------------------------------------
// (3) Argument locals and the slice-length side table
// ---------------------------------------------------------------------------

/// A walked body's argument `v` (`_2`) reads its own length, not an entry the
/// caller left at index 2 (seeded here as 6), and the caller's entry is back
/// after the walk. Before, the walk saved and restored the body's entries
/// but never cleared them, so `v.len()` was 6 (review 6 round 2, finding 3,
/// `rp3b_slice_len_index.rs`).
#[test]
fn test_argument_local_ignores_the_callers_slice_len_entry() {
    with_probe(|tcx| {
        let ctx_name = "walker_repair2__probe_arg_len";
        let instance = find_instance_by_suffix(tcx, "probe_arg_len");
        let body = instance.body().expect("function body");
        let params = arg_params(&body);
        let mut chc_ctx = ChcCtx::new(tcx, &body, ctx_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        let six = Expr::bitvec_const(6u64, 64);
        chc_ctx.ref_resolution.subslice_len.insert(2, six.clone());
        let walked = translate_inline_body(
            &mut chc_ctx,
            &body,
            &params,
            0,
            &HashMap::new(),
            Some(instance),
            0,
        )
        .expect("the walk finishes");
        let len = as_u128(eval_with(
            &walked.value,
            &[("arg1", Expr::bool_const(true)), ("arg2", slice_of_len(2))],
        ));
        assert_eq!(len, Some(2), "the argument's own length");
        assert_eq!(
            chc_ctx.ref_resolution.subslice_len.get(&2),
            Some(&six),
            "the caller's entry is restored after the walk"
        );
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn().remove(ctx_name);
    });
}

// ---------------------------------------------------------------------------
// (4) Collection writes through `ManuallyDrop::deref_mut`
// ---------------------------------------------------------------------------

/// Two pushes through `ManuallyDrop<Vec<u8>>::deref_mut` fail closed; a
/// `deref_mut` that only feeds `as_mut_ptr` keeps the exact identity.
/// Before, the pushes reached the wrapper's memory but not the capacity side
/// state, and `capacity() == 1` verified clean (review 6 round 2, finding 4,
/// `m4_cap_after_growth_bug`).
#[test]
fn test_manually_drop_collection_write_fails_closed() {
    with_probe(|tcx| {
        let (_, reasons) = chc_verdict_with(tcx, "probe_md_push_cap", ChcConfig::default());
        assert!(
            reasons.contains_key("manually_drop_collection_write_unmodelled"),
            "the pushes fail closed, reasons = {reasons:?}"
        );
        let (verdict, reasons) = chc_verdict_with(tcx, "probe_md_ptr_cap", ChcConfig::default());
        assert!(
            !reasons.contains_key("manually_drop_collection_write_unmodelled"),
            "`as_mut_ptr` writes no side state, reasons = {reasons:?}"
        );
        assert_eq!(verdict, "unsat", "the capacity is still the Vec's");
    });
}

// ---------------------------------------------------------------------------
// (6) An oversized declared-unwind walk
// ---------------------------------------------------------------------------

/// A feedback loop walked under `unwind(12)` writes out past the ceiling:
/// the walk fails closed instead of handing AY a query it rejects or cannot
/// decide; under `unwind(4)` the walk is small and kept. Before, the walk was
/// always kept, and AY refused such a query ("datatype signature surface
/// exceeds copy/comparison work bound"; review 6 round 2, finding 6,
/// `ct_contains_u8_safe`).
#[test]
fn test_oversized_declared_unwind_walk_fails_closed() {
    with_probe(|tcx| {
        let walked = walk_with(tcx, "probe_feedback", unwind(12));
        assert!(walked.result.is_none(), "the oversized walk is discarded");
        assert!(
            walked.reasons.contains_key("walker_declared_replay_too_large"),
            "and fails closed, reasons = {:?}",
            walked.reasons
        );
        let small = walk_with(tcx, "probe_feedback", unwind(4));
        assert!(small.result.is_some(), "a small declared replay is kept");
        assert!(
            !small.reasons.contains_key("walker_declared_replay_too_large"),
            "reasons = {:?}",
            small.reasons
        );
    });
}

// ---------------------------------------------------------------------------
// (7) The host-assumed raise
// ---------------------------------------------------------------------------

/// The host's `kani::assume(n <= 10)` raises the walked loop's replay past
/// the built-in count; `kani::assume(n <= 19)` does not, because 20 passes
/// are past the replay ceiling and the loop would stay abandoned. Before,
/// both were raised to the ceiling (review 6 round 2, finding 7,
/// `rg_region.rs`).
#[test]
fn test_assumed_bound_raises_only_a_coverable_loop() {
    with_probe(|tcx| {
        let covered = walk_from_host(tcx, "probe_raise_host10", "probe_raise_callee");
        let covered = covered.result.expect("the walk finishes");
        let deepest = deepest_replayed_pass(&covered.value);
        assert!(deepest.is_some_and(|k| k >= 10), "raised to the bound (deepest {deepest:?})");

        let past = walk_from_host(tcx, "probe_raise_host19", "probe_raise_callee");
        let past = past.result.expect("the walk finishes");
        let deepest = deepest_replayed_pass(&past.value);
        assert!(deepest.is_some_and(|k| k <= 6), "the built-in replay (deepest {deepest:?})");
    });
}

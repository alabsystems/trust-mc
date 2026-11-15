// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The inline walker's precision items of the second package round of
//! fix/chc-walker-fail-closed (docs/chc-hole-fix-designs-2026-09-24.md,
//! "Walker fail-closed: package round 2"): (a) the region scan's interval
//! analysis, (b) the declared-unwind replay, the adaptive constant-loop
//! refund and the pruned reach-check arm, (c) exact array aggregates, (d)
//! `kani::panic`, (e) the vtable reads and `__rust_dealloc`, and the
//! contained-foreign arm. Every probe asserts the shape it is about.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

use crate::codegen_ay::chc::call::inline_body::{InlineReturn, translate_inline_body};
use ay_bindings::{Expr, ExprValue, rebuild_with_children};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, TerminatorKind};
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};
use trust_mc_core::chc_const_prop::eval::try_eval_to_const;
use trust_mc_core::violation::PropertyKind;

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]
    #![feature(register_tool, core_intrinsics)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "PanicHook"]
        pub fn panic(message: &'static str) -> ! {
            let _ = message;
            loop {}
        }
        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    // (a) a walked loop that outruns the replay (symbolic `n`, no declared
    // unwind): its body is the abandoned region. `j % 4` indexes a
    // four-element table, so the bounds check always holds; `j % 5` does not.
    pub fn probe_region_mod4(a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            acc = acc.wrapping_add(table[(j % 4) as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
    pub fn probe_region_mod5(a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            acc = acc.wrapping_add(table[(j % 5) as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
    // A widening add that cannot overflow, and one that can.
    pub fn probe_region_widen(a: u8, n: u8) -> u16 {
        let mut acc = 0u16;
        let mut j: u8 = 0;
        while j < n {
            acc = (a as u16) + 1;
            j = j.wrapping_add(1);
        }
        acc
    }
    pub fn probe_region_mul_overflow(a: u8, n: u8) -> u16 {
        let mut acc = 0u16;
        let mut j: u8 = 0;
        while j < n {
            acc = (a as u16) * 300;
            j = j.wrapping_add(1);
        }
        acc
    }

    // (b) `while i < n`: MIR tests the header once per pass.
    pub fn probe_while_count(n: u8) -> u8 {
        let mut i = 0u8;
        let mut acc = 0u8;
        while i < n {
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }
    // (b) a constant loop longer than the old 69-iteration refund cap.
    pub fn probe_const_hundred(x: u8) -> u8 {
        let mut acc = x;
        let mut i: u16 = 0;
        while i < 100 {
            acc = acc.wrapping_add(1);
            i += 1;
        }
        acc
    }
    // (b) nested loops: the inner loop is entered afresh per outer pass.
    pub fn probe_nested_loops(x: u8) -> u8 {
        let mut acc = x;
        let mut i = 0u8;
        while i < 2 {
            let mut j = 0u8;
            while j < 2 {
                acc = acc.wrapping_add(1);
                j += 1;
            }
            i += 1;
        }
        acc
    }
    // (b) an abandoned arm whose region carries a check: its path ends.
    pub fn probe_pruned_arm(a: u8, skipped: u8) -> u8 {
        if a > 10 {
            assert!(skipped != 100);
            skipped
        } else {
            a
        }
    }

    // (b) a loop bounded only by what its caller assumes: the checked add
    // makes the region past the replay one that can carry an obligation.
    #[inline(never)]
    pub fn probe_assume_callee(x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i = 0u8;
        while i < n {
            acc = acc + 1;
            i = i.wrapping_add(1);
        }
        acc
    }
    pub fn probe_assume_host(x: u8, n: u8) -> u8 {
        kani::assume(n <= 10);
        probe_assume_callee(x, n)
    }
    pub fn probe_assume_host_none(x: u8, n: u8) -> u8 {
        probe_assume_callee(x, n)
    }

    // (b) certification: a walked callee whose loop outruns the replay (a
    // reach check) and whose nested callee has an overflow check (a panic-path
    // fallback every consumer strips).
    #[inline(never)]
    fn bump(acc: u8) -> u8 {
        acc + 1
    }
    #[inline(never)]
    fn cert_loop(x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i = 0u8;
        loop {
            if i == n {
                break;
            }
            acc = bump(acc);
            i = i.wrapping_add(1);
        }
        acc
    }
    pub fn probe_cert_host(x: u8, n: u8) -> u8 {
        cert_loop(x, n)
    }

    // (c) exact array aggregates.
    pub fn probe_array_read(a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        arr[(i % 4) as usize]
    }
    pub fn probe_option_array_read(a: u8, i: u8) -> u8 {
        let arr = [Some(a), None, Some(1), Some(2)];
        match arr[(i % 4) as usize] {
            Some(v) => v,
            None => 77,
        }
    }
    pub fn probe_single_element_array(a: u8, i: u8) -> u8 {
        let arr = [a];
        arr[(i % 1) as usize]
    }

    // (d) `kani::panic`: on an arm, and straight-line.
    pub fn probe_kani_panic_arm(a: u8) -> u8 {
        if a == 7 {
            kani::panic("seven is not allowed");
        }
        a
    }
    pub fn probe_kani_panic_straight(a: u8) -> u8 {
        kani::panic("always reached")
    }

    // The contained-foreign arm: `Iter::new` walked on an exact array.
    #[inline(never)]
    fn sink_iter<T>(_v: T) {}
    pub fn probe_slice_iter(a: u8) -> u8 {
        let arr = [a, a, a];
        sink_iter(arr.iter());
        a
    }

    // (e) the deallocator reached through `std::alloc::dealloc`.
    pub fn probe_dealloc(p: *mut u8, size: usize) {
        unsafe {
            std::alloc::dealloc(p, std::alloc::Layout::from_size_align_unchecked(size, 8));
        }
    }

    // (e) the vtable reads and the deallocator.
    pub fn probe_vtable_size(p: *const ()) -> usize {
        unsafe { core::intrinsics::vtable_size(p) }
    }
    pub fn probe_vtable_align(p: *const ()) -> usize {
        unsafe { core::intrinsics::vtable_align(p) }
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

/// Fresh parameters `arg<local>`, leaving trailing `skipped*` arguments
/// unseeded (see `test_walker_fail_closed.rs`).
fn arg_params(body: &Body) -> Vec<Expr> {
    let skipped: std::collections::HashSet<usize> = body
        .var_debug_info
        .iter()
        .filter(|info| info.name.starts_with("skipped"))
        .filter_map(|info| match &info.value {
            rustc_public::mir::VarDebugInfoContents::Place(place)
                if place.projection.is_empty() =>
            {
                Some(place.local)
            }
            _ => None,
        })
        .collect();
    let seeded = (1..=body.arg_locals().len()).take_while(|l| !skipped.contains(l)).count();
    (1..=seeded)
        .map(|local| {
            let sort =
                ChcCtx::translate_ty(body.locals()[local].ty).expect("argument type translates");
            Expr::var(format!("arg{local}"), sort)
        })
        .collect()
}

/// A walk, what it booked, and the site reasons it recorded.
struct Walked {
    result: Option<InlineReturn>,
    reasons: BTreeMap<String, usize>,
    freed: Vec<String>,
}

fn walk_with(
    tcx: TyCtxt<'_>,
    fn_name: &str,
    config: ChcConfig,
    params: Option<Vec<Expr>>,
    vtable_layouts: &[(u64, (u64, u64))],
) -> Walked {
    let ctx_name = format!("walker_package2__{fn_name}");
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let params = params.unwrap_or_else(|| arg_params(&body));
    let mut chc_ctx = ChcCtx::new(tcx, &body, ctx_name.as_str(), config);
    for (id, layout) in vtable_layouts {
        chc_ctx.vtable_type_metadata.insert(*id, *layout);
    }
    chc_ctx.declare_block_relations();
    chc_ctx.mark_inline_field_reads(&body, &params, 0);
    let freed = chc_ctx.vc.approximated_vars.len();
    let result =
        translate_inline_body(&mut chc_ctx, &body, &params, 0, &HashMap::new(), Some(instance), 0);
    let freed = chc_ctx.vc.approximated_vars[freed..].to_vec();
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(&ctx_name)
        .unwrap_or_default();
    Walked { result, reasons, freed }
}

fn walk(tcx: TyCtxt<'_>, fn_name: &str) -> Walked {
    walk_with(tcx, fn_name, ChcConfig::default(), None, &[])
}

fn vars_of(expr: &Expr) -> Vec<String> {
    let mut names = Vec::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
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

fn eval_with(expr: &Expr, values: &[(&str, Expr)]) -> Option<Expr> {
    let values: HashMap<String, Expr> =
        values.iter().map(|(name, value)| ((*name).to_string(), value.clone())).collect();
    let folded = fold_deep(&substitute(expr, &values));
    try_eval_to_const(&folded)
}

/// Fold `expr` bottom-up with the constant evaluator, resolving a `select`
/// over a store chain on a constant array at a constant index (which the
/// evaluator alone does not reach through a computed index).
fn fold_deep(expr: &Expr) -> Expr {
    let children: Vec<Expr> = expr.value().children().map(fold_deep).collect();
    let rebuilt =
        if children.is_empty() { expr.clone() } else { rebuild_with_children(expr, children) };
    if let ExprValue::Select { array, index } = rebuilt.value()
        && let Some(read) = select_constant(array, index)
    {
        return fold_deep(&read);
    }
    // `is-C(C'(..))` and `sel(C(..))` over a constructor.
    match rebuilt.value() {
        ExprValue::DatatypeTester { constructor_name, expr: inner, .. } => {
            if let ExprValue::DatatypeConstructor { constructor_name: built, .. } = inner.value() {
                return Expr::bool_const(built == constructor_name);
            }
        }
        ExprValue::DatatypeSelector { selector_name, expr: inner, .. } => {
            if let ExprValue::DatatypeConstructor { constructor_name, args, .. } = inner.value()
                && let Some(dt) = inner.sort().datatype_sort()
                && let Some(ctor) = dt.constructors.iter().find(|c| c.name == *constructor_name)
                && let Some(idx) = ctor.fields.iter().position(|f| f.name == *selector_name)
                && let Some(arg) = args.get(idx)
            {
                return fold_deep(arg);
            }
        }
        _ => {}
    }
    try_eval_to_const(&rebuilt).unwrap_or(rebuilt)
}

fn select_constant(array: &Expr, index: &Expr) -> Option<Expr> {
    let index_value = |e: &Expr| match e.value() {
        ExprValue::BitVecConst { value, .. } => Some(value.clone()),
        _ => None,
    };
    match array.value() {
        ExprValue::ConstArray { value, .. } => Some(value.clone()),
        ExprValue::Store { array: inner, index: stored_at, value } => {
            let (at, want) = (index_value(stored_at)?, index_value(index)?);
            if at == want { Some(value.clone()) } else { select_constant(inner, index) }
        }
        _ => None,
    }
}

fn bv(value: u64, width: u32) -> Expr {
    Expr::bitvec_const(value, width)
}

fn as_u64(expr: Option<Expr>) -> Option<u64> {
    match expr?.value() {
        ExprValue::BitVecConst { value, .. } => u64::try_from(value.clone()).ok(),
        _ => None,
    }
}

fn as_bool(expr: Option<Expr>) -> Option<bool> {
    match expr?.value() {
        ExprValue::BoolConst(b) => Some(*b),
        _ => None,
    }
}

/// The deferred checks reading an uncertified reach-check variable.
fn reach_checks(walked: &InlineReturn) -> Vec<(PropertyKind, Option<String>)> {
    walked
        .deferred_checks
        .iter()
        .filter(|c| vars_of(&c.check).iter().any(|n| n.starts_with("__walker_uncertified_reach")))
        .map(|c| (c.kind, c.message.clone()))
        .collect()
}

fn body_has_loop(body: &Body) -> bool {
    body.blocks.iter().enumerate().any(|(bb, block)| match &block.terminator.kind {
        TerminatorKind::Goto { target } => *target <= bb,
        TerminatorKind::SwitchInt { targets, .. } => {
            targets.branches().any(|(_, t)| t <= bb) || targets.otherwise() <= bb
        }
        _ => false,
    })
}

// ---------------------------------------------------------------------------
// (a) The region scan's interval analysis
// ---------------------------------------------------------------------------

/// The region a walked loop abandons when it outruns the replay holds a
/// bounds check on `table[(j % 4) as usize]` for a four-element table: it
/// always holds, so the arm keeps its value havoc and records no reach
/// check. With `j % 5` the check can fail and the arm is an uncertified
/// reach check. Before, every `Assert` counted, and both arms were reach
/// checks (the review's `c2_free_region_safe`).
#[test]
fn test_region_scan_discharges_a_bounds_check_that_always_holds() {
    with_probe(|tcx| {
        for fn_name in ["probe_region_mod4", "probe_region_mod5"] {
            let body = find_instance_by_suffix(tcx, fn_name).body().expect("body");
            assert!(body_has_loop(&body), "{fn_name}: the probe loops");
            assert!(
                body.blocks
                    .iter()
                    .any(|b| matches!(b.terminator.kind, TerminatorKind::Assert { .. })),
                "{fn_name}: the probe has a bounds Assert"
            );
        }
        let safe = walk(tcx, "probe_region_mod4");
        let safe_result = safe.result.expect("probe_region_mod4: the walk finishes");
        assert!(
            safe.reasons.contains_key("switchint_branch_overapprox"),
            "the loop really outruns the replay, reasons = {:?}",
            safe.reasons
        );
        assert!(
            reach_checks(&safe_result).is_empty(),
            "no reach check for an always-true bounds check"
        );

        let bug = walk(tcx, "probe_region_mod5");
        let bug_result = bug.result.expect("probe_region_mod5: the walk finishes");
        assert!(
            !reach_checks(&bug_result).is_empty(),
            "an index that can leave the table keeps the reach check"
        );
    });
}

/// `(a as u16) + 1` cannot overflow a `u16`; `(a as u16) * 300` can. The
/// first region's overflow Assert is discharged, the second's is not.
#[test]
fn test_region_scan_discharges_an_overflow_check_that_cannot_overflow() {
    with_probe(|tcx| {
        let widen = walk(tcx, "probe_region_widen").result.expect("widen: the walk finishes");
        assert!(reach_checks(&widen).is_empty(), "the widening add cannot overflow");
        let mul = walk(tcx, "probe_region_mul_overflow").result.expect("mul: the walk finishes");
        assert!(!reach_checks(&mul).is_empty(), "the multiply can overflow");
    });
}

// ---------------------------------------------------------------------------
// (b) Declared unwind, constant loops, pruned reach-check arms
// ---------------------------------------------------------------------------

fn unwind_config(unwind: u32, unwinding_assertions: bool) -> ChcConfig {
    ChcConfig { recursive_unwind_depth: unwind, unwinding_assertions, ..ChcConfig::default() }
}

/// Under `#[kani::unwind(3)]` Kani passes a loop header three times per entry:
/// two iterations pass, a third fails the unwinding assertion. The walk
/// records exactly that failure (`n >= 3`) and ends the path; with unwinding
/// assertions off it only ends the path. Before, the fuel was at least six
/// passes and a path past it was the bailed-arm havoc.
#[test]
fn test_declared_unwind_is_replayed_exactly() {
    with_probe(|tcx| {
        let fn_name = "probe_while_count";
        let walked = walk_with(tcx, fn_name, unwind_config(3, true), None, &[]);
        let result = walked.result.expect("the walk finishes");
        let unwind: Vec<_> = result
            .deferred_checks
            .iter()
            .filter(|c| c.message.as_deref() == Some("unwinding assertion loop"))
            .collect();
        assert!(!unwind.is_empty(), "the unwinding assertion is recorded");
        let fails_at = |n: u64| {
            unwind
                .iter()
                .any(|c| as_bool(eval_with(&c.check, &[("arg1", bv(n, 8))])) == Some(false))
        };
        assert!(
            !fails_at(0) && !fails_at(1) && !fails_at(2),
            "two iterations are within unwind(3)"
        );
        assert!(fails_at(3), "a third iteration fails the unwinding assertion");
        assert!(reach_checks(&result).is_empty(), "no uncertified record for the unwind bound");
        assert!(
            !walked.reasons.contains_key("switchint_branch_overapprox"),
            "no bailed-arm havoc: {:?}",
            walked.reasons
        );
        // Within the bound the value is exact: n passes add n.
        for n in 0..3u64 {
            assert_eq!(as_u64(eval_with(&result.value, &[("arg1", bv(n, 8))])), Some(n));
        }

        let quiet = walk_with(tcx, fn_name, unwind_config(3, false), None, &[]);
        let quiet = quiet.result.expect("the walk finishes");
        assert!(
            !quiet
                .deferred_checks
                .iter()
                .any(|c| c.message.as_deref() == Some("unwinding assertion loop")),
            "no unwinding assertion without unwinding checks"
        );
        assert!(
            vars_of(&quiet.value).iter().any(|n| n.starts_with("__assume_pruned_inline")),
            "the path past the bound is cut"
        );
    });
}

/// The inner loop of a nested pair is entered afresh on each outer pass, as
/// Kani counts: under `unwind(3)` two outer passes of two inner passes each
/// replay exactly, with no unwinding failure.
#[test]
fn test_declared_unwind_counts_per_loop_entry() {
    with_probe(|tcx| {
        let walked = walk_with(tcx, "probe_nested_loops", unwind_config(3, true), None, &[]);
        let result = walked.result.expect("the walk finishes");
        assert!(
            !result
                .deferred_checks
                .iter()
                .any(|c| as_bool(eval_with(&c.check, &[])) == Some(false)),
            "no check fails: the inner loop's count restarts per entry"
        );
        assert_eq!(as_u64(eval_with(&result.value, &[("arg1", bv(10, 8))])), Some(14));
    });
}

/// A constant loop of 100 iterations replays exactly (the old refund cap was
/// 64 on five passes of fuel): the value folds to `x + 100`.
#[test]
fn test_constant_loop_past_sixty_nine_iterations_replays_exactly() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_const_hundred");
        let result = walked.result.expect("the walk finishes");
        assert!(
            !walked.reasons.contains_key("switchint_branch_overapprox"),
            "{:?}",
            walked.reasons
        );
        assert_eq!(as_u64(eval_with(&result.value, &[("arg1", bv(3, 8))])), Some(103));
    });
}

/// An abandoned arm whose region carries a check is an uncertified reach
/// check, and its path ends there: its value is the assume-pruned marker, and
/// no freed havoc rides the merged result.
#[test]
fn test_abandoned_arm_with_a_reach_check_ends_its_path() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_pruned_arm");
        let result = walked.result.expect("the walk finishes");
        assert_eq!(reach_checks(&result).len(), 1, "one reach check for the arm");
        let names = vars_of(&result.value);
        assert!(
            names.iter().any(|n| n.starts_with("__assume_pruned_inline")),
            "the arm's path ends"
        );
        assert!(
            !names.iter().any(|n| n.starts_with("__switchint_branch_overapprox")),
            "no freed havoc in the value: {names:?}"
        );
        assert!(
            !walked.reasons.contains_key("walker_bailed_arm_lost_effect"),
            "a pruned path needs no lost-write record"
        );
    });
}

/// The callee's walk started from `host_fn`'s call to it, the host being the
/// function under translation: the arguments are `arg1`, `arg2`.
fn walk_from_host(tcx: TyCtxt<'_>, host_fn: &str, callee_fn: &str) -> Walked {
    let ctx_name = format!("walker_package2__{host_fn}");
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
    let freed = chc_ctx.vc.approximated_vars.len();
    let result = translate_inline_body(
        &mut chc_ctx,
        &callee_body,
        &params,
        call_bb,
        &HashMap::new(),
        Some(callee),
        0,
    );
    let freed = chc_ctx.vc.approximated_vars[freed..].to_vec();
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(&ctx_name)
        .unwrap_or_default();
    Walked { result, reasons, freed }
}

/// Does some reach check fail at `n` (every reach-check variable `false`,
/// `x = 0`)? A reach check holds on a path that does not reach its arm.
fn reach_check_fails_at(walked: &InlineReturn, n: u64) -> bool {
    walked.deferred_checks.iter().any(|c| {
        let names = vars_of(&c.check);
        let reach: Vec<&String> =
            names.iter().filter(|n| n.starts_with("__walker_uncertified_reach")).collect();
        if reach.is_empty() {
            return false;
        }
        let mut values: Vec<(&str, Expr)> = vec![("arg1", bv(0, 8)), ("arg2", bv(n, 8))];
        values.extend(reach.iter().map(|name| (name.as_str(), Expr::bool_const(false))));
        as_bool(eval_with(&c.check, &values)) == Some(false)
    })
}

/// A walked loop bounded only by its caller's `kani::assume(n <= 10)`: the
/// assumed bound raises the replay (`walker.rs` `host_call_assumed_bound`),
/// so every path within it is replayed and the abandoned arm's reach check
/// fails only past the bound (`n = 11`), never at `n = 8`. Without the
/// assumption the default replay abandons the loop sooner, and the reach
/// check fails at `n = 8`, as it did for every such host before.
#[test]
fn test_callers_assumed_bound_sizes_the_replay() {
    with_probe(|tcx| {
        let bounded = walk_from_host(tcx, "probe_assume_host", "probe_assume_callee");
        let bounded = bounded.result.expect("the walk finishes");
        assert!(
            !reach_checks(&bounded).is_empty(),
            "the arm past the replay keeps its reach check"
        );
        let first_abandoned = (0..=40u64).find(|&n| reach_check_fails_at(&bounded, n));
        assert!(
            first_abandoned.is_some_and(|n| n > 10),
            "every n <= 10 is replayed, and past the bound the reach check still fails \
             (first abandoned n: {first_abandoned:?})"
        );

        let unbounded = walk_from_host(tcx, "probe_assume_host_none", "probe_assume_callee");
        let unbounded = unbounded.result.expect("the walk finishes");
        assert!(
            reach_check_fails_at(&unbounded, 8),
            "without the assumption the default replay abandons n = 8"
        );
    });
}

/// A walked callee whose loop outruns the replay records its reach check
/// with the reach variable as the approximation's identity, and its nested
/// `bump`'s overflow check builds a panic-path fallback that the nested walk
/// and the host both strip. The harness's identity accounting is
/// complete, so the overflow check, which reads no freed value, is
/// independent and a counterexample to it can be certified. Before, every
/// fallback the walker BUILT counted as an unidentified gap, the accounting
/// was incomplete, and no counterexample of such a harness was certified
/// (`walker_declared_unwind_dual.rs` `b_assume_bound_bug`).
#[test]
fn test_stripped_panic_fallbacks_leave_the_identity_accounting_complete() {
    with_probe(|tcx| {
        let fn_name = "probe_cert_host";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("host body");
        let vc = mir_to_chc_with_instance(tcx, &body, instance, fn_name, ChcConfig::default());
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove(fn_name)
            .unwrap_or_default();
        let summary = || {
            vc.properties
                .iter()
                .map(|p| (p.message.clone(), p.approximation_dependent))
                .collect::<Vec<_>>()
        };
        assert!(
            vc.approximated_vars.iter().any(|v| v.starts_with("__walker_uncertified_reach")),
            "the loop outruns the replay and records its reach check: {:?}",
            vc.approximated_vars
        );
        assert!(
            !vc.approximated_vars.iter().any(|v| v.starts_with("__assert_fail_inline")),
            "no stripped fallback is an approximation: {:?}",
            vc.approximated_vars
        );
        assert!(
            vc.approximation_identity_complete,
            "every approximation is identified (accounted {}, vars {:?}, site reasons {reasons:?})",
            vc.accounted_approximations, vc.approximated_vars
        );
        assert!(
            vc.properties.iter().any(|p| p
                .message
                .as_deref()
                .is_some_and(|m| m.contains("add") && m.contains("overflow"))
                && p.approximation_dependent == Some(false)),
            "the overflow check is independent of the reach variable: {:?}",
            summary()
        );
    });
}

// ---------------------------------------------------------------------------
// (c) Exact array aggregates
// ---------------------------------------------------------------------------

/// `[a, 1, 2, 3]` built in a walked body reads exactly at every index.
/// Before, the aggregate was skipped and the read did not translate.
#[test]
fn test_walked_array_aggregate_reads_exactly() {
    with_probe(|tcx| {
        let result = walk(tcx, "probe_array_read").result.expect("the walk finishes");
        let at = |a: u64, i: u64| {
            as_u64(eval_with(&result.value, &[("arg1", bv(a, 8)), ("arg2", bv(i, 8))]))
        };
        assert_eq!(at(9, 0), Some(9));
        assert_eq!(at(9, 1), Some(1));
        assert_eq!(at(9, 6), Some(2));
        assert_eq!(at(9, 7), Some(3));
        let single = walk(tcx, "probe_single_element_array").result.expect("the walk finishes");
        assert_eq!(
            as_u64(eval_with(&single.value, &[("arg1", bv(5, 8)), ("arg2", bv(3, 8))])),
            Some(5)
        );
    });
}

/// An array of `Option<u8>` is stored packed and read back unpacked: the
/// match sees `Some(a)`, `None`, `Some(1)` exactly.
#[test]
fn test_walked_datatype_array_aggregate_reads_exactly() {
    with_probe(|tcx| {
        let result = walk(tcx, "probe_option_array_read").result.expect("the walk finishes");
        let at = |a: u64, i: u64| {
            as_u64(eval_with(&result.value, &[("arg1", bv(a, 8)), ("arg2", bv(i, 8))]))
        };
        assert_eq!(at(9, 0), Some(9));
        assert_eq!(at(9, 1), Some(77));
        assert_eq!(at(9, 2), Some(1));
        assert_eq!(at(9, 3), Some(2));
    });
}

// ---------------------------------------------------------------------------
// (d) kani::panic
// ---------------------------------------------------------------------------

/// `kani::panic(msg)` (what trust-mc's std lowers `panic!` and `unreachable!`
/// to) is a failing assertion with its message, exactly: on an arm, "the arm
/// is not taken" is the obligation; straight-line, the check is `false`.
/// Before, it was an unmodelled diverging call: an uncertified reach check.
#[test]
fn test_kani_panic_is_an_exact_failing_assertion() {
    with_probe(|tcx| {
        let arm = walk(tcx, "probe_kani_panic_arm");
        let result = arm.result.expect("the walk finishes");
        assert!(reach_checks(&result).is_empty(), "no uncertified record");
        let checks: Vec<_> = result
            .deferred_checks
            .iter()
            .filter(|c| c.message.as_deref() == Some("seven is not allowed"))
            .collect();
        assert_eq!(checks.len(), 1, "one check with the panic's message");
        assert_eq!(checks[0].kind, PropertyKind::Assertion);
        assert_eq!(as_bool(eval_with(&checks[0].check, &[("arg1", bv(7, 8))])), Some(false));
        assert_eq!(as_bool(eval_with(&checks[0].check, &[("arg1", bv(6, 8))])), Some(true));

        let straight = walk(tcx, "probe_kani_panic_straight");
        let result = straight.result.expect("the walk finishes");
        assert!(reach_checks(&result).is_empty(), "no uncertified record");
        assert!(
            result.deferred_checks.iter().any(|c| c.message.as_deref() == Some("always reached")
                && as_bool(eval_with(&c.check, &[])) == Some(false)),
            "the straight-line panic fails"
        );
        assert!(
            !straight.reasons.contains_key("walker_diverging_call_uncertified"),
            "{:?}",
            straight.reasons
        );
    });
}

// ---------------------------------------------------------------------------
// (e) The vtable reads
// ---------------------------------------------------------------------------

/// `vtable_size` / `vtable_align` on a registered vtable identity read its
/// layout exactly; on a pointer no identity names they are the accounted
/// havoc, and neither books `walker_nested_call_lost_effect`. Before, the
/// intrinsic was an unsafe foreign callee havocked with that demoting
/// booking.
#[test]
fn test_vtable_reads_are_modelled_without_an_obligation() {
    with_probe(|tcx| {
        let layouts = [(3u64, (16u64, 8u64)), (5, (4, 4))];
        let exact = walk_with(
            tcx,
            "probe_vtable_size",
            ChcConfig::default(),
            Some(vec![bv(5, 64)]),
            &layouts,
        );
        assert_eq!(as_u64(eval_with(&exact.result.expect("walk").value, &[])), Some(4));
        assert!(
            !exact.reasons.contains_key("walker_nested_call_lost_effect"),
            "{:?}",
            exact.reasons
        );
        let align = walk_with(
            tcx,
            "probe_vtable_align",
            ChcConfig::default(),
            Some(vec![bv(3, 64)]),
            &layouts,
        );
        assert_eq!(as_u64(eval_with(&align.result.expect("walk").value, &[])), Some(8));

        let symbolic = walk_with(tcx, "probe_vtable_size", ChcConfig::default(), None, &layouts);
        let value = symbolic.result.expect("walk").value;
        assert_eq!(
            as_u64(eval_with(&value, &[("arg1", bv(3, 64))])),
            Some(16),
            "resolved by identity"
        );
        assert!(
            !symbolic.reasons.contains_key("walker_nested_call_lost_effect"),
            "{:?}",
            symbolic.reasons
        );
        assert!(
            symbolic.freed.iter().any(|n| n.starts_with("__nested_call_overapprox_vtable_read")),
            "an unregistered pointer's read is the accounted havoc: {:?}",
            symbolic.freed
        );
    });
}

// ---------------------------------------------------------------------------
// (e) The deallocator
// ---------------------------------------------------------------------------

/// `__rust_dealloc` reached in a walked body is the deallocator contract,
/// recorded under the path condition, with the free applied: never the
/// havoc with its demoting `walker_nested_call_lost_effect`.
#[test]
fn test_rust_dealloc_is_modelled() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_dealloc");
        assert!(
            !walked.reasons.contains_key("walker_nested_call_lost_effect"),
            "no havoc of the deallocator: {:?}",
            walked.reasons
        );
        assert!(
            !walked.reasons.contains_key("walker_dealloc_layout_unstated"),
            "the packed Layout is built and read, so the size and alignment are stated: {:?}",
            walked.reasons
        );
        let result = walked.result.expect("the walk finishes");
        assert!(
            result.deferred_checks.iter().any(|c| c.kind == PropertyKind::MemorySafety
                && c.message.as_deref().is_some_and(|m| m.starts_with("rust_dealloc"))),
            "the deallocator contract is recorded: {:?}",
            result.deferred_checks.iter().map(|c| (c.kind, c.message.clone())).collect::<Vec<_>>()
        );
    });
}

// ---------------------------------------------------------------------------
// The abandoned arm inside a foreign function
// ---------------------------------------------------------------------------

/// `<[T]>::iter` on an array the walked body built is walked into
/// `Iter::new`, whose arm the walker cannot finish. The branch made such an
/// arm, inside a safe foreign function that cannot fail for its caller, a
/// plain value havoc; the merge with main keeps Rule D's one predicate at the
/// bailed-arm site instead, because the function's internal checks fail once
/// unsafe code has broken its argument's invariant. The abandoned arm is
/// accounted for (its reach check, or the lost effect), never a silent havoc.
#[test]
fn test_abandoned_arm_in_a_foreign_function_is_accounted() {
    with_probe(|tcx| {
        let walked = walk(tcx, "probe_slice_iter");
        assert!(walked.result.is_some(), "the walk finishes");
        let accounted = [
            "walker_bailed_arm_obligation_uncertified",
            "walker_bailed_arm_lost_effect",
            "walker_nested_call_lost_effect",
        ];
        assert!(
            !walked.reasons.contains_key("switchint_bailed_arm_in_contained_foreign"),
            "{:?}",
            walked.reasons
        );
        if walked.reasons.contains_key("switchint_branch_overapprox") {
            assert!(
                accounted.iter().any(|reason| walked.reasons.contains_key(*reason)),
                "an abandoned arm is accounted: {:?}",
                walked.reasons
            );
        }
    });
}

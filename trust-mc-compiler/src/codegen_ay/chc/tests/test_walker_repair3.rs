// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Repair round 3 of fix/chc-walker-fail-closed (walker fail-closed review 6
//! round 3; docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed:
//! repair round 3"): `Iterator::sum` is modelled only for core's own `Sum`
//! impls (1, 2, 4), the loop replay refunds only a header's own exit test
//! (3), an unwinding assertion the host's dominating bounds discharge is not a
//! property (5), a whole collection stored through a reference fails closed
//! (7), `retain`'s closure obligations are a reach check (8), an adapter's
//! fresh value is an identified sound havoc (9), and `Skip` takes its inner
//! rule only over a loop-free `nth` (10). (6) is in
//! `kani_middle/transform/simple_str_iter_tests.rs`, the BMC half of (8) in
//! `codegen_function/integration_bmc_collect_adapter_tests.rs`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

use crate::codegen_ay::chc::call::codegen_call_virtual_inline::host_bound_discharge::{
    LOOP_UNWINDING_ASSERTION_MESSAGE, drop_host_discharged_assume_guard,
    drop_host_discharged_unwinding_checks,
};
use crate::codegen_ay::chc::call::inline_body::translate_inline_body;
use crate::codegen_ay::reduce_loop_rule::{
    ReduceLoopRule, SumModel, is_inlined_sum_instance, iter_sum_call_model, reduce_loop_rule,
};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, TerminatorKind};
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};
use trust_mc_core::chc_const_prop::eval::try_eval_to_const;

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    use std::iter::Sum;
    use std::num::{Saturating, Wrapping};

    mod kani {
        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    #[inline(never)]
    fn sink<T>(_v: T) {}

    // (1, 2, 4) `Iterator::sum` into core's and into user `Sum` impls.
    pub struct Mx(pub u8);
    impl<'a> Sum<&'a u8> for Mx {
        fn sum<I: Iterator<Item = &'a u8>>(it: I) -> Mx {
            Mx(it.fold(0, |a, b| a.max(*b)))
        }
    }
    pub struct First(pub u8);
    impl<'a> Sum<&'a u8> for First {
        fn sum<I: Iterator<Item = &'a u8>>(mut it: I) -> First {
            First(*it.next().unwrap_or(&0))
        }
    }
    pub struct M(pub u8);
    impl<'a> Sum<&'a M> for u8 {
        fn sum<I: Iterator<Item = &'a M>>(it: I) -> u8 {
            it.fold(0u8, |acc, m| if m.0 > acc { m.0 } else { acc })
        }
    }
    pub fn probe_sum_u8(a: [u8; 3]) -> u8 { a.iter().sum() }
    pub fn probe_sum_mx(a: [u8; 3]) -> Mx { a.iter().sum() }
    pub fn probe_sum_first(a: [u8; 3]) -> First { a.iter().sum() }
    pub fn probe_sum_prim_target(a: [M; 3]) -> u8 { a.iter().sum() }
    pub fn probe_sum_wrapping(a: [Wrapping<u8>; 3]) -> Wrapping<u8> { a.iter().sum() }
    pub fn probe_sum_saturating(a: [Saturating<u8>; 3]) -> Saturating<u8> { a.iter().sum() }

    // (3) A closure whose result folds to a constant, inside `any`'s loop.
    pub fn probe_any_const_false(a: [u8; 3]) -> bool {
        a.iter().any(|_| false)
    }

    // (5) An obligation-free loop bounded by the host's assumption.
    #[inline(never)]
    pub fn free_loop(x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        while i < n {
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }
    pub fn probe_host_n10(x: u8, n: u8) -> u8 {
        kani::assume(n <= 10);
        free_loop(x, n)
    }
    pub fn probe_host_n12(x: u8, n: u8) -> u8 {
        kani::assume(n <= 12);
        free_loop(x, n)
    }
    pub fn probe_host_branch_n10(x: u8, n: u8, c: bool) -> u8 {
        if c {
            kani::assume(n <= 10);
        }
        free_loop(x, n)
    }

    // (7) A whole value stored through a reference.
    pub fn probe_deref_vec_store() -> usize {
        let mut v = Vec::<u8>::new();
        {
            let r = &mut v;
            *r = vec![1, 2, 3];
        }
        v.len()
    }
    pub fn probe_deref_u8_store() -> u8 {
        let mut x = 0u8;
        {
            let r = &mut x;
            *r = 5;
        }
        x
    }

    // (8) `retain` with a closure that carries an obligation, and one that
    // does not.
    pub fn probe_retain_assert(mut v: Vec<u8>) -> usize {
        v.retain(|x| {
            assert!(*x < 200);
            true
        });
        v.len()
    }
    pub fn probe_retain_plain(mut v: Vec<u8>) -> usize {
        v.retain(|x| *x > 1);
        v.len()
    }

    // (10) `Skip` over receivers whose `nth` does and does not loop.
    pub fn probe_skip_types(a: [u8; 4]) -> usize {
        let s1 = a.iter().skip(1);
        let s2 = a.iter().copied().skip(1);
        let s3 = a.iter().filter(|x| **x > 1).skip(1);
        let s4 = a.iter().map(|x| *x).skip(1);
        s1.count() + s2.count() + s3.count() + s4.count()
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

/// The call operand and its body's locals of the call in `body` whose
/// callee's name ends with `suffix`.
fn call_named<'b>(body: &'b Body, suffix: &str) -> &'b rustc_public::mir::Operand {
    body.blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(body.locals()).ok()?.kind() else {
                return None;
            };
            def.name().ends_with(suffix).then_some(func)
        })
        .unwrap_or_else(|| panic!("the body calls `{suffix}`"))
}

fn sum_model(tcx: TyCtxt<'_>, probe: &str) -> Option<SumModel> {
    let body = find_instance_by_suffix(tcx, probe).body().expect("probe body");
    iter_sum_call_model(call_named(&body, "Iterator::sum"), body.locals())
}

fn sum_instance(tcx: TyCtxt<'_>, probe: &str) -> Instance {
    let body = find_instance_by_suffix(tcx, probe).body().expect("probe body");
    let func = call_named(&body, "Iterator::sum");
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(body.locals()).unwrap().kind() else {
        panic!("a function call");
    };
    Instance::resolve(def, &args).expect("Iterator::sum resolves")
}

fn reasons_of(ctx_name: &str) -> BTreeMap<String, usize> {
    crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(ctx_name)
        .unwrap_or_default()
}

// ---------------------------------------------------------------------------
// (1, 2, 4) `Iterator::sum`
// ---------------------------------------------------------------------------

/// The sum models were keyed on the method NAME: every `Sum` impl was the
/// checked integer fold, so a user `max` / first-element / loop impl, a user
/// `Sum<&M> for u8`, and std's `Wrapping` / `Saturating` were all modelled as
/// `+` with an overflow check (walker fail-closed review 6 round 3, findings
/// 1, 2 and 4). Only core's impls are modelled now, each with its own step.
#[test]
fn test_sum_model_follows_the_impl_the_call_runs() {
    with_probe(|tcx| {
        assert_eq!(sum_model(tcx, "probe_sum_u8"), Some(SumModel::Checked), "core's u8 sum");
        assert_eq!(sum_model(tcx, "probe_sum_mx"), None, "a user Sum impl");
        assert_eq!(sum_model(tcx, "probe_sum_first"), None, "a user Sum impl");
        assert_eq!(
            sum_model(tcx, "probe_sum_prim_target"),
            None,
            "a user `Sum<&M> for u8`: a primitive target, a user impl"
        );
        assert_eq!(sum_model(tcx, "probe_sum_wrapping"), Some(SumModel::Wrapping));
        assert_eq!(
            sum_model(tcx, "probe_sum_saturating"),
            Some(SumModel::Saturating { signed: false })
        );
    });
}

/// A user `Sum` impl that is one `fold` is inlined into the harness, where
/// the reduction models replay its closure; one that is not stays a call the
/// walker walks. Core's modelled impls are never inlined.
#[test]
fn test_fold_shaped_user_sum_is_inlined() {
    with_probe(|tcx| {
        assert!(is_inlined_sum_instance(&sum_instance(tcx, "probe_sum_mx")), "Mx(it.fold(..))");
        assert!(
            !is_inlined_sum_instance(&sum_instance(tcx, "probe_sum_first")),
            "First(*it.next()..) is walked"
        );
        assert!(!is_inlined_sum_instance(&sum_instance(tcx, "probe_sum_u8")), "core's u8 sum");
    });
}

/// `Saturating` adds with `saturating_add` (finding 4: the checked step
/// failed `Wrapping` / `Saturating` sums Kani proves).
#[test]
fn test_saturating_sum_step_saturates() {
    use crate::codegen_ay::chc::call::codegen_call_iterator_adapter::saturating_add;
    let value = |a: i128, b: i128, width: u32, signed: bool| {
        let mask = (1i128 << width) - 1;
        let e = saturating_add(
            &Expr::bitvec_const(a & mask, width),
            &Expr::bitvec_const(b & mask, width),
            signed,
        )
        .expect("a step");
        match try_eval_to_const(&e).map(|c| c.value().clone()) {
            Some(ExprValue::BitVecConst { value, .. }) => i128::try_from(value).unwrap(),
            other => panic!("constant expected, got {other:?}"),
        }
    };
    assert_eq!(value(200, 100, 8, false), 255, "u8 saturates at MAX");
    assert_eq!(value(20, 100, 8, false), 120, "u8 below MAX adds");
    assert_eq!(value(-100, -100, 8, true), 0x80, "i8 saturates at MIN");
    assert_eq!(value(100, 100, 8, true), 127, "i8 saturates at MAX");
    assert_eq!(value(100, -50, 8, true), 50, "i8 of mixed signs adds");
}

// ---------------------------------------------------------------------------
// (3) The loop replay's refund
// ---------------------------------------------------------------------------

/// `iter().any(|_| false)`: the closure's `if f(x) { return true }` folds to
/// "stay" every pass. It is a test with an edge out of the loop but not the
/// loop's exit test, and refunding it ran the replay to the SwitchInt depth
/// limit (15 refunds) and compilation into a 600 s timeout (finding 3). Only
/// the header's own exit test is refunded now: at most one per element.
#[test]
fn test_loop_refund_is_only_the_headers_exit_test() {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::loop_replay::CONCRETE_LOOP_REFUNDS;
    with_probe(|tcx| {
        let name = "walker_repair3__probe_any_const_false";
        let instance = find_instance_by_suffix(tcx, "probe_any_const_false");
        let body = instance.body().expect("body");
        CONCRETE_LOOP_REFUNDS.store(0, Ordering::SeqCst);
        let started = std::time::Instant::now();
        let _vc = mir_to_chc_with_instance(tcx, &body, instance, name, ChcConfig::default());
        let refunds = CONCRETE_LOOP_REFUNDS.load(Ordering::SeqCst);
        assert!(refunds <= 4, "at most one refund per element and the exit, got {refunds}");
        assert!(
            started.elapsed() < std::time::Duration::from_secs(120),
            "the translation finishes (took {:?})",
            started.elapsed()
        );
        let _ = reasons_of(name);
    });
}

// ---------------------------------------------------------------------------
// (5) The host's dominating bounds
// ---------------------------------------------------------------------------

/// Walk `free_loop` from `host` under `#[kani::unwind(12)]` and hand the
/// walk to `f` with the host context, the call block and the modified set.
fn with_free_loop_walk_from_host<R>(
    tcx: TyCtxt<'_>,
    host: &str,
    f: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        usize,
        &HashSet<usize>,
        crate::codegen_ay::chc::call::inline_body::InlineReturn,
        &[Expr],
    ) -> R,
) -> R {
    let ctx_name = format!("walker_repair3__{host}");
    let host_body = find_instance_by_suffix(tcx, host).body().expect("host body");
    let callee = find_instance_by_suffix(tcx, "free_loop");
    let callee_body = callee.body().expect("callee body");
    let (call_bb, args) = host_body
        .blocks
        .iter()
        .enumerate()
        .find_map(|(bb, block)| {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                return None;
            };
            let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(host_body.locals()).ok()?.kind()
            else {
                return None;
            };
            def.name().ends_with("free_loop").then(|| (bb, args.clone()))
        })
        .expect("the host calls free_loop");
    let config = ChcConfig { recursive_unwind_depth: 12, unwinding_assertions: true, ..ChcConfig::default() };
    let mut chc_ctx = ChcCtx::new(tcx, &host_body, ctx_name.as_str(), config);
    chc_ctx.declare_block_relations();
    let modified = HashSet::new();
    let params: Vec<Expr> = args
        .iter()
        .map(|arg| chc_ctx.translate_operand_with_modified(arg, &modified).expect("argument"))
        .collect();
    chc_ctx.mark_inline_field_reads(&callee_body, &params, 0);
    let walked = translate_inline_body(
        &mut chc_ctx,
        &callee_body,
        &params,
        call_bb,
        &HashMap::new(),
        Some(callee),
        0,
    )
    .expect("the walk finishes");
    let result = f(&mut chc_ctx, call_bb, &modified, walked, &params);
    let _ = reasons_of(&ctx_name);
    result
}

/// The unwinding checks of `free_loop` walked from `host` under
/// `#[kani::unwind(12)]`, and those left after the host-bound discharge.
fn unwinding_checks_from_host(tcx: TyCtxt<'_>, host: &str) -> (usize, usize) {
    with_free_loop_walk_from_host(tcx, host, |chc_ctx, call_bb, modified, walked, _| {
        let is_unwinding = |c: &crate::codegen_ay::chc::call::inline_body::DeferredInlineCheck| {
            c.message.as_deref() == Some(LOOP_UNWINDING_ASSERTION_MESSAGE)
        };
        let before = walked.deferred_checks.iter().filter(|c| is_unwinding(c)).count();
        let kept = drop_host_discharged_unwinding_checks(chc_ctx, call_bb, modified, walked.deferred_checks);
        let after = kept.iter().filter(|c| is_unwinding(c)).count();
        (before, after)
    })
}

/// Whether the walk of `free_loop` from `host` cut a path (an assume guard
/// on the value), and whether that guard survives the host-bound discharge.
fn assume_guard_from_host(tcx: TyCtxt<'_>, host: &str) -> (bool, bool) {
    with_free_loop_walk_from_host(tcx, host, |chc_ctx, call_bb, modified, walked, _| {
        let guard = crate::codegen_ay::chc::call::inline_body::extract_inline_assume_guard(&walked.value);
        let had = guard.is_some();
        let kept = drop_host_discharged_assume_guard(chc_ctx, call_bb, modified, guard);
        (had, kept.is_some())
    })
}

/// Repair round 1's finding 6 (`l_free_sym_safe`): the unwinding assertion on
/// pass 13 of a loop the host bounds by `n <= 10` under `unwind(12)` was a
/// second property that split the solve budget. It is unviolable under the
/// host's dominating assumption and no longer emitted; under `n <= 12`, or
/// an assumption on one branch only, it stays.
#[test]
fn test_host_bound_discharges_only_an_unviolable_unwinding_check() {
    with_probe(|tcx| {
        let (before, after) = unwinding_checks_from_host(tcx, "probe_host_n10");
        assert!(before >= 1, "the walk states the unwinding assertion");
        assert_eq!(after, 0, "n <= 10 needs 11 passes of 12: discharged");
        let (before, after) = unwinding_checks_from_host(tcx, "probe_host_n12");
        assert!(before >= 1 && after == before, "n <= 12 needs 13 passes: kept");
        let (before, after) = unwinding_checks_from_host(tcx, "probe_host_branch_n10");
        assert!(before >= 1 && after == before, "an assumption on one branch does not dominate");
    });
}

/// The walker's reach check on an abandoned arm is `¬guard ∨ t`, `t` free.
/// Under the host's `assume(n <= 10)` an arm only `n > 10` takes can never
/// be reached, and its check is dropped; an arm `n > 3` takes is kept, and so
/// is any other check. (`walker_loop_exit_test_dual.rs`
/// `safe_break_sym_bound_small` carried such a check as a second property
/// beside `assume(n <= 5)` where main had one.)
#[test]
fn test_host_bound_discharges_an_unreachable_abandoned_arm_check() {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::host_bound_discharge::WALKER_BAILED_ARM_REACH_MESSAGE;
    use crate::codegen_ay::chc::call::inline_body::DeferredInlineCheck;
    with_probe(|tcx| {
        let kept = with_free_loop_walk_from_host(tcx, "probe_host_n10", |chc_ctx, call_bb, modified, _, params| {
            let n = params[1].clone();
            let t = Expr::var("__walker_uncertified_reach_test", ay_bindings::Sort::bool());
            let reach = |k: u64, message: &str| DeferredInlineCheck {
                check: n.clone().bvugt(Expr::bitvec_const(k, 8)).not().or(t.clone()),
                kind: trust_mc_core::violation::PropertyKind::Other,
                message: Some(message.to_string()),
                write_mark: chc_ctx.heap_state.write_mark(),
                merge_key: None,
            };
            let arm = format!("{WALKER_BAILED_ARM_REACH_MESSAGE} (abandoned branch bb3 of `free_loop`)");
            let checks = vec![reach(10, &arm), reach(3, &arm), reach(10, "assertion failed: x < 9")];
            drop_host_discharged_unwinding_checks(chc_ctx, call_bb, modified, checks)
        });
        let kept: Vec<_> = kept.iter().map(|c| c.message.clone().unwrap_or_default()).collect();
        assert_eq!(kept.len(), 2, "only the arm n > 10 is unreachable: {kept:?}");
        assert!(kept.iter().any(|m| m.starts_with(WALKER_BAILED_ARM_REACH_MESSAGE)), "{kept:?}");
        assert!(kept.iter().any(|m| m == "assertion failed: x < 9"), "{kept:?}");
    });
}

/// The walk ends a path that needs a thirteenth pass (Kani's `assume(false)`
/// after the unwinding assertion), and the host took that cut as an assume
/// guard: a twelve-arm chain beside `kani::assume(n <= 10)`, which already
/// says so. `free_sym_unwind12_safe` missed its 30 s budget on it at load 29
/// where main proves in 13 s (repair round 4, finding 5). A guard the host's
/// dominating bounds imply is dropped, exactly; one they do not imply stays.
#[test]
fn test_host_bound_discharges_an_implied_assume_guard() {
    with_probe(|tcx| {
        assert_eq!(assume_guard_from_host(tcx, "probe_host_n10"), (true, false), "n <= 10: implied");
        assert_eq!(assume_guard_from_host(tcx, "probe_host_n12"), (true, true), "n <= 12: kept");
        assert_eq!(
            assume_guard_from_host(tcx, "probe_host_branch_n10"),
            (true, true),
            "an assumption on one branch does not dominate"
        );
    });
}

// ---------------------------------------------------------------------------
// (7) A whole collection stored through a reference
// ---------------------------------------------------------------------------

/// `*r = vec![1, 2, 3]` with `r = &mut v` left `v`'s length side state as it
/// was: `v.len() == 0` verified clean where Kani fails (finding 7). The
/// store fails closed; a scalar stored through a reference does not.
#[test]
fn test_whole_collection_store_through_a_reference_fails_closed() {
    with_probe(|tcx| {
        for (probe, expected) in [("probe_deref_vec_store", true), ("probe_deref_u8_store", false)] {
            let name = format!("walker_repair3__{probe}");
            let instance = find_instance_by_suffix(tcx, probe);
            let body = instance.body().expect("body");
            let _vc = mir_to_chc_with_instance(tcx, &body, instance, name.as_str(), ChcConfig::default());
            let reasons = reasons_of(&name);
            assert_eq!(
                reasons.contains_key("deref_store_collection_side_state_unmodelled"),
                expected,
                "{probe}: {reasons:?}"
            );
        }
    });
}

// ---------------------------------------------------------------------------
// (8) `retain`'s closure
// ---------------------------------------------------------------------------

/// The Vec models never walk the closure `retain` runs, and an `assert!` in
/// it was lost (finding 8, `h17_retain_bug`). A closure that can carry an
/// obligation gets an uncertified reach check; one that cannot does not.
#[test]
fn test_retain_closure_obligation_gets_a_reach_check() {
    with_probe(|tcx| {
        for (probe, expected) in [("probe_retain_assert", true), ("probe_retain_plain", false)] {
            let name = format!("walker_repair3__{probe}");
            let instance = find_instance_by_suffix(tcx, probe);
            let body = instance.body().expect("body");
            let _vc = mir_to_chc_with_instance(tcx, &body, instance, name.as_str(), ChcConfig::default());
            let reasons = reasons_of(&name);
            assert_eq!(
                reasons.contains_key("vec_closure_step_uncertified"),
                expected,
                "{probe}: {reasons:?}"
            );
        }
    });
}

// ---------------------------------------------------------------------------
// (9) An adapter's fresh value
// ---------------------------------------------------------------------------

/// An iterator adapter's fresh value recorded only `aggregate_encoding_gap`,
/// which no verdict reads, so a counterexample built on it was certified
/// Genuine (finding 9, `c1_filter_fold_n4_u4_safe`). It is an identified
/// sound havoc now: a proof stays clean, a dependent counterexample is not
/// certified.
#[test]
fn test_adapter_symbol_is_an_identified_sound_havoc() {
    assert!(matches!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness("iter_adapter_symbol_overapprox"),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::SoundHavoc
    ));
    with_probe(|tcx| {
        let name = "walker_repair3__probe_sum_u8";
        let body = find_instance_by_suffix(tcx, "probe_sum_u8").body().expect("body");
        let mut chc_ctx = ChcCtx::new(tcx, &body, name, ChcConfig::default());
        let before = chc_ctx.vc.accounted_approximations;
        let symbol = chc_ctx.fresh_adapter_symbol("iter_fold_value", ay_bindings::Sort::bitvec(8));
        assert!(matches!(symbol.value(), ExprValue::Var { .. }), "a fresh variable");
        assert_eq!(chc_ctx.vc.accounted_approximations, before + 1, "its identity is recorded");
        let reasons = reasons_of(name);
        assert!(reasons.contains_key("iter_adapter_symbol_overapprox"), "{reasons:?}");
    });
}

// ---------------------------------------------------------------------------
// (10) `Skip`
// ---------------------------------------------------------------------------

/// `Skip::fold` first runs the inner iterator's `nth`, a loop for `Filter`,
/// `Map` and `Cloned` (the default `advance_by`): the rule table gave `Skip`
/// its inner rule whatever the inner iterator was (finding 10). Only a
/// receiver whose `nth` is index arithmetic keeps it.
#[test]
fn test_skip_takes_the_inner_rule_only_over_a_loop_free_nth() {
    with_probe(|tcx| {
        let body = find_instance_by_suffix(tcx, "probe_skip_types").body().expect("body");
        // The last path segment of the type directly under the outermost
        // `Skip<`.
        let inner_of_skip = |ty: &rustc_public::ty::Ty| {
            let text = format!("{ty}");
            let after = &text[text.find("Skip<")? + 5..];
            let inner = after.split('<').next()?;
            Some(inner.rsplit("::").next()?.to_string())
        };
        let rule_of_skip = |inner: &str| {
            body.locals()
                .iter()
                .map(|decl| decl.ty)
                .find(|ty| inner_of_skip(ty).as_deref() == Some(inner))
                .map(reduce_loop_rule)
                .unwrap_or_else(|| panic!("a Skip<{inner}..> local"))
        };
        assert_eq!(rule_of_skip("Iter"), Some(ReduceLoopRule::PassesPastBound));
        assert_eq!(rule_of_skip("Copied"), Some(ReduceLoopRule::PassesPastBound));
        assert_eq!(rule_of_skip("Filter"), None, "Filter::nth loops");
        assert_eq!(rule_of_skip("Map"), None, "Map::nth loops");
    });
}

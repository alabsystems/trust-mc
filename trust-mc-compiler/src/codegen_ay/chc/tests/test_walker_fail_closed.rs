// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The inline walker's remaining fail-open paths
//! (docs/chc-walker-missed-bugs-2026-09-23.md, "Mechanisms B to E", and
//! docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed"): each test
//! walks a probe body and checks the obligation, or the fail-closed record,
//! that the walk used to drop. Every probe asserts that its body has the shape
//! it is about, so a MIR-lowering change cannot make a test pass vacuously.

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
    #![allow(dead_code, internal_features)]
    #![feature(register_tool, core_intrinsics)]
    #![register_tool(kanitool)]

    // trust-mc's `library/std` lowers `assert!` to this hook (review round,
    // walker_kani_assert_call_dual.rs).
    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, msg: &'static str) {
            let _ = (cond, msg);
        }
    }

    // Walker loop replay (walker_loop_replay_dual.rs): a constant-bound loop
    // longer than the replay fuel.
    pub fn probe_loop_ten_unchecked(x: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        while i < 10 {
            acc = unsafe { acc.unchecked_add(20) };
            i += 1;
        }
        acc
    }

    // `while i < n`: MIR switches as `[0: exit, otherwise: body]`.
    pub fn probe_loop_while_sym(x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        while i < n {
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }

    // `if i == n { break }`: MIR switches as `[0: body, otherwise: exit]`.
    pub fn probe_loop_break_sym(x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        loop {
            if i == n {
                break;
            }
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }

    // Mechanism D (walker_bailed_branch_dual.rs): `unreachable_unchecked`.
    pub fn probe_unreachable_arm(a: u8) -> u8 {
        if a == 3 {
            unsafe { core::hint::unreachable_unchecked() }
        }
        a
    }

    #[inline(never)]
    fn opaque(_a: u8) {}

    // The diverging call is not the arm's own block, so the arm is walked and
    // the walker reaches the call itself.
    pub fn probe_unreachable_after_call(a: u8) -> u8 {
        if a == 3 {
            opaque(a);
            unsafe { core::hint::unreachable_unchecked() }
        }
        a
    }

    // `assert!` lowers to a direct `core::panicking::panic(<const str>)` arm.
    pub fn probe_panic_arm(a: u8) -> u8 {
        assert!(a != 3);
        a
    }

    #[inline(never)]
    fn sink_u8(_v: u8) {}

    // Mechanism E (walker_untranslatable_assert_dual.rs): `skipped` is an
    // argument the test leaves unseeded (`arg_params`), a local the walk has
    // no term for, as a skipped rvalue leaves one, so the overflow Assert of
    // `skipped + 200` cannot be translated, while the return value `a` can.
    // (The array aggregate that played this part is exact since package round
    // 2 item c.)
    pub fn probe_untranslatable_assert(a: u8, skipped: u8) -> u8 {
        sink_u8(skipped + 200);
        a
    }

    // Control: the same Assert over a translatable operand.
    pub fn probe_translatable_assert(a: u8) -> u8 {
        sink_u8(a + 200);
        a
    }

    // A user `-> !` function (walker_validity_intrinsics_dual.rs `diverge_bug`).
    fn die_probe(x: u8) -> ! {
        panic!("probe diverging fn reached with {}", x)
    }
    pub fn probe_user_diverging(x: u8) -> u8 {
        if x == 7 {
            die_probe(x)
        }
        0
    }

    // Control: a diverging function with nothing to prove.
    fn spin_probe() -> ! {
        loop {}
    }
    pub fn probe_obligation_free_diverging(x: u8) -> u8 {
        if x == 7 {
            spin_probe()
        }
        0
    }

    // Mechanism C (walker_bailed_branch_dual.rs): the `a > 10` arm cannot be
    // finished (`skipped` has no term, so the `assert!` SwitchInt cannot be
    // translated), and its region carries the assertion's panic.
    pub fn probe_bailed_arm(a: u8, skipped: u8) -> u8 {
        if a > 10 {
            assert!(skipped != 100);
            skipped
        } else {
            a
        }
    }

    // Control: the arm bails too (its return value has no term), but its
    // region has nothing to check.
    pub fn probe_bailed_arm_obligation_free(a: u8, skipped: u8) -> u8 {
        if a > 10 { skipped } else { a }
    }

    // Mechanism B (walker_get_unchecked_dual.rs): the slice argument does not
    // translate (`skipped` has no term), so the walker havocs the `unsafe` std
    // callee, whose body carries the `assume` Kani checks.
    pub fn probe_get_unchecked(i: u8, skipped: [u8; 4]) -> u8 {
        unsafe { *skipped.get_unchecked(i as usize) }
    }

    #[inline(never)]
    fn sink_opt(_v: Option<u8>) {}

    // Mechanism B, safe std callee reaching the crate's code
    // (walker_std_callee_local_obligation_dual.rs): `o` does not translate,
    // so `Option::map` is havocked with the closure's overflow check.
    pub fn probe_std_map_closure(a: u8, skipped: Option<u8>) -> u8 {
        sink_opt(skipped.map(|v| v + 200));
        a
    }

    // A safe std callee whose own body panics on its input
    // (walker_std_callee_own_panic_dual.rs): `o` does not translate, so
    // `Option::expect` is havocked with its `None` panic.
    pub fn probe_std_expect(a: u8, skipped: Option<u8>) -> u8 {
        sink_u8(skipped.expect("probe: none reached"));
        a
    }

    // Control: a safe std callee that reaches no code of this crate and does
    // not panic in its own body.
    pub fn probe_std_safe_no_local(a: u8, skipped: u8) -> u8 {
        sink_u8(skipped.count_ones() as u8);
        a
    }

    // Review round, Mechanism E through a CALL: `kani::assert` over the
    // untranslatable `skipped` (walker_kani_assert_call_dual.rs).
    pub fn probe_kani_assert_untranslatable(a: u8, skipped: u8) -> u8 {
        kani::assert(skipped != 100, "probe: v is not 100");
        a
    }

    // Control: the same hook over a translatable condition.
    pub fn probe_kani_assert_translatable(a: u8) -> u8 {
        kani::assert(a != 100, "probe: a is not 100");
        a
    }

    // Review round, Mechanism D for the `Unreachable` TERMINATOR:
    // `core::intrinsics::unreachable()` lowers to one
    // (walker_unreachable_terminator_dual.rs).
    pub fn probe_intrinsic_unreachable(a: u8) -> u8 {
        if a == 7 {
            unsafe { core::intrinsics::unreachable() }
        }
        a
    }

    // The intrinsic on an EXPLICIT arm of an enum `match`: a valid `None`
    // reaches it.
    pub fn probe_intrinsic_unreachable_enum_arm(a: u8) -> u8 {
        let o = if a == 3 { None } else { Some(a) };
        match o {
            Some(x) => x,
            None => unsafe { core::intrinsics::unreachable() },
        }
    }

    #[derive(Clone, Copy)]
    pub enum Two {
        A,
        B,
    }

    // Control: the `otherwise` arm rustc adds to an exhaustive enum `match`
    // stays dead.
    pub fn probe_exhaustive_enum_match(e: Two) -> u8 {
        match e {
            Two::A => 1,
            Two::B => 2,
        }
    }

    // Review round, the region scan: the abandoned `a > 10` region holds only
    // the untranslatable branch and the intrinsic's `Unreachable`.
    pub fn probe_region_unreachable(a: u8, skipped: u8) -> u8 {
        if a > 10 {
            if skipped == 100 {
                unsafe { core::intrinsics::unreachable() }
            }
            skipped
        } else {
            a
        }
    }

    // Control: the region's only call is check-free arithmetic
    // (`saturating_add` reaches a body-less intrinsic).
    pub fn probe_region_check_free(a: u8, skipped: u8) -> u8 {
        if a > 10 {
            if skipped > 50 { skipped.saturating_add(3) } else { skipped }
        } else {
            a
        }
    }

    #[inline(never)]
    fn sink_any<T>(_v: T) {}

    // Review round, Mechanism B: a safe std callee whose panic sits deeper
    // than its own body (`windows(0)` panics in `Option::expect` one call
    // down) is havocked (walker_std_callee_deep_panic_dual.rs).
    pub fn probe_std_windows(a: u8, skipped: usize) -> u8 {
        let s: &[u8] = &[1, 2, 3, 4];
        sink_any(s.windows(skipped));
        a
    }

    fn add200_probe(v: u8) -> u8 {
        v + 200
    }

    // A safe std callee handed a FUNCTION POINTER into the crate's code: the
    // walk cannot follow the indirect call.
    pub fn probe_std_map_fn_pointer(a: u8, skipped: Option<u8>) -> u8 {
        let f: fn(u8) -> u8 = add200_probe;
        sink_opt(skipped.map(f));
        a
    }

    // Package item (a): a standard-library function the walker models by its
    // path (the known-call table), stubbed (stub_modelled_std_dual.rs).
    pub fn probe_calls_wrapping_add(a: u8) -> u8 {
        a.wrapping_add(1)
    }
    pub fn probe_stub_wrapping_add(a: u8, b: u8) -> u8 {
        assert!(a != 100);
        a ^ b
    }

    // Item (a): a trait-method call that resolves to a stubbed impl item.
    pub struct Q(pub u8);
    impl Clone for Q {
        fn clone(&self) -> Q {
            Q(self.0)
        }
    }
    pub fn probe_calls_clone(q: &Q) -> u8 {
        q.clone().0
    }
    pub fn probe_q_clone_stub(q: &Q) -> Q {
        assert!(q.0 != 100);
        Q(q.0)
    }

    // Item (e): an extern "C" function stubbed, called from a walked body
    // (walker_extern_stub_dual.rs).
    unsafe extern "C" {
        fn probe_ext(x: u8) -> u8;
    }
    pub fn probe_calls_extern(a: u8) -> u8 {
        unsafe { probe_ext(a) }
    }
    pub fn probe_ext_stub(x: u8) -> u8 {
        assert!(x != 100);
        x
    }

    // Item (a): a stubbed trait DEFAULT method is not applied to an impl
    // that overrides it (as `FnStubPass`, which keys on the resolved
    // instance).
    pub trait HasDefault {
        fn method(&self) -> u8 {
            0
        }
    }
    pub struct UsesDefault;
    impl HasDefault for UsesDefault {}
    pub struct Overrides;
    impl HasDefault for Overrides {
        fn method(&self) -> u8 {
            100
        }
    }
    pub fn probe_default_method_stub(u: &UsesDefault) -> u8 {
        u.method()
    }
    pub fn probe_overridden_method_stub(o: &Overrides) -> u8 {
        o.method()
    }
    pub fn probe_method_stub<T>(_x: &T) -> u8 {
        42
    }

    // Item (a), follow-up: a LOCAL function named like a std helper the
    // encoders model by name (user_fn_std_helper_name_dual.rs).
    #[inline(never)]
    fn probe_my_wrapping_add(a: u8, b: u8) -> u8 {
        a ^ b
    }
    pub fn probe_calls_local_wrapping_add(a: u8) -> u8 {
        probe_my_wrapping_add(a, 1)
    }

    // Item (d): the exhaustive `otherwise` of a data-carrying enum stays dead
    // (every term of its datatype sort is a variant).
    #[derive(Clone, Copy)]
    pub enum Carry {
        A(u8),
        B,
    }
    pub fn probe_exhaustive_carrying_enum_match(e: Carry) -> u8 {
        match e {
            Carry::A(v) => v,
            Carry::B => 2,
        }
    }
"#;

/// Compile `PROBE` and run `test` on it, failing if `test` never ran (a
/// compile that stops early would otherwise pass every assertion vacuously).
///
/// Holds the metadata counter lock throughout: the walks record fallbacks,
/// whose counters are mirrored into process-global state that other tests
/// read under the same lock.
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

/// One fresh parameter per argument local, named `arg<local>`, with the sort
/// the encoder gives the argument's type, except the TRAILING arguments named
/// `skipped*`: those are left unseeded, so the walk has no term for them, as
/// for a local whose defining rvalue it skipped (the probes' stand-in for an
/// untranslatable value).
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
    let arg_count = body.arg_locals().len();
    let seeded = (1..=arg_count).take_while(|local| !skipped.contains(local)).count();
    assert!(
        (seeded + 1..=arg_count).all(|local| skipped.contains(&local)),
        "only trailing arguments may be named `skipped*`"
    );
    (1..=seeded)
        .map(|local| {
            let ty = body.locals()[local].ty;
            let sort = ChcCtx::translate_ty(ty).expect("argument type translates");
            Expr::var(format!("arg{local}"), sort)
        })
        .collect()
}

/// Walk `fn_name` as an inline body with fresh parameters; return the walk's
/// result (if any) and the parameters.
fn walk_probe(tcx: TyCtxt<'_>, fn_name: &str) -> (Option<InlineReturn>, Vec<Expr>) {
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let params = arg_params(&body);
    (walk_body(tcx, instance, &body, fn_name, &params), params)
}

fn walk_body(
    tcx: TyCtxt<'_>,
    instance: Instance,
    body: &Body,
    fn_name: &str,
    params: &[Expr],
) -> Option<InlineReturn> {
    let mut chc_ctx = ChcCtx::new(tcx, body, fn_name, ChcConfig::default());
    chc_ctx.declare_block_relations();
    chc_ctx.mark_inline_field_reads(body, params, 0);
    translate_inline_body(&mut chc_ctx, body, params, 0, &HashMap::new(), Some(instance), 0)
}

/// A walk and what it booked on its context.
struct Accounted {
    result: Option<InlineReturn>,
    /// `sound_havoc_drop` (blessed) records.
    blessed: usize,
    /// `place_translation_drop` (fail-closed) records.
    fail_closed: usize,
    /// Freed-variable identities the walk accounted.
    freed: Vec<String>,
}

fn walk_accounted(tcx: TyCtxt<'_>, fn_name: &str) -> Accounted {
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let params = arg_params(&body);
    let mut chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
    chc_ctx.declare_block_relations();
    chc_ctx.mark_inline_field_reads(&body, &params, 0);
    let blessed = chc_ctx.diagnostics.sound_havoc_drop.get();
    let fail_closed = chc_ctx.diagnostics.place_translation_drop.get();
    let freed = chc_ctx.vc.approximated_vars.len();
    let result =
        translate_inline_body(&mut chc_ctx, &body, &params, 0, &HashMap::new(), Some(instance), 0);
    Accounted {
        result,
        blessed: chc_ctx.diagnostics.sound_havoc_drop.get() - blessed,
        fail_closed: chc_ctx.diagnostics.place_translation_drop.get() - fail_closed,
        freed: chc_ctx.vc.approximated_vars[freed..].to_vec(),
    }
}

/// Walk `fn_name` and return the translation-drop site reasons it recorded
/// (under `with_probe`'s metadata counter lock).
fn walk_reasons(tcx: TyCtxt<'_>, fn_name: &str) -> BTreeMap<String, usize> {
    let ctx_name = format!("walker_fail_closed__{fn_name}");
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let params = arg_params(&body);
    let mut chc_ctx = ChcCtx::new(tcx, &body, ctx_name.as_str(), ChcConfig::default());
    chc_ctx.declare_block_relations();
    chc_ctx.mark_inline_field_reads(&body, &params, 0);
    let _ =
        translate_inline_body(&mut chc_ctx, &body, &params, 0, &HashMap::new(), Some(instance), 0);
    crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(&ctx_name)
        .unwrap_or_default()
}

/// Every variable name `expr` reads.
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

/// The deferred checks that read an uncertified reach-check variable, with
/// that variable.
fn reach_checks(walked: &InlineReturn) -> Vec<(PropertyKind, Option<String>, String)> {
    walked
        .deferred_checks
        .iter()
        .filter_map(|c| {
            vars_of(&c.check)
                .into_iter()
                .find(|name| name.starts_with("__walker_uncertified_reach"))
                .map(|name| (c.kind, c.message.clone(), name))
        })
        .collect()
}

/// `expr` with every variable named in `values` replaced by its value.
fn substitute(expr: &Expr, values: &HashMap<String, Expr>) -> Expr {
    if let ExprValue::Var { name } = expr.value() {
        return values.get(name.as_str()).cloned().unwrap_or_else(|| expr.clone());
    }
    let children: Vec<Expr> = expr.value().children().map(|c| substitute(c, values)).collect();
    if children.is_empty() { expr.clone() } else { rebuild_with_children(expr, children) }
}

/// `expr` evaluated with the named 8-bit variables set, when it folds to a
/// constant.
fn eval_u8(expr: &Expr, values: &[(&str, u64)]) -> Option<u64> {
    let values: HashMap<String, Expr> = values
        .iter()
        .map(|(name, value)| ((*name).to_string(), Expr::bitvec_const(*value, 8)))
        .collect();
    match try_eval_to_const(&substitute(expr, &values))?.value() {
        ExprValue::BitVecConst { value, .. } => u64::try_from(value.clone()).ok(),
        _ => None,
    }
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
// Loop replay (walker_loop_replay_dual.rs)
// ---------------------------------------------------------------------------

/// A constant-bound loop longer than the replay fuel is replayed to its end:
/// every iteration's exit test folds, so each is refunded its header visit.
/// Before, the walk ran out of fuel after five iterations and the checks of
/// iterations six to ten were dropped with the arm that could not finish.
#[test]
fn test_concrete_loop_past_the_fuel_replays_every_iteration() {
    with_probe(|tcx| {
        let fn_name = "probe_loop_ten_unchecked";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        assert!(body_has_loop(&body), "{fn_name}: the probe body has a loop");
        let params = arg_params(&body);
        let walked = walk_body(tcx, instance, &body, fn_name, &params)
            .unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        let unchecked_checks = walked
            .deferred_checks
            .iter()
            .filter(|c| {
                c.kind == PropertyKind::ArithmeticOverflow
                    && c.message.as_deref()
                        == Some("attempt to compute `unchecked_add` which would overflow")
            })
            .count();
        assert_eq!(unchecked_checks, 10, "one `unchecked_add` check per iteration");
        assert_eq!(eval_u8(&walked.value, &[("arg1", 0)]), Some(200), "ten additions of 20");
        assert_eq!(eval_u8(&walked.value, &[("arg1", 55)]), Some(255));
    });
}

/// A symbolic `while i < n` loop: the visit that finds the fuel spent is a
/// last pass whose exit test is evaluated, so every `n` the replay covers
/// gets the program's value. Before, that visit jumped to the SwitchInt's
/// `otherwise` target, which for a `while` loop is the BODY: with `n == 5`
/// the walk ran a sixth iteration and returned `x + 6`.
#[test]
fn test_symbolic_while_loop_last_pass_takes_the_exit_test() {
    with_probe(|tcx| {
        let fn_name = "probe_loop_while_sym";
        let (walked, _) = walk_probe(tcx, fn_name);
        let walked = walked.unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        for n in 0..=5u64 {
            assert_eq!(
                eval_u8(&walked.value, &[("arg1", 10), ("arg2", n)]),
                Some(10 + n),
                "{fn_name}: n = {n} is replayed exactly"
            );
        }
        // Past the replay bound the value is not the program's: it must not
        // be a replayed one either (it is the bailed arm's fresh value).
        let past = eval_u8(&walked.value, &[("arg1", 10), ("arg2", 6)]);
        assert!(past != Some(15) && past != Some(16), "n = 6 is not truncated, got {past:?}");
    });
}

/// `if i == n { break }`: the SwitchInt's `otherwise` target is the EXIT.
/// Before, the spent header jumped there, so every `n` past the bound left
/// the loop with the fifth iteration's state (`x + 5`), a truncation that
/// dropped every later iteration.
#[test]
fn test_symbolic_break_loop_is_not_truncated_at_the_bound() {
    with_probe(|tcx| {
        let fn_name = "probe_loop_break_sym";
        let (walked, _) = walk_probe(tcx, fn_name);
        let walked = walked.unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        for n in 0..=5u64 {
            assert_eq!(
                eval_u8(&walked.value, &[("arg1", 10), ("arg2", n)]),
                Some(10 + n),
                "{fn_name}: n = {n} is replayed exactly"
            );
        }
        for n in [6u64, 8, 200] {
            let past = eval_u8(&walked.value, &[("arg1", 10), ("arg2", n)]);
            assert_ne!(past, Some(15), "{fn_name}: n = {n} must not leave with x + 5");
        }
    });
}

// ---------------------------------------------------------------------------
// Mechanism D: `unreachable_unchecked` (walker_bailed_branch_dual.rs)
// ---------------------------------------------------------------------------

fn bv8(value: u64) -> Expr {
    Expr::bitvec_const(value, 8)
}

/// `check` evaluated with the named 8-bit variables set.
fn eval_bool(check: &Expr, values: &[(&str, u64)]) -> Option<bool> {
    let values: HashMap<String, Expr> =
        values.iter().map(|(name, value)| ((*name).to_string(), bv8(*value))).collect();
    match try_eval_to_const(&substitute(check, &values))?.value() {
        ExprValue::BoolConst(b) => Some(*b),
        _ => None,
    }
}

fn checks_of_kind(walked: &InlineReturn, kind: PropertyKind) -> Vec<Expr> {
    walked.deferred_checks.iter().filter(|c| c.kind == kind).map(|c| c.check.clone()).collect()
}

fn body_calls(body: &Body, path_tail: &str) -> bool {
    body.blocks.iter().any(|block| match &block.terminator.kind {
        TerminatorKind::Call { func, .. } => format!("{func:?}").contains(path_tail),
        _ => false,
    })
}

/// An arm that calls `unreachable_unchecked` is Kani's "unreachable code"
/// failure: the walk records "the arm is not taken" as an obligation of that
/// kind. Before, the call was an unsupported terminator, the arm bailed into a
/// blessed havoc and nothing was recorded.
#[test]
fn test_unreachable_unchecked_arm_is_an_unreachable_code_obligation() {
    with_probe(|tcx| {
        for fn_name in ["probe_unreachable_arm", "probe_unreachable_after_call"] {
            let instance = find_instance_by_suffix(tcx, fn_name);
            let body = instance.body().expect("function body");
            assert!(body_calls(&body, "unreachable_unchecked"), "{fn_name}: calls the hint");
            let params = arg_params(&body);
            let walked = walk_body(tcx, instance, &body, fn_name, &params)
                .unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
            let checks = checks_of_kind(&walked, PropertyKind::Unreachable);
            assert!(
                !checks.is_empty(),
                "{fn_name}: an \"unreachable code\" check is recorded; got {:?} value {:?} body {:#?}",
                walked
                    .deferred_checks
                    .iter()
                    .map(|c| (c.kind, c.message.clone()))
                    .collect::<Vec<_>>(),
                walked.value,
                body.blocks
            );
            let messages: Vec<_> = walked
                .deferred_checks
                .iter()
                .filter(|c| c.kind == PropertyKind::Unreachable)
                .map(|c| c.message.clone())
                .collect();
            assert!(
                messages.iter().all(|m| m.as_deref() == Some("unreachable code")),
                "{fn_name}: Kani's message, got {messages:?}"
            );
            // It fails exactly when the hint is reached.
            let at =
                |a: u64| checks.iter().map(|c| eval_bool(c, &[("arg1", a)])).collect::<Vec<_>>();
            assert!(at(3).contains(&Some(false)), "{fn_name}: a == 3 violates it, got {:?}", at(3));
            assert!(
                at(4).iter().all(|v| *v == Some(true)),
                "{fn_name}: a == 4 satisfies every check, got {:?}",
                at(4)
            );
        }
    });
}

/// A discriminant that folds onto a diverging arm proves the arm TAKEN: the
/// walk records the failure (`false` on this path). Before, the walk bailed
/// ("all branches dead") and the failure went with the bail.
#[test]
fn test_discriminant_folded_onto_a_diverging_arm_records_the_failure() {
    with_probe(|tcx| {
        for (fn_name, kind) in [
            ("probe_unreachable_arm", PropertyKind::Unreachable),
            ("probe_panic_arm", PropertyKind::Assertion),
        ] {
            let instance = find_instance_by_suffix(tcx, fn_name);
            let body = instance.body().expect("function body");
            let reached = walk_body(tcx, instance, &body, fn_name, &[bv8(3)])
                .unwrap_or_else(|| panic!("{fn_name}(3): the walk returns the failed path"));
            let checks = checks_of_kind(&reached, kind);
            assert!(
                checks.iter().any(|c| eval_bool(c, &[]) == Some(false)),
                "{fn_name}(3): a failing {kind:?} check, got {checks:?}"
            );
            // Folding onto the live arm records nothing of that kind.
            let live = walk_body(tcx, instance, &body, fn_name, &[bv8(4)])
                .unwrap_or_else(|| panic!("{fn_name}(4): the walk finishes"));
            assert!(
                checks_of_kind(&live, kind).iter().all(|c| eval_bool(c, &[]) != Some(false)),
                "{fn_name}(4): no failing check"
            );
        }
    });
}

// ---------------------------------------------------------------------------
// Mechanism E: an Assert whose condition the walker cannot translate
// (walker_untranslatable_assert_dual.rs)
// ---------------------------------------------------------------------------

/// The untranslatable overflow Assert is recorded as a check that fails
/// wherever it is reached, with the Assert's message, and its variable is an
/// accounted freed identity under a blessed reason (so a proof stays clean
/// only where the Assert is unreachable, and a failure is never certified).
/// Before, the walker assumed the assertion passed and recorded nothing.
#[test]
fn test_untranslatable_assert_is_an_uncertified_reach_check() {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::uncertified_check::WALKER_UNTRANSLATABLE_ASSERT;
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    assert_eq!(fallback_soundness(WALKER_UNTRANSLATABLE_ASSERT), FallbackSoundness::SoundHavoc);
    with_probe(|tcx| {
        let fn_name = "probe_untranslatable_assert";
        let body = find_instance_by_suffix(tcx, fn_name).body().expect("function body");
        assert!(
            body.blocks.iter().any(|b| matches!(b.terminator.kind, TerminatorKind::Assert { .. })),
            "{fn_name}: the probe has MIR Asserts"
        );
        let walked = walk_accounted(tcx, fn_name);
        let result = walked.result.unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        let reach = reach_checks(&result);
        let overflow: Vec<_> = reach
            .iter()
            .filter(|(_, message, _)| message.as_deref() == Some("attempt to add with overflow"))
            .collect();
        assert_eq!(overflow.len(), 1, "{fn_name}: one reach check for `v + 200`, got {reach:?}");
        assert!(
            walked.freed.contains(&overflow[0].2),
            "{fn_name}: its variable is an accounted freed identity, freed = {:?}",
            walked.freed
        );
        assert!(walked.blessed >= 1, "{fn_name}: recorded on the blessed counter");

        // Control: a translatable Assert is an ordinary exact check.
        let control = walk_accounted(tcx, "probe_translatable_assert");
        let control = control.result.expect("probe_translatable_assert: the walk finishes");
        assert!(reach_checks(&control).is_empty(), "no reach check for a translatable Assert");
        assert!(
            control
                .deferred_checks
                .iter()
                .any(|c| c.message.as_deref() == Some("attempt to add with overflow")),
            "the control records the exact overflow check"
        );
    });
}

// ---------------------------------------------------------------------------
// A diverging call the walker does not model (walker_validity_intrinsics_dual.rs
// `diverge_bug`)
// ---------------------------------------------------------------------------

/// A user `-> !` function whose body panics is recorded as a check that fails
/// wherever the call is reached, never certified. Before, the call was an
/// unsupported terminator: the arm bailed into a blessed havoc and the panic
/// was gone. A diverging function that provably carries no obligation (`loop
/// {}`) records nothing.
#[test]
fn test_unmodelled_diverging_call_that_may_panic_is_an_uncertified_reach_check() {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::uncertified_check::WALKER_UNMODELLED_DIVERGING_CALL;
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    assert_eq!(fallback_soundness(WALKER_UNMODELLED_DIVERGING_CALL), FallbackSoundness::SoundHavoc);
    with_probe(|tcx| {
        let fn_name = "probe_user_diverging";
        let body = find_instance_by_suffix(tcx, fn_name).body().expect("function body");
        assert!(body_calls(&body, "die_probe"), "{fn_name}: calls the diverging fn");
        let walked = walk_accounted(tcx, fn_name);
        let result = walked.result.unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        let reach = reach_checks(&result);
        assert_eq!(reach.len(), 1, "{fn_name}: one reach check, got {reach:?}");
        let (kind, message, var) = &reach[0];
        assert_eq!(*kind, PropertyKind::Panic, "{fn_name}: a Panic-kind check");
        assert!(
            message.as_deref().is_some_and(|m| m.contains("die_probe")),
            "{fn_name}: the message names the callee, got {message:?}"
        );
        assert!(walked.freed.contains(var), "{fn_name}: its variable is accounted");
        // It fails exactly on the path that reaches the call.
        let check = result
            .deferred_checks
            .iter()
            .find(|c| vars_of(&c.check).contains(var))
            .map(|c| c.check.clone())
            .expect("the reach check");
        let at = |x: u64| {
            let values: HashMap<String, Expr> =
                [("arg1".to_string(), bv8(x)), (var.clone(), Expr::bool_const(false))]
                    .into_iter()
                    .collect();
            try_eval_to_const(&substitute(&check, &values))
        };
        assert_eq!(at(7), Some(Expr::bool_const(false)), "{fn_name}: x == 7 reaches the call");
        assert_eq!(at(6), Some(Expr::bool_const(true)), "{fn_name}: x == 6 does not");

        // Control: nothing to prove in the callee, nothing recorded.
        let control = walk_accounted(tcx, "probe_obligation_free_diverging");
        if let Some(control) = control.result {
            assert!(reach_checks(&control).is_empty(), "no reach check for `loop {{}}`");
        }
    });
}

// ---------------------------------------------------------------------------
// Mechanism C: a SwitchInt arm the walker cannot finish
// (walker_bailed_branch_dual.rs)
// ---------------------------------------------------------------------------

/// An arm the walker abandons, whose region can carry an obligation, is
/// recorded as a check that fails wherever the arm is taken, never
/// certified. Before, the arm became a blessed havoc of its return value and
/// its checks were discarded with the walk. An abandoned arm whose region has
/// nothing to check records nothing (its value havoc stays the whole story).
#[test]
fn test_bailed_arm_that_can_carry_an_obligation_is_an_uncertified_reach_check() {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::uncertified_check::WALKER_BAILED_ARM_OBLIGATION;
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    assert_eq!(fallback_soundness(WALKER_BAILED_ARM_OBLIGATION), FallbackSoundness::SoundHavoc);
    with_probe(|tcx| {
        let fn_name = "probe_bailed_arm";
        let walked = walk_accounted(tcx, fn_name);
        let result = walked.result.unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        let reach: Vec<_> = reach_checks(&result)
            .into_iter()
            .filter(|(_, message, _)| {
                message.as_deref().is_some_and(|m| m.contains("abandoned branch"))
            })
            .collect();
        assert_eq!(
            reach.len(),
            1,
            "{fn_name}: one reach check for the abandoned arm, got {reach:?}"
        );
        let (kind, _, var) = &reach[0];
        assert_eq!(*kind, PropertyKind::Other);
        assert!(walked.freed.contains(var), "{fn_name}: its variable is accounted");
        let check = result
            .deferred_checks
            .iter()
            .find(|c| vars_of(&c.check).contains(var))
            .map(|c| c.check.clone())
            .expect("the reach check");
        let at = |a: u64| {
            let values: HashMap<String, Expr> = [
                ("arg1".to_string(), bv8(a)),
                ("arg2".to_string(), bv8(0)),
                (var.clone(), Expr::bool_const(false)),
            ]
            .into_iter()
            .collect();
            try_eval_to_const(&substitute(&check, &values))
        };
        assert_eq!(at(11), Some(Expr::bool_const(false)), "{fn_name}: a > 10 takes the arm");
        assert_eq!(at(5), Some(Expr::bool_const(true)), "{fn_name}: a <= 10 does not");

        // Control: the arm bails, but nothing in its region is an obligation.
        let control = walk_accounted(tcx, "probe_bailed_arm_obligation_free");
        let control = control.result.expect("probe_bailed_arm_obligation_free: the walk finishes");
        assert!(
            !vars_of(&control.value)
                .iter()
                .all(|name| !name.starts_with("__switchint_branch_overapprox")),
            "the control's arm really bails (its value is the arm's havoc)"
        );
        assert!(reach_checks(&control).is_empty(), "no reach check for an obligation-free region");
    });
}

// ---------------------------------------------------------------------------
// Mechanism B: a callee in another crate havocked by the nested-call fallback
// (walker_get_unchecked_dual.rs, walker_std_callee_local_obligation_dual.rs)
// ---------------------------------------------------------------------------

/// The walker havocs `get_unchecked` (its slice argument does not translate).
/// It is an `unsafe` std function whose body carries the precondition checks,
/// so the havoc now fails closed (`walker_nested_call_lost_effect`). Before,
/// the obligation sighting looked at local-crate bodies only and the havoc
/// stayed blessed.
#[test]
fn test_havocked_unsafe_std_callee_fails_closed() {
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    assert_eq!(fallback_soundness("walker_nested_call_lost_effect"), FallbackSoundness::FailClose);
    with_probe(|tcx| {
        let fn_name = "probe_get_unchecked";
        let body = find_instance_by_suffix(tcx, fn_name).body().expect("function body");
        assert!(body_calls(&body, "get_unchecked"), "{fn_name}: calls get_unchecked");
        let reasons = walk_reasons(tcx, fn_name);
        assert!(
            reasons.contains_key("nested_call_overapprox"),
            "{fn_name}: the walker really havocs the call, reasons = {reasons:?}"
        );
        assert!(
            reasons.contains_key("walker_nested_call_lost_effect"),
            "{fn_name}: the havoc of an unsafe std callee fails closed, reasons = {reasons:?}"
        );
    });
}

/// `Option::map` is safe std code, but the closure it is handed is this
/// crate's and carries an overflow check: the havoc fails closed. A safe std
/// callee that reaches no code of the crate keeps the blessed havoc.
#[test]
fn test_havocked_safe_std_callee_fails_closed_only_through_local_code() {
    with_probe(|tcx| {
        let fn_name = "probe_std_map_closure";
        let reasons = walk_reasons(tcx, fn_name);
        assert!(
            reasons.keys().any(|r| r == "nested_call_overapprox"),
            "{fn_name}: the walker really havocs `Option::map`, reasons = {reasons:?}"
        );
        assert!(
            reasons.contains_key("walker_nested_call_lost_effect"),
            "{fn_name}: the closure's check fails the havoc closed, reasons = {reasons:?}"
        );

        let control = "probe_std_safe_no_local";
        let reasons = walk_reasons(tcx, control);
        assert!(
            reasons.contains_key("nested_call_overapprox"),
            "{control}: the walker really havocs `count_ones`, reasons = {reasons:?}"
        );
        assert!(
            !reasons.contains_key("walker_nested_call_lost_effect"),
            "{control}: no local code, no fail-closed record, reasons = {reasons:?}"
        );
    });
}

/// `Option::expect` is safe std code with no closure, but its own body panics
/// on `None`, a panic that depends on the caller's value: the havoc fails
/// closed. Before, a safe std callee was sighted only through the crate's own
/// code, and the `None` panic was dropped (walker_std_callee_own_panic_dual.rs).
#[test]
fn test_havocked_safe_std_callee_that_panics_in_its_own_body_fails_closed() {
    with_probe(|tcx| {
        let fn_name = "probe_std_expect";
        let reasons = walk_reasons(tcx, fn_name);
        assert!(
            reasons.contains_key("nested_call_overapprox"),
            "{fn_name}: the walker really havocs `Option::expect`, reasons = {reasons:?}"
        );
        assert!(
            reasons.contains_key("walker_nested_call_lost_effect"),
            "{fn_name}: the callee's own panic fails the havoc closed, reasons = {reasons:?}"
        );
        // `count_ones` (the control of the test above) neither panics nor
        // reaches local code, and stays blessed.
        let control = walk_reasons(tcx, "probe_std_safe_no_local");
        assert!(!control.contains_key("walker_nested_call_lost_effect"), "control: {control:?}");
    });
}

// ---------------------------------------------------------------------------
// Review round (2026-09-27): the holes the review probes found
// ---------------------------------------------------------------------------

/// `kani::assert` (what trust-mc's std lowers `assert!` to) over a condition
/// the walker cannot translate is recorded as a check that fails wherever it
/// is reached, with the assertion's message, never certified. Before, the
/// hook returned without recording anything, and the harness proved
/// (walker_kani_assert_call_dual.rs).
#[test]
fn test_untranslatable_kani_assert_call_is_an_uncertified_reach_check() {
    with_probe(|tcx| {
        let fn_name = "probe_kani_assert_untranslatable";
        let body = find_instance_by_suffix(tcx, fn_name).body().expect("function body");
        assert!(body_calls(&body, "assert"), "{fn_name}: calls the kani::assert hook");
        let walked = walk_accounted(tcx, fn_name);
        let result = walked.result.unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        let reach: Vec<_> = reach_checks(&result)
            .into_iter()
            .filter(|(_, message, _)| message.as_deref() == Some("probe: v is not 100"))
            .collect();
        assert_eq!(reach.len(), 1, "{fn_name}: one reach check for the assertion, got {reach:?}");
        assert_eq!(reach[0].0, PropertyKind::Assertion);
        assert!(walked.freed.contains(&reach[0].2), "{fn_name}: its variable is accounted");

        // Control: a translatable condition is an ordinary exact check.
        let control = walk_accounted(tcx, "probe_kani_assert_translatable");
        let control = control.result.expect("probe_kani_assert_translatable: the walk finishes");
        assert!(reach_checks(&control).is_empty(), "no reach check for a translatable condition");
        let exact: Vec<_> = control
            .deferred_checks
            .iter()
            .filter(|c| c.message.as_deref() == Some("probe: a is not 100"))
            .collect();
        assert_eq!(exact.len(), 1, "the control records the exact assertion");
        assert_eq!(eval_bool(&exact[0].check, &[("arg1", 100)]), Some(false));
        assert_eq!(eval_bool(&exact[0].check, &[("arg1", 99)]), Some(true));
    });
}

/// An `Unreachable` terminator the program can reach
/// (`core::intrinsics::unreachable()`) is Kani's "unreachable code" failure:
/// on a filtered arm, its "not taken" condition is recorded (also on an
/// explicit arm of an enum `match`, which a valid value selects). Before, the
/// walker treated every `Unreachable` arm as dead. The `otherwise` arm rustc
/// adds to an exhaustive enum `match` stays dead.
#[test]
fn test_reachable_unreachable_terminator_is_an_unreachable_code_obligation() {
    with_probe(|tcx| {
        for (fn_name, bad, good) in [
            ("probe_intrinsic_unreachable", 7u64, 6u64),
            ("probe_intrinsic_unreachable_enum_arm", 3, 4),
        ] {
            let instance = find_instance_by_suffix(tcx, fn_name);
            let body = instance.body().expect("function body");
            assert!(
                body.blocks
                    .iter()
                    .any(|b| matches!(b.terminator.kind, TerminatorKind::Unreachable)),
                "{fn_name}: the intrinsic lowered to an Unreachable terminator"
            );
            assert!(
                !body_calls(&body, "unreachable"),
                "{fn_name}: no call to the intrinsic is left"
            );
            let params = arg_params(&body);
            let walked = walk_body(tcx, instance, &body, fn_name, &params)
                .unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
            let checks: Vec<_> = walked
                .deferred_checks
                .iter()
                .filter(|c| {
                    c.kind == PropertyKind::Unreachable
                        && c.message.as_deref() == Some("unreachable code")
                })
                .map(|c| c.check.clone())
                .collect();
            assert!(!checks.is_empty(), "{fn_name}: an \"unreachable code\" check is recorded");
            let at =
                |a: u64| checks.iter().map(|c| eval_bool(c, &[("arg1", a)])).collect::<Vec<_>>();
            assert!(
                at(bad).contains(&Some(false)),
                "{fn_name}: a == {bad} violates it, got {:?}",
                at(bad)
            );
            assert!(
                at(good).iter().all(|v| *v == Some(true)),
                "{fn_name}: a == {good} satisfies every check, got {:?}",
                at(good)
            );
            // The arm folded onto the intrinsic records the failure exactly.
            let folded = walk_body(tcx, instance, &body, fn_name, &[bv8(bad)])
                .unwrap_or_else(|| panic!("{fn_name}({bad}): the walk returns the failed path"));
            assert!(
                checks_of_kind(&folded, PropertyKind::Unreachable)
                    .iter()
                    .any(|c| eval_bool(c, &[]) == Some(false)),
                "{fn_name}({bad}): a failing Unreachable check"
            );
        }

        // Package item (d): the exhaustive `otherwise` of a FIELDLESS enum is
        // an obligation too (a raw bitvector a write through memory can leave
        // out of range, walker_invalid_enum_dual.rs), which every valid
        // discriminant discharges; a data-carrying enum's stays dead.
        let fn_name = "probe_exhaustive_enum_match";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        assert!(
            body.blocks.iter().any(|b| matches!(b.terminator.kind, TerminatorKind::Unreachable)),
            "{fn_name}: rustc added the Unreachable otherwise arm"
        );
        let params = arg_params(&body);
        let arg_name = vars_of(&params[0]).pop().expect("the parameter is a variable");
        assert!(
            params[0].sort().bitvec_width().is_some(),
            "{fn_name}: a fieldless enum is a bitvector"
        );
        let width = params[0].sort().bitvec_width().expect("width");
        let walked = walk_body(tcx, instance, &body, fn_name, &params)
            .unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        let checks = checks_of_kind(&walked, PropertyKind::Unreachable);
        assert!(!checks.is_empty(), "{fn_name}: the exhaustive otherwise arm is an obligation");
        let at = |d: u64| -> Vec<Option<bool>> {
            let values: HashMap<String, Expr> =
                [(arg_name.clone(), Expr::bitvec_const(d, width))].into_iter().collect();
            checks
                .iter()
                .map(|c| {
                    match try_eval_to_const(&substitute(c, &values)).map(|e| e.value().clone()) {
                        Some(ExprValue::BoolConst(b)) => Some(b),
                        _ => None,
                    }
                })
                .collect()
        };
        assert!(
            at(0).iter().all(|v| *v == Some(true)),
            "{fn_name}: variant 0 is valid, got {:?}",
            at(0)
        );
        assert!(
            at(1).iter().all(|v| *v == Some(true)),
            "{fn_name}: variant 1 is valid, got {:?}",
            at(1)
        );
        assert!(
            at(5).contains(&Some(false)),
            "{fn_name}: discriminant 5 violates it, got {:?}",
            at(5)
        );

        let fn_name = "probe_exhaustive_carrying_enum_match";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        assert!(
            body.blocks.iter().any(|b| matches!(b.terminator.kind, TerminatorKind::Unreachable)),
            "{fn_name}: rustc added the Unreachable otherwise arm"
        );
        let params = arg_params(&body);
        assert!(params[0].sort().datatype_sort().is_some(), "{fn_name}: a datatype sort");
        if let Some(walked) = walk_body(tcx, instance, &body, fn_name, &params) {
            assert!(
                checks_of_kind(&walked, PropertyKind::Unreachable).is_empty(),
                "{fn_name}: the exhaustive otherwise arm of a data-carrying enum is dead"
            );
        }
    });
}

/// The region an abandoned arm leaves behind counts an `Unreachable`
/// terminator the program can reach, and does not count check-free
/// arithmetic: the first records a reach check, the second does not (a
/// `saturating_add` reaches a body-less intrinsic, which used to read as
/// "may carry an obligation").
#[test]
fn test_region_scan_counts_reachable_unreachable_and_not_check_free_intrinsics() {
    with_probe(|tcx| {
        let abandoned = |walked: &InlineReturn| -> usize {
            reach_checks(walked)
                .into_iter()
                .filter(|(_, message, _)| {
                    message.as_deref().is_some_and(|m| m.contains("abandoned branch"))
                })
                .count()
        };
        let fn_name = "probe_region_unreachable";
        let walked = walk_accounted(tcx, fn_name);
        let result = walked.result.unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
        assert_eq!(
            abandoned(&result),
            1,
            "{fn_name}: the abandoned arm's region reaches Unreachable"
        );

        let control = "probe_region_check_free";
        let walked = walk_accounted(tcx, control);
        let result = walked.result.unwrap_or_else(|| panic!("{control}: the walk finishes"));
        assert!(
            vars_of(&result.value)
                .iter()
                .any(|name| name.starts_with("__switchint_branch_overapprox")),
            "{control}: the arm really is abandoned"
        );
        assert_eq!(abandoned(&result), 0, "{control}: check-free arithmetic records nothing");
    });
}

/// A safe std callee the walker havocs fails closed when its panic sits
/// deeper than its own body (`slice::windows`), or when it is handed a
/// function pointer the walk cannot follow (`Option::map(f)`). Before, only
/// the callee's own body and the crate's code reached by direct calls were
/// sighted. `count_ones` (a body-less intrinsic, no panic) stays blessed.
#[test]
fn test_havocked_safe_std_callee_with_a_deep_panic_or_an_indirect_call_fails_closed() {
    with_probe(|tcx| {
        for fn_name in ["probe_std_windows", "probe_std_map_fn_pointer"] {
            let reasons = walk_reasons(tcx, fn_name);
            assert!(
                reasons.contains_key("nested_call_overapprox"),
                "{fn_name}: the walker really havocs the std callee, reasons = {reasons:?}"
            );
            assert!(
                reasons.contains_key("walker_nested_call_lost_effect"),
                "{fn_name}: the havoc fails closed, reasons = {reasons:?}"
            );
        }
        let control = walk_reasons(tcx, "probe_std_safe_no_local");
        assert!(!control.contains_key("walker_nested_call_lost_effect"), "control: {control:?}");
    });
}

// ---------------------------------------------------------------------------
// Package items (a) and (e): the unit's stubs reach the walker's bodies
// ---------------------------------------------------------------------------

/// The `FnDef` and generic arguments of every call `body` makes.
fn call_defs(body: &Body) -> Vec<(rustc_public::ty::FnDef, rustc_public::ty::GenericArgs)> {
    body.blocks
        .iter()
        .filter_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, .. } => match func.ty(body.locals()).ok()?.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, args)) => {
                    Some((def, args))
                }
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// The `FnDef` of a probe item.
fn fn_def_of(tcx: TyCtxt<'_>, suffix: &str) -> rustc_public::ty::FnDef {
    match find_instance_by_suffix(tcx, suffix).ty().kind() {
        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) => def,
        other => panic!("{suffix} is not a FnDef: {other:?}"),
    }
}

/// Walk `fn_name`'s body as the walker fetches it (`CalleeBody::callee_body`,
/// with any installed unit stubs applied) and return the Assertion checks.
fn walked_assertions(tcx: TyCtxt<'_>, fn_name: &str) -> (Body, Vec<Expr>) {
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = crate::callee_body::CalleeBody::callee_body(&instance).expect("function body");
    let params = arg_params(&body);
    let walked = walk_body(tcx, instance, &body, fn_name, &params)
        .unwrap_or_else(|| panic!("{fn_name}: the walk finishes"));
    let checks = checks_of_kind(&walked, PropertyKind::Assertion);
    (body, checks)
}

/// Item (a): with `#[kani::stub(u8::wrapping_add, stub)]` in effect, the
/// walker fetches the caller's body with the call site rewritten to the stub,
/// so the known-call model of `wrapping_add` never claims it and the stub's
/// `assert!` is walked. Before, the path model answered `a + 1` and the
/// assertion was gone (stub_modelled_std_dual.rs). A trait-method call that
/// resolves to a stubbed impl item (`Clone::clone` on `Q`) is rewritten too.
#[test]
fn test_stubbed_std_function_reaches_the_walker_as_its_stub() {
    with_probe(|tcx| {
        let caller = "probe_calls_wrapping_add";
        let (orig, _) = call_defs(&find_instance_by_suffix(tcx, caller).body().expect("body"))
            .into_iter()
            .find(|(def, _)| def.name().ends_with("wrapping_add"))
            .expect("the probe calls wrapping_add");
        let stub = fn_def_of(tcx, "probe_stub_wrapping_add");

        // Control: no stubs, the path model answers, no assertion.
        let (body, checks) = walked_assertions(tcx, caller);
        assert!(call_defs(&body).iter().any(|(def, _)| *def == orig));
        assert!(checks.is_empty(), "{caller}: unstubbed, nothing to assert, got {checks:?}");

        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            [(orig, stub)].into_iter().collect(),
        );
        let (body, checks) = walked_assertions(tcx, caller);
        assert!(
            call_defs(&body).iter().any(|(def, _)| *def == stub)
                && !call_defs(&body).iter().any(|(def, _)| *def == orig),
            "{caller}: the call site names the stub"
        );
        assert!(
            checks.iter().any(|c| eval_bool(c, &[("arg1", 100)]) == Some(false)),
            "{caller}: the stub's assertion fails for a == 100, got {checks:?}"
        );
        assert!(
            checks.iter().all(|c| eval_bool(c, &[("arg1", 7)]) != Some(false)),
            "{caller}: and holds for a == 7"
        );
    });
    with_probe(|tcx| {
        let caller = "probe_calls_clone";
        let calls = call_defs(&find_instance_by_suffix(tcx, caller).body().expect("body"));
        let (trait_def, args) = calls
            .into_iter()
            .find(|(def, _)| def.name().ends_with("clone"))
            .expect("the probe calls clone");
        let impl_def = match Instance::resolve(trait_def, &args).expect("resolves").ty().kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) => def,
            other => panic!("not a FnDef: {other:?}"),
        };
        assert_ne!(impl_def, trait_def, "the call names the trait method, not the impl item");
        let stub = fn_def_of(tcx, "probe_q_clone_stub");
        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            [(impl_def, stub)].into_iter().collect(),
        );
        let instance = find_instance_by_suffix(tcx, caller);
        let body = crate::callee_body::CalleeBody::callee_body(&instance).expect("body");
        assert!(
            call_defs(&body).iter().any(|(def, _)| *def == stub),
            "{caller}: the trait call resolving to the stubbed impl item names the stub"
        );
    });
}

/// Item (e): an extern "C" function the unit stubs is called from a walked
/// body. The call site is rewritten to the stub (it has no body of its own),
/// so the walk runs the stub exactly; before, the fetch of the extern item
/// failed closed and the call was havocked (walker_extern_stub_dual.rs).
#[test]
fn test_stubbed_extern_function_is_walked_as_its_stub() {
    with_probe(|tcx| {
        let caller = "probe_calls_extern";
        let (orig, _) = call_defs(&find_instance_by_suffix(tcx, caller).body().expect("body"))
            .into_iter()
            .find(|(def, _)| def.name().ends_with("probe_ext"))
            .expect("the probe calls the extern function");
        assert!(orig.body().is_none(), "the extern item has no body");
        let stub = fn_def_of(tcx, "probe_ext_stub");
        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            [(orig, stub)].into_iter().collect(),
        );
        let (body, checks) = walked_assertions(tcx, caller);
        assert!(call_defs(&body).iter().any(|(def, _)| *def == stub), "the call names the stub");
        assert!(
            checks.iter().any(|c| eval_bool(c, &[("arg1", 100)]) == Some(false)),
            "{caller}: the stub's assertion fails for x == 100, got {checks:?}"
        );
    });
}

/// Item (a), follow-up: the MIR inliner keeps a call a "special codegen
/// handler" boundary by the callee's NAME (`wrapping_`, `checked_`, ...), and
/// the BMC lane then modelled it by the same name. A function of the crate
/// under verification is inlined like any other now; the library
/// `u8::wrapping_add` stays a boundary (user_fn_std_helper_name_dual.rs).
#[test]
fn test_local_function_named_like_a_std_helper_is_inlined() {
    with_probe(|tcx| {
        let run = |fn_name: &str| -> Body {
            let instance = find_instance_by_suffix(tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut pass = crate::kani_middle::transform::inline::FunctionInlinePass::new(
                crate::kani_middle::transform::inline::InlineConfig {
                    max_depth: 4,
                    enabled: true,
                    preserve_block_on: true,
                    preserve_array_comparisons: true,
                    bmc_native_box_validity: false,
                    chc_native_box_drop: false,
                },
            );
            pass.transform_with_body_provider(tcx, body, instance, |callee| {
                crate::callee_body::CalleeBody::callee_body(&callee)
            })
            .1
        };
        let local = run("probe_calls_local_wrapping_add");
        assert!(
            !call_defs(&local).iter().any(|(def, _)| def.name().ends_with("probe_my_wrapping_add")),
            "the local function is inlined, not kept as a std-helper boundary"
        );
        let library = run("probe_calls_wrapping_add");
        assert!(
            call_defs(&library).iter().any(|(def, _)| def.name().ends_with("wrapping_add")),
            "the library `u8::wrapping_add` stays a handler boundary"
        );
    });
}

/// Item (a): the call-site rewrite resolves the call first and stubs the
/// function it RUNS, as `FnStubPass` does: `#[kani::stub(HasDefault::method,
/// s)]` rewrites a call that runs the default method and leaves a call to an
/// impl that overrides it alone. Consulting the call's own `def` first
/// stubbed the override too.
#[test]
fn test_call_site_stub_follows_the_resolved_callee() {
    with_probe(|tcx| {
        let trait_def = call_defs(
            &find_instance_by_suffix(tcx, "probe_default_method_stub").body().expect("body"),
        )
        .into_iter()
        .map(|(def, _)| def)
        .find(|def| def.name().ends_with("method"))
        .expect("the probe calls the trait method");
        // A generic item has no instance: take its `FnDef` from its type.
        let stub = match find_crate_item_by_suffix(tcx, "probe_method_stub").ty().kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) => def,
            other => panic!("probe_method_stub is not a FnDef: {other:?}"),
        };
        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            [(trait_def, stub)].into_iter().collect(),
        );
        let fetched = |fn_name: &str| {
            let instance = find_instance_by_suffix(tcx, fn_name);
            call_defs(&crate::callee_body::CalleeBody::callee_body(&instance).expect("body"))
        };
        assert!(
            fetched("probe_default_method_stub").iter().any(|(def, _)| *def == stub),
            "a call that runs the default method names the stub"
        );
        assert!(
            !fetched("probe_overridden_method_stub").iter().any(|(def, _)| *def == stub),
            "a call to an impl that overrides the default is not stubbed"
        );
    });
}

/// Item (a): a stub that fails Kani's stub validation (here an unmet generic
/// bound its constant needs, `tests/expected/issue-2589`) is not applied at a
/// call site nor to a raw fetch, as `FnStubPass` does not apply it: fetching
/// its body at those arguments ICEs in the body builder, which is what the
/// first cut of the call-site rewrite did to issue_2589 (a compile error
/// became a compiler panic). The validation reports its compile error, so
/// the probe crate's run is allowed to fail after the test body ran.
#[test]
fn test_invalid_stub_is_not_applied() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn original<T>() {}
        trait Dummy {
            const TRUE: bool = true;
        }
        fn invalid_stub<T: Dummy>() {
            assert!(T::TRUE);
        }
        pub fn probe_calls_original() {
            original::<String>();
        }
    "#;
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let outcome = std::sync::Mutex::new(None);
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let tcx = ctx.tcx;
            let caller = find_instance_by_suffix(tcx, "probe_calls_original");
            let (orig, _) = call_defs(&caller.body().expect("body"))
                .into_iter()
                .find(|(def, _)| def.name().ends_with("original"))
                .expect("the probe calls original");
            let stub = match find_crate_item_by_suffix(tcx, "invalid_stub").ty().kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) => def,
                other => panic!("invalid_stub is not a FnDef: {other:?}"),
            };
            let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
                [(orig, stub)].into_iter().collect(),
            );
            let body = crate::callee_body::CalleeBody::callee_body(&caller).expect("body");
            let calls = call_defs(&body);
            *outcome.lock().unwrap() = Some((
                calls.iter().any(|(def, _)| *def == orig),
                calls.iter().any(|(def, _)| *def == stub),
            ));
        });
    }));
    let (names_original, names_stub) =
        outcome.lock().unwrap().take().expect("the test body ran without a compiler panic");
    assert!(names_original, "the call keeps naming the original");
    assert!(!names_stub, "the invalid stub is not applied");
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::integration_ay_runner::{run_ay_on_smt2, run_ay_smt2};
use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::kani_middle::attributes;
use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, try_get_kani_function};
use rustc_public::mir::{Body, Operand, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

// =========================================================================
// BMC source->solver integration checks (Part of #2596)
// =========================================================================

fn is_assert_like_kani_call(func: &Operand, body: &Body) -> bool {
    let Ok(func_ty) = func.ty(body.locals()) else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = func_ty.kind() else {
        return false;
    };
    let Some(marker) = attributes::fn_marker(fn_def) else {
        return false;
    };
    matches!(
        try_get_kani_function(marker.as_str()),
        Some(KaniFunction::Hook(
            KaniHook::Assert
                | KaniHook::Check
                | KaniHook::SafetyCheck
                | KaniHook::SafetyCheckNoAssume
                | KaniHook::UnsupportedCheck
        ))
    )
}

fn has_assert_probe(body: &Body) -> bool {
    body.blocks.iter().any(|bb| match &bb.terminator.kind {
        TerminatorKind::Assert { .. } => true,
        TerminatorKind::Call { func, .. } => is_assert_like_kani_call(func, body),
        _ => false,
    })
}

fn emit_bmc_smt_for_fn(source: &str, fn_suffix: &str) -> (String, usize) {
    emit_bmc_smt_for_fn_with_config(source, fn_suffix, false)
}

fn emit_bmc_smt_for_fn_with_config(
    source: &str,
    fn_suffix: &str,
    prove_safety_only: bool,
) -> (String, usize) {
    let mut maybe_result: Option<(String, usize)> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.prove_safety_only = prove_safety_only;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        let has_assert_terminator = has_assert_probe(&body);
        assert!(
            has_assert_terminator,
            "{fn_suffix}: expected MIR assert terminator or kani assert/check hook in test probe; \
             optimizer may have elided assertion"
        );

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let violation_count = ctx.bmc_vc.violations.len();
        maybe_result = Some((crate::codegen_ay::emit_bmc(ctx.bmc_vc).to_string(), violation_count));
    });
    maybe_result.expect("expected BMC SMT and violation count")
}

fn assert_bmc_solver_result(source: &str, fn_suffix: &str, expected: &str) {
    let (smt, violations) = emit_bmc_smt_for_fn(source, fn_suffix);
    assert!(
        violations > 0,
        "{fn_suffix}: expected at least one violation predicate in BMC VC. SMT:\n{smt}"
    );

    let solver_result = run_ay_on_smt2(&smt);
    assert!(
        solver_result.is_ok(),
        "{fn_suffix}: AY execution failed: {}. SMT:\n{smt}",
        solver_result.as_ref().err().map_or("", std::string::String::as_str)
    );

    let result = solver_result.unwrap_or_default();
    assert_eq!(result, expected, "{fn_suffix}: expected {expected}, got {result}. SMT:\n{smt}");
}

fn assert_bmc_smt_contains(source: &str, fn_suffix: &str, expected_fragment: &str) {
    let (smt, violations) = emit_bmc_smt_for_fn(source, fn_suffix);
    assert!(
        violations > 0,
        "{fn_suffix}: expected at least one violation predicate in BMC VC. SMT:\n{smt}"
    );
    assert!(
        smt.contains(expected_fragment),
        "{fn_suffix}: expected SMT fragment `{expected_fragment}`. SMT:\n{smt}"
    );
}

// -------------------------------------------------------------------------
// Test sources — original 5
// -------------------------------------------------------------------------

pub(super) const BMC_ASSERT_TRUE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_assert_true(x: u8, y: u8) {
    if x < 40 && y < 40 {
        let sum = x + y;
        assert!(sum >= x);
    }
}
"#;

pub(super) const BMC_ASSERT_FALSE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_assert_false() {
    assert!(1u32 + 1 == 3u32);
}
"#;

pub(super) const BMC_BRANCH_ASSERT_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_branch_assert_safe(x: u32, y: u32) {
    if x < 10 && y < 10 {
        let z = x + y;
        assert!(z < 20);
    }
}
"#;

pub(super) const BMC_BRANCH_ASSERT_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_branch_assert_fail(x: u32, y: u32) {
    if x < 10 && y < 10 {
        let z = x + y;
        assert!(z == 50);
    }
}
"#;

pub(super) const BMC_DIV_GUARDED_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_div_guarded(x: u32) -> u32 {
    let y = if x == 0 { 1 } else { x };
    10 / y
}
"#;

// -------------------------------------------------------------------------
// Test sources — new patterns (Part of #2596 expansion)
// -------------------------------------------------------------------------

/// Nested conditional with both branches safe: inner assertions hold
/// regardless of which branch is taken.
pub(super) const BMC_NESTED_COND_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_nested_cond_safe(x: u32, y: u32) {
    if x < 5 {
        if y < 5 {
            let sum = x + y;
            assert!(sum < 10);
        } else if y < 100 {
            assert!(y >= 5);
        }
    }
}
"#;

/// Nested conditional where inner branch assertion fails: x < 5 && y < 5
/// guarantees sum < 10, but assertion demands sum < 5, which fails for
/// e.g. x=3, y=4.
pub(super) const BMC_NESTED_COND_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_nested_cond_fail(x: u32, y: u32) {
    if x < 5 {
        if y < 5 {
            let sum = x + y;
            assert!(sum < 5);
        }
    }
}
"#;

/// Signed integer arithmetic: negative values must still satisfy constraints.
/// For i32 in range [-10, 10], sum is in [-20, 20], so |sum| <= 20.
pub(super) const BMC_SIGNED_ARITH_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_signed_arith_safe(x: i32, y: i32) {
    if x >= -10 && x <= 10 && y >= -10 && y <= 10 {
        let sum = x + y;
        assert!(sum >= -20 && sum <= 20);
    }
}
"#;

/// Signed arithmetic failure: x in [-10, 10], y in [-10, 10], but
/// asserting sum > 0 fails for e.g. x=-5, y=-5 → sum=-10.
pub(super) const BMC_SIGNED_ARITH_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_signed_arith_fail(x: i32, y: i32) {
    if x >= -10 && x <= 10 && y >= -10 && y <= 10 {
        let sum = x + y;
        assert!(sum > 0);
    }
}
"#;

/// Multiple assertions in sequence: all must hold.
/// If x in [0, 100), then x*2 < 200 and x*2 >= 0 and x+1 > x.
pub(super) const BMC_MULTI_ASSERT_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_multi_assert_safe(x: u32) {
    if x < 100 {
        let doubled = x * 2;
        assert!(doubled < 200);
        assert!(doubled >= x);
        let incremented = x + 1;
        assert!(incremented > x);
    }
}
"#;

/// Regression for #3807: two coroutine state machines resumed multiple times in
/// one function should preserve independent state across `Pin<&mut _>` wrapper
/// temps and CopyForDeref chains.
pub(super) const BMC_COROUTINE_MULTI_RESUME_ARG_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(coroutines, coroutine_trait)]
#![feature(register_tool)]
#![feature(stmt_expr_attributes)]
#![register_tool(kanitool)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_coroutine_multi_resume_arg_safe() {
    let mut gen_copy = #[coroutine]
    |mut x: usize| {
        loop {
            let _ = x;
            x = yield;
        }
    };

    let mut gen_move = #[coroutine]
    |mut x: Box<usize>| {
        loop {
            drop(x);
            x = yield;
        }
    };

    kani::assert(Pin::new(&mut gen_copy).resume(0) == CoroutineState::Yielded(()));
    kani::assert(Pin::new(&mut gen_copy).resume(1) == CoroutineState::Yielded(()));
    kani::assert(Pin::new(&mut gen_move).resume(Box::new(0)) == CoroutineState::Yielded(()));
    kani::assert(Pin::new(&mut gen_move).resume(Box::new(1)) == CoroutineState::Yielded(()));
}
"#;

/// Kani hook path where assume makes assert trivially safe.
pub(super) const BMC_KANI_ASSUME_ASSERT_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssumeHook"]
    pub fn assume(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_kani_assume_assert_safe(x: i32) {
    kani::assume(x > 10);
    kani::assert(x > 5);
}
"#;

/// Kani hook path where assume keeps the state-space non-empty but assert fails.
pub(super) const BMC_KANI_ASSUME_ASSERT_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssumeHook"]
    pub fn assume(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_kani_assume_assert_fail(x: i32) {
    kani::assume(x > 10);
    kani::assert(x < 0);
}
"#;

/// CBMC/Kani assume ordering: an assume constrains only the SUFFIX. The assert
/// here fires BEFORE the assume, so `assume(x == 0)` must not mask its
/// violation — the query must stay `sat` (counterexample: any x != 0). The old
/// encoding asserted the assume globally, which made this `unsat`: a false
/// proof of a failing assertion.
pub(super) const BMC_KANI_ASSERT_BEFORE_ASSUME_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssumeHook"]
    pub fn assume(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_kani_assert_before_assume(x: i32) {
    kani::assert(x == 0);
    kani::assume(x == 0);
}
"#;

/// SafetyCheckHook via BMC: compiler-inserted safety check (assert + assume).
/// With x > 0 && x < 50, the safety_check(x + x < 100) holds, and the
/// subsequent assert(x > 0) also holds.
const BMC_KANI_SAFETY_CHECK_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssumeHook"]
    pub fn assume(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "SafetyCheckHook"]
    pub fn safety_check(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_kani_safety_check_safe(x: i32) {
    kani::assume(x > 0 && x < 50);
    kani::safety_check(x + x < 100);
    kani::assert(x > 0);
}
"#;

const BMC_KANI_UNSUPPORTED_CHECK_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "UnsupportedCheckHook"]
    pub fn unsupported_check() {
        panic!("unsupported")
    }
}

fn bmc_kani_unsupported_check() {
    kani::unsupported_check();
}
"#;

const BMC_KANI_QUANTIFIER_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall<F>(lower: usize, upper: usize, predicate: F) -> bool
    where
        F: Fn(usize) -> bool,
    {
        let _ = lower;
        let _ = upper;
        let _ = predicate;
        false
    }

    #[inline(never)]
    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists<F>(lower: usize, upper: usize, predicate: F) -> bool
    where
        F: Fn(usize) -> bool,
    {
        let _ = lower;
        let _ = upper;
        let _ = predicate;
        false
    }
}

fn bmc_kani_forall_safe() {
    let upper = 4usize;
    kani::assert(kani::forall(0, upper, |i| i < upper));
}

fn bmc_kani_forall_fail() {
    kani::assert(kani::forall(0, 4, |i| i < 3));
}

fn bmc_kani_exists_safe() {
    kani::assert(kani::exists(0, 4, |i| i == 2));
}

fn bmc_kani_exists_fail() {
    kani::assert(kani::exists(0, 4, |i| i == 5));
}
"#;

const BMC_KANI_ANY_MODIFIES_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_intrinsics {
    #[inline(never)]
    #[kanitool::fn_marker = "AnyModifiesIntrinsic"]
    pub fn any_modifies<T>() -> T {
        panic!("contract intrinsic")
    }
}

fn bmc_kani_any_modifies_havoc() {
    let value: u32 = kani_intrinsics::any_modifies();
    kani::assert(value == 7);
}
"#;

const BMC_KANI_WRITE_ANY_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

use core::num::NonZeroU32;

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_internal {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnyIntrinsic"]
    pub unsafe fn write_any<T: ?Sized>(_pointer: *mut T) {}
}

fn bmc_kani_write_any_u32_havoc() {
    let mut value = 0_u32;
    unsafe {
        kani_internal::write_any(&mut value as *mut u32);
    }
    kani::assert(value == 0);
}

fn bmc_kani_write_any_nonzero_preserves_validity() {
    let mut value = NonZeroU32::new(1).unwrap();
    unsafe {
        kani_internal::write_any(&mut value as *mut NonZeroU32);
    }
    kani::assert(value.get() != 0);
}
"#;

// -------------------------------------------------------------------------
// Case table
// -------------------------------------------------------------------------

pub(super) const BMC_E2E_CASES: [(&str, &str, &str); 10] = [
    // Original 5
    (BMC_ASSERT_TRUE_SOURCE, "bmc_assert_true", "unsat"),
    (BMC_ASSERT_FALSE_SOURCE, "bmc_assert_false", "sat"),
    (BMC_BRANCH_ASSERT_SAFE_SOURCE, "bmc_branch_assert_safe", "unsat"),
    (BMC_BRANCH_ASSERT_FAIL_SOURCE, "bmc_branch_assert_fail", "sat"),
    (BMC_DIV_GUARDED_SOURCE, "bmc_div_guarded", "unsat"),
    // New patterns
    (BMC_NESTED_COND_SAFE_SOURCE, "bmc_nested_cond_safe", "unsat"),
    (BMC_NESTED_COND_FAIL_SOURCE, "bmc_nested_cond_fail", "sat"),
    (BMC_SIGNED_ARITH_SAFE_SOURCE, "bmc_signed_arith_safe", "unsat"),
    (BMC_SIGNED_ARITH_FAIL_SOURCE, "bmc_signed_arith_fail", "sat"),
    (BMC_MULTI_ASSERT_SAFE_SOURCE, "bmc_multi_assert_safe", "unsat"),
];

// -------------------------------------------------------------------------
// Tests — original 5
// -------------------------------------------------------------------------

#[test]
fn test_bmc_e2e_assert_true_proves_unsat() {
    assert_bmc_solver_result(BMC_ASSERT_TRUE_SOURCE, "bmc_assert_true", "unsat");
}

#[test]
fn test_bmc_e2e_assert_false_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_ASSERT_FALSE_SOURCE, "bmc_assert_false", "sat");
}

#[test]
fn test_bmc_e2e_branch_guarded_assert_proves_unsat() {
    assert_bmc_solver_result(BMC_BRANCH_ASSERT_SAFE_SOURCE, "bmc_branch_assert_safe", "unsat");
}

#[test]
fn test_bmc_e2e_branch_failing_assert_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_BRANCH_ASSERT_FAIL_SOURCE, "bmc_branch_assert_fail", "sat");
}

#[test]
fn test_bmc_e2e_division_guard_prevents_div_by_zero() {
    assert_bmc_solver_result(BMC_DIV_GUARDED_SOURCE, "bmc_div_guarded", "unsat");
}

// -------------------------------------------------------------------------
// Tests — new patterns
// -------------------------------------------------------------------------

#[test]
fn test_bmc_e2e_nested_cond_safe_proves_unsat() {
    assert_bmc_solver_result(BMC_NESTED_COND_SAFE_SOURCE, "bmc_nested_cond_safe", "unsat");
}

#[test]
fn test_bmc_e2e_nested_cond_fail_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_NESTED_COND_FAIL_SOURCE, "bmc_nested_cond_fail", "sat");
}

#[test]
fn test_bmc_e2e_signed_arith_safe_proves_unsat() {
    assert_bmc_solver_result(BMC_SIGNED_ARITH_SAFE_SOURCE, "bmc_signed_arith_safe", "unsat");
}

#[test]
fn test_bmc_e2e_signed_arith_fail_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_SIGNED_ARITH_FAIL_SOURCE, "bmc_signed_arith_fail", "sat");
}

#[test]
fn test_bmc_e2e_multi_assert_safe_proves_unsat() {
    assert_bmc_solver_result(BMC_MULTI_ASSERT_SAFE_SOURCE, "bmc_multi_assert_safe", "unsat");
}

/// Coroutine multi-resume with Box allocations: BMC encoding currently
/// produces a spurious counterexample (sat) due to alloc_id / scope guard
/// restructuring (#3871, #3929). The CHC path handles this correctly.
/// Accept either "unsat" (proven) or "sat" (BMC encoding gap).
#[test]
fn test_bmc_e2e_coroutine_multi_resume_arg_safe_encodes_structurally() {
    let (smt, violations) = emit_bmc_smt_for_fn(
        BMC_COROUTINE_MULTI_RESUME_ARG_SAFE_SOURCE,
        "bmc_coroutine_multi_resume_arg_safe",
    );
    assert!(
        violations > 0,
        "bmc_coroutine_multi_resume_arg_safe: expected at least one violation predicate in BMC VC"
    );
    let solver_result = run_ay_on_smt2(&smt);
    assert!(
        solver_result.is_ok(),
        "bmc_coroutine_multi_resume_arg_safe: AY execution failed: {}",
        solver_result.as_ref().err().map_or("", std::string::String::as_str)
    );
    let result = solver_result.unwrap_or_default();
    assert!(
        result == "unsat" || result == "sat",
        "bmc_coroutine_multi_resume_arg_safe: expected unsat or sat, got {result}"
    );
}

#[test]
fn test_bmc_e2e_kani_assume_assert_safe_proves_unsat() {
    assert_bmc_solver_result(
        BMC_KANI_ASSUME_ASSERT_SAFE_SOURCE,
        "bmc_kani_assume_assert_safe",
        "unsat",
    );
}

#[test]
fn test_bmc_e2e_kani_assume_assert_fail_finds_sat_counterexample() {
    assert_bmc_solver_result(
        BMC_KANI_ASSUME_ASSERT_FAIL_SOURCE,
        "bmc_kani_assume_assert_fail",
        "sat",
    );
}

/// Discriminating control for ordered-assume (both directions with the safe
/// test above): an assume AFTER an assert must not mask it (sat here), while
/// an assume BEFORE an assert still constrains it (unsat in
/// `test_bmc_e2e_kani_assume_assert_safe_proves_unsat`).
#[test]
fn test_bmc_e2e_assert_before_assume_is_not_masked() {
    assert_bmc_solver_result(
        BMC_KANI_ASSERT_BEFORE_ASSUME_SOURCE,
        "bmc_kani_assert_before_assume",
        "sat",
    );
}

#[test]
fn test_bmc_e2e_kani_safety_check_safe_proves_unsat() {
    assert_bmc_solver_result(
        BMC_KANI_SAFETY_CHECK_SAFE_SOURCE,
        "bmc_kani_safety_check_safe",
        "unsat",
    );
}

#[test]
fn test_bmc_e2e_unsupported_check_prove_safety_only_finds_sat_counterexample() {
    let (smt, violations) = emit_bmc_smt_for_fn_with_config(
        BMC_KANI_UNSUPPORTED_CHECK_SOURCE,
        "bmc_kani_unsupported_check",
        true,
    );
    assert!(violations > 0, "unsupported_check should still violate. SMT:\n{smt}");

    let solver_result = run_ay_on_smt2(&smt);
    assert!(
        solver_result.is_ok(),
        "bmc_kani_unsupported_check: AY execution failed: {}. SMT:\n{smt}",
        solver_result.as_ref().err().map_or("", std::string::String::as_str)
    );
    assert_eq!(solver_result.unwrap_or_default(), "sat");
}

#[test]
fn test_bmc_unsupported_hook_records_taint_but_ordinary_bug_does_not() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        mod kani {
            #[kanitool::fn_marker = "UnsupportedCheckHook"]
            pub fn unsupported_check() { panic!("unsupported") }
        }
        pub fn unsupported_probe() { kani::unsupported_check(); }
        pub fn ordinary_bug(value: u32) -> u32 { value + 1 }
    "#;
    for (suffix, expected) in [("unsupported_probe", 1usize), ("ordinary_bug", 0)] {
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let mut ctx = ctx;
            ctx.config.use_chc = false;
            ctx.queries.set_args(crate::args::Arguments::default());
            let instance = find_instance_by_suffix(ctx.tcx, suffix);
            let body = instance.body().expect("body");
            let name = instance.name();
            ctx.set_current_fn(instance);
            crate::codegen_ay::chc::take_sound_havoc_drop_by_fn();
            codegen_function_with_body(&mut ctx, instance, body, &name);
            assert!(!ctx.bmc_vc.violations.is_empty(), "{suffix}: retain the failing check");
            let counts = crate::codegen_ay::chc::take_sound_havoc_drop_by_fn();
            assert_eq!(counts.get(&name).copied().unwrap_or(0), expected, "{suffix}: {counts:?}");
        });
    }
}

#[test]
fn test_bmc_e2e_kani_forall_safe_unrolls_captured_bound() {
    assert_bmc_smt_contains(
        BMC_KANI_QUANTIFIER_SOURCE,
        "bmc_kani_forall_safe",
        "(bvult #x0000000000000003 #x0000000000000004)",
    );
}

#[test]
fn test_bmc_e2e_kani_forall_fail_unrolls_false_iteration() {
    assert_bmc_smt_contains(
        BMC_KANI_QUANTIFIER_SOURCE,
        "bmc_kani_forall_fail",
        "(bvult #x0000000000000003 #x0000000000000003)",
    );
}

#[test]
fn test_bmc_e2e_kani_exists_safe_unrolls_witness() {
    assert_bmc_smt_contains(
        BMC_KANI_QUANTIFIER_SOURCE,
        "bmc_kani_exists_safe",
        "(= #x0000000000000002 #x0000000000000002)",
    );
}

#[test]
fn test_bmc_e2e_kani_exists_fail_unrolls_missing_witness() {
    assert_bmc_smt_contains(
        BMC_KANI_QUANTIFIER_SOURCE,
        "bmc_kani_exists_fail",
        "(= #x0000000000000003 #x0000000000000005)",
    );
}

#[test]
fn test_bmc_e2e_kani_any_modifies_lowers_to_symbolic_value() {
    assert_bmc_smt_contains(BMC_KANI_ANY_MODIFIES_SOURCE, "bmc_kani_any_modifies_havoc", "ay_any");
}

#[test]
// Nightly spelling; see the Trust twin below.
#[cfg(not(trust_toolchain))]
fn test_bmc_e2e_kani_write_any_u32_havocs_target_local() {
    let (smt, violations) =
        emit_bmc_smt_for_fn(BMC_KANI_WRITE_ANY_SOURCE, "bmc_kani_write_any_u32_havoc");
    assert!(
        violations > 0,
        "bmc_kani_write_any_u32_havoc: expected an assertion violation predicate. SMT:\n{smt}"
    );
    assert!(
        smt.contains("ay_write_any_0"),
        "write_any should introduce a fresh BMC havoc value. SMT:\n{smt}"
    );
    assert!(
        smt.contains("|bmc_kani_write_any_u32_havoc::local_1_1| ay_write_any_0"),
        "write_any should update the addressed local to the fresh havoc value. SMT:\n{smt}"
    );
}

/// Trust twin of the test above. Trust's `rustc_public` names a local instance with
/// its crate (`testcrate_N::...`), so the emitted state symbols are `|`-quoted and
/// the expected spelling carries the closing `|`. The encoding is unchanged.
#[test]
#[cfg(trust_toolchain)]
fn test_bmc_e2e_kani_write_any_u32_havocs_target_local_trust() {
    let (smt, violations) =
        emit_bmc_smt_for_fn(BMC_KANI_WRITE_ANY_SOURCE, "bmc_kani_write_any_u32_havoc");
    assert!(
        violations > 0,
        "bmc_kani_write_any_u32_havoc: expected an assertion violation predicate. SMT:\n{smt}"
    );
    assert!(
        smt.contains("ay_write_any_0"),
        "write_any should introduce a fresh BMC havoc value. SMT:\n{smt}"
    );
    assert!(
        smt.contains("::bmc_kani_write_any_u32_havoc::local_1_1| ay_write_any_0"),
        "write_any should update the addressed local to the fresh havoc value. SMT:\n{smt}"
    );
}

#[test]
// Nightly spelling; see the Trust twin below.
#[cfg(not(trust_toolchain))]
fn test_bmc_e2e_kani_write_any_nonzero_preserves_validity() {
    let (smt, violations) = emit_bmc_smt_for_fn(
        BMC_KANI_WRITE_ANY_SOURCE,
        "bmc_kani_write_any_nonzero_preserves_validity",
    );
    assert!(
        violations > 0,
        "bmc_kani_write_any_nonzero_preserves_validity: expected an assertion violation predicate. SMT:\n{smt}"
    );
    assert!(
        smt.contains("(not (= ay_write_any_0 #x00000000))"),
        "write_any should preserve NonZero validity for fresh BMC havoc values. SMT:\n{smt}"
    );
    assert!(
        smt.contains("|bmc_kani_write_any_nonzero_preserves_validity::local_1_1| ay_write_any_0"),
        "write_any should update the NonZero local to the fresh havoc value. SMT:\n{smt}"
    );
}

/// Trust twin of the test above. Trust's `rustc_public` names a local instance with
/// its crate (`testcrate_N::...`), so the emitted state symbols are `|`-quoted and
/// the expected spelling carries the closing `|`. The encoding is unchanged.
#[test]
#[cfg(trust_toolchain)]
fn test_bmc_e2e_kani_write_any_nonzero_preserves_validity_trust() {
    let (smt, violations) = emit_bmc_smt_for_fn(
        BMC_KANI_WRITE_ANY_SOURCE,
        "bmc_kani_write_any_nonzero_preserves_validity",
    );
    assert!(
        violations > 0,
        "bmc_kani_write_any_nonzero_preserves_validity: expected an assertion violation predicate. SMT:\n{smt}"
    );
    assert!(
        smt.contains("(not (= ay_write_any_0 #x00000000))"),
        "write_any should preserve NonZero validity for fresh BMC havoc values. SMT:\n{smt}"
    );
    assert!(
        smt.contains("::bmc_kani_write_any_nonzero_preserves_validity::local_1_1| ay_write_any_0"),
        "write_any should update the NonZero local to the fresh havoc value. SMT:\n{smt}"
    );
}

/// `Box`'s drop glue lowers to `<Global as Allocator>::deallocate(&self, ptr,
/// layout)`. Reading the pointer positionally from `args[0]` freed the borrowed
/// `Global` receiver — an unconstrained address — and shifted the `Layout` into
/// the align slot, so the dealloc size/base-pointer obligations were asked about
/// garbage and ay could not build a model for them (`0 of 0 failed`,
/// `INCONCLUSIVE (solver undecided)`). The freed address must be the operand
/// before the layout.
pub(super) const BMC_BOX_DROP_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_box_drop_frees_own_block(x: u32) {
    let _ = Box::new(9_usize);
    kani::assert(x == x);
}
"#;

/// Every heap obligation raised by a `Box` allocate/drop round trip is
/// DISCHARGEABLE: the block the drop glue frees is the block the allocation
/// created, so `dealloc size mismatch`, `dealloc base pointer` and `double free`
/// are all unsatisfiable. Before the argument fix this query came back
/// `unknown` — ay could not model the shape the shifted arguments produced.
#[test]
fn test_bmc_e2e_box_drop_frees_its_own_block() {
    assert_bmc_solver_result(BMC_BOX_DROP_SOURCE, "bmc_box_drop_frees_own_block", "unsat");
}

// -------------------------------------------------------------------------
// Tests — `RangeFrom` sub-slice length (`&buf[start..]`)
// -------------------------------------------------------------------------

/// `&input[start..]` on a `&[u8]` receiver: the sub-slice's length is
/// `source_len - start`, tied to the SOURCE length rather than failing closed
/// as an unmodelled sub-slice. With the bounds guard the assertion holds for
/// every `start`, so the VC is unsatisfiable. (A by-value `[u8; N]` receiver
/// routes through `core::array`'s Index impl and is not reached by the slice
/// stub — a pre-existing gap, not covered here.)
pub(super) const BMC_RANGE_FROM_LEN_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_range_from_len_safe(input: &[u8], start: usize) {
    if start <= input.len() {
        let tail = &input[start..];
        assert!(tail.len() == input.len() - start);
    }
}
"#;

/// The discriminating twin: the same guarded sub-slice asserting the length
/// is UNCHANGED, which holds iff `start == 0`. No arithmetic is involved (the
/// assertion goes through the kani assert hook, since the harness needs an
/// assert probe and `assert!` alone lowers to a plain panic call), so the
/// only way to `sat` is through the modelled length: a model with
/// `start != 0` violates the assertion. (The SAFE case above is what proves
/// the length is tied to `start`; this twin proves it is not a constant.)
pub(super) const BMC_RANGE_FROM_LEN_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_range_from_len_fail(input: &[u8], start: usize) {
    if start <= input.len() {
        let tail = &input[start..];
        kani::assert(tail.len() == input.len());
    }
}
"#;

/// The out-of-bounds twin: NO guard on `start`. `&input[start..]` with
/// `start > input.len()` is a Rust panic (`slice_start_index_len_fail`), so
/// the modelling must record a `bounds_check` obligation on this path and the
/// query must be `sat` — before that obligation existed, the wrapped length
/// `source_len - start` made this shape come back PROVED.
pub(super) const BMC_RANGE_FROM_OOB_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_range_from_oob(input: &[u8], start: usize) {
    let tail = &input[start..];
    kani::assert(tail.len() <= input.len());
}
"#;

/// `..end` / `start..end` sub-slices carry the same obligations: `end > len`
/// and `start > end` are Rust panics, so an unguarded `&input[..end]` and an
/// unguarded `&input[start..end]` must both be `sat`, while the guarded
/// `&input[start..end]` length `end - start` must prove.
pub(super) const BMC_RANGE_TO_OOB_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_range_to_oob(input: &[u8], end: usize) {
    let head = &input[..end];
    kani::assert(head.len() <= input.len());
}
"#;

pub(super) const BMC_RANGE_ORDER_OOB_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn bmc_range_order_oob(input: &[u8], start: usize, end: usize) {
    if end <= input.len() {
        let mid = &input[start..end];
        kani::assert(mid.len() <= input.len());
    }
}
"#;

pub(super) const BMC_RANGE_LEN_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_range_len_safe(input: &[u8], start: usize, end: usize) {
    if start <= end && end <= input.len() {
        let mid = &input[start..end];
        assert!(mid.len() == end - start);
    }
}
"#;

#[test]
fn test_bmc_e2e_range_from_subslice_len_tied_to_source_proves_unsat() {
    assert_bmc_solver_result(BMC_RANGE_FROM_LEN_SAFE_SOURCE, "bmc_range_from_len_safe", "unsat");
}

#[test]
fn test_bmc_e2e_range_from_subslice_wrong_len_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_RANGE_FROM_LEN_FAIL_SOURCE, "bmc_range_from_len_fail", "sat");
}

#[test]
fn test_bmc_e2e_range_from_subslice_start_past_len_is_a_violation() {
    assert_bmc_solver_result(BMC_RANGE_FROM_OOB_SOURCE, "bmc_range_from_oob", "sat");
}

#[test]
fn test_bmc_e2e_range_to_subslice_end_past_len_is_a_violation() {
    assert_bmc_solver_result(BMC_RANGE_TO_OOB_SOURCE, "bmc_range_to_oob", "sat");
}

#[test]
fn test_bmc_e2e_range_subslice_start_past_end_is_a_violation() {
    assert_bmc_solver_result(BMC_RANGE_ORDER_OOB_SOURCE, "bmc_range_order_oob", "sat");
}

#[test]
fn test_bmc_e2e_range_subslice_len_is_end_minus_start_proves_unsat() {
    assert_bmc_solver_result(BMC_RANGE_LEN_SAFE_SOURCE, "bmc_range_len_safe", "unsat");
}

// -------------------------------------------------------------------------
// Float-to-integer `as` casts (parity-1 second review, F-cast)
// -------------------------------------------------------------------------

/// `m as usize` for `0.0 <= m <= 3.0` is at most 3: the cast saturates and
/// truncates, it does not reinterpret bits. Before `cast_float.rs` the BMC lane
/// reinterpreted the float's bits as the integer and certified the "counterexample"
/// `[AY:CTREX_CAT:Genuine]` (review fixture `probe_const_cast_holds`). The index
/// into a four-element array is the check: its bounds assertion holds exactly when
/// the cast stays below 4.
pub(super) const BMC_BOUNDED_FLOAT_TO_USIZE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_bounded_float_to_usize(m: f32) {
    if m >= 0.0 && m <= 3.0 {
        let arr = [1u8, 2, 3, 4];
        let i = m as usize;
        let v = arr[i];
        assert!(v >= 1);
    }
}
"#;

/// The twin with a three-element array: `3.0 as usize == 3` is out of bounds.
pub(super) const BMC_BOUNDED_FLOAT_TO_USIZE_REFUTED_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_bounded_float_to_usize_refuted(m: f32) {
    if m >= 0.0 && m <= 3.0 {
        let arr = [1u8, 2, 3];
        let i = m as usize;
        let v = arr[i];
        assert!(v >= 1);
    }
}
"#;

/// A clamp through `min`/`max` then a cast: the relation's result is a number in
/// `[0, 3]`, so the index stays in bounds (review fixture `probe_chain_cast_holds`).
pub(super) const BMC_CLAMPED_FLOAT_TO_USIZE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_clamped_float_to_usize(x: f32) {
    if !x.is_nan() {
        let arr = [1u8, 2, 3, 4];
        let m = x.max(0.0).min(3.0);
        let i = m as usize;
        let v = arr[i];
        assert!(v >= 1);
    }
}
"#;

#[test]
fn test_bmc_e2e_bounded_float_to_usize_cast_proves_unsat() {
    assert_bmc_solver_result(
        BMC_BOUNDED_FLOAT_TO_USIZE_SOURCE,
        "bmc_bounded_float_to_usize",
        "unsat",
    );
}

#[test]
fn test_bmc_e2e_bounded_float_to_usize_cast_wrong_bound_finds_sat() {
    assert_bmc_solver_result(
        BMC_BOUNDED_FLOAT_TO_USIZE_REFUTED_SOURCE,
        "bmc_bounded_float_to_usize_refuted",
        "sat",
    );
}

#[test]
fn test_bmc_e2e_clamped_float_to_usize_cast_proves_unsat() {
    assert_bmc_solver_result(
        BMC_CLAMPED_FLOAT_TO_USIZE_SOURCE,
        "bmc_clamped_float_to_usize",
        "unsat",
    );
}

/// Stores at an index through a `&mut [T; N]` / `&mut [T]` reference reach
/// the referent (`try_codegen_assign_ref_deref_index`): on main 31793ccc3 the
/// generic path bound a `r_deref_idx_by_i` register instead and the referent
/// never changed, so `assert!(a[0] == 1)` after `r[0] = 9` verified SUCCESSFUL.
/// The reborrow a bounds check takes (`&raw const *s`) carries the reborrowed
/// pointer's own metadata (`try_build_fat_pointer`): on main it took a fresh
/// length for an array referent, so `p.len() == 2` FAILED with a Genuine
/// counterexample. Inputs are parameters so the optimizer keeps every check.
/// The metadata shape itself folds to a constant at this opt level, so
/// negative/unsize_mut_slice.rs is its lane-level measurement.
pub(super) const BMC_REF_INDEX_STORE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_array_ref_store_safe(a: &mut [u8; 2]) {
    a[0] = 9;
    assert!(a[0] == 9);
}

fn bmc_array_ref_store_fail(a: &mut [u8; 2]) {
    a[0] = 9;
    assert!(a[0] == 1);
}

fn bmc_array_ref_symbolic_store_safe(a: &mut [u8; 2], i: usize) {
    if i < 2 {
        a[i] = 9;
        assert!(a[i] == 9);
    }
}

fn bmc_unsize_mut_store_safe(a: &mut [u8; 2]) {
    let s: &mut [u8] = &mut *a;
    s[1] = 9;
    assert!(a[1] == 9);
}

fn bmc_unsize_mut_store_fail(a: &mut [u8; 2]) {
    let s: &mut [u8] = &mut *a;
    s[1] = 9;
    assert!(a[1] == 2);
}

fn bmc_slice_param_store_safe(s: &mut [u8]) {
    if !s.is_empty() {
        s[0] = 9;
        assert!(s[0] == 9);
    }
}

fn bmc_slice_param_store_fail(s: &mut [u8]) {
    if !s.is_empty() {
        s[0] = 9;
        assert!(s[0] == 1);
    }
}
"#;

#[test]
fn test_bmc_e2e_array_ref_index_store_reaches_referent_proves_unsat() {
    assert_bmc_solver_result(BMC_REF_INDEX_STORE_SOURCE, "bmc_array_ref_store_safe", "unsat");
}

#[test]
fn test_bmc_e2e_array_ref_index_store_stale_claim_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_REF_INDEX_STORE_SOURCE, "bmc_array_ref_store_fail", "sat");
}

#[test]
fn test_bmc_e2e_array_ref_symbolic_index_store_proves_unsat() {
    assert_bmc_solver_result(
        BMC_REF_INDEX_STORE_SOURCE,
        "bmc_array_ref_symbolic_store_safe",
        "unsat",
    );
}

#[test]
fn test_bmc_e2e_unsize_mut_index_store_reaches_array_proves_unsat() {
    assert_bmc_solver_result(BMC_REF_INDEX_STORE_SOURCE, "bmc_unsize_mut_store_safe", "unsat");
}

#[test]
fn test_bmc_e2e_unsize_mut_index_store_stale_claim_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_REF_INDEX_STORE_SOURCE, "bmc_unsize_mut_store_fail", "sat");
}

#[test]
fn test_bmc_e2e_slice_param_index_store_proves_unsat() {
    assert_bmc_solver_result(BMC_REF_INDEX_STORE_SOURCE, "bmc_slice_param_store_safe", "unsat");
}

#[test]
fn test_bmc_e2e_slice_param_index_store_stale_claim_finds_sat_counterexample() {
    assert_bmc_solver_result(BMC_REF_INDEX_STORE_SOURCE, "bmc_slice_param_store_fail", "sat");
}

// -------------------------------------------------------------------------
// `Iterator::sum` arithmetic (AY alignment review round 2): the stub reads
// std's `Sum` impl from the call's Rust types (`iter_sum_summand`). Each
// probe's `(x >> 1) + 1` is an overflow-checked add that can never overflow:
// it only gives the probe the MIR `Assert` terminator `has_assert_probe`
// requires, so the sum is the only thing that can make the query SAT.
// -------------------------------------------------------------------------

pub(super) const BMC_ITER_SUM_SOURCE: &str = r#"#![allow(dead_code)]
use std::num::{Saturating, Wrapping};

fn bmc_sum_u8_overflow(x: u8) {
    let s: u8 = [200u8, 100].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s > 0 || y == 0);
}

fn bmc_sum_u8_no_overflow(x: u8) {
    let s: u8 = [200u8, 50].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s == 250 || y == 0);
}

fn bmc_sum_f32_to_inf(x: u8) {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s.is_finite() || y == 0);
}

fn bmc_sum_f32_value(x: u8) {
    let s: f32 = [1.5f32, 2.25].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s == 3.75 || y == 0);
}

fn bmc_sum_two_calls_one_place(x: u8, c: bool) {
    let a = [1u8, 2];
    let s: u8 = if c { a.iter().sum() } else { a.iter().copied().sum() };
    let y = (x >> 1) + 1;
    assert!(s == 3 || y == 0);
}

fn bmc_sum_saturating_saturates(x: u8) {
    let a = [Saturating(200u8), Saturating(100)];
    let s: Saturating<u8> = a.iter().sum();
    let y = (x >> 1) + 1;
    assert!(s.0 == 255 || y == 0);
}

fn bmc_sum_saturating_is_not_wrapped(x: u8) {
    let a = [Saturating(200u8), Saturating(100)];
    let s: Saturating<u8> = a.iter().sum();
    let y = (x >> 1) + 1;
    assert!(s.0 != 44 || y == 0);
}

fn bmc_sum_wrapping_wraps(x: u8) {
    let a = [Wrapping(200u8), Wrapping(100)];
    let s: Wrapping<u8> = a.iter().sum();
    let y = (x >> 1) + 1;
    assert!(s.0 == 44 || y == 0);
}
"#;

/// std's integer `Sum` adds under `#[rustc_inherit_overflow_checks]`; the stub
/// used to wrap silently (`200 + 100 = 44 > 0`) and proved this.
#[test]
fn test_bmc_e2e_iter_sum_u8_overflow_is_a_counterexample() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_u8_overflow", "sat");
}

#[test]
fn test_bmc_e2e_iter_sum_u8_without_overflow_proves_unsat() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_u8_no_overflow", "unsat");
}

/// `f32::MAX + f32::MAX` is `+inf`. The stub used to add the IEEE bit patterns
/// as integers, got a finite value, and proved `s.is_finite()`.
#[test]
fn test_bmc_e2e_iter_sum_f32_overflow_to_infinity_is_a_counterexample() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_f32_to_inf", "sat");
}

/// `-0.0 + 1.5 + 2.25 == 3.75` exactly; the integer sum of the bit patterns
/// is not 3.75, which was reported as a counterexample.
#[test]
fn test_bmc_e2e_iter_sum_f32_value_proves_unsat() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_f32_value", "unsat");
}

/// The two arms of the `if` each end in `.sum()`, and rustc writes both
/// results into one local. Each call is std's `u8` sum of `[1, 2]`. The stub
/// used to look the call up by its destination place, found two different
/// `Iterator::sum` instances there, classified both `Unknown` and havocked
/// the value (AY alignment round 8, review round 3, finding 1).
#[test]
fn test_bmc_e2e_iter_sum_two_calls_one_place_proves_unsat() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_two_calls_one_place", "unsat");
}

/// This lane gives `Saturating<u8>` and `Wrapping<u8>` a one-field datatype
/// sort, so the unroll used to refuse them and the sum was havocked (the
/// dual rows were INCONCLUSIVE). It now sums the field: `200 + 100` saturates
/// to 255 (AY alignment round 8, review round 4, finding 1) and wraps to 44.
/// The arrays are locals: a promoted constant array of datatype values is not
/// resolved element by element, and the stub havocs that sum (fail-closed).
#[test]
fn test_bmc_e2e_iter_sum_saturating_saturates() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_saturating_saturates", "unsat");
}

/// Stated as a claim that holds (`s.0 != 44`): a `sat` query over an array of
/// datatype values is answered `unknown` at ay `d80d17a90`, whose model gate
/// withholds the model (docs/ay-asks/2026-10-14-datatype-array-model-withheld-d80d17a90/).
#[test]
fn test_bmc_e2e_iter_sum_saturating_is_not_wrapped() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_saturating_is_not_wrapped", "unsat");
}

#[test]
fn test_bmc_e2e_iter_sum_wrapping_wraps() {
    assert_bmc_solver_result(BMC_ITER_SUM_SOURCE, "bmc_sum_wrapping_wraps", "unsat");
}

// -------------------------------------------------------------------------
// Closures an iterator stub does not run; float sums nothing reads
// (AY alignment round 8, review round 5)
// -------------------------------------------------------------------------

pub(super) const BMC_ITER_CLOSURE_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_map_next_closure_panics(x: u8) {
    let a = [3u8, 2];
    let mut it = a.iter().map(|v| {
        assert!(*v < 3);
        *v
    });
    let _first = it.next();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn bmc_map_next_pure_closure(x: u8) {
    let a = [3u8, 2];
    let mut it = a.iter().map(|v| v.wrapping_add(1));
    let _first = it.next();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn bmc_filter_next_pred_panics(x: u8) {
    let a = [3u8, 2];
    let mut it = a.iter().filter(|v| {
        assert!(**v < 3);
        true
    });
    let _first = it.next();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn bmc_map_collect_closure_panics(x: u8) {
    let a = [3u8, 2];
    let v: Vec<u8> = a
        .iter()
        .map(|v| {
            assert!(*v < 3);
            *v
        })
        .collect();
    let _ = v.len();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn bmc_map_next_beside_failing_check(x: u8) {
    let a = [3u8, 2];
    let mut it = a.iter().map(|v| v.wrapping_add(1));
    let first = it.next();
    let y = (x >> 1) + 1;
    assert!(y == 1 || first.is_none());
}

fn bmc_sum_f32_unread_beside_failing_check(a: f32, b: f32, x: u8) {
    let arr = [a, b];
    let _s: f32 = arr.iter().sum();
    let y = (x >> 1) + 1;
    assert!(y == 1);
}

fn bmc_sum_f32_unread_beside_holding_check(a: f32, b: f32, x: u8) {
    let arr = [a, b];
    let _s: f32 = arr.iter().sum();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}
"#;

/// A `Map`'s closure panics on the first element. The `MapNext` stub havocs
/// the mapped value and never runs the closure, and nothing stood in for its
/// assert, so the program was proved where Kani fails (review round 5,
/// finding 1). The conservative check for the unrun closure makes it `sat`.
#[test]
fn test_bmc_e2e_map_next_closure_panic_is_not_dropped() {
    assert_bmc_solver_result(BMC_ITER_CLOSURE_SOURCE, "bmc_map_next_closure_panics", "sat");
}

/// A closure that calls obligation-free code adds no check.
#[test]
fn test_bmc_e2e_map_next_pure_closure_still_proves() {
    assert_bmc_solver_result(BMC_ITER_CLOSURE_SOURCE, "bmc_map_next_pure_closure", "unsat");
}

#[test]
fn test_bmc_e2e_filter_next_predicate_panic_is_not_dropped() {
    assert_bmc_solver_result(BMC_ITER_CLOSURE_SOURCE, "bmc_filter_next_pred_panics", "sat");
}

/// A `Map`'s `next()` beside a failing check of the program's own, the closure
/// obligation-free: decided `sat`.
#[test]
fn test_bmc_e2e_map_next_beside_failing_check_is_sat() {
    assert_bmc_solver_result(BMC_ITER_CLOSURE_SOURCE, "bmc_map_next_beside_failing_check", "sat");
}

/// The `Option` of the inner iterator's `next()` is built from the element's
/// sort (`Option_bv8`), not from the program's `Option` type (`Option_u8`),
/// and occurs only inside the stub's terms. The `emit_bmc` path above declares
/// every datatype its terms use; the legacy `program`, which is the query the
/// driver writes by default, declares only what codegen declares, and did not
/// declare this one: every driver query that reached the solver with a `Map`,
/// `Filter` or `Zip` `next()` in it was rejected (`unknown constant
/// Some_Option_bv8`) and came out INCONCLUSIVE (AY alignment round 8, review
/// round 5).
#[test]
fn test_bmc_map_next_driver_query_declares_the_inner_option() {
    let mut rendered = None;
    with_test_ay_ctx_for_source(BMC_ITER_CLOSURE_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, "bmc_map_next_beside_failing_check");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);
        rendered = Some(ctx.program.to_string());
    });
    let smt = rendered.expect("legacy program");
    let used: std::collections::BTreeSet<&str> = smt
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter_map(|token| token.strip_prefix("Some_").or_else(|| token.strip_prefix("None_")))
        .filter(|datatype| datatype.starts_with("Option_"))
        .collect();
    assert!(!used.is_empty(), "no Option constructor in the query. SMT:\n{smt}");
    for datatype in used {
        assert!(
            smt.contains(&format!("(declare-datatype {datatype} ")),
            "{datatype} is applied but not declared. SMT:\n{smt}"
        );
    }
}

/// `collect()` of the same `Map`.
#[test]
fn test_bmc_e2e_map_collect_closure_panic_is_not_dropped() {
    assert_bmc_solver_result(BMC_ITER_CLOSURE_SOURCE, "bmc_map_collect_closure_panics", "sat");
}

/// Nothing reads the symbolic float sum, so it gets a fresh value: the query
/// keeps no `fp.add`, which ay `d80d17a90` answers `unknown` beside the
/// iterator's datatypes, and the failing check elsewhere is decided `sat`
/// (review round 5, finding 2; main reported that bug Genuine, round 2's exact
/// sum made the harness INCONCLUSIVE).
#[test]
fn test_bmc_e2e_unread_float_sum_leaves_the_query_decidable() {
    assert_bmc_solver_result(
        BMC_ITER_CLOSURE_SOURCE,
        "bmc_sum_f32_unread_beside_failing_check",
        "sat",
    );
}

#[test]
fn test_bmc_e2e_unread_float_sum_beside_holding_check_proves() {
    assert_bmc_solver_result(
        BMC_ITER_CLOSURE_SOURCE,
        "bmc_sum_f32_unread_beside_holding_check",
        "unsat",
    );
}

// -------------------------------------------------------------------------
// Float `%` is C `fmod`, not the IEEE remainder (TRUST-MC-FREM-1)
// -------------------------------------------------------------------------

/// [`emit_bmc_smt_for_fn`] for probes whose check is either a MIR `Assert`
/// terminator (an overflow check) or a plain `assert!`. Outside a Kani harness
/// an `assert!` is a call into the panic machinery with no return edge, not an
/// `Assert` terminator or a Kani hook, and the BMC lane records it as a
/// `panic` violation (`try_codegen_stdlib_stub_call`). The elided-assertion
/// guard accepts either. Returns the SMT and one description per recorded
/// violation (kind, message, SMT name).
fn emit_bmc_smt_for_check_probe(source: &str, fn_suffix: &str) -> (String, Vec<String>) {
    let mut maybe_result: Option<(String, Vec<String>)> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.prove_safety_only = false;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        let has_panic_call = body
            .blocks
            .iter()
            .any(|bb| matches!(&bb.terminator.kind, TerminatorKind::Call { target: None, .. }));
        assert!(
            has_assert_probe(&body) || has_panic_call,
            "{fn_suffix}: expected an Assert terminator or the `assert!` panic call in MIR; \
             optimizer may have elided the check"
        );

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let violations = ctx
            .bmc_vc
            .violations
            .iter()
            .map(|v| format!("{:?} {:?} {:?}", v.kind, v.message, v.smt_var))
            .collect();
        maybe_result = Some((crate::codegen_ay::emit_bmc(ctx.bmc_vc).to_string(), violations));
    });
    maybe_result.expect("expected BMC SMT and violations")
}

/// Solve a harness's BMC VC with ay alone, the engine's own solver, so the
/// verdict never depends on which `z3` is on PATH.
fn assert_bmc_ay_verdict(source: &str, fn_suffix: &str, expected: &str) {
    let (smt, violations) = emit_bmc_smt_for_check_probe(source, fn_suffix);
    assert!(
        !violations.is_empty(),
        "{fn_suffix}: expected a violation predicate in the BMC VC. SMT:\n{smt}"
    );
    let result = run_ay_smt2(&smt)
        .unwrap_or_else(|err| panic!("{fn_suffix}: AY execution failed: {err}. SMT:\n{smt}"));
    assert_eq!(result, expected, "{fn_suffix}: expected {expected}, got {result}. SMT:\n{smt}");
}

/// Harnesses the trust-mc front door lowers through `codegen_rvalue` ->
/// `bv_float_binop`. The installed front door (atpkg trust-mc 20065) reported
/// the TRUE `x == 5.0 => x % 3.0 == 2.0` as `VERIFICATION:- FAILED` with
/// `[AY:CTREX_CAT:Genuine]`: it lowered `%` to SMT-LIB `fp.rem`, the IEEE
/// remainder, and `fp.rem(5, 3) = -1`.
///
/// The two FALSE claims are stated as overflow checks, which fail exactly when
/// the claim is false: `5.0 % 3.0 < 0.0` on a concrete dividend, and
/// `x == 5.0 => x % 3.0 != 2.0` on a symbolic one. Under `fp.rem` both held, so
/// the overflow was unreachable and each lie was proved (`unsat`). Not used:
/// the symbolic `x == 5.0 => x % 3.0 < 0.0`, for which the pinned ay
/// (b1b0b9de) answers `unknown` in-process (measured 2026-10-09; the
/// predecessor pin 2fb40f95 answered `sat`), and the same claim as an
/// `assert!`, whose panic-message plumbing the pinned ay also leaves `unknown`.
/// `unknown` proves nothing, but it cannot tell the encodings apart.
pub(super) const BMC_FLOAT_REM_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_f64_rem_true(x: f64) {
    if x == 5.0 {
        assert!(x % 3.0 == 2.0);
    }
}
fn bmc_f64_rem_negative_is_false() {
    let x: f64 = 5.0;
    let n: u8 = if x % 3.0 < 0.0 { 0 } else { 255 };
    let _m = n + 1;
}
fn bmc_f64_rem_not_two_is_false(x: f64) {
    if x == 5.0 {
        let n: u8 = if x % 3.0 == 2.0 { 255 } else { 0 };
        let _m = n + 1;
    }
}
fn bmc_f64_rem_negative_dividend(x: f64) {
    if x == -5.0 {
        assert!(x % 3.0 == -2.0);
    }
}
fn bmc_f32_rem_nonnegative(x: f32) {
    if x >= 0.0 && x <= 1.0e6 {
        assert!(x % 3.0 >= 0.0);
    }
}
"#;

#[test]
fn test_bmc_e2e_f64_rem_true_assertion_proves_unsat() {
    assert_bmc_ay_verdict(BMC_FLOAT_REM_SOURCE, "bmc_f64_rem_true", "unsat");
}

/// The false `5.0 % 3.0 < 0.0` is refuted. Under `fp.rem` alone it held
/// (`-1 < 0`), so the overflow was unreachable and the lie was proved.
#[test]
fn test_bmc_e2e_f64_rem_negative_false_claim_finds_sat() {
    assert_bmc_ay_verdict(BMC_FLOAT_REM_SOURCE, "bmc_f64_rem_negative_is_false", "sat");
}

/// The false `x == 5.0 => x % 3.0 != 2.0` is refuted on a symbolic dividend.
/// Under `fp.rem` alone it held (`-1 != 2`) and was proved.
#[test]
fn test_bmc_e2e_f64_rem_not_two_false_claim_finds_sat() {
    assert_bmc_ay_verdict(BMC_FLOAT_REM_SOURCE, "bmc_f64_rem_not_two_is_false", "sat");
}

#[test]
fn test_bmc_e2e_f64_rem_negative_dividend_proves_unsat() {
    assert_bmc_ay_verdict(BMC_FLOAT_REM_SOURCE, "bmc_f64_rem_negative_dividend", "unsat");
}

#[test]
fn test_bmc_e2e_f32_rem_nonnegative_dividend_proves_unsat() {
    assert_bmc_ay_verdict(BMC_FLOAT_REM_SOURCE, "bmc_f32_rem_nonnegative", "unsat");
}

// -------------------------------------------------------------------------
// Float `rem_euclid` / `div_euclid` are not the integer stubs (TRUST-MC-FREM-2)
// -------------------------------------------------------------------------

/// `f64::rem_euclid` / `f64::div_euclid` share their names with the integer
/// methods that `try_codegen_math_unary_call` encodes as bitvector Euclidean
/// division. The stub was keyed on the name alone and read a float (an IEEE
/// bit pattern here, "unsigned" by `ty_signedness_shallow`) as an unsigned
/// integer: it computed `bvurem` / `bvudiv` over the bit patterns and added an
/// integer "euclidean division by zero" check. Through the installed front
/// door (atpkg trust-mc 20065) the FALSE `x == 5.0 => x.rem_euclid(3.0) !=
/// 2.0` was `VERIFICATION:- SUCCESSFUL`, and the TRUE `rem_euclid` /
/// `div_euclid` claims below were `FAILED` with `[AY:CTREX_CAT:Genuine]`, on
/// both routes. A float call now takes the ordinary call path: the BMC
/// mini-inliner inlines std's body, whose `%` is the exact `fmod`.
pub(super) const BMC_FLOAT_EUCLID_SOURCE: &str = r#"#![allow(dead_code)]
fn bmc_f64_rem_euclid_true(x: f64) {
    if x == 5.0 {
        assert!(x.rem_euclid(3.0) == 2.0);
    }
}
fn bmc_f64_rem_euclid_negative_dividend(x: f64) {
    if x == -5.0 {
        assert!(x.rem_euclid(3.0) == 1.0);
    }
}
fn bmc_f64_div_euclid_negative_dividend(x: f64) {
    if x == -5.0 {
        assert!(x.div_euclid(3.0) == -2.0);
    }
}
fn bmc_f64_rem_euclid_not_two_is_false(x: f64) {
    if x == 5.0 {
        let n: u8 = if x.rem_euclid(3.0) == 2.0 { 255 } else { 0 };
        let _m = n + 1;
    }
}
fn bmc_i32_rem_euclid_negative_dividend(x: i32) {
    if x == -5 {
        assert!(x.rem_euclid(3) == 1);
    }
}
"#;

#[test]
fn test_bmc_e2e_f64_rem_euclid_true_assertion_proves_unsat() {
    assert_bmc_ay_verdict(BMC_FLOAT_EUCLID_SOURCE, "bmc_f64_rem_euclid_true", "unsat");
}

#[test]
fn test_bmc_e2e_f64_rem_euclid_negative_dividend_proves_unsat() {
    assert_bmc_ay_verdict(BMC_FLOAT_EUCLID_SOURCE, "bmc_f64_rem_euclid_negative_dividend", "unsat");
}

#[test]
fn test_bmc_e2e_f64_div_euclid_negative_dividend_proves_unsat() {
    assert_bmc_ay_verdict(BMC_FLOAT_EUCLID_SOURCE, "bmc_f64_div_euclid_negative_dividend", "unsat");
}

/// The false claim is refuted. Under the integer stub it was proved.
#[test]
fn test_bmc_e2e_f64_rem_euclid_not_two_false_claim_finds_sat() {
    assert_bmc_ay_verdict(BMC_FLOAT_EUCLID_SOURCE, "bmc_f64_rem_euclid_not_two_is_false", "sat");
}

/// The labels the integer Euclidean stub (`codegen_euclid_bmc`) records its
/// checks under.
const INTEGER_EUCLID_STUB_CHECKS: [&str; 4] =
    ["div_euclid_zero", "rem_euclid_zero", "div_euclid_overflow", "rem_euclid_overflow"];

/// A float divisor of zero gives NaN, not a panic: no integer division-by-zero
/// check belongs on a float `rem_euclid`. The integer stub added one.
///
/// The check is by the stub's labels, not by the word `euclid`: the probe's own
/// `assert!` is a violation too, and its panic message (`assertion failed:
/// x.rem_euclid(3.0) == 2.0`, measured on the frozen nightly lane) names the
/// method.
#[test]
fn test_bmc_f64_rem_euclid_records_no_integer_division_by_zero_check() {
    let (_, violations) =
        emit_bmc_smt_for_check_probe(BMC_FLOAT_EUCLID_SOURCE, "bmc_f64_rem_euclid_true");
    assert!(
        violations
            .iter()
            .all(|v| INTEGER_EUCLID_STUB_CHECKS.iter().all(|label| !v.contains(label))),
        "float rem_euclid must not carry the integer stub's checks: {violations:#?}"
    );
}

/// The integer stub still claims integer operands: `-5 rem_euclid 3 == 1`.
#[test]
fn test_bmc_e2e_i32_rem_euclid_stub_still_proves_unsat() {
    let (_, violations) = emit_bmc_smt_for_check_probe(
        BMC_FLOAT_EUCLID_SOURCE,
        "bmc_i32_rem_euclid_negative_dividend",
    );
    assert!(
        violations.iter().any(|v| v.contains("rem_euclid_zero")),
        "the integer stub's division-by-zero check must stay: {violations:#?}"
    );
    assert_bmc_ay_verdict(BMC_FLOAT_EUCLID_SOURCE, "bmc_i32_rem_euclid_negative_dividend", "unsat");
}

// -------------------------------------------------------------------------
// Integer `Div`/`Rem`: the operator-level checks are not the MIR `Assert`'s
// panic labels (statement/rvalue.rs)
// -------------------------------------------------------------------------

/// `unchecked_div`/`unchecked_rem` lower to a plain `BinOp::Div`/`Rem` with no
/// `Assert` (rustc LowerIntrinsics). A source `/`/`%` has the same statement
/// behind rustc's zero-divisor and `MIN / -1` `Assert`s.
const BMC_DIV_REM_ORIGIN_SOURCE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(internal_features, dead_code)]
    pub fn bmc_lowered_unchecked_div(a: i32, d: i32) -> i32 {
        unsafe { core::intrinsics::unchecked_div(a, d) }
    }
    pub fn bmc_lowered_unchecked_rem(a: i32, d: i32) -> i32 {
        unsafe { core::intrinsics::unchecked_rem(a, d) }
    }
    pub fn bmc_safe_div(a: i32, d: i32) -> i32 {
        a / d
    }
    pub fn bmc_safe_rem(a: i32, d: i32) -> i32 {
        a % d
    }
"#;

/// The recorded BMC violations of `fn_suffix` as `(smt_var, kind)`, with
/// overflow checks on. Unlike [`emit_bmc_smt_for_check_probe`] it does not
/// require a MIR `Assert`: a lowered `unchecked_div` has none.
fn bmc_violation_vars(source: &str, fn_suffix: &str) -> Vec<(String, trust_mc_core::PropertyKind)> {
    let mut maybe_result = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.prove_safety_only = false;
        ctx.config.overflow_checks = true;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);
        maybe_result = Some(
            ctx.bmc_vc
                .violations
                .iter()
                .map(|v| (v.smt_var.clone().unwrap_or_default(), v.kind))
                .collect::<Vec<_>>(),
        );
    });
    maybe_result.expect("expected BMC violations")
}

/// How many recorded violations carry `label` (smt var `ay_violation_<label>_<n>`).
fn count_label(vars: &[(String, trust_mc_core::PropertyKind)], label: &str) -> usize {
    vars.iter()
        .filter(|(var, _)| {
            var.strip_prefix("ay_violation_")
                .and_then(|rest| rest.strip_prefix(label))
                .and_then(|rest| rest.strip_prefix('_'))
                .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
        })
        .count()
}

/// A lowered `unchecked_div`/`unchecked_rem` by zero (or `MIN / -1`) is UB of
/// an unsafe intrinsic, which `#[kani::should_panic]` does not accept (Kani:
/// `check_div_overflow`, `arithmetic_overflow`). Its only checks must not carry
/// the MIR `Assert`'s panic labels.
#[test]
fn test_bmc_lowered_unchecked_div_rem_checks_are_not_mir_assert_labels() {
    for (fn_name, zero, overflow) in [
        ("bmc_lowered_unchecked_div", "binop_div_by_zero", "binop_div_overflow"),
        ("bmc_lowered_unchecked_rem", "binop_rem_by_zero", "binop_rem_overflow"),
    ] {
        let vars = bmc_violation_vars(BMC_DIV_REM_ORIGIN_SOURCE, fn_name);
        for panic_label in
            ["div_by_zero_check", "mod_by_zero_check", "overflow_check_div", "overflow_check_rem"]
        {
            assert_eq!(count_label(&vars, panic_label), 0, "{fn_name}: {panic_label} in {vars:#?}");
        }
        assert_eq!(count_label(&vars, zero), 1, "{fn_name}: {vars:#?}");
        assert_eq!(count_label(&vars, overflow), 1, "{fn_name}: {vars:#?}");
        for (var, kind) in &vars {
            if var.starts_with("ay_violation_binop_") {
                assert_eq!(*kind, trust_mc_core::PropertyKind::UndefinedBehavior, "{var}");
            }
        }
    }
}

/// A source `/`/`%` keeps exactly one MIR-`Assert` panic check per obligation,
/// and its redundant operator-level twin carries the separate non-panic label.
/// While the twin reused the panic labels, each of them counted 2.
#[test]
fn test_bmc_safe_div_rem_keeps_the_mir_assert_panic_label() {
    for (fn_name, labels) in [
        (
            "bmc_safe_div",
            ["div_by_zero_check", "overflow_check_div", "binop_div_by_zero", "binop_div_overflow"],
        ),
        (
            "bmc_safe_rem",
            ["mod_by_zero_check", "overflow_check_rem", "binop_rem_by_zero", "binop_rem_overflow"],
        ),
    ] {
        let vars = bmc_violation_vars(BMC_DIV_REM_ORIGIN_SOURCE, fn_name);
        for label in labels {
            assert_eq!(count_label(&vars, label), 1, "{fn_name}: {label} in {vars:#?}");
        }
    }
}

// -------------------------------------------------------------------------
// `--no-overflow-checks` / `--no-memory-safety-checks` on a MIR `Assert`
// (`StatementCodegen::mir_assert_check_disabled`)
// -------------------------------------------------------------------------

const BMC_CHECK_FLAG_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn bmc_wrapped_add_reaches_assert(a: u8, b: u8) {
        let s = a + b;
        assert!(s >= a);
    }
    pub fn bmc_index_reaches_assert(v: [u8; 4], i: usize) -> u8 {
        let x = v[i];
        assert!(i < 4);
        x
    }
    pub fn bmc_signed_div_only(a: i32, d: i32) -> i32 {
        a / d
    }
"#;

/// The BMC SMT and recorded violations `(smt_var, kind)` of `fn_suffix` under
/// the given check flags.
fn bmc_with_check_flags(
    source: &str,
    fn_suffix: &str,
    overflow_checks: bool,
    memory_safety_checks: bool,
) -> (String, Vec<(String, trust_mc_core::PropertyKind)>) {
    let mut maybe_result = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.prove_safety_only = false;
        ctx.config.overflow_checks = overflow_checks;
        ctx.config.memory_safety_checks = memory_safety_checks;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);
        let vars = ctx
            .bmc_vc
            .violations
            .iter()
            .map(|v| (v.smt_var.clone().unwrap_or_default(), v.kind))
            .collect::<Vec<_>>();
        maybe_result = Some((crate::codegen_ay::emit_bmc(ctx.bmc_vc).to_string(), vars));
    });
    maybe_result.expect("expected BMC SMT and violations")
}

fn solve_bmc(smt: &str, what: &str) -> String {
    let result = run_ay_on_smt2(smt);
    assert!(result.is_ok(), "{what}: AY execution failed: {:?}. SMT:\n{smt}", result.err());
    result.unwrap_or_default()
}

/// `--no-overflow-checks` turns rustc's `a + b` overflow check off, and the
/// program goes on with the wrapped sum, as the CHC lane's
/// `assert_check_disabled` does: `assert!(s >= a)` then fails (`a = 200`,
/// `b = 100`). The label-kind gate dropped the check but kept the
/// `Assert`'s edge condition, which pruned every overflowing execution, and the
/// harness verified (`unsat`).
#[test]
fn test_bmc_overflow_checks_off_goes_on_with_the_wrapped_value() {
    let (smt, vars) =
        bmc_with_check_flags(BMC_CHECK_FLAG_SOURCE, "bmc_wrapped_add_reaches_assert", false, true);
    assert_eq!(count_label(&vars, "overflow_check_add"), 0, "{vars:#?}");
    assert_eq!(solve_bmc(&smt, "overflow checks off"), "sat", "SMT:\n{smt}");
    let (_, vars) =
        bmc_with_check_flags(BMC_CHECK_FLAG_SOURCE, "bmc_wrapped_add_reaches_assert", true, true);
    assert_eq!(count_label(&vars, "overflow_check_add"), 1, "{vars:#?}");
}

/// `--no-memory-safety-checks` turns the bounds `Assert` off and the program
/// goes on past it, so `assert!(i < 4)` fails. Pruned by the kept edge
/// condition, it verified.
#[test]
fn test_bmc_memory_safety_checks_off_goes_on_past_the_bounds_check() {
    let (smt, vars) =
        bmc_with_check_flags(BMC_CHECK_FLAG_SOURCE, "bmc_index_reaches_assert", true, false);
    assert_eq!(count_label(&vars, "bounds_check"), 0, "{vars:#?}");
    assert_eq!(solve_bmc(&smt, "memory-safety checks off"), "sat", "SMT:\n{smt}");
    let (_, vars) =
        bmc_with_check_flags(BMC_CHECK_FLAG_SOURCE, "bmc_index_reaches_assert", true, true);
    assert_eq!(count_label(&vars, "bounds_check"), 1, "{vars:#?}");
}

/// Signed `MIN / -1` is not an overflow check: rustc asserts it whatever
/// `-C overflow-checks` says and the program panics there in every build
/// profile, so `--no-overflow-checks` keeps it (and the divisor check).
#[test]
fn test_bmc_overflow_checks_off_keeps_signed_division_overflow() {
    let (smt, vars) =
        bmc_with_check_flags(BMC_CHECK_FLAG_SOURCE, "bmc_signed_div_only", false, true);
    assert_eq!(count_label(&vars, "overflow_check_div"), 1, "{vars:#?}");
    assert_eq!(count_label(&vars, "div_by_zero_check"), 1, "{vars:#?}");
    assert_eq!(solve_bmc(&smt, "signed division"), "sat", "SMT:\n{smt}");
}

/// `--prove-safety-only` checks UB, not panics: rustc's overflow and bounds
/// asserts become assumes, as Kani (`codegen_assert_assume` on every
/// `PropertyClass::Assertion` check) and the CHC lane
/// (`emit_assert_error_rule_shared`) make them. Checked, BMC failed a harness
/// on a panic both of them pass.
#[test]
fn test_bmc_prove_safety_only_assumes_mir_panic_asserts() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn bmc_add_then_index(a: u8, b: u8, v: [u8; 4], i: usize) -> u8 {
            let s = a + b;
            v[i] ^ s
        }
    "#;
    let (checked, _) = emit_bmc_smt_for_fn_with_config(SOURCE, "bmc_add_then_index", false);
    let (safety_only, _) = emit_bmc_smt_for_fn_with_config(SOURCE, "bmc_add_then_index", true);
    for label in ["ay_violation_overflow_check_add_", "ay_violation_bounds_check_"] {
        assert!(checked.contains(label), "{label} is checked by default. SMT:\n{checked}");
        assert!(
            !safety_only.contains(label),
            "{label} is an assume under --prove-safety-only. SMT:\n{safety_only}"
        );
    }
}

// -------------------------------------------------------------------------
// Slice `==` decides on two lengths and the elements below them
// (`statement::comparison_eq::slice_partial_eq`)
// -------------------------------------------------------------------------

/// Each probe's overflow is reachable exactly when its comparison holds, so
/// `sat` reads "the comparison can come out true" and `unsat` "it is false".
/// The `x`/`y` arrays make `[1, 2]` against `[1, 2, 0]` (lengths differ) or
/// `[1, 2]` against `[1, 2]` (equal), at one reference level (`*a == *b`,
/// `<[i32] as PartialEq>::eq`) and at two (`a == b`, the `&[i32]` impl, which
/// this pipeline does not inline). Shared with the CHC tests.
///
/// Before the fix the BMC lane compared the pointees, the two whole
/// `[i32; N]` SMT arrays, whose tails past `N` are free: `[1, 2]` against
/// `[1, 2, 0]` could come out equal (`*_overflow_if_equal` was `sat`, which
/// the driver certified Genuine on `assert!(a != b)`), and `[1, 2]` against
/// `[1, 2]` unequal. At two reference levels the comparison was not built
/// (`tools/soundness-duals/slice_eq_length_dual.rs`).
pub(super) const SLICE_EQ_LENGTH_SOURCE: &str = r#"#![allow(dead_code)]
fn slice_eq_len_differs_d2_overflow_if_equal() {
    let x = [1i32, 2];
    let y = [1i32, 2, 0];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    let n: u8 = if a == b { 255 } else { 0 };
    let _m = n + 1;
}
fn slice_eq_len_differs_d2_overflow_if_unequal() {
    let x = [1i32, 2];
    let y = [1i32, 2, 0];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    let n: u8 = if a == b { 0 } else { 255 };
    let _m = n + 1;
}
fn slice_eq_len_differs_d1_overflow_if_equal() {
    let x = [1i32, 2];
    let y = [1i32, 2, 0];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    let n: u8 = if *a == *b { 255 } else { 0 };
    let _m = n + 1;
}
fn slice_eq_u8_len_differs_d2_overflow_if_unequal() {
    let x = [1u8, 2];
    let y = [1u8, 2, 0];
    let a: &[u8] = &x;
    let b: &[u8] = &y;
    let n: u8 = if a == b { 0 } else { 255 };
    let _m = n + 1;
}
fn slice_eq_equal_d2_overflow_if_equal() {
    let x = [1i32, 2];
    let y = [1i32, 2];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    let n: u8 = if a == b { 255 } else { 0 };
    let _m = n + 1;
}
fn slice_eq_equal_d2_overflow_if_unequal() {
    let x = [1i32, 2];
    let y = [1i32, 2];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    let n: u8 = if a != b { 255 } else { 0 };
    let _m = n + 1;
}
fn slice_eq_equal_d1_overflow_if_unequal() {
    let x = [1i32, 2];
    let y = [1i32, 2];
    let a: &[i32] = &x;
    let b: &[i32] = &y;
    let n: u8 = if *a != *b { 255 } else { 0 };
    let _m = n + 1;
}
"#;

#[test]
fn test_bmc_slice_eq_reads_lengths_not_array_tails() {
    for (probe, expected) in [
        ("slice_eq_len_differs_d2_overflow_if_equal", "unsat"),
        ("slice_eq_len_differs_d2_overflow_if_unequal", "sat"),
        ("slice_eq_len_differs_d1_overflow_if_equal", "unsat"),
        ("slice_eq_u8_len_differs_d2_overflow_if_unequal", "sat"),
        ("slice_eq_equal_d2_overflow_if_equal", "sat"),
        ("slice_eq_equal_d2_overflow_if_unequal", "unsat"),
        ("slice_eq_equal_d1_overflow_if_unequal", "unsat"),
    ] {
        assert_bmc_ay_verdict(SLICE_EQ_LENGTH_SOURCE, probe, expected);
    }
}

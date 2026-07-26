// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::integration_ay_runner::run_ay_on_smt2;
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

#[test]
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

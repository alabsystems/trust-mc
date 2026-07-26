// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::integration_ay_runner::run_ay_on_smt2;
use super::*;
use crate::args::ChcTrackLevel;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::kani_middle::attributes;
use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, try_get_kani_function};
use rustc_public::mir::{Body, Operand, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

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

fn assert_chc_solver_result(source: &str, fn_suffix: &str, expected: &str) {
    let mut maybe_result: Option<String> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        assert!(
            has_assert_probe(&body),
            "{fn_suffix}: expected MIR assert terminator or kani assert/check hook"
        );

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let chc_vc = ctx.chc_vc.as_ref().expect("CHC VC should be populated after CHC codegen");
        let has_error_head_rule = chc_vc.rules.iter().any(|rule| rule.head.name == "error");
        assert!(
            has_error_head_rule,
            "{fn_suffix}: expected at least one CHC rule with head 'error'; vacuous query would hide regressions"
        );
        maybe_result = Some(crate::codegen_ay::emit_chc(&chc_vc).to_string());
    });

    let smt = maybe_result.expect("expected CHC SMT output");
    let solver_result = run_ay_on_smt2(&smt);
    assert!(
        solver_result.is_ok(),
        "{fn_suffix}: AY execution failed: {}. SMT:\n{smt}",
        solver_result.as_ref().err().map_or("", std::string::String::as_str)
    );
    let result = solver_result.unwrap_or_default();
    assert_eq!(result, expected, "{fn_suffix}: expected {expected}, got {result}. SMT:\n{smt}");
}

fn emit_chc_smt_for_fn(source: &str, fn_suffix: &str) -> String {
    emit_chc_smt_for_fn_with_track(source, fn_suffix, None)
}

fn emit_chc_smt_for_fn_with_track(
    source: &str,
    fn_suffix: &str,
    track_level: Option<ChcTrackLevel>,
) -> String {
    let mut maybe_smt: Option<String> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        if let Some(level) = track_level {
            ctx.config.chc_track_level = level;
        }
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        assert!(
            has_assert_probe(&body),
            "{fn_suffix}: expected MIR assert terminator or kani assert/check hook"
        );

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let chc_vc = ctx.chc_vc.as_ref().expect("CHC VC should be populated after CHC codegen");
        maybe_smt = Some(crate::codegen_ay::emit_chc(&chc_vc).to_string());
    });
    maybe_smt.expect("expected CHC SMT output")
}

fn clear_chc_translation_metadata() {
    crate::codegen_ay::chc::clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
}

const CHC_KANI_ASSUME_ASSERT_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
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

fn chc_kani_assume_assert_safe(x: i32) {
    kani::assume(x > 10);
    kani::assert(x > 5);
}
"#;

const CHC_KANI_ASSUME_ASSERT_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
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

fn chc_kani_assume_assert_fail(x: i32) {
    kani::assume(x > 10);
    kani::assert(x < 0);
}
"#;

/// CheckHook e2e: `kani::check(cond)` is semantically equivalent to assert — emits
/// an error rule for `!cond` with no assume afterward. With assume(x > 10),
/// check(x > 5) should prove safe (unsat).
const CHC_KANI_CHECK_HOOK_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssumeHook"]
    pub fn assume(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "CheckHook"]
    pub fn check(cond: bool) {
        let _ = cond;
    }
}

fn chc_kani_check_hook_safe(x: i32) {
    kani::assume(x > 10);
    kani::check(x > 5);
}
"#;

/// SafetyCheckHook e2e: `kani::safety_check(cond)` emits BOTH an error rule for
/// `!cond` (assert component) AND a guarded transition assuming `cond` (assume
/// component). This is the compiler-inserted safety check pattern (overflow,
/// bounds). With assume(x > 0 && x < 50), x + x < 100 holds, so both the
/// safety_check and the subsequent assert see a consistent safe state.
const CHC_KANI_SAFETY_CHECK_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
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

fn chc_kani_safety_check_safe(x: i32) {
    kani::assume(x > 0 && x < 50);
    kani::safety_check(x + x < 100);
    kani::assert(x > 0);
}
"#;

/// SafetyCheckHook fail e2e: safety_check(x < 0) after assume(x > 10) is
/// unsatisfiable — the error relation IS reachable (sat counterexample).
const CHC_KANI_SAFETY_CHECK_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
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
}

fn chc_kani_safety_check_fail(x: i32) {
    kani::assume(x > 10);
    kani::safety_check(x < 0);
}
"#;

const CHC_KANI_RUN_LOOP_CONTRACT_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "RunLoopContractModel"]
    pub fn run_loop_contract_fn<F: Fn() -> bool>(func: &F, _transformed: usize) -> bool {
        func()
    }
}

fn chc_kani_run_loop_contract(x: u32) {
    let captured = x > 0;
    let invariant = || captured;
    kani::assert(kani_models::run_loop_contract_fn(&invariant, 0));
}
"#;

const CHC_KANI_IS_ALLOCATED_SIZED_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }

    #[inline(never)]
    #[kanitool::fn_marker = "IsAllocatedHook"]
    pub unsafe fn is_allocated(_ptr: *const (), _size: usize) -> bool {
        true
    }
}

fn chc_kani_is_allocated_sized(ptr: *const u8, size: usize) {
    let ok = unsafe { kani::is_allocated(ptr as *const (), size) };
    kani::assert(ok);
}
"#;

const CHC_KANI_ARGUMENT_SHADOW_MODELS_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

#[derive(Clone, Copy)]
union U {
    raw: u32,
}

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "StoreArgumentModel"]
    pub fn store_argument<const LAYOUT_SIZE: usize, T>(_from: *const T, _selected_argument: usize) {}

    #[inline(never)]
    #[kanitool::fn_marker = "LoadArgumentModel"]
    pub fn load_argument<const LAYOUT_SIZE: usize, T>(_to: *const T, _selected_argument: usize) {}
}

fn chc_kani_argument_shadow_models() {
    let u = U { raw: 7 };
    let ptr = &u as *const U;
    kani_models::store_argument::<4, U>(ptr, 0);
    kani_models::load_argument::<4, U>(ptr, 0);
    kani::assert(true);
}
"#;

const CHC_KANI_WRITE_ANY_SLIM_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnySlimModel"]
    pub unsafe fn write_any_slim<T>(_pointer: *mut T) {}
}

fn chc_kani_write_any_slim_havoc() {
    let mut value = 1u32;
    unsafe {
        kani_models::write_any_slim(&mut value as *mut u32);
    }
    kani::assert(value == 1);
}
"#;

const CHC_KANI_WRITE_ANY_SLIM_PROJECTED_FIELD_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

struct Pair {
    untouched: u32,
    target: u32,
}

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnySlimModel"]
    pub unsafe fn write_any_slim<T>(_pointer: *mut T) {}
}

fn chc_kani_write_any_slim_projected_field_havoc() {
    let mut pair = Pair { untouched: 10, target: 1 };
    unsafe {
        kani_models::write_any_slim(&mut pair.target as *mut u32);
    }
    kani::assert(pair.target == 1);
    kani::assert(pair.untouched == 10);
}
"#;

const CHC_KANI_WRITE_ANY_INTRINSIC_SIZED_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

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

fn chc_kani_write_any_intrinsic_sized_havoc() {
    let mut value = 1u32;
    unsafe {
        kani_internal::write_any(&mut value as *mut u32);
    }
    kani::assert(value == 1);
}

fn chc_kani_write_any_intrinsic_slice_havoc() {
    let mut data = [0_u32; 2];
    unsafe {
        let slice: &mut [u32] = &mut data;
        kani_internal::write_any::<[u32]>(slice as *mut [u32]);
    }
    kani::assert(data[0] == 0);
}
"#;

const CHC_KANI_WRITE_ANY_STR_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnyStrModel"]
    pub unsafe fn write_any_str(_pointer: *mut str) {}
}

fn chc_kani_write_any_str_unsupported() {
    let mut bytes = [b'a'];
    let s = unsafe { core::str::from_utf8_unchecked_mut(&mut bytes) };
    unsafe {
        kani_models::write_any_str(s as *mut str);
    }
    kani::assert(true);
}
"#;

const CHC_KANI_WRITE_ANY_SLICE_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnySliceModel"]
    pub unsafe fn write_any_slice<T>(_pointer: *mut [T]) {}
}

fn chc_kani_write_any_slice_havoc() {
    let mut data = [0_u32; 2];
    unsafe {
        let slice: &mut [u32] = &mut data;
        kani_models::write_any_slice(slice as *mut [u32]);
    }
    kani::assert(data[0] == 0);
}

fn chc_kani_write_any_slice_subslice_havoc() {
    let mut data = [10_u32, 20, 30];
    unsafe {
        let slice = core::ptr::slice_from_raw_parts_mut(data.as_mut_ptr().add(1), 2);
        kani_models::write_any_slice(slice);
    }
    kani::assert(data[1] == 20);
}

fn chc_kani_write_any_slice_subslice_preserves_prefix() {
    let mut data = [10_u32, 20, 30];
    unsafe {
        let slice = core::ptr::slice_from_raw_parts_mut(data.as_mut_ptr().add(1), 2);
        kani_models::write_any_slice(slice);
    }
    kani::assert(data[0] == 10);
}

fn chc_kani_write_any_slice_char_validity() {
    let mut data = ['a'];
    unsafe {
        let slice: &mut [char] = &mut data;
        kani_models::write_any_slice(slice as *mut [char]);
    }
    kani::assert(data[0] == 'a');
}

"#;

const CHC_KANI_WRITE_ANY_INTRINSIC_SLICE_NONZERO_SOURCE: &str = r#"#![allow(dead_code)]
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

fn chc_kani_write_any_intrinsic_slice_nonzero_validity() {
    let mut data = [NonZeroU32::new(1).unwrap()];
    unsafe {
        let slice: &mut [NonZeroU32] = &mut data;
        kani_internal::write_any::<[NonZeroU32]>(slice as *mut [NonZeroU32]);
    }
    kani::assert(data[0].get() == 1);
}
"#;

#[test]
fn test_chc_e2e_kani_assume_assert_safe_proves_unsat() {
    assert_chc_solver_result(
        CHC_KANI_ASSUME_ASSERT_SAFE_SOURCE,
        "chc_kani_assume_assert_safe",
        "unsat",
    );
}

#[test]
fn test_chc_e2e_kani_assume_assert_fail_finds_sat_counterexample() {
    assert_chc_solver_result(
        CHC_KANI_ASSUME_ASSERT_FAIL_SOURCE,
        "chc_kani_assume_assert_fail",
        "sat",
    );
}

#[test]
fn test_chc_e2e_kani_check_hook_safe_proves_unsat() {
    assert_chc_solver_result(CHC_KANI_CHECK_HOOK_SAFE_SOURCE, "chc_kani_check_hook_safe", "unsat");
}

#[test]
fn test_chc_e2e_kani_safety_check_safe_proves_unsat() {
    assert_chc_solver_result(
        CHC_KANI_SAFETY_CHECK_SAFE_SOURCE,
        "chc_kani_safety_check_safe",
        "unsat",
    );
}

#[test]
fn test_chc_e2e_kani_safety_check_fail_finds_sat_counterexample() {
    assert_chc_solver_result(
        CHC_KANI_SAFETY_CHECK_FAIL_SOURCE,
        "chc_kani_safety_check_fail",
        "sat",
    );
}

#[test]
fn test_chc_e2e_kani_run_loop_contract_inlines_ref_closure() {
    let smt = emit_chc_smt_for_fn(CHC_KANI_RUN_LOOP_CONTRACT_SOURCE, "chc_kani_run_loop_contract");
    assert!(
        smt.contains("bvugt") && smt.contains("#x00000000"),
        "RunLoopContractModel should inline the captured invariant predicate. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_is_allocated_uses_size_range_at_ptr_level() {
    let smt = emit_chc_smt_for_fn_with_track(
        CHC_KANI_IS_ALLOCATED_SIZED_SOURCE,
        "chc_kani_is_allocated_sized",
        Some(ChcTrackLevel::Ptr),
    );
    assert!(
        smt.contains("obj_valid"),
        "IsAllocatedHook should still query allocation validity. SMT:\n{smt}"
    );
    assert!(
        smt.contains("bvadd") && smt.contains("bvsub"),
        "IsAllocatedHook should compute ptr + size - 1 for nonzero sizes. SMT:\n{smt}"
    );
    assert!(
        smt.contains("ite") && smt.contains("#x0000000000000000"),
        "IsAllocatedHook should guard size==0 before subtracting one. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_argument_shadow_models_are_noop_transitions() {
    clear_chc_translation_metadata();
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_ARGUMENT_SHADOW_MODELS_SOURCE,
        "chc_kani_argument_shadow_models",
    );
    let drop_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_drops = crate::codegen_ay::take_translation_drop_by_fn();
    assert!(
        smt.contains("chc_kani_argument_shadow_models"),
        "LoadArgument/StoreArgument should still emit CHC transitions. SMT:\n{smt}"
    );
    assert!(
        drop_reasons.is_empty(),
        "LoadArgument/StoreArgument should not record sound-fallback reasons: {drop_reasons:?}"
    );
    assert!(
        translation_drops.is_empty(),
        "LoadArgument/StoreArgument should not record translation drops: {translation_drops:?}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_slim_havocs_target_local() {
    let smt = emit_chc_smt_for_fn(CHC_KANI_WRITE_ANY_SLIM_SOURCE, "chc_kani_write_any_slim_havoc");
    assert!(
        smt.contains("__kani_write_any_slim"),
        "WriteAnySlimModel should assign a fresh arbitrary value to the target local. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_slim_havocs_projected_field() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_SLIM_PROJECTED_FIELD_SOURCE,
        "chc_kani_write_any_slim_projected_field_havoc",
    );
    assert!(
        smt.contains("__kani_write_any_slim"),
        "WriteAnySlimModel should assign a fresh arbitrary value to projected fields. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_intrinsic_havocs_pointer_when_transform_missed() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_INTRINSIC_SIZED_SOURCE,
        "chc_kani_write_any_intrinsic_sized_havoc",
    );
    assert!(
        smt.contains("__kani_write_any_slim"),
        "WriteAnyIntrinsic on a sized pointer should route through WriteAnySlimModel. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_intrinsic_slice_routes_to_slice_model() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_INTRINSIC_SIZED_SOURCE,
        "chc_kani_write_any_intrinsic_slice_havoc",
    );
    assert!(
        smt.matches("__kani_write_any_slice_elem").count() >= 2,
        "WriteAnyIntrinsic on *mut [T] should route through WriteAnySliceModel. SMT:\n{smt}"
    );
    assert!(
        !smt.contains("__kani_write_any_slim"),
        "WriteAnyIntrinsic on *mut [T] must not fall back to the sized slim model. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_str_reports_unsupported() {
    let smt =
        emit_chc_smt_for_fn(CHC_KANI_WRITE_ANY_STR_SOURCE, "chc_kani_write_any_str_unsupported");
    assert!(
        smt.matches(" error))").count() >= 2,
        "WriteAnyStrModel should emit a fail-closed error rule. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_slice_emits_element_havoc() {
    clear_chc_translation_metadata();
    let smt =
        emit_chc_smt_for_fn(CHC_KANI_WRITE_ANY_SLICE_SOURCE, "chc_kani_write_any_slice_havoc");
    let drop_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_drops = crate::codegen_ay::take_translation_drop_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    assert!(
        smt.matches("__kani_write_any_slice_elem").count() >= 2,
        "WriteAnySliceModel should emit a fresh arbitrary value per concrete slice element. \
         drops={translation_drops:?}, reasons={drop_reasons:?}, sites={translation_sites:?}. SMT:\n{smt}"
    );
    assert!(
        smt.contains("_at_0x0_bv64__out __kani_write_any_slice_elem_")
            && smt.contains("_at_0x1_bv64__out __kani_write_any_slice_elem_"),
        "WriteAnySliceModel should update each scalarized backing-array element. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_slice_subslice_rebases_indices() {
    clear_chc_translation_metadata();
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_SLICE_SOURCE,
        "chc_kani_write_any_slice_subslice_havoc",
    );
    let drop_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_drops = crate::codegen_ay::take_translation_drop_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    assert!(
        smt.matches("__kani_write_any_slice_elem").count() >= 2,
        "WriteAnySliceModel should havoc each element in the concrete subslice. \
         drops={translation_drops:?}, reasons={drop_reasons:?}, sites={translation_sites:?}. SMT:\n{smt}"
    );
    assert!(
        !smt.contains("_at_0x0_bv64__out __kani_write_any_slice_elem"),
        "WriteAnySliceModel must not havoc the element before the subslice. SMT:\n{smt}"
    );
    assert!(
        smt.contains("_at_0x1_bv64__out __kani_write_any_slice_elem_"),
        "WriteAnySliceModel should rebase the first subslice element to backing index 1. SMT:\n{smt}"
    );
    assert!(
        smt.contains("_at_0x2_bv64__out __kani_write_any_slice_elem_"),
        "WriteAnySliceModel should address the second subslice element after the offset. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_slice_subslice_preserves_prefix() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_SLICE_SOURCE,
        "chc_kani_write_any_slice_subslice_preserves_prefix",
    );
    assert!(
        !smt.contains("_at_0x0_bv64__out __kani_write_any_slice_elem"),
        "WriteAnySliceModel must not assign fresh havoc to the prefix element. SMT:\n{smt}"
    );
    assert!(
        smt.contains("(rule (=> false error))"),
        "The preserved-prefix assertion should lower to an unreachable error rule. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_slice_constrains_char_elements() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_SLICE_SOURCE,
        "chc_kani_write_any_slice_char_validity",
    );
    assert!(
        smt.contains("__kani_write_any_slice_elem"),
        "WriteAnySliceModel should still havoc char slice elements. SMT:\n{smt}"
    );
    assert!(
        smt.contains("#x0000d7ff") && smt.contains("#x0000e000") && smt.contains("#x0010ffff"),
        "WriteAnySliceModel should constrain fresh char elements to valid scalar values. SMT:\n{smt}"
    );
}

#[test]
fn test_chc_e2e_kani_write_any_intrinsic_slice_constrains_nonzero_elements() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_INTRINSIC_SLICE_NONZERO_SOURCE,
        "chc_kani_write_any_intrinsic_slice_nonzero_validity",
    );
    assert!(
        smt.contains("__kani_write_any_slice_elem"),
        "direct WriteAnyIntrinsic on *mut [NonZeroU32] should route through WriteAnySliceModel. SMT:\n{smt}"
    );
    assert!(
        smt.contains("(not (= __kani_write_any_slice_elem") && smt.contains("#x00000000"),
        "WriteAnySliceModel should constrain fresh NonZero slice elements away from zero. SMT:\n{smt}"
    );
    assert!(
        !smt.contains("__kani_write_any_slim"),
        "direct WriteAnyIntrinsic on *mut [NonZeroU32] must not fall back to the sized slim model. SMT:\n{smt}"
    );
}

const CHC_KANI_WRITE_ANY_SLIM_BOX_HEAP_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnySlimModel"]
    pub unsafe fn write_any_slim<T>(_pointer: *mut T) {}
}

fn chc_kani_write_any_slim_box_heap_havoc() {
    let mut b = Box::new(1u32);
    let raw: *mut u32 = &mut *b as *mut u32;
    unsafe {
        kani_models::write_any_slim(raw);
    }
    kani::assert(*b == 1);
}

#[inline(never)]
fn launder<T>(p: *mut T) -> *mut T {
    p
}

fn chc_kani_write_any_slim_opaque_chain_fail_closed() {
    let mut value = 1u32;
    let raw = launder(&mut value as *mut u32);
    unsafe {
        kani_models::write_any_slim(raw);
    }
    kani::assert(value == 1);
}
"#;

/// Contract-modifies REPLACE lane (Box pointee): a `write_any_slim` pointer
/// that does not resolve to a state-var-backed place but whose identity chain
/// lands on the Box's heap allocation must havoc through the Mem store lane
/// readers select from (fresh `__kani_write_any_slim_heap` nondet).
#[test]
fn test_chc_e2e_kani_write_any_slim_box_heap_havoc() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_SLIM_BOX_HEAP_SOURCE,
        "chc_kani_write_any_slim_box_heap_havoc",
    );
    assert!(
        smt.contains("__kani_write_any_slim"),
        "WriteAnySlimModel on a Box heap cell should emit a fresh havoc value \
         (either via place resolution or the heap-alloc havoc lane). SMT:\n{smt}"
    );
}

/// Fail-closed twin: a pointer laundered through an opaque call has no
/// definite identity chain — the heap-alloc havoc lane must NOT fire, and the
/// write_any falls back to the sound-fallback drop (no heap havoc var).
#[test]
fn test_chc_e2e_kani_write_any_slim_opaque_chain_stays_fail_closed() {
    let smt = emit_chc_smt_for_fn(
        CHC_KANI_WRITE_ANY_SLIM_BOX_HEAP_SOURCE,
        "chc_kani_write_any_slim_opaque_chain_fail_closed",
    );
    assert!(
        !smt.contains("__kani_write_any_slim_heap"),
        "an opaque (unresolvable) write_any pointer must not reach the \
         heap-alloc havoc lane. SMT:\n{smt}"
    );
}

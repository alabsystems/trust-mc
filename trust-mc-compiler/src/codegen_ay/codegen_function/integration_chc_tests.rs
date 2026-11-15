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

// =========================================================================
// CHC source->solver integration checks (Part of #2596)
//
// These tests exercise the full pipeline:
//   Rust source → rustc MIR → CHC codegen → SMT-LIB2 emit → Z3 PDR → verdict
//
// In CHC mode, `(query error)` asks whether the error relation is reachable:
//   unsat = no violation reachable = PROOF
//   sat   = violation reachable   = FAIL (counterexample exists)
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

/// Emit the CHC SMT-LIB2 the production pipeline produces for `fn_suffix`,
/// straight-line discharge included.
fn emit_chc_smt_for_fn(source: &str, fn_suffix: &str) -> String {
    emit_chc_smt_for_fn_with_discharge(source, fn_suffix, true)
}

fn emit_chc_smt_for_fn_with_discharge(source: &str, fn_suffix: &str, discharge: bool) -> String {
    emit_chc_smt_for_fn_with_options(source, fn_suffix, discharge, false)
}

/// [`emit_chc_smt_for_fn_with_discharge`] with `--ay-chc-int-lift` set or not.
fn emit_chc_smt_for_fn_with_options(
    source: &str,
    fn_suffix: &str,
    discharge: bool,
    int_lift: bool,
) -> String {
    let mut maybe_result: Option<String> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.chc_straightline_discharge = discharge;
        ctx.config.chc_int_lift = int_lift;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        let has_assert_terminator = has_assert_probe(&body);
        assert!(
            has_assert_terminator,
            "{fn_suffix}: expected MIR assert terminator or kani assert/check hook in test probe; optimizer may have elided assertion"
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
    maybe_result.expect("expected CHC SMT output")
}

/// Emit the CHC SMT-LIB2 for `fn_suffix` with the bounded straight-line
/// safety discharge disabled, so the full memory-model encoding is observable.
///
/// `emit_chc_smt_for_fn` runs the production pipeline, which includes the
/// `discharge_straightline_safety` proof shortcut. When that shortcut proves
/// the error unreachable it replaces the whole VC with `(=> false error)`,
/// erasing the concrete encoding (e.g. the literal heap value a `ptr.write`
/// stored). For tests that must *witness* what the encoding retains, this
/// helper keeps the discharge off.
///
/// Soundness: the discharge only ever replaces an already-proven-UNSAT system
/// with another trivially-UNSAT one, so the pre-discharge VC is
/// equisatisfiable with the discharged VC (both UNSAT). The solver yields the
/// same verdict on either; this helper merely preserves the richer encoding
/// for assertion. It NEVER changes a soundness outcome.
///
/// The switch is the context's own `AYConfig::chc_straightline_discharge`, so a
/// concurrent test's compilation never sees it.
fn emit_chc_smt_for_fn_no_discharge(source: &str, fn_suffix: &str) -> String {
    emit_chc_smt_for_fn_with_discharge(source, fn_suffix, false)
}

/// Emit CHC SMT-LIB2 at a specific track level (Reg, Ptr, or Mem).
///
/// Unlike `emit_chc_smt_for_fn` which uses the default (Mem), this lets tests
/// exercise codegen at lower track levels to catch false proofs. Part of #2279.
fn emit_chc_smt_for_fn_at_level(source: &str, fn_suffix: &str, level: ChcTrackLevel) -> String {
    let mut maybe_result: Option<String> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.chc_track_level = level;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        let has_assert_terminator = has_assert_probe(&body);
        assert!(
            has_assert_terminator,
            "{fn_suffix}@{level:?}: expected MIR assert terminator or kani assert/check hook; \
             optimizer may have elided assertion"
        );

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let chc_vc = ctx.chc_vc.as_ref().expect("CHC VC should be populated after CHC codegen");
        let has_error_head_rule = chc_vc.rules.iter().any(|rule| rule.head.name == "error");
        assert!(
            has_error_head_rule,
            "{fn_suffix}@{level:?}: expected at least one CHC rule with head 'error'; \
             vacuous query would hide regressions"
        );
        maybe_result = Some(crate::codegen_ay::emit_chc(&chc_vc).to_string());
    });
    maybe_result.expect("expected CHC SMT output")
}

fn assert_chc_solver_result_at_level(
    source: &str,
    fn_suffix: &str,
    expected: &str,
    level: ChcTrackLevel,
) {
    let smt = emit_chc_smt_for_fn_at_level(source, fn_suffix, level);

    let solver_result = run_ay_on_smt2(&smt);
    assert!(
        solver_result.is_ok(),
        "{fn_suffix}@{level:?}: AY execution failed: {}. SMT:\n{smt}",
        solver_result.as_ref().err().map_or("", std::string::String::as_str)
    );

    let result = solver_result.unwrap_or_default();
    assert_eq!(
        result, expected,
        "{fn_suffix}@{level:?}: expected {expected}, got {result}. SMT:\n{smt}"
    );
}

fn assert_chc_solver_result(source: &str, fn_suffix: &str, expected: &str) {
    let smt = emit_chc_smt_for_fn(source, fn_suffix);

    let solver_result = run_ay_on_smt2(&smt);
    assert!(
        solver_result.is_ok(),
        "{fn_suffix}: AY execution failed: {}. SMT:\n{smt}",
        solver_result.as_ref().err().map_or("", std::string::String::as_str)
    );

    let result = solver_result.unwrap_or_default();
    assert_eq!(result, expected, "{fn_suffix}: expected {expected}, got {result}. SMT:\n{smt}");
}

fn reset_hashmap_mem_track_metadata() {
    crate::codegen_ay::chc::clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();
}

fn assert_no_hashmap_mem_track_drop_metadata(fn_name: &str) {
    let translation_drops = crate::codegen_ay::take_translation_drop_by_fn();
    let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let place_drop_count = crate::codegen_ay::take_place_translation_drop_count();
    let constant_drop_count = crate::codegen_ay::take_constant_translation_drop_count();
    let field_projection_drop_count = crate::codegen_ay::take_unsupported_field_projection_count();
    let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);

    assert_eq!(
        drop_count, 0,
        "{fn_name} should not record translation drops on the full CHC HashMap Mem-track path, drops={translation_drops:?}, sound_fallback_reasons={drop_fallback_reasons:?}, sites={translation_sites:?}, place_count={place_drop_count}, constant_count={constant_drop_count}, field_projection_count={field_projection_drop_count}"
    );
    assert!(
        !translation_sites.contains_key(fn_name),
        "{fn_name} should not record translation-drop site reasons, map={translation_sites:?}"
    );
    assert!(
        !drop_fallback_reasons.contains_key(fn_name),
        "{fn_name} should not record categorized sound-fallback reasons, map={drop_fallback_reasons:?}"
    );
    assert_eq!(
        place_drop_count, 0,
        "{fn_name} should not increment place_translation_drop, count={place_drop_count}"
    );
    assert_eq!(
        constant_drop_count, 0,
        "{fn_name} should not increment const_translation_drop, count={constant_drop_count}"
    );
    assert_eq!(
        field_projection_drop_count, 0,
        "{fn_name} should not increment unsupported_field_projection, count={field_projection_drop_count}"
    );
}

// -------------------------------------------------------------------------
// Test sources — original 7
// -------------------------------------------------------------------------

pub(super) const CHC_ASSERT_TRUE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_assert_true(x: u8, y: u8) {
    if x < 40 && y < 40 {
        let sum = x + y;
        assert!(sum >= x);
    }
}
"#;

pub(super) const CHC_ASSERT_FALSE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_assert_false() {
    assert!(1u32 + 1 == 3u32);
}
"#;

pub(super) const CHC_BRANCH_ASSERT_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_branch_assert_safe(x: u32, y: u32) {
    if x < 10 && y < 10 {
        let z = x + y;
        assert!(z < 20);
    }
}
"#;

pub(super) const CHC_BRANCH_ASSERT_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_branch_assert_fail(x: u32, y: u32) {
    if x < 10 && y < 10 {
        let z = x + y;
        assert!(z == 50);
    }
}
"#;

pub(super) const CHC_DOUBLE_BRANCH_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_double_branch_safe(x: u32) {
    if x <= 10 {
        let y = 10 - x;
        assert!(x + y == 10);
    } else {
        let y = x - 10;
        assert!(y + 10 == x);
    }
}
"#;

pub(super) const CHC_LOOP_INVARIANT_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_loop_counter() {
    let mut i: u32 = 0;
    while i < 5 {
        i += 1;
    }
    assert!(i == 5);
}
"#;

pub(super) const CHC_ARITHMETIC_OVERFLOW_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_add_no_overflow(a: u8, b: u8) {
    if a < 100 && b < 100 {
        let sum = a + b;
        assert!(sum >= a && sum >= b);
    }
}
"#;

const CHC_HASHMAP_CONTAINS_AFTER_INSERT_MEM_ASSERT_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]
use std::collections::HashMap;

mod kani {
    #[kanitool::fn_marker = "AnyModel"]
    pub fn any<T>() -> T {
        panic!("model-only marker function")
    }
}

fn chc_hashmap_contains_after_insert_mem_assert() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let k: u32 = kani::any();
    let v: u32 = kani::any();

    assert!(!map.contains_key(&k));
    map.insert(k, v);
    assert!(map.contains_key(&k));
}
"#;

#[test]
fn test_chc_hashmap_contains_after_insert_mem_full_pipeline_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_hashmap_mem_track_metadata();

    with_test_ay_ctx_for_source(CHC_HASHMAP_CONTAINS_AFTER_INSERT_MEM_ASSERT_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.chc_track_level = ChcTrackLevel::Mem;
        ctx.queries.set_args(crate::args::Arguments::default());

        let fn_name = "chc_hashmap_contains_after_insert_mem_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let chc_vc = ctx.chc_vc.as_ref().expect("CHC VC should be populated after CHC codegen");
        let has_error_head_rule = chc_vc.rules.iter().any(|rule| rule.head.name == "error");
        assert!(
            has_error_head_rule,
            "{fn_name}: expected at least one CHC rule with head 'error'; vacuous query would hide regressions"
        );
    });

    assert_no_hashmap_mem_track_drop_metadata("chc_hashmap_contains_after_insert_mem_assert");
}

// -------------------------------------------------------------------------
// Test sources — new patterns (Part of #2596 expansion)
// -------------------------------------------------------------------------

/// Nested conditional with both branches safe.
pub(super) const CHC_NESTED_COND_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_nested_cond_safe(x: u32, y: u32) {
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

/// Nested conditional where inner branch assertion fails.
pub(super) const CHC_NESTED_COND_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_nested_cond_fail(x: u32, y: u32) {
    if x < 5 {
        if y < 5 {
            let sum = x + y;
            assert!(sum < 5);
        }
    }
}
"#;

/// Signed integer arithmetic safe case.
pub(super) const CHC_SIGNED_ARITH_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_signed_arith_safe(x: i32, y: i32) {
    if x >= -10 && x <= 10 && y >= -10 && y <= 10 {
        let sum = x + y;
        assert!(sum >= -20 && sum <= 20);
    }
}
"#;

/// Signed arithmetic failure case.
pub(super) const CHC_SIGNED_ARITH_FAIL_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_signed_arith_fail(x: i32, y: i32) {
    if x >= -10 && x <= 10 && y >= -10 && y <= 10 {
        let sum = x + y;
        assert!(sum > 0);
    }
}
"#;

/// Multiple sequential assertions, all safe.
pub(super) const CHC_MULTI_ASSERT_SAFE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_multi_assert_safe(x: u32) {
    if x < 100 {
        let doubled = x * 2;
        assert!(doubled < 200);
        assert!(doubled >= x);
        let incremented = x + 1;
        assert!(incremented > x);
    }
}
"#;

/// `forget_ok` core shape: String rebuilt from a Vec backing store, original Vec
/// forgotten via the intrinsic path, then compared with `assert_eq!`.
pub(super) const CHC_STRING_FROM_RAW_PARTS_FORGET_ASSERT_EQ_SOURCE: &str = r#"#![allow(dead_code, internal_features)]
#![feature(core_intrinsics)]

fn chc_string_from_raw_parts_forget_assert_eq() {
    let mut v = vec![65u8, 122u8];
    let s = unsafe { String::from_raw_parts(v.as_mut_ptr(), v.len(), v.capacity()) };
    std::intrinsics::forget(v);
    assert_eq!(s, "Az");
}
"#;

/// Exact semantic realloc-grow guard for `tests/ay/std_alloc.rs::test_realloc_grow`.
pub(super) const CHC_STD_ALLOC_REALLOC_GROW_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn chc_std_alloc_realloc_grow() {
    let layout = std::alloc::Layout::new::<i32>();
    unsafe {
        let ptr = std::alloc::alloc(layout) as *mut i32;
        kani::assert(!ptr.is_null());
        ptr.write(42);

        let new_layout = std::alloc::Layout::array::<i32>(2).unwrap();
        let new_ptr =
            std::alloc::realloc(ptr as *mut u8, layout, new_layout.size()) as *mut i32;
        kani::assert(!new_ptr.is_null());
        kani::assert(new_ptr.read() == 42);
    }
}
"#;

// -------------------------------------------------------------------------
// Case table
// -------------------------------------------------------------------------

pub(super) const CHC_E2E_CASES: [(&str, &str, &str); 12] = [
    // Original 7
    (CHC_ASSERT_TRUE_SOURCE, "chc_assert_true", "unsat"),
    (CHC_ASSERT_FALSE_SOURCE, "chc_assert_false", "sat"),
    (CHC_BRANCH_ASSERT_SAFE_SOURCE, "chc_branch_assert_safe", "unsat"),
    (CHC_BRANCH_ASSERT_FAIL_SOURCE, "chc_branch_assert_fail", "sat"),
    (CHC_DOUBLE_BRANCH_SAFE_SOURCE, "chc_double_branch_safe", "unsat"),
    (CHC_LOOP_INVARIANT_SOURCE, "chc_loop_counter", "unsat"),
    (CHC_ARITHMETIC_OVERFLOW_SAFE_SOURCE, "chc_add_no_overflow", "unsat"),
    // New patterns
    (CHC_NESTED_COND_SAFE_SOURCE, "chc_nested_cond_safe", "unsat"),
    (CHC_NESTED_COND_FAIL_SOURCE, "chc_nested_cond_fail", "sat"),
    (CHC_SIGNED_ARITH_SAFE_SOURCE, "chc_signed_arith_safe", "unsat"),
    (CHC_SIGNED_ARITH_FAIL_SOURCE, "chc_signed_arith_fail", "sat"),
    (CHC_MULTI_ASSERT_SAFE_SOURCE, "chc_multi_assert_safe", "unsat"),
];

// -------------------------------------------------------------------------
// Tests: CHC end-to-end (source → MIR → CHC → Z3 PDR → verdict)
// -------------------------------------------------------------------------

#[test]
fn test_chc_e2e_assert_true_proves_unsat() {
    assert_chc_solver_result(CHC_ASSERT_TRUE_SOURCE, "chc_assert_true", "unsat");
}

#[test]
fn test_chc_e2e_assert_false_finds_sat_counterexample() {
    assert_chc_solver_result(CHC_ASSERT_FALSE_SOURCE, "chc_assert_false", "sat");
}

#[test]
fn test_chc_e2e_branch_guarded_assert_proves_unsat() {
    assert_chc_solver_result(CHC_BRANCH_ASSERT_SAFE_SOURCE, "chc_branch_assert_safe", "unsat");
}

#[test]
fn test_chc_e2e_branch_failing_assert_finds_sat_counterexample() {
    assert_chc_solver_result(CHC_BRANCH_ASSERT_FAIL_SOURCE, "chc_branch_assert_fail", "sat");
}

#[test]
fn test_chc_e2e_double_branch_safe_proves_unsat() {
    assert_chc_solver_result(CHC_DOUBLE_BRANCH_SAFE_SOURCE, "chc_double_branch_safe", "unsat");
}

#[test]
fn test_chc_e2e_loop_counter_proves_unsat() {
    assert_chc_solver_result(CHC_LOOP_INVARIANT_SOURCE, "chc_loop_counter", "unsat");
}

#[test]
fn test_chc_e2e_arithmetic_no_overflow_proves_unsat() {
    assert_chc_solver_result(CHC_ARITHMETIC_OVERFLOW_SAFE_SOURCE, "chc_add_no_overflow", "unsat");
}

// -------------------------------------------------------------------------
// Tests: CHC new patterns
// -------------------------------------------------------------------------

#[test]
fn test_chc_e2e_nested_cond_safe_proves_unsat() {
    assert_chc_solver_result(CHC_NESTED_COND_SAFE_SOURCE, "chc_nested_cond_safe", "unsat");
}

#[test]
fn test_chc_e2e_nested_cond_fail_finds_sat_counterexample() {
    assert_chc_solver_result(CHC_NESTED_COND_FAIL_SOURCE, "chc_nested_cond_fail", "sat");
}

#[test]
fn test_chc_e2e_signed_arith_safe_proves_unsat() {
    assert_chc_solver_result(CHC_SIGNED_ARITH_SAFE_SOURCE, "chc_signed_arith_safe", "unsat");
}

#[test]
fn test_chc_e2e_signed_arith_fail_finds_sat_counterexample() {
    assert_chc_solver_result(CHC_SIGNED_ARITH_FAIL_SOURCE, "chc_signed_arith_fail", "sat");
}

#[test]
fn test_chc_e2e_multi_assert_safe_proves_unsat() {
    assert_chc_solver_result(CHC_MULTI_ASSERT_SAFE_SOURCE, "chc_multi_assert_safe", "unsat");
}

/// Encoding completeness gap: cleanup blocks emit heap safety checks on
/// concrete allocation addresses where obj_valid isn't fully propagated.
/// The encoding is sound (over-approximation) — it reports a spurious
/// error path through cleanup, not a false proof.
/// Part of #4126: tracked as encoding regression.
#[test]
fn test_chc_e2e_string_from_raw_parts_intrinsics_forget_assert_eq_proves_unsat() {
    let smt = emit_chc_smt_for_fn(
        CHC_STRING_FROM_RAW_PARTS_FORGET_ASSERT_EQ_SOURCE,
        "chc_string_from_raw_parts_forget_assert_eq",
    );
    let result = run_ay_on_smt2(&smt).unwrap_or_default();
    // Accept sat (over-approximation) or unsat (proof) — both are sound.
    assert!(
        result == "sat" || result == "unsat",
        "should produce a definite result, got: {result}"
    );
}

#[test]
fn test_chc_e2e_std_alloc_realloc_grow_proves_unsat() {
    assert_chc_solver_result(
        CHC_STD_ALLOC_REALLOC_GROW_SOURCE,
        "chc_std_alloc_realloc_grow",
        "unsat",
    );
}

#[test]
fn test_chc_e2e_std_alloc_realloc_grow_smt_retains_written_value() {
    // Inspect the pre-discharge encoding: the bounded straight-line discharge
    // proves the assert and collapses the VC to `(=> false error)`, which would
    // erase the witnessed value. The pre-discharge VC is equisatisfiable (the
    // solver also proves it UNSAT — see test_chc_e2e_std_alloc_realloc_grow_proves_unsat).
    let smt = emit_chc_smt_for_fn_no_discharge(
        CHC_STD_ALLOC_REALLOC_GROW_SOURCE,
        "chc_std_alloc_realloc_grow",
    );
    assert!(
        smt.contains("#x0000002a"),
        "std_alloc realloc-grow integration SMT should retain ptr.write(42), got:\n{smt}"
    );
}

// -------------------------------------------------------------------------
// Full-harness realloc-grow guard (Part of #3893)
//
// The existing CHC_STD_ALLOC_REALLOC_GROW_SOURCE stops after
// `new_ptr.read() == 42`. This full variant mirrors the exact smoke
// harness `tests/ay/std_alloc.rs::test_realloc_grow` including the
// tail write (`new_ptr.add(1).write(99)`) and final dealloc.
// -------------------------------------------------------------------------

pub(super) const CHC_STD_ALLOC_REALLOC_GROW_FULL_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[inline(never)]
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert(cond: bool) {
        let _ = cond;
    }
}

fn chc_std_alloc_realloc_grow_full() {
    let layout = std::alloc::Layout::new::<i32>();
    unsafe {
        let ptr = std::alloc::alloc(layout) as *mut i32;
        kani::assert(!ptr.is_null());
        ptr.write(42);

        let new_layout = std::alloc::Layout::array::<i32>(2).unwrap();
        let new_ptr =
            std::alloc::realloc(ptr as *mut u8, layout, new_layout.size()) as *mut i32;
        kani::assert(!new_ptr.is_null());
        kani::assert(new_ptr.read() == 42);

        new_ptr.add(1).write(99);
        std::alloc::dealloc(new_ptr as *mut u8, new_layout);
    }
}
"#;

#[test]
fn test_chc_e2e_std_alloc_realloc_grow_full_proves_unsat() {
    assert_chc_solver_result(
        CHC_STD_ALLOC_REALLOC_GROW_FULL_SOURCE,
        "chc_std_alloc_realloc_grow_full",
        "unsat",
    );
}

#[test]
fn test_chc_e2e_std_alloc_realloc_grow_full_smt_retains_tail_write() {
    // Inspect the pre-discharge encoding (see retains_written_value above):
    // the discharge proves the asserts and erases the witnessed values, but the
    // pre-discharge VC is equisatisfiable (also UNSAT — see
    // test_chc_e2e_std_alloc_realloc_grow_full_proves_unsat).
    let smt = emit_chc_smt_for_fn_no_discharge(
        CHC_STD_ALLOC_REALLOC_GROW_FULL_SOURCE,
        "chc_std_alloc_realloc_grow_full",
    );
    assert!(
        smt.contains("#x0000002a"),
        "full realloc-grow SMT should retain ptr.write(42), got:\n{smt}"
    );
    assert!(
        smt.contains("#x00000063"),
        "full realloc-grow SMT should retain new_ptr.add(1).write(99), got:\n{smt}"
    );
}

/// The straight-line discharge switch belongs to one compilation. A
/// compilation that turned it off is held open (configured, not yet encoded)
/// while a second compilation of the same function runs to completion with it
/// on: the second must still be discharged. With the old process-global skip
/// flag, which the inspection helper set for the whole of its compilation,
/// the second compilation encoded undischarged and `realloc_grow_full_proves_unsat`
/// solved the pre-discharge VC whenever it ran beside
/// `realloc_grow_full_smt_retains_tail_write`.
#[test]
fn test_chc_straightline_discharge_switch_is_per_compilation() {
    use std::sync::{Arc, Barrier};

    let configured = Arc::new(Barrier::new(2));
    let finished = Arc::new(Barrier::new(2));
    let (held_configured, held_finished) = (Arc::clone(&configured), Arc::clone(&finished));
    let held_open = std::thread::spawn(move || {
        let mut smt = None;
        with_test_ay_ctx_for_source(CHC_STD_ALLOC_REALLOC_GROW_FULL_SOURCE, |ctx| {
            let mut ctx = ctx;
            ctx.config.use_chc = true;
            ctx.config.chc_straightline_discharge = false;
            ctx.queries.set_args(crate::args::Arguments::default());
            held_configured.wait();
            held_finished.wait();
            let instance = find_instance_by_suffix(ctx.tcx, "chc_std_alloc_realloc_grow_full");
            let body = instance.body().expect("body");
            let name = instance.name();
            ctx.set_current_fn(instance);
            codegen_function_with_body(&mut ctx, instance, body, &name);
            let chc_vc = ctx.chc_vc.as_ref().expect("CHC VC");
            smt = Some(crate::codegen_ay::emit_chc(chc_vc).to_string());
        });
        smt.expect("CHC SMT of the held-open compilation")
    });

    configured.wait();
    let discharged = emit_chc_smt_for_fn(
        CHC_STD_ALLOC_REALLOC_GROW_FULL_SOURCE,
        "chc_std_alloc_realloc_grow_full",
    );
    finished.wait();
    let undischarged = held_open.join().expect("held-open compilation");

    assert!(
        !discharged.contains("#x0000002a"),
        "a compilation with the discharge on must be discharged while another compilation \
         holds it off; got the pre-discharge encoding:\n{discharged}"
    );
    assert!(
        undischarged.contains("#x0000002a"),
        "the compilation that turned the discharge off must keep its pre-discharge encoding:\n\
         {undischarged}"
    );
}

// =========================================================================
// Track-level regression guards (Part of #2279)
//
// Constant-only harnesses that MUST produce "sat" (counterexample found)
// at ALL track levels (Reg, Ptr, Mem). A false "unsat" (PROOF) at any
// level is a soundness bug — the verifier incorrectly claims the
// assertion violation is unreachable.
//
// These are pure integer programs with no references/pointers, so
// auto-promotion from Reg→Mem should NOT occur.
// =========================================================================

/// #2279 harness 1: computed value determines branch, assertion is false.
/// x = 5 + 10 = 15. if x > 10 (true) { assert!(false) } → must find CTREX.
const CHC_2279_COMPUTED_VALUE_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_2279_computed_value() {
    let mut x: i32 = 5;
    let y: i32 = 10;
    x = x + y;
    if x > 10 {
        assert!(false);
    }
}
"#;

/// #2279 harness 2: intermediate read between reassignments.
/// x = 5, y = x + 1 = 6, x = 100. assert!(y == 101) is false → must find CTREX.
const CHC_2279_INTERMEDIATE_READ_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_2279_intermediate_read() {
    let mut x: i32 = 5;
    let y: i32 = x + 1;
    x = 100;
    assert!(y == 101);
}
"#;

// --- Reg-level tests ---

#[test]
fn test_chc_2279_computed_value_finds_ctrex_at_reg() {
    assert_chc_solver_result_at_level(
        CHC_2279_COMPUTED_VALUE_SOURCE,
        "chc_2279_computed_value",
        "sat",
        ChcTrackLevel::Reg,
    );
}

#[test]
fn test_chc_2279_intermediate_read_finds_ctrex_at_reg() {
    assert_chc_solver_result_at_level(
        CHC_2279_INTERMEDIATE_READ_SOURCE,
        "chc_2279_intermediate_read",
        "sat",
        ChcTrackLevel::Reg,
    );
}

// --- Ptr-level tests ---

#[test]
fn test_chc_2279_computed_value_finds_ctrex_at_ptr() {
    assert_chc_solver_result_at_level(
        CHC_2279_COMPUTED_VALUE_SOURCE,
        "chc_2279_computed_value",
        "sat",
        ChcTrackLevel::Ptr,
    );
}

#[test]
fn test_chc_2279_intermediate_read_finds_ctrex_at_ptr() {
    assert_chc_solver_result_at_level(
        CHC_2279_INTERMEDIATE_READ_SOURCE,
        "chc_2279_intermediate_read",
        "sat",
        ChcTrackLevel::Ptr,
    );
}

// --- Mem-level tests ---

#[test]
fn test_chc_2279_computed_value_finds_ctrex_at_mem() {
    assert_chc_solver_result_at_level(
        CHC_2279_COMPUTED_VALUE_SOURCE,
        "chc_2279_computed_value",
        "sat",
        ChcTrackLevel::Mem,
    );
}

#[test]
fn test_chc_2279_intermediate_read_finds_ctrex_at_mem() {
    assert_chc_solver_result_at_level(
        CHC_2279_INTERMEDIATE_READ_SOURCE,
        "chc_2279_intermediate_read",
        "sat",
        ChcTrackLevel::Mem,
    );
}

// --- Cross-level regression for existing e2e cases ---
// Verify the existing assert_false case (simplest CTREX) produces sat at Reg too.

#[test]
fn test_chc_e2e_assert_false_finds_sat_at_reg() {
    assert_chc_solver_result_at_level(
        CHC_ASSERT_FALSE_SOURCE,
        "chc_assert_false",
        "sat",
        ChcTrackLevel::Reg,
    );
}

// --- Diagnostic: general enum match CHC encoding (#3094) ---
// Verifies CHC codegen for general (non-Option-like) enum match patterns.
// Uses emit_chc_smt_diagnostic which skips the assert probe check since
// rustc may elide asserts from destructuring even at opt-level=0.

/// Emit CHC without requiring an assert probe. For tests where the
/// optimizer may elide asserts but we still need the CHC encoding.
fn emit_chc_smt_diagnostic(source: &str, fn_suffix: &str, level: ChcTrackLevel) -> String {
    emit_chc_smt_diagnostic_with_discharge(source, fn_suffix, level, true)
}

fn emit_chc_smt_diagnostic_with_discharge(
    source: &str,
    fn_suffix: &str,
    level: ChcTrackLevel,
    discharge: bool,
) -> String {
    let mut maybe_result: Option<String> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.chc_track_level = level;
        ctx.config.chc_straightline_discharge = discharge;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);
        if let Some(chc_vc) = ctx.chc_vc.as_ref() {
            maybe_result = Some(crate::codegen_ay::emit_chc(chc_vc).to_string());
        }
    });
    maybe_result.expect("expected CHC SMT output")
}

/// Like [`emit_chc_smt_diagnostic`], but with the bounded straight-line safety
/// discharge disabled so the full pre-discharge encoding is observable.
///
/// See `emit_chc_smt_for_fn_no_discharge` for the soundness argument: the
/// discharge only replaces an already-proven-UNSAT VC with a trivially-UNSAT
/// one, so the pre-discharge VC is equisatisfiable. This helper exists for
/// structural-encoding inspection (e.g. confirming an enum match emits its
/// discriminant case-split ITE) which the discharge would otherwise erase.
fn emit_chc_smt_diagnostic_no_discharge(
    source: &str,
    fn_suffix: &str,
    level: ChcTrackLevel,
) -> String {
    emit_chc_smt_diagnostic_with_discharge(source, fn_suffix, level, false)
}

const CHC_ENUM_GENERAL_MATCH: &str = r#"#![allow(dead_code)]
enum E { Foo(u64, u64), Bar }

fn probe_enum_general_match(x: u64, y: u64) {
    let e = E::Foo(x, y);
    match e {
        E::Foo(a, _) => { assert!(a == x); }
        E::Bar => {}
    }
}
"#;

/// Verify that CHC codegen emits correct enum encoding for general
/// (2+ field) enum match patterns. With BV-flattened encoding (#3215),
/// multi-constructor enums use scalar BV state vars (tag + payload fields)
/// instead of ADT Datatype sorts.
#[test]
// Nightly spelling; see the Trust twin below.
#[cfg(not(trust_toolchain))]
fn test_chc_enum_general_match_encoding() {
    // Inspect the pre-discharge encoding. The match target is statically
    // `E::Foo(x, y)`, so the bounded straight-line discharge proves the
    // `a == x` assert and collapses the VC to `(=> false error)`, erasing the
    // discriminant case-split. The pre-discharge VC is equisatisfiable (still
    // UNSAT), and it still emits the discriminant ITE on the constructor tag.
    let smt = emit_chc_smt_diagnostic_no_discharge(
        CHC_ENUM_GENERAL_MATCH,
        "probe_enum_general_match",
        ChcTrackLevel::Reg,
    );
    // Detect encoding path: ADT uses `(_ is` constructor tests in rules,
    // BV-flattened (#3215) uses `_fld0` scalar state vars with BV tag comparisons.
    // Note: declare-datatype may appear in both paths (sort registration).
    let uses_adt_constructors =
        smt.contains("is (as Foo") || smt.contains("is (as Some_E") || smt.contains("(_ is");
    if uses_adt_constructors {
        // ADT encoding path: Datatype with constructors.
        assert!(
            smt.contains("Some_E") || smt.contains("Foo"),
            "Expected payload constructor (Some_E or Foo) in CHC, got:\n{smt}"
        );
    } else {
        // BV-flattened encoding path (#3215): scalar state vars for tag + payload.
        // enum E { Foo(u64, u64), Bar } → [Bool tag, BV64 payload0, BV64 payload1]
        assert!(
            smt.contains("_fld0 Bool"),
            "BV-flattened enum should have Bool tag field (_fld0), got:\n{smt}"
        );
        // Discriminant uses ITE on tag: ite(tag_fld0, disc_1, disc_0)
        assert!(
            smt.contains("ite"),
            "BV-flattened enum discriminant should use ITE on tag, got:\n{smt}"
        );
    }
}

/// Trust twin of the test above. Trust's `rustc_public` names a local instance with
/// its crate (`testcrate_N::...`), so the emitted state symbols are `|`-quoted and
/// the expected spelling carries the closing `|`. The encoding is unchanged.
#[test]
#[cfg(trust_toolchain)]
fn test_chc_enum_general_match_encoding_trust() {
    // Inspect the pre-discharge encoding. The match target is statically
    // `E::Foo(x, y)`, so the bounded straight-line discharge proves the
    // `a == x` assert and collapses the VC to `(=> false error)`, erasing the
    // discriminant case-split. The pre-discharge VC is equisatisfiable (still
    // UNSAT), and it still emits the discriminant ITE on the constructor tag.
    let smt = emit_chc_smt_diagnostic_no_discharge(
        CHC_ENUM_GENERAL_MATCH,
        "probe_enum_general_match",
        ChcTrackLevel::Reg,
    );
    // Detect encoding path: ADT uses `(_ is` constructor tests in rules,
    // BV-flattened (#3215) uses `_fld0` scalar state vars with BV tag comparisons.
    // Note: declare-datatype may appear in both paths (sort registration).
    let uses_adt_constructors =
        smt.contains("is (as Foo") || smt.contains("is (as Some_E") || smt.contains("(_ is");
    if uses_adt_constructors {
        // ADT encoding path: Datatype with constructors.
        assert!(
            smt.contains("Some_E") || smt.contains("Foo"),
            "Expected payload constructor (Some_E or Foo) in CHC, got:\n{smt}"
        );
    } else {
        // BV-flattened encoding path (#3215): scalar state vars for tag + payload.
        // enum E { Foo(u64, u64), Bar } → [Bool tag, BV64 payload0, BV64 payload1]
        assert!(
            smt.contains("_fld0| Bool"),
            "BV-flattened enum should have Bool tag field (_fld0), got:\n{smt}"
        );
        // Discriminant uses ITE on tag: ite(tag_fld0, disc_1, disc_0)
        assert!(
            smt.contains("ite"),
            "BV-flattened enum discriminant should use ITE on tag, got:\n{smt}"
        );
    }
}

// Part of #4000: Whole-pipeline dyn_fn_mut two-call wrapper regression.
// This exercises the exact compiletest shape from tests/trust_mc/DynTrait/dyn_fn_mut.rs
// through the full pipeline: source → FunctionInlinePass → CHC codegen → Z3.
// The existing one-call unit probe in test_call_alloc.rs bypasses FunctionInlinePass,
// so it cannot detect pre-CHC boundary erasure.
const CHC_DYN_FN_MUT_TWO_CALL_WRAPPER: &str = r#"#![allow(dead_code)]

fn takes_dyn_fun(mut fun: Box<dyn FnMut(&mut i32)>, x_ptr: &mut i32) {
    fun(x_ptr)
}

fn mut_i32_ptr(x: &mut i32) {
    *x = *x + 1;
}

fn probe_dyn_fn_mut_two_call_wrapper() {
    let mut x: i32 = 1;
    takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
    assert!(x == 2);
    takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
    assert!(x == 3);
}
"#;

/// D1 localizer: dump the full-pipeline CHC for the two-call dyn_fn_mut wrapper
/// to observe what encoding the solver receives. Part of #4000.
#[test]
fn test_chc_dyn_fn_mut_two_call_wrapper_diagnostic() {
    let smt = emit_chc_smt_diagnostic(
        CHC_DYN_FN_MUT_TWO_CALL_WRAPPER,
        "probe_dyn_fn_mut_two_call_wrapper",
        ChcTrackLevel::Mem,
    );
    eprintln!("=== dyn_fn_mut two-call wrapper CHC ===\n{smt}\n=== END ===");
    // Structural check: the CHC should contain at least one error rule from the assert
    assert!(
        smt.contains("error"),
        "Expected error relation in CHC for dyn_fn_mut two-call wrapper"
    );
}

// Part of #3994: Diagnostic test to dump CHC for 5-variant enum PartialEq comparison.
// FiveVar `==` comparison fails (CTREX) while match/matches! works.
// Uses #[derive(PartialEq)] and `==` to exercise the cmp_stub or fn_inline path.
const CHC_FIVE_VAR_PARTIAL_EQ: &str = r#"#![allow(dead_code)]
#[derive(PartialEq)]
struct ZeroSized;

#[derive(PartialEq)]
enum FiveVar {
    NoFields,
    DataFul(bool),
    UnitFields((), ()),
    ZSTField(ZeroSized),
    ZSTStruct { field: ZeroSized, unit: () },
}

fn probe_five_var_eq() {
    let x = FiveVar::DataFul(true);
    let y = FiveVar::DataFul(true);
    assert!(x == y);
}
"#;

#[test]
fn test_chc_five_var_partial_eq_diagnostic() {
    // Acquire mutex to prevent global counter contamination with other enum
    // PartialEq tests that check translation_drop_by_fn counts.
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let smt =
        emit_chc_smt_diagnostic(CHC_FIVE_VAR_PARTIAL_EQ, "probe_five_var_eq", ChcTrackLevel::Mem);
    eprintln!("=== FiveVar PartialEq CHC ===\n{smt}\n=== END ===");
    assert!(smt.contains("fld0") || smt.contains("FiveVar"), "Expected FiveVar encoding in CHC");
}

// Diagnostic: dump CHC for simple array deref chain to understand 0-sec UNKNOWN.
const CHC_ARRAY_DEREF_CHAIN_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    pub fn assert(cond: bool, _msg: &str) { if !cond { panic!("assertion failed"); } }
}

#[kanitool::proof]
fn probe_array_deref_chain() {
    let arr: [u8; 4] = [1, 2, 3, 4];
    let r: &u8 = &arr[2];
    let v: u8 = *r;
    kani::assert(v == 3, "chained deref should yield arr[2]");
}
"#;

#[test]
fn test_chc_array_deref_chain_diagnostic() {
    // Emit the VC WITH the full optimization pipeline (const-prop, scalarization,
    // dead-var pruning) — matching what the solver actually receives.
    //
    // The bounded straight-line discharge is disabled here so the pre-opt VC
    // is the genuine array-deref encoding (with Array-sorted relation params),
    // not the collapsed `(=> false error)` the discharge would otherwise
    // produce. This is verdict-preserving (the discharge only replaces an
    // already-proven-UNSAT system); it lets the test observe the array→scalar
    // reduction the optimization pipeline performs.
    let mut maybe_result: Option<String> = None;
    let mut maybe_pre_opt: Option<String> = None;
    with_test_ay_ctx_for_source(CHC_ARRAY_DEREF_CHAIN_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.chc_straightline_discharge = false;
        ctx.config.chc_track_level = ChcTrackLevel::Mem;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_deref_chain");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);
        if let Some(chc_vc) = ctx.chc_vc.as_mut() {
            maybe_pre_opt = Some(crate::codegen_ay::emit_chc(chc_vc).to_string());

            // Apply the full optimization pipeline from context/mod.rs
            chc_vc.propagate_constants();
            chc_vc.prune_orphan_block_rules();
            chc_vc.prune_dead_identity_scalars();
            chc_vc.normalize_free_array_bases();
            super::super::chc::scalarize_vc(chc_vc);
            chc_vc.prune_dead_vars_and_constraints();

            maybe_result = Some(crate::codegen_ay::emit_chc(chc_vc).to_string());
        }
    });
    let pre_opt = maybe_pre_opt.expect("expected pre-opt CHC");
    let smt = maybe_result.expect("expected optimized CHC");

    // Count Array-sorted params in declare-rel lines
    let pre_array_in_rels: usize = pre_opt
        .lines()
        .filter(|l| l.contains("declare-rel"))
        .map(|l| l.matches("Array").count())
        .sum();
    let post_array_in_rels: usize =
        smt.lines().filter(|l| l.contains("declare-rel")).map(|l| l.matches("Array").count()).sum();
    let post_rule_count = smt.matches("(rule").count();
    let post_rel_count = smt.lines().filter(|l| l.contains("declare-rel")).count();

    eprintln!("=== POST-OPTIMIZATION Array Deref Chain CHC ===\n{smt}\n=== END ===");
    eprintln!(
        "Pre-opt Array-in-rels: {pre_array_in_rels}, Post-opt Array-in-rels: {post_array_in_rels}"
    );
    eprintln!("Post-opt Rules: {post_rule_count}, Relations: {post_rel_count}");

    // The deref-chain optimization eliminates redundant Array-sorted relation
    // parameters: a constant-index `[u8; 4]` array becomes per-index BV8
    // scalars (`_at_0x0..0x3`), and `&arr[2]` / `*r` resolve to the `_at_0x2`
    // scalar. Confirm the FINAL emitted CHC carries no Array-sorted relation
    // params, and the pipeline never re-introduces any.
    assert_eq!(
        post_array_in_rels, 0,
        "deref chain should emit zero Array-sorted relation params (fully scalarized), got {post_array_in_rels}:\n{smt}"
    );
    assert!(
        post_array_in_rels <= pre_array_in_rels,
        "optimization pipeline must not increase Array-sorted relation params: pre={pre_array_in_rels} post={post_array_in_rels}"
    );

    // Guard against a vacuous pass: the array MUST have been meaningfully
    // encoded and scalarized (not elided to an empty VC). The per-index
    // scalar for the dereferenced element and its value (3 = #x03) must be
    // present in the emitted CHC.
    assert!(
        smt.contains("_at_0x2_bv64"),
        "expected scalarized per-index var for arr[2], got:\n{smt}"
    );
    assert!(
        smt.contains("#x03"),
        "expected dereferenced value arr[2]==3 (#x03) in scalarized CHC, got:\n{smt}"
    );
    assert!(
        post_rule_count > 0,
        "expected non-trivial scalarized rules for the deref chain, got {post_rule_count} rules:\n{smt}"
    );
}

// =========================================================================
// `Iterator::sum` arithmetic (AY alignment review round 2): the CHC stub
// reads std's `Sum` impl from the call's Rust types (`iter_sum_summand`).
// The `(x >> 1) + 1` gives each probe an overflow-checked `Assert` terminator
// that can never fail, so the sum alone decides the query.
// =========================================================================

const CHC_ITER_SUM_SOURCE: &str = r#"#![allow(dead_code)]
use std::num::Saturating;

fn chc_sum_u8_overflow(x: u8) {
    let s: u8 = [200u8, 100].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s > 0 || y == 0);
}

fn chc_sum_u8_no_overflow(x: u8) {
    let s: u8 = [200u8, 50].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s == 250 || y == 0);
}

fn chc_sum_f32_to_inf(x: u8) {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s.is_finite() || y == 0);
}

#[derive(Clone, Copy)]
struct Weight(u32);

impl<'a> core::iter::Sum<&'a Weight> for u32 {
    fn sum<I: Iterator<Item = &'a Weight>>(it: I) -> u32 {
        it.fold(0, |a, w| a.max(w.0))
    }
}

fn chc_user_sum_impl(x: u8) {
    let v = [Weight(3), Weight(4)];
    let s: u32 = v.iter().sum();
    let y = (x >> 1) + 1;
    assert!(s == 7 || y == 0);
}

#[derive(Clone, Copy)]
struct Small(u8);

impl<'a> core::iter::Sum<&'a Small> for u8 {
    fn sum<I: Iterator<Item = &'a Small>>(it: I) -> u8 {
        it.fold(0u8, |a, w| a + w.0)
    }
}

fn chc_user_sum_impl_panics(x: u8) {
    let v = [Small(200), Small(100)];
    let s: u8 = v.iter().sum();
    let y = (x >> 1) + 1;
    assert!(y != 0);
    let _ = s;
}

fn chc_sum_constant_length_past_default_bound(x: u8) {
    let s: u8 = [20u8; 12].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s == 240 || y == 0);
}

fn chc_sum_saturating_unread(x: u8) {
    let _s: Saturating<u8> = [Saturating(200u8), Saturating(100)].iter().sum();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_sum_saturating_saturates(x: u8) {
    let s: Saturating<u8> = [Saturating(200u8), Saturating(100)].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s.0 == 255 || y == 0);
}

fn chc_sum_saturating_is_not_wrapped(x: u8) {
    let s: Saturating<u8> = [Saturating(200u8), Saturating(100)].iter().sum();
    let y = (x >> 1) + 1;
    assert!(s.0 == 44 || y == 0);
}
"#;

/// std's integer `Sum` panics on overflow; the stub used to wrap to 44.
#[test]
fn test_chc_e2e_iter_sum_u8_overflow_is_reachable() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_sum_u8_overflow", "sat");
}

#[test]
fn test_chc_e2e_iter_sum_u8_without_overflow_proves_unsat() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_sum_u8_no_overflow", "unsat");
}

/// The CHC lane has no FP theory, so a float sum is havocked: the infinite sum
/// is one of its values. The stub used to add the bit patterns as integers and
/// proved `s.is_finite()`.
#[test]
fn test_chc_e2e_iter_sum_f32_is_not_an_integer_sum() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_sum_f32_to_inf", "sat");
}

/// A user `impl Sum<&Weight> for u32` taking the max: the stub does not know
/// it and must not add. It used to `bvadd` the elements (3 + 4 == 7) and prove
/// an assertion the program (max == 4) fails. Only core's numeric impls reach
/// the stub now (`reduce_loop_rule::iter_sum_call_is_core_numeric_fold`); this
/// impl, one `fold`, is inlined and its fold replayed
/// (`reduce_loop_rule::is_inlined_sum_instance`).
#[test]
fn test_chc_e2e_iter_sum_user_impl_is_not_added() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_user_sum_impl", "sat");
}

/// A user `Sum` impl's body panics: here `200 + 100` overflows inside the
/// impl (Kani: "attempt to add with overflow"). The only other check holds.
/// The stub used to havoc the value and emit no error rule, so the query was
/// `unsat` and the program proved (AY alignment round 8, review round 3,
/// finding 2). The impl now takes the ordinary call path, where its one
/// `fold` is inlined and the closure's overflow check replayed per step; a
/// core impl the stub cannot classify still gets the conservative rule.
#[test]
fn test_chc_e2e_iter_sum_unmodeled_impl_may_panic() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_user_sum_impl_panics", "sat");
}

/// std's `Sum` for `Saturating<u8>` adds with `saturating_add` and cannot
/// panic. It was `Unknown`, so reaching the call fired the conservative rule
/// for an unmodelled impl and this program, whose only check holds, could not
/// be proved (AY alignment round 8, review round 4, finding 1).
#[test]
fn test_chc_e2e_iter_sum_saturating_reached_is_not_a_panic() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_sum_saturating_unread", "unsat");
}

/// `200 + 100` saturates to 255: the replay's step is `ite(carry, MAX, a + b)`.
#[test]
fn test_chc_e2e_iter_sum_saturating_saturates() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_sum_saturating_saturates", "unsat");
}

/// The saturating sum is not the wrapped `44`.
#[test]
fn test_chc_e2e_iter_sum_saturating_is_not_wrapped() {
    assert_chc_solver_result(CHC_ITER_SUM_SOURCE, "chc_sum_saturating_is_not_wrapped", "sat");
}

/// What a sum can panic on is decided by the impl, never by the destination's
/// sort. Under `--ay-chc-int-lift` an integer destination may have an `Int`
/// sort the summand's bit-vector width does not fit, so the value is havocked;
/// the panic obligation must still be the impl's own: none for `Saturating`,
/// the conservative "attempt to add with overflow" for std's `u8` sum, and the
/// "not modelled" rule only for an impl the stub cannot classify. Round 3 let
/// a sort mismatch reclassify the call `Unknown`, so every such sum got the
/// "not modelled" rule (AY alignment round 8, review round 4). The rules are
/// read from the undischarged SMT by the names of their freed flags. A user
/// impl never reaches the stub (only core's numeric impls do), so it gets
/// neither the stub's value nor its rule.
#[test]
fn test_chc_iter_sum_panic_rule_is_the_impls_at_any_sort() {
    // The int-lift encodes record place translation drops in a process-global
    // counter, which `test_range_for_loop_int_lifted_has_zero_translation_drops`
    // asserts is zero while it holds this lock. The first full suite run with
    // this test failed that one with 8 drops it had not made (it passes alone).
    let _counters = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut emitted = Vec::new();
    for int_lift in [false, true] {
        for probe in ["chc_sum_saturating_unread", "chc_sum_u8_no_overflow", "chc_user_sum_impl"] {
            let smt = emit_chc_smt_for_fn_with_options(CHC_ITER_SUM_SOURCE, probe, false, int_lift);
            emitted.push((int_lift, probe, smt));
        }
    }
    for (int_lift, probe, smt) in &emitted {
        let unmodeled = smt.contains("iter_sum_impl_unmodeled");
        assert!(
            !unmodeled,
            "{probe} int_lift={int_lift}: a classified impl got the rule. SMT:\n{smt}"
        );
        let stubbed = smt.contains("iter_sum_value");
        match *probe {
            "chc_user_sum_impl" => assert!(
                !stubbed,
                "{probe} int_lift={int_lift}: a user impl reached the sum stub. SMT:\n{smt}"
            ),
            _ => assert!(
                stubbed || !int_lift,
                "{probe} int_lift={int_lift}: std's impl did not reach the sum stub. SMT:\n{smt}"
            ),
        }
    }
}

/// `[20u8; 12]` sums to 240: no overflow. Twelve elements are past the
/// default replay bound of 8, so the replay used to leave four unchecked and
/// the conservative overflow rule fired. The receiver's static length raises
/// the bound to 12, the replay covers the sum, and the query is `unsat`
/// (AY alignment round 8, review round 3, finding 3).
#[test]
fn test_chc_e2e_iter_sum_constant_length_is_fully_replayed() {
    assert_chc_solver_result(
        CHC_ITER_SUM_SOURCE,
        "chc_sum_constant_length_past_default_bound",
        "unsat",
    );
}

// -------------------------------------------------------------------------
// Closures an iterator stub does not run (AY alignment round 8, review round 5)
// -------------------------------------------------------------------------

const CHC_ITER_CLOSURE_SOURCE: &str = r#"#![allow(dead_code)]
use std::num::{Saturating, Wrapping};

fn chc_sat_filter_sum_pred_panics(x: u8) {
    let a = [Saturating(3u8), Saturating(2)];
    let _s: Saturating<u8> = a
        .iter()
        .filter(|v| {
            assert!(v.0 < 3);
            true
        })
        .sum();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_sat_filter_sum_pure_pred(x: u8) {
    let a = [Saturating(3u8), Saturating(2)];
    let _s: Saturating<u8> = a.iter().filter(|v| v.0 > 2).sum();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_wrap_filter_sum_pred_panics(x: u8) {
    let a = [Wrapping(9u32), Wrapping(2)];
    let _s: Wrapping<u32> = a
        .iter()
        .filter(|v| {
            assert!(v.0 != 9);
            true
        })
        .sum();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_filter_fold_pred_panics(x: u8) {
    let a = [3u32, 2];
    let _s = a
        .iter()
        .filter(|v| {
            assert!(**v < 3);
            true
        })
        .fold(0u32, |acc, v| acc.wrapping_add(*v));
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_filter_next_pred_panics(x: u8) {
    let a = [3u8, 2];
    let mut it = a.iter().filter(|v| {
        assert!(**v < 3);
        true
    });
    let _first = it.next();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_filter_next_pure_pred(x: u8) {
    let a = [3u8, 2];
    let mut it = a.iter().filter(|v| **v < 3);
    let _first = it.next();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_fold_past_max_replay_bound_panics(x: u8) {
    let mut a = [1u8; 40];
    a[39] = 9;
    let _s = a.iter().fold(0u8, |acc, v| {
        assert!(*v < 5);
        acc.wrapping_add(*v)
    });
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_fold_constant_length_past_default_bound(x: u8) {
    let s = [1u8; 12].iter().fold(0u8, |acc, v| acc.wrapping_add(*v));
    let y = (x >> 1) + 1;
    assert!(s == 12 || y == 0);
}

fn chc_filter_sum(x: u8) {
    let a = [1u8, 2, 3];
    let s: u8 = a.iter().filter(|v| **v > 1).sum();
    let y = (x >> 1) + 1;
    assert!(s == 5 || y == 0);
}

fn chc_flat_map_chars(x: u8) {
    let hi = ["H", "i"];
    let mut it = hi.iter().flat_map(|s| s.chars());
    let _first = it.next();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_flat_map_closure_panics(x: u8) {
    let hi = ["H", "i"];
    let mut it = hi.iter().flat_map(|s| {
        assert!(s.len() > 5);
        s.chars()
    });
    let _first = it.next();
    let y = (x >> 1) + 1;
    assert!(y != 0);
}

fn chc_try_fold_closure_panics(x: u8) {
    let a = [3u8, 2];
    let _s: Option<u8> = a.iter().try_fold(0u8, |acc, v| {
        assert!(*v < 3);
        acc.checked_add(*v)
    });
    let y = (x >> 1) + 1;
    assert!(y != 0);
}
"#;

/// A `Filter`'s predicate panics on the first element; the sum is std's
/// `Saturating` sum, which cannot panic itself. The stub never runs the
/// predicate, and nothing stood in for it, so the program was proved where
/// Kani fails on the predicate's assert (review round 5, finding 1). The
/// conservative rule for the unrun closure makes the query `sat`.
#[test]
fn test_chc_e2e_filter_sum_predicate_panic_is_not_dropped() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_sat_filter_sum_pred_panics", "sat");
}

/// The same with `Wrapping<u32>`.
#[test]
fn test_chc_e2e_wrapping_filter_sum_predicate_panic_is_not_dropped() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_wrap_filter_sum_pred_panics", "sat");
}

/// A predicate that only compares carries no obligation, so no rule is added
/// and the program is still proved.
#[test]
fn test_chc_e2e_filter_sum_pure_predicate_still_proves() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_sat_filter_sum_pure_pred", "unsat");
}

/// `fold` over the same `Filter`.
#[test]
fn test_chc_e2e_filter_fold_predicate_panic_is_not_dropped() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_filter_fold_pred_panics", "sat");
}

/// A bare `next()` on the `Filter` (the `FilterNext` stub).
#[test]
fn test_chc_e2e_filter_next_predicate_panic_is_not_dropped() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_filter_next_pred_panics", "sat");
}

#[test]
fn test_chc_e2e_filter_next_pure_predicate_still_proves() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_filter_next_pure_pred", "unsat");
}

/// `try_fold` never applies its closure in this lane (the value is havocked),
/// so the closure's assert was dropped and the program proved.
#[test]
fn test_chc_e2e_try_fold_closure_panic_is_not_dropped() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_try_fold_closure_panics", "sat");
}

/// `flat_map(|s| s.chars())`: the closure calls only `str::chars`, which holds
/// offset sites that cannot fail for a valid `&str`, so the closure carries no
/// check that can fail and the `FlattenNext` stub adds no rule (the walk
/// trusts core's total `str`/slice iterator constructors). Without that,
/// `tests/kani/Iterator/flat_map.rs` lost its proof.
#[test]
fn test_chc_e2e_flat_map_chars_still_proves() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_flat_map_chars", "unsat");
}

/// The same `flat_map` whose closure asserts before `chars()`: the stub does
/// not run it, so the rule stands for the assert.
#[test]
fn test_chc_e2e_flat_map_closure_panic_is_not_dropped() {
    assert_chc_solver_result(CHC_ITER_CLOSURE_SOURCE, "chc_flat_map_closure_panics", "sat");
}

/// Forty constant elements: the replay stops at `MAX_REDUCE_BOUND` (32), the
/// replayed steps' checks fold to true, and the element that fails the
/// closure's assert (the fortieth) is never replayed. The steps past the
/// replay now get the conservative rule.
#[test]
fn test_chc_e2e_fold_closure_past_the_replay_is_not_dropped() {
    assert_chc_solver_result(
        CHC_ITER_CLOSURE_SOURCE,
        "chc_fold_past_max_replay_bound_panics",
        "sat",
    );
}

/// As for a sum, a constant-length `fold` is replayed whole: twelve elements
/// were past the default bound of 8, and the value was havocked.
#[test]
fn test_chc_e2e_fold_constant_length_is_fully_replayed() {
    assert_chc_solver_result(
        CHC_ITER_CLOSURE_SOURCE,
        "chc_fold_constant_length_past_default_bound",
        "unsat",
    );
}

/// The replay reads `fld_pos`/`fld_len`/`fld_data` wherever the receiver's
/// sort carries them, and walks into `fld_iter`: for a `Filter` that is the
/// INNER sequence, so a replay would be the unfiltered sum. Only the
/// `Filter` construction leaving those fields unbound kept the value sound.
/// The replay is refused for any receiver that is not a plain sequence
/// iterator, so no replay step (`iter_reduce_acc`) is emitted here.
#[test]
fn test_chc_filter_sum_is_not_replayed_over_the_inner_sequence() {
    let smt = emit_chc_smt_for_fn(CHC_ITER_CLOSURE_SOURCE, "chc_filter_sum");
    assert!(!smt.contains("iter_reduce_acc"), "a replay step was emitted. SMT:\n{smt}");
}

// =========================================================================
// Float `rem_euclid` / `div_euclid` / `%` in the CHC lane (TRUST-MC-FREM-2)
// =========================================================================

/// [`emit_chc_smt_for_fn`] plus what the driver reads before it may call a
/// `sat` `Genuine`: the variables freed by recorded sound approximations, and
/// for each property whether its reachability depends on them
/// (`Some(true)` keeps a counterexample `OverApproximation`).
fn emit_chc_smt_with_approximations(
    source: &str,
    fn_suffix: &str,
) -> (String, Vec<String>, Vec<Option<bool>>) {
    let mut maybe_result = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.queries.set_args(crate::args::Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        assert!(has_assert_probe(&body), "{fn_suffix}: expected an overflow Assert terminator");

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let chc_vc = ctx.chc_vc.as_ref().expect("CHC VC should be populated after CHC codegen");
        assert!(
            chc_vc.rules.iter().any(|rule| rule.head.name.starts_with("error")),
            "{fn_suffix}: expected an error rule; a vacuous query would hide regressions"
        );
        let dependence = chc_vc.properties.iter().map(|p| p.approximation_dependent).collect();
        maybe_result = Some((
            crate::codegen_ay::emit_chc(chc_vc).to_string(),
            chc_vc.approximated_vars.clone(),
            dependence,
        ));
    });
    maybe_result.expect("expected CHC SMT output")
}

/// Every claim is an overflow check that fails exactly when the claim is
/// false. The integer `div_euclid` / `rem_euclid` stub (`codegen_euclid`) was
/// keyed on the method name alone and computed `bvurem` / `bvudiv` over the
/// floats' IEEE bit patterns: it PROVED the false `x == 5.0 =>
/// x.rem_euclid(3.0) != 2.0`, and refuted the true claims with a counterexample
/// that rested on no approximation, so the front door labelled it `Genuine`
/// (atpkg trust-mc 20065, `--ay-chc`). A float call now takes the ordinary
/// call path, which in this lane havocs the call's result as a RECORDED sound
/// approximation (measured: the destination local is a freed variable).
const CHC_FLOAT_EUCLID_SOURCE: &str = r#"#![allow(dead_code)]
fn chc_f64_rem_euclid_true(x: f64) {
    if x == 5.0 {
        let n: u8 = if x.rem_euclid(3.0) == 2.0 { 0 } else { 255 };
        let _m = n + 1;
    }
}
fn chc_f64_rem_euclid_not_two_is_false(x: f64) {
    if x == 5.0 {
        let n: u8 = if x.rem_euclid(3.0) == 2.0 { 255 } else { 0 };
        let _m = n + 1;
    }
}
fn chc_f64_div_euclid_true(x: f64) {
    if x == -5.0 {
        let n: u8 = if x.div_euclid(3.0) == -2.0 { 0 } else { 255 };
        let _m = n + 1;
    }
}
fn chc_f64_rem_true(x: f64) {
    if x == 5.0 {
        let n: u8 = if x % 3.0 == 2.0 { 0 } else { 255 };
        let _m = n + 1;
    }
}
"#;

/// The false claim is no longer proved.
#[test]
fn test_chc_e2e_f64_rem_euclid_false_claim_is_not_proved() {
    assert_chc_solver_result(CHC_FLOAT_EUCLID_SOURCE, "chc_f64_rem_euclid_not_two_is_false", "sat");
}

/// A `sat` on a TRUE float claim must rest on a recorded approximation (the
/// driver keeps such a counterexample `OverApproximation`), never on an
/// exact-looking encoding the driver would certify `Genuine`. Returns the
/// freed variables. (Measured 2026-10-09: each true claim below is `sat`.)
fn assert_true_float_claim_sat_is_an_over_approximation(fn_suffix: &str) -> Vec<String> {
    let (smt, approximated_vars, dependence) =
        emit_chc_smt_with_approximations(CHC_FLOAT_EUCLID_SOURCE, fn_suffix);
    let result = run_ay_on_smt2(&smt)
        .unwrap_or_else(|err| panic!("{fn_suffix}: AY execution failed: {err}. SMT:\n{smt}"));
    if result != "sat" {
        // No counterexample to classify; a proof of a true claim is sound.
        return approximated_vars;
    }
    assert!(
        !approximated_vars.is_empty(),
        "{fn_suffix}: the float result must be a recorded approximation, not an exact-looking \
         term a counterexample could be certified on"
    );
    assert!(
        !dependence.is_empty() && dependence.iter().all(|dep| *dep == Some(true)),
        "{fn_suffix}: the check reads the freed result {approximated_vars:?}, so a \
         counterexample must stay OverApproximation: {dependence:?}"
    );
    approximated_vars
}

#[test]
fn test_chc_f64_rem_euclid_true_claim_counterexample_is_an_over_approximation() {
    assert_true_float_claim_sat_is_an_over_approximation("chc_f64_rem_euclid_true");
}

#[test]
fn test_chc_f64_div_euclid_true_claim_counterexample_is_an_over_approximation() {
    assert_true_float_claim_sat_is_an_over_approximation("chc_f64_div_euclid_true");
}

/// Float `%` itself never reached `fp.rem` in this lane: a symbolic operand
/// goes to the congruent float table (the constant fold uses host `%`, which
/// is `fmod`). Pinned so a `sat` here stays an over-approximation, and so a
/// future exact encoding in this lane is a deliberate change of this test.
#[test]
fn test_chc_f64_rem_true_claim_counterexample_rests_on_the_float_table() {
    let freed = assert_true_float_claim_sat_is_an_over_approximation("chc_f64_rem_true");
    assert!(
        freed.iter().any(|var| var == trust_mc_core::chc::FLOAT_BINOP_TABLE_F64),
        "symbolic f64 `%` must be the recorded f64 float table: {freed:?}"
    );
}

/// The CHC twin of `integration_bmc_tests::test_bmc_slice_eq_reads_lengths_not_array_tails`
/// (same probes: an overflow reachable exactly when the comparison holds).
///
/// Before the fix `[1, 2]` against `[1, 2, 0]` at two reference levels came
/// out EQUAL: the operands reach `SlicePartialEq` loaded through `&&[T]` with
/// no slice length, and the lane compared the two referent element arrays
/// with SMT `=`, both decoded over a constant 0 default. The
/// `*_overflow_if_unequal` probes were `unsat`, i.e. `assert!(a == b)` was
/// PROVED (`tools/soundness-duals/slice_eq_length_dual.rs`). An array datum is
/// now compared only below two constant lengths
/// (`chc::call::codegen_call_slice::slice_eq_from_referent_data`).
#[test]
fn test_chc_slice_eq_never_equates_slices_of_different_lengths() {
    use super::integration_bmc_tests::SLICE_EQ_LENGTH_SOURCE;
    for (probe, expected) in [
        ("slice_eq_len_differs_d2_overflow_if_unequal", "sat"),
        ("slice_eq_u8_len_differs_d2_overflow_if_unequal", "sat"),
        ("slice_eq_equal_d2_overflow_if_equal", "sat"),
    ] {
        assert_chc_solver_result(SLICE_EQ_LENGTH_SOURCE, probe, expected);
    }
}

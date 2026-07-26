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

fn emit_chc_smt_for_fn(source: &str, fn_suffix: &str) -> String {
    let mut maybe_result: Option<String> = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
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
/// The discharge skip is a process-global flag (codegen runs on a rustc worker
/// thread, so a thread-local would not reach it). [`DISCHARGE_FLAG_MUTEX`]
/// serializes these inspection runs so no concurrent test observes the
/// disabled state.
fn emit_chc_smt_for_fn_no_discharge(source: &str, fn_suffix: &str) -> String {
    let _guard = DISCHARGE_FLAG_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let prev = crate::codegen_ay::chc::set_straightline_discharge_disabled(true);
    let smt = emit_chc_smt_for_fn(source, fn_suffix);
    crate::codegen_ay::chc::set_straightline_discharge_disabled(prev);
    smt
}

/// Serializes all straight-line-discharge inspection helpers so the
/// process-global skip flag is never observed by a concurrent test.
static DISCHARGE_FLAG_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

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
    let _guard = DISCHARGE_FLAG_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let prev = crate::codegen_ay::chc::set_straightline_discharge_disabled(true);
    let smt = emit_chc_smt_diagnostic(source, fn_suffix, level);
    crate::codegen_ay::chc::set_straightline_discharge_disabled(prev);
    smt
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
    let _guard = DISCHARGE_FLAG_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let prev_discharge = crate::codegen_ay::chc::set_straightline_discharge_disabled(true);
    let mut maybe_result: Option<String> = None;
    let mut maybe_pre_opt: Option<String> = None;
    with_test_ay_ctx_for_source(CHC_ARRAY_DEREF_CHAIN_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
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
    crate::codegen_ay::chc::set_straightline_discharge_disabled(prev_discharge);
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

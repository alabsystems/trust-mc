// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Part of #4140: Localizer tests for unstable atomic_cxchg / atomic_cxchgweak.
//!
//! These tests convert the compiletest-only CTREX(OverApprox) symptom into a
//! unit-level ownership signal on committed HEAD.
//!
//! D1: Dispatch localizer (atomic calls only, no assert infrastructure).
//! D2: Full-shape localizer (atomic calls + assert tuple eq, matching compiletest).
//!
//! Design: designs/2026-03-21-issue-4140-unstable-atomic-cxchg-localizer.md.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// Probe sources
// =============================================================================

/// Probe: single unstable const-generic atomic_cxchg call.
const UNSTABLE_ATOMIC_CXCHG_PROBE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code)]
    use std::intrinsics::{AtomicOrdering, atomic_cxchg};

    pub fn probe_unstable_cxchg() -> (u8, bool) {
        let mut a = 0u8;
        let ptr: *mut u8 = &mut a;
        unsafe {
            atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(ptr, 0, 1)
        }
    }
"#;

/// Probe: single unstable const-generic atomic_cxchgweak call.
const UNSTABLE_ATOMIC_CXCHGWEAK_PROBE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code)]
    use std::intrinsics::{AtomicOrdering, atomic_cxchgweak};

    pub fn probe_unstable_cxchgweak() -> (u8, bool) {
        let mut a = 0u8;
        let ptr: *mut u8 = &mut a;
        unsafe {
            atomic_cxchgweak::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(ptr, 0, 1)
        }
    }
"#;

/// Probe: unstable atomic_cxchg with all 15 valid (success, failure) ordering pairs.
/// Mirrors the shape of `tests/trust_mc/Intrinsics/Atomic/Unstable/AtomicCxchg/main.rs`.
const UNSTABLE_ATOMIC_CXCHG_MATRIX_PROBE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code)]
    use std::intrinsics::{AtomicOrdering, atomic_cxchg};

    pub fn probe_unstable_cxchg_matrix() {
        let mut a1 = 0u8; let mut a2 = 0u8; let mut a3 = 0u8;
        let mut a4 = 0u8; let mut a5 = 0u8; let mut a6 = 0u8;
        let mut a7 = 0u8; let mut a8 = 0u8; let mut a9 = 0u8;
        let mut a10 = 0u8; let mut a11 = 0u8; let mut a12 = 0u8;
        let mut a13 = 0u8; let mut a14 = 0u8; let mut a15 = 0u8;
        unsafe {
            let _ = atomic_cxchg::<_, {AtomicOrdering::AcqRel}, {AtomicOrdering::Acquire}>(&mut a1 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::AcqRel}, {AtomicOrdering::Relaxed}>(&mut a2 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::AcqRel}, {AtomicOrdering::SeqCst}>(&mut a3 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Acquire}, {AtomicOrdering::Acquire}>(&mut a4 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Acquire}, {AtomicOrdering::Relaxed}>(&mut a5 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Acquire}, {AtomicOrdering::SeqCst}>(&mut a6 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Relaxed}, {AtomicOrdering::Acquire}>(&mut a7 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Relaxed}, {AtomicOrdering::Relaxed}>(&mut a8 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Relaxed}, {AtomicOrdering::SeqCst}>(&mut a9 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Release}, {AtomicOrdering::Acquire}>(&mut a10 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Release}, {AtomicOrdering::Relaxed}>(&mut a11 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::Release}, {AtomicOrdering::SeqCst}>(&mut a12 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::SeqCst}, {AtomicOrdering::Acquire}>(&mut a13 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::SeqCst}, {AtomicOrdering::Relaxed}>(&mut a14 as *mut u8, 0, 1);
            let _ = atomic_cxchg::<_, {AtomicOrdering::SeqCst}, {AtomicOrdering::SeqCst}>(&mut a15 as *mut u8, 0, 1);
        }
    }
"#;

/// Probe: unstable atomic_cxchgweak with all 15 valid (success, failure) ordering pairs.
const UNSTABLE_ATOMIC_CXCHGWEAK_MATRIX_PROBE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code)]
    use std::intrinsics::{AtomicOrdering, atomic_cxchgweak};

    pub fn probe_unstable_cxchgweak_matrix() {
        let mut a1 = 0u8; let mut a2 = 0u8; let mut a3 = 0u8;
        let mut a4 = 0u8; let mut a5 = 0u8; let mut a6 = 0u8;
        let mut a7 = 0u8; let mut a8 = 0u8; let mut a9 = 0u8;
        let mut a10 = 0u8; let mut a11 = 0u8; let mut a12 = 0u8;
        let mut a13 = 0u8; let mut a14 = 0u8; let mut a15 = 0u8;
        unsafe {
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::AcqRel}, {AtomicOrdering::Acquire}>(&mut a1 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::AcqRel}, {AtomicOrdering::Relaxed}>(&mut a2 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::AcqRel}, {AtomicOrdering::SeqCst}>(&mut a3 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Acquire}, {AtomicOrdering::Acquire}>(&mut a4 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Acquire}, {AtomicOrdering::Relaxed}>(&mut a5 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Acquire}, {AtomicOrdering::SeqCst}>(&mut a6 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Relaxed}, {AtomicOrdering::Acquire}>(&mut a7 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Relaxed}, {AtomicOrdering::Relaxed}>(&mut a8 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Relaxed}, {AtomicOrdering::SeqCst}>(&mut a9 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Release}, {AtomicOrdering::Acquire}>(&mut a10 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Release}, {AtomicOrdering::Relaxed}>(&mut a11 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::Release}, {AtomicOrdering::SeqCst}>(&mut a12 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::SeqCst}, {AtomicOrdering::Acquire}>(&mut a13 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::SeqCst}, {AtomicOrdering::Relaxed}>(&mut a14 as *mut u8, 0, 1);
            let _ = atomic_cxchgweak::<_, {AtomicOrdering::SeqCst}, {AtomicOrdering::SeqCst}>(&mut a15 as *mut u8, 0, 1);
        }
    }
"#;

// =============================================================================
// D1 tests: dispatch claimed
// =============================================================================

/// CHC dispatch must claim the unstable const-generic atomic_cxchg call.
/// Mirrors `test_unstable_atomic_xadd_dispatch_claimed` in test_call_atomic.rs.
#[test]
fn test_unstable_atomic_cxchg_dispatch_claimed() {
    with_test_ay_ctx_for_source(UNSTABLE_ATOMIC_CXCHG_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unstable_cxchg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unstable_cxchg", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut atomic_claimed = false;
        let mut all_paths = Vec::new();
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let path =
                    chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func));
                match path {
                    Some(p) => {
                        if p.contains("atomic_cxchg") {
                            atomic_claimed = true;
                        }
                        all_paths.push(format!("bb{bb_idx}: {p}"));
                    }
                    None => {
                        all_paths.push(format!("bb{bb_idx}: <None>"));
                    }
                }
            }
        }

        assert!(
            atomic_claimed,
            "resolve_callee_path (or fallback) must recover an atomic_cxchg path \
             for unstable const-generic intrinsics. \
             Observed paths: {all_paths:?}"
        );
    });
}

/// CHC dispatch must claim the unstable const-generic atomic_cxchgweak call.
#[test]
fn test_unstable_atomic_cxchgweak_dispatch_claimed() {
    with_test_ay_ctx_for_source(UNSTABLE_ATOMIC_CXCHGWEAK_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unstable_cxchgweak");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_unstable_cxchgweak", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut atomic_claimed = false;
        let mut all_paths = Vec::new();
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let path =
                    chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func));
                match path {
                    Some(p) => {
                        if p.contains("atomic_cxchg") {
                            atomic_claimed = true;
                        }
                        all_paths.push(format!("bb{bb_idx}: {p}"));
                    }
                    None => {
                        all_paths.push(format!("bb{bb_idx}: <None>"));
                    }
                }
            }
        }

        assert!(
            atomic_claimed,
            "resolve_callee_path (or fallback) must recover an atomic_cxchgweak path \
             for unstable const-generic intrinsics. \
             Observed paths: {all_paths:?}"
        );
    });
}

// =============================================================================
// D1 tests: matrix stays off call_dispatch_fallback
// =============================================================================

/// Full 15-ordering matrix for unstable atomic_cxchg must not increment
/// call_dispatch_fallback. This is the unit-level equivalent of the compiletest
/// harness `AtomicCxchg/main.rs`.
#[test]
fn test_unstable_atomic_cxchg_matrix_stays_off_call_dispatch_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(UNSTABLE_ATOMIC_CXCHG_MATRIX_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unstable_cxchg_matrix");
        let body = instance.body().expect("function body");
        let _vc = mir_to_chc(ctx.tcx, &body, "probe_unstable_cxchg_matrix", ChcConfig::default());

        let fallback_count =
            get_chc_fallback_counts().get("probe_unstable_cxchg_matrix").copied().unwrap_or(0);

        let translation_drops = take_translation_drop_by_fn();
        let drop_reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let drop_count = translation_drops.get("probe_unstable_cxchg_matrix").copied().unwrap_or(0);
        let dispatch_fallback = drop_reasons
            .get("probe_unstable_cxchg_matrix")
            .and_then(|m| m.get("call_dispatch_fallback"))
            .copied()
            .unwrap_or(0);

        assert_eq!(
            fallback_count, 0,
            "unstable cxchg 15-ordering matrix should have zero CHC fallbacks, \
             got {fallback_count}"
        );
        assert_eq!(
            dispatch_fallback, 0,
            "unstable cxchg 15-ordering matrix should have zero call_dispatch_fallback, \
             got {dispatch_fallback}; drop_count={drop_count}, reasons={drop_reasons:?}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

/// Full 15-ordering matrix for unstable atomic_cxchgweak must not increment
/// call_dispatch_fallback.
#[test]
fn test_unstable_atomic_cxchgweak_matrix_stays_off_call_dispatch_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(UNSTABLE_ATOMIC_CXCHGWEAK_MATRIX_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unstable_cxchgweak_matrix");
        let body = instance.body().expect("function body");
        let _vc =
            mir_to_chc(ctx.tcx, &body, "probe_unstable_cxchgweak_matrix", ChcConfig::default());

        let fallback_count =
            get_chc_fallback_counts().get("probe_unstable_cxchgweak_matrix").copied().unwrap_or(0);

        let translation_drops = take_translation_drop_by_fn();
        let drop_reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let drop_count =
            translation_drops.get("probe_unstable_cxchgweak_matrix").copied().unwrap_or(0);
        let dispatch_fallback = drop_reasons
            .get("probe_unstable_cxchgweak_matrix")
            .and_then(|m| m.get("call_dispatch_fallback"))
            .copied()
            .unwrap_or(0);

        assert_eq!(
            fallback_count, 0,
            "unstable cxchgweak 15-ordering matrix should have zero CHC fallbacks, \
             got {fallback_count}"
        );
        assert_eq!(
            dispatch_fallback, 0,
            "unstable cxchgweak 15-ordering matrix should have zero call_dispatch_fallback, \
             got {dispatch_fallback}; drop_count={drop_count}, reasons={drop_reasons:?}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

// =============================================================================
// D2 probes: full compiletest shape (cxchg + assert tuple eq)
// =============================================================================

/// Probe matching the exact compiletest harness shape:
/// atomic_cxchg calls followed by `assert!(result == (val, true))`.
/// This is the minimal reproducer for the 10 call_dispatch_fallback sites.
const CXCHG_WITH_ASSERT_PROBE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code)]
    use std::intrinsics::{AtomicOrdering, atomic_cxchg};

    pub fn probe_cxchg_with_assert() {
        let mut a1 = 0u8;
        let mut a2 = 0u8;
        let ptr1: *mut u8 = &mut a1;
        let ptr2: *mut u8 = &mut a2;
        unsafe {
            let x1 = atomic_cxchg::<_, {AtomicOrdering::SeqCst}, {AtomicOrdering::SeqCst}>(ptr1, 0, 1);
            let x2 = atomic_cxchg::<_, {AtomicOrdering::Relaxed}, {AtomicOrdering::Relaxed}>(ptr2, 0, 1);
            assert!(x1 == (0, true));
            assert!(x2 == (0, true));
        }
    }
"#;

// =============================================================================
// D2 tests: identify fallback source in full harness shape
// =============================================================================

/// D2 localizer: compile the full-shape probe (cxchg + assert) and measure
/// where call_dispatch_fallback sites come from. This identifies whether the
/// compiletest's 10 fallbacks originate in tuple PartialEq, assert/panic
/// infrastructure, or something else.
#[test]
fn test_d2_cxchg_with_assert_fallback_attribution() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(CXCHG_WITH_ASSERT_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cxchg_with_assert");
        let body = instance.body().expect("function body");
        let _vc = mir_to_chc(ctx.tcx, &body, "probe_cxchg_with_assert", ChcConfig::default());

        let fallback_count =
            get_chc_fallback_counts().get("probe_cxchg_with_assert").copied().unwrap_or(0);

        let translation_drops = take_translation_drop_by_fn();
        let drop_reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let drop_count = translation_drops.get("probe_cxchg_with_assert").copied().unwrap_or(0);
        let dispatch_fallback = drop_reasons
            .get("probe_cxchg_with_assert")
            .and_then(|m| m.get("call_dispatch_fallback"))
            .copied()
            .unwrap_or(0);

        // Print full attribution for diagnosis
        eprintln!(
            "D2 attribution: fallback_count={fallback_count}, drop_count={drop_count}, \
             dispatch_fallback={dispatch_fallback}"
        );
        if let Some(reasons) = drop_reasons.get("probe_cxchg_with_assert") {
            for (reason, count) in reasons {
                eprintln!("  reason: {reason} = {count}");
            }
        }

        // The dispatch_fallback should be > 0 here (proving the assert/eq
        // infrastructure is the source, not the atomic dispatch itself).
        // D1 already proved atomic-only probes have 0 fallback.
        // This test documents the actual count for D3 production fix scoping.
        eprintln!(
            "D2 conclusion: assert!(tuple == literal) adds {dispatch_fallback} \
             call_dispatch_fallback sites per probe function"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

/// D2 control probe: assert on tuple WITHOUT atomics.
/// If this produces fallback > 0, the source is assert/tuple infrastructure.
/// If this produces fallback == 0, the source is atomic-specific fn-inlining.
const ASSERT_TUPLE_ONLY_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_assert_tuple_only() {
        let x: (u8, bool) = (0, true);
        let y: (u8, bool) = (1, true);
        assert!(x == (0, true));
        assert!(y == (1, true));
    }
"#;

/// D2 control test: measure fallback from assert!(tuple == literal) without atomics.
#[test]
fn test_d2_assert_tuple_only_fallback_control() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(ASSERT_TUPLE_ONLY_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_tuple_only");
        let body = instance.body().expect("function body");
        let _vc = mir_to_chc(ctx.tcx, &body, "probe_assert_tuple_only", ChcConfig::default());

        let fallback_count =
            get_chc_fallback_counts().get("probe_assert_tuple_only").copied().unwrap_or(0);
        let translation_drops = take_translation_drop_by_fn();
        let drop_reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let drop_count = translation_drops.get("probe_assert_tuple_only").copied().unwrap_or(0);
        let dispatch_fallback = drop_reasons
            .get("probe_assert_tuple_only")
            .and_then(|m| m.get("call_dispatch_fallback"))
            .copied()
            .unwrap_or(0);

        eprintln!(
            "D2 control (no atomics): fallback_count={fallback_count}, drop_count={drop_count}, \
             dispatch_fallback={dispatch_fallback}"
        );
        if let Some(reasons) = drop_reasons.get("probe_assert_tuple_only") {
            for (reason, count) in reasons {
                eprintln!("  reason: {reason} = {count}");
            }
        }
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

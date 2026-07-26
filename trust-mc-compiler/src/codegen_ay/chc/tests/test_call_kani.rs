// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for codegen_call_kani.rs — KaniHook::Exists dispatch and fallback.
//!
//! Part of #2630: soundness-critical coverage for KaniHook::Exists dispatch arm.
//!
//! Covers:
//! - KaniHook::Exists dispatch arm at codegen_call_kani.rs:294
//! - Nondet fallback path at codegen_call_kani.rs:326-331 (when quantifier
//!   encoding fails, destination should be unconstrained but transition emitted)
//! - Structural invariant: VC rules are always emitted regardless of quantifier
//!   encoding success/failure

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_dispatch_kani::CallDispatchKani;
use super::super::quantifier_encoding::QuantifierEncoding;
use super::common::*;
use crate::kani_middle::kani_functions::{KaniHook, KaniIntrinsic, KaniModel};

// =============================================================================
// Probe sources
// =============================================================================

/// Source with ExistsHook marker for positive dispatch testing.
/// The closure uses a function pointer (not a real closure) so that
/// quantifier encoding will likely fail (function pointer MIR is too complex),
/// exercising the nondet fallback path at codegen_call_kani.rs:326-331.
const EXISTS_DISPATCH_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists(lower: u32, upper: u32, pred: fn(u32) -> bool) -> bool {
        let mut i = lower;
        while i < upper {
            if pred(i) { return true; }
            i += 1;
        }
        false
    }
}

fn check(x: u32) -> bool { x > 5 }

pub fn probe_exists_dispatch(lo: u32, hi: u32) -> bool {
    kani::exists(lo, hi, check)
}
"#;

/// Source with both Exists and Forall to verify they produce separate dispatch.
const BOTH_QUANTIFIERS_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists(lower: u32, upper: u32, pred: fn(u32) -> bool) -> bool {
        let mut i = lower;
        while i < upper {
            if pred(i) { return true; }
            i += 1;
        }
        false
    }

    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall(lower: u32, upper: u32, pred: fn(u32) -> bool) -> bool {
        let mut i = lower;
        while i < upper {
            if !pred(i) { return false; }
            i += 1;
        }
        true
    }
}

fn positive(x: u32) -> bool { x > 0 }

pub fn probe_both_quantifiers(lo: u32, hi: u32) -> (bool, bool) {
    let e = kani::exists(lo, hi, positive);
    let f = kani::forall(lo, hi, positive);
    (e, f)
}
"#;

/// Source with two Exists calls:
/// - `probe_exists_encoded` uses a closure and should encode successfully.
/// - `probe_exists_fallback` uses a function item and should hit nondet fallback.
const EXISTS_SUCCESS_AND_FALLBACK_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists<F>(lower: u32, upper: u32, pred: F) -> bool
    where
        F: Fn(u32) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if pred(i) { return true; }
            i += 1;
        }
        false
    }
}

fn positive_ptr(x: u32) -> bool { x > 0 }

pub fn probe_exists_encoded() -> bool {
    kani::exists(0, 3, |x| x > 0)
}

pub fn probe_exists_fallback() -> bool {
    kani::exists(0, 3, positive_ptr)
}
"#;

// =============================================================================
// KaniHook::Exists dispatch detection
// =============================================================================

/// Verify that `detect_kani_hook` returns `KaniHook::Exists` for ExistsHook-marked
/// function calls, exercising the positive detection path that feeds into the
/// dispatch arm at codegen_call_kani.rs:294.
#[test]
fn test_detect_kani_hook_exists_positive() {
    with_test_ay_ctx_for_source(EXISTS_DISPATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_exists_dispatch");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_exists_dispatch", ChcConfig::default());

        let mut exists_detected = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                if matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Exists)) {
                    exists_detected = true;
                }
                // Verify mutual exclusivity: Exists call should not match model/intrinsic
                if chc_ctx.detect_kani_hook(func).is_some() {
                    assert!(
                        chc_ctx.detect_kani_model(func).is_none(),
                        "KaniHook::Exists should not also match as kani model"
                    );
                    assert!(
                        chc_ctx.detect_kani_intrinsic(func).is_none(),
                        "KaniHook::Exists should not also match as kani intrinsic"
                    );
                }
            }
        }
        assert!(
            exists_detected,
            "should detect at least one KaniHook::Exists in probe_exists_dispatch"
        );
    });
}

// =============================================================================
// Nondet fallback: VC emitted even when quantifier encoding fails
// =============================================================================

/// Verify that the full pipeline emits a goto rule even when quantifier encoding
/// fails (the nondet fallback path at codegen_call_kani.rs:326-331).
///
/// The soundness concern: if `build_quantifier_expr` returns None and no goto
/// rule is emitted, the transition from the Exists call BB would be missing,
/// potentially disconnecting the CFG and silently dropping subsequent assertions.
///
/// The correct behavior (verified by this test): `emit_goto_rule` at line 333
/// fires unconditionally — the `constraints` vector simply has fewer entries
/// when quantifier encoding fails (destination left unconstrained = nondet).
#[test]
fn test_exists_dispatch_emits_goto_rule_on_fallback() {
    with_test_ay_ctx_for_source(EXISTS_DISPATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_exists_dispatch");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_exists_dispatch", ChcConfig::default());

        assert_vc_structure(&vc, "probe_exists_dispatch", body.blocks.len());

        // Every BB in the MIR should have at least one rule targeting a successor.
        // The Exists call BB must have a goto rule to its target BB — verify by
        // checking that the rule count is sufficient for the BB count.
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "VC should have at least one rule per BB ({bb_count}), got {}; \
             a missing rule suggests the Exists dispatch did not emit goto",
            vc.rules.len()
        );
    });
}

/// Verify that when quantifier encoding fails (function pointer closure body too
/// complex for translation), the sound fallback counter increments.  Before
/// Part of #2616, the quantifier fallback was fail-open: it left the
/// destination unconstrained but did NOT call any recording function.
/// Part of #3099: reclassified from record_fallback() (DEMOTED) to
/// record_sound_fallback() (SOUND_APPROXIMATION) — leaving the destination
/// nondet is a sound over-approximation, not an unsound fallback.
#[test]
fn test_quantifier_fallback_increments_sound_fallback_counter() {
    use crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering::Relaxed;

    const SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists(lower: u32, upper: u32, pred: fn(u32) -> bool) -> bool {
        let mut i = lower;
        while i < upper {
            if pred(i) { return true; }
            i += 1;
        }
        false
    }
}

fn check(x: u32) -> bool { x > 5 }

pub fn probe_exists_dispatch_fallback_counter(lo: u32, hi: u32) -> bool {
    kani::exists(lo, hi, check)
}
"#;

    let before = GLOBAL_COUNTERS.place_translation_drop.load(Relaxed);
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_exists_dispatch_fallback_counter");
        let body = instance.body().expect("function body");

        let _vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_exists_dispatch_fallback_counter",
            ChcConfig::default(),
        );
    });
    let after = GLOBAL_COUNTERS.place_translation_drop.load(Relaxed);
    assert!(
        after > before,
        "quantifier encoding failure should increment sound fallback counter \
         (place_translation_drop) for probe_exists_dispatch_fallback_counter \
         (before={before}, after={after})"
    );
}

// =============================================================================
// Both Forall and Exists in same function
// =============================================================================

/// Verify that a function containing both ExistsHook and ForallHook calls
/// produces a valid VC with rules for both quantifier dispatch arms.
#[test]
fn test_both_quantifiers_dispatch_produces_valid_vc() {
    with_test_ay_ctx_for_source(BOTH_QUANTIFIERS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_both_quantifiers");
        let body = instance.body().expect("function body");

        // Verify both hooks are detected
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_both_quantifiers", ChcConfig::default());

        let mut exists_count = 0usize;
        let mut forall_count = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                match chc_ctx.detect_kani_hook(func) {
                    Some(KaniHook::Exists) => exists_count += 1,
                    Some(KaniHook::Forall) => forall_count += 1,
                    _ => {}
                }
            }
        }
        assert!(exists_count >= 1, "expected at least one Exists detection, got {exists_count}");
        assert!(forall_count >= 1, "expected at least one Forall detection, got {forall_count}");

        // Verify full pipeline VC
        let vc = mir_to_chc(ctx.tcx, &body, "probe_both_quantifiers", ChcConfig::default());
        assert_vc_structure(&vc, "probe_both_quantifiers", body.blocks.len());
    });
}

/// Verify Mem-level VC also succeeds with quantifier dispatch.
/// Mem level uses additional memory model constraints — ensure the
/// quantifier dispatch arm doesn't conflict with memory tracking.
#[test]
fn test_exists_dispatch_at_mem_level() {
    with_test_ay_ctx_for_source(EXISTS_DISPATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_exists_dispatch");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_exists_dispatch",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_exists_dispatch", body.blocks.len());
    });
}

#[test]
fn test_exists_success_constrains_destination_and_fallback_is_unconstrained() {
    fn total_transition_constraints(vc: &trust_mc_core::chc::ChcVc) -> usize {
        vc.rules
            .iter()
            .filter(|rule| rule.body.relation.is_some())
            .map(|rule| rule.body.constraints.len())
            .sum()
    }

    with_test_ay_ctx_for_source(EXISTS_SUCCESS_AND_FALLBACK_SOURCE, |ctx| {
        let encoded_instance = find_instance_by_suffix(ctx.tcx, "probe_exists_encoded");
        let encoded_body = encoded_instance.body().expect("encoded body");
        let mut encoded_chc_ctx =
            ChcCtx::new(ctx.tcx, &encoded_body, "probe_exists_encoded", ChcConfig::default());
        let (encoded_bb_idx, encoded_func, encoded_args) = encoded_body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, args, .. } => {
                    Some((bb_idx, func, args.as_slice()))
                }
                _ => None,
            })
            .expect("encoded probe should contain a call");
        assert!(
            matches!(encoded_chc_ctx.detect_kani_hook(encoded_func), Some(KaniHook::Exists)),
            "encoded probe call should dispatch as Exists hook"
        );
        let encoded_quant_expr = encoded_chc_ctx.build_quantifier_expr(
            encoded_func,
            encoded_args,
            &HashSet::new(),
            encoded_bb_idx,
            false,
        );
        assert!(
            encoded_quant_expr.is_some(),
            "closure-based Exists should produce quantifier expression"
        );

        let fallback_instance = find_instance_by_suffix(ctx.tcx, "probe_exists_fallback");
        let fallback_body = fallback_instance.body().expect("fallback body");
        let mut fallback_chc_ctx =
            ChcCtx::new(ctx.tcx, &fallback_body, "probe_exists_fallback", ChcConfig::default());
        let (fallback_bb_idx, fallback_func, fallback_args) = fallback_body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, args, .. } => {
                    Some((bb_idx, func, args.as_slice()))
                }
                _ => None,
            })
            .expect("fallback probe should contain a call");
        assert!(
            matches!(fallback_chc_ctx.detect_kani_hook(fallback_func), Some(KaniHook::Exists)),
            "fallback probe call should dispatch as Exists hook"
        );
        let fallback_quant_expr = fallback_chc_ctx.build_quantifier_expr(
            fallback_func,
            fallback_args,
            &HashSet::new(),
            fallback_bb_idx,
            false,
        );
        assert!(
            fallback_quant_expr.is_none(),
            "function-item Exists should fail quantifier encoding and fall back to nondet"
        );

        let encoded_vc =
            mir_to_chc(ctx.tcx, &encoded_body, "probe_exists_encoded", ChcConfig::default());
        let fallback_vc =
            mir_to_chc(ctx.tcx, &fallback_body, "probe_exists_fallback", ChcConfig::default());
        assert_vc_structure(&encoded_vc, "probe_exists_encoded", encoded_body.blocks.len());
        assert_vc_structure(&fallback_vc, "probe_exists_fallback", fallback_body.blocks.len());

        let encoded_constraints = total_transition_constraints(&encoded_vc);
        let fallback_constraints = total_transition_constraints(&fallback_vc);
        assert!(
            encoded_constraints > fallback_constraints,
            "encoded Exists should constrain destination more than fallback (encoded={encoded_constraints}, fallback={fallback_constraints})"
        );
    });
}

// =============================================================================
// Kani hook/intrinsic/model dispatch tests.
// Part of #2694: supplementary CHC coverage for kani dispatch paths.
// =============================================================================

/// IsInitialized intrinsic produces a rule constraining destination to true.
#[test]
fn test_kani_intrinsic_is_initialized_constrains_dest_to_true() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani_intrinsics {
            #[kanitool::fn_marker = "IsInitializedIntrinsic"]
            pub fn is_initialized(_ptr: *const u8) -> bool { true }
        }

        pub fn probe_is_initialized(ptr: *const u8) -> bool {
            kani_intrinsics::is_initialized(ptr)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_initialized");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_is_initialized", ChcConfig::default());
        let has_intrinsic = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_intrinsic(func), Some(KaniIntrinsic::IsInitialized))
            } else {
                false
            }
        });
        assert!(has_intrinsic, "MIR should contain IsInitializedIntrinsic call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_is_initialized", ChcConfig::default());
        assert_vc_structure(&vc, "probe_is_initialized", body.blocks.len());

        let has_true_constraint = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| r.body.constraints.iter().any(|c| c.to_string().contains("true")));
        assert!(has_true_constraint, "IsInitialized should produce a 'true' constraint");
    });
}

/// ValidValue intrinsic produces a rule constraining destination to true.
#[test]
fn test_kani_intrinsic_valid_value_constrains_dest_to_true() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani_intrinsics {
            #[kanitool::fn_marker = "ValidValueIntrinsic"]
            pub fn valid_value(x: u32) -> bool { x != 0 }
        }

        pub fn probe_valid_value(x: u32) -> bool {
            kani_intrinsics::valid_value(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_valid_value");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_valid_value", ChcConfig::default());
        let has_intrinsic = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_intrinsic(func), Some(KaniIntrinsic::ValidValue))
            } else {
                false
            }
        });
        assert!(has_intrinsic, "MIR should contain ValidValueIntrinsic call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_valid_value", ChcConfig::default());
        assert_vc_structure(&vc, "probe_valid_value", body.blocks.len());

        let has_true_constraint = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| r.body.constraints.iter().any(|c| c.to_string().contains("true")));
        assert!(has_true_constraint, "ValidValue should produce a 'true' constraint");
    });
}

/// AnyModifies intrinsic produces a goto rule with unconstrained (nondet) destination.
#[test]
fn test_kani_intrinsic_any_modifies_produces_nondet_dest() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani_intrinsics {
            #[kanitool::fn_marker = "AnyModifiesIntrinsic"]
            pub fn any_modifies() -> u32 { 42 }
        }

        pub fn probe_any_modifies() -> u32 { kani_intrinsics::any_modifies() }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_any_modifies");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_any_modifies", ChcConfig::default());
        let has_intrinsic = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_intrinsic(func), Some(KaniIntrinsic::AnyModifies))
            } else {
                false
            }
        });
        assert!(has_intrinsic, "MIR should contain AnyModifiesIntrinsic call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_any_modifies", ChcConfig::default());
        assert_vc_structure(&vc, "probe_any_modifies", body.blocks.len());
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "AnyModifies should produce at least one transition rule"
        );
    });
}

/// SafetyCheck hook emits BOTH an error rule (assert) AND a guarded transition (assume).
#[test]
fn test_kani_hook_safety_check_emits_error_and_assume_rules() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "SafetyCheckHook"]
            pub fn safety_check(cond: bool) { if !cond { panic!("safety check") } }
        }

        pub fn probe_safety_check(x: u32) {
            kani::safety_check(x > 0);
            let _ = x + 1;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_safety_check");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_safety_check", ChcConfig::default());
        let has_safety_check = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::SafetyCheck))
            } else {
                false
            }
        });
        assert!(has_safety_check, "MIR should contain SafetyCheckHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_safety_check", ChcConfig::default());
        assert_vc_structure(&vc, "probe_safety_check", body.blocks.len());
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "SafetyCheck should emit at least one error rule (assert component)"
        );
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "SafetyCheck should emit at least one transition rule (assume component)"
        );
    });
}

/// Panic hook emits an unconditional error rule.
#[test]
fn test_kani_hook_panic_emits_unconditional_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "PanicHook"]
            pub fn panic_hook() { panic!("always fails") }
        }

        pub fn probe_panic() { kani::panic_hook(); }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_panic");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_panic", ChcConfig::default());
        let has_panic = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Panic))
            } else {
                false
            }
        });
        assert!(has_panic, "MIR should contain PanicHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_panic", ChcConfig::default());
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "Panic hook should emit at least one error rule"
        );
    });
}

/// IsAllocated hook at Reg level constrains destination to true (no heap arrays).
#[test]
fn test_kani_hook_is_allocated_reg_level_constrains_dest_to_true() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "IsAllocatedHook"]
            pub fn is_allocated(_ptr: *const u8) -> bool { true }
        }

        pub fn probe_is_allocated(ptr: *const u8) -> bool { kani::is_allocated(ptr) }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_allocated");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_is_allocated", ChcConfig::default());
        let has_hook = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::IsAllocated))
            } else {
                false
            }
        });
        assert!(has_hook, "MIR should contain IsAllocatedHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_is_allocated", ChcConfig::default());
        assert_vc_structure(&vc, "probe_is_allocated", body.blocks.len());
        let has_true_constraint = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && r.head.name != "error")
            .flat_map(|r| r.body.constraints.iter())
            .any(|c| c.to_string().contains("true"));
        assert!(has_true_constraint, "IsAllocated should produce a 'true' constraint");
    });
}

/// IsAllocated hook at Ptr level queries obj_valid[obj_id] instead of true.
/// Part of #2616: CRITICAL finding — IsAllocated previously always returned true,
/// bypassing obj_valid and making CHC unable to detect use-after-free.
#[test]
fn test_kani_hook_is_allocated_ptr_level_queries_obj_valid() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "IsAllocatedHook"]
            pub fn is_allocated(_ptr: *const u8) -> bool { true }
        }

        pub fn probe_is_allocated(ptr: *const u8) -> bool { kani::is_allocated(ptr) }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_allocated");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_is_allocated",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
        assert_vc_structure(&vc, "probe_is_allocated", body.blocks.len());

        // At Ptr level, the constraint should reference obj_valid (via select),
        // NOT a hardcoded "true".
        let has_obj_valid_ref = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && r.head.name != "error")
            .any(|r| r.body.constraints.iter().any(|c| c.to_string().contains("obj_valid")));
        assert!(has_obj_valid_ref, "IsAllocated at Ptr level should query obj_valid");
    });
}

/// Part of #4158: when the destination local has no state index, IsAllocated
/// must still emit a successor transition rather than claiming the call and
/// dropping the edge.
#[test]
fn test_kani_hook_is_allocated_missing_dest_state_idx_emits_transition_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "IsAllocatedHook"]
            pub fn is_allocated(_ptr: *const u8) -> bool { true }
        }

        pub fn probe_is_allocated_missing_dest(ptr: *const u8) -> bool { kani::is_allocated(ptr) }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_allocated_missing_dest");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_is_allocated_missing_dest", ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target) =
            body.blocks
                .iter()
                .enumerate()
                .find_map(|(bb_idx, block)| {
                    let TerminatorKind::Call { func, args, destination, target, .. } =
                        &block.terminator.kind
                    else {
                        return None;
                    };
                    matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::IsAllocated))
                        .then_some((bb_idx, func, args, destination, target))
                })
                .expect("expected IsAllocatedHook call terminator");
        let target = target.expect("IsAllocated call target");

        assert!(chc_ctx.state_var_mgr.local_to_state_idx.remove(&destination.local).is_some());
        assert!(chc_ctx.try_state_idx_for_local(destination.local).is_none());

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();
        let before_rules = chc_ctx.vc.rules.len();
        let before_sound_fallback = chc_ctx.sound_fallback_count();

        let target_some = Some(target);
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_some,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: None,
        };

        assert!(chc_ctx.try_dispatch_call_kani(&dcx));
        assert!(
            chc_ctx.sound_fallback_count() > before_sound_fallback,
            "missing-dest IsAllocated hook should record at least one sound fallback"
        );
        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert!(!emitted.is_empty());
        assert!(
            emitted.iter().any(|rule| rule.body.relation.is_some() && &*rule.head.name != "error")
        );
    });
}

/// Part of #3099: IsAllocated Ptr-level fallback (unsupported pointer arg shape)
/// is now a SOUND over-approximation (nondeterministic boolean). The unsound
/// fallback counter (chc_fallback / DEMOTED) should NOT be incremented.
#[test]
fn test_kani_hook_is_allocated_ptr_level_fallback_increments_chc_fallback_counter() {
    use crate::codegen_ay::chc::get_chc_fallback_counts;

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "IsAllocatedHook"]
            pub fn is_allocated_u32(_x: u32) -> bool { true }
        }

        pub fn probe_is_allocated_u32_fallback_counter(x: u32) -> bool { kani::is_allocated_u32(x) }
    "#;

    let before = get_chc_fallback_counts()
        .get("probe_is_allocated_u32_fallback_counter")
        .copied()
        .unwrap_or(0);
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_allocated_u32_fallback_counter");
        let body = instance.body().expect("function body");

        let _vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_is_allocated_u32_fallback_counter",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
    });
    let after = get_chc_fallback_counts()
        .get("probe_is_allocated_u32_fallback_counter")
        .copied()
        .unwrap_or(0);
    // Part of #3099: IsAllocated reclassified to SOUND_APPROXIMATION.
    // The unsound fallback counter should NOT be incremented.
    assert_eq!(
        after, before,
        "IsAllocated Ptr-level fallback (sound over-approximation) should NOT increment \
         unsound fallback counter for probe_is_allocated_u32_fallback_counter \
         (before={before}, after={after})"
    );
}

/// IsAllocated Ptr-level fallback must produce a nondeterministic boolean, not
/// a hardcoded `true`. A `true` fallback silently hides dangling-pointer bugs
/// by claiming every unresolvable pointer is allocated.
///
/// Regression for #2840: soundness fix.
#[test]
fn test_kani_hook_is_allocated_ptr_level_fallback_is_nondeterministic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "IsAllocatedHook"]
            pub fn is_allocated_u32(_x: u32) -> bool { true }
        }

        pub fn probe_is_allocated_nondet(x: u32) -> bool { kani::is_allocated_u32(x) }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_allocated_nondet");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_is_allocated_nondet",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        // The fallback path should declare a fresh `__is_allocated_nondet_*` variable
        // in the VC variable declarations. If we see `true` hardcoded instead, the
        // soundness bug has regressed.
        let has_nondet_var =
            vc.vars().iter().any(|decl| decl.name.contains("__is_allocated_nondet"));
        assert!(
            has_nondet_var,
            "IsAllocated fallback should declare a nondeterministic variable; \
             vars: {:?}",
            vc.vars().iter().map(|d| &d.name).collect::<Vec<_>>()
        );

        // The constraint should reference the nondeterministic variable, not `true`.
        assert!(
            any_constraint_str(&vc, |c| c.contains("__is_allocated_nondet")),
            "IsAllocated constraint should reference the nondeterministic variable"
        );
    });
}

/// Assume hook emits a guarded transition rule.
#[test]
fn test_kani_hook_assume_emits_guarded_transition() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(cond: bool) { if !cond { panic!("assumption violated") } }
        }

        pub fn probe_assume(x: u32) -> u32 { kani::assume(x > 10); x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assume");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assume", ChcConfig::default());
        let has_assume = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Assume))
            } else {
                false
            }
        });
        assert!(has_assume, "MIR should contain AssumeHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_assume", ChcConfig::default());
        assert_vc_structure(&vc, "probe_assume", body.blocks.len());
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "Assume should emit at least one guarded transition rule"
        );
    });
}

#[test]
fn test_kani_hook_assume_constrains_unit_destination() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(cond: bool) { if !cond { panic!("assumption violated") } }
        }

        pub fn probe_assume_unit_dest(x: u32) -> u32 {
            let marker = kani::assume(x > 10);
            let _ = marker;
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assume_unit_dest");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_assume_unit_dest", ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, args, destination, target, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Assume)).then_some((
                    bb_idx,
                    func,
                    args,
                    destination,
                    target,
                ))
            })
            .expect("expected AssumeHook call terminator");
        let target = target.expect("assume call target");

        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for assume block").clone();
        let from_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, from_args);
        let modified_locals = HashSet::new();
        let before_rules = chc_ctx.vc.rules.len();

        let target_some = Some(target);
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_some,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: None,
        };

        assert!(chc_ctx.try_dispatch_call_kani(&dcx), "kani dispatch should handle AssumeHook");
        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "assume dispatch should emit one rule"
        );

        let rule = chc_ctx.vc.rules.last().expect("assume transition rule");
        let dest_vec_idx = chc_ctx
            .try_state_idx_for_local(destination.local)
            .expect("assume destination state index");
        let dest_out_name = &chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0;
        let dest_constrained = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name == dest_out_name.as_ref())
            })
        });
        assert!(
            dest_constrained,
            "kani::assume should constrain its unit destination output slot {}; constraints={:?}",
            dest_out_name, rule.body.constraints
        );
    });
}

/// PointerObject hook returns nondeterministic value (destination unconstrained).
#[test]
fn test_kani_hook_pointer_object_produces_nondet_dest() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "PointerObjectHook"]
            pub fn pointer_object(_ptr: *const u8) -> usize { 0 }
        }

        pub fn probe_pointer_object(ptr: *const u8) -> usize { kani::pointer_object(ptr) }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pointer_object");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_pointer_object", ChcConfig::default());
        let has_hook = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::PointerObject))
            } else {
                false
            }
        });
        assert!(has_hook, "MIR should contain PointerObjectHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_pointer_object", ChcConfig::default());
        assert_vc_structure(&vc, "probe_pointer_object", body.blocks.len());
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "PointerObject should emit at least one transition rule"
        );
    });
}

/// UnsupportedCheck hook emits unconditional error rule.
#[test]
fn test_kani_hook_unsupported_check_emits_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "UnsupportedCheckHook"]
            pub fn unsupported_check() { panic!("unsupported") }
        }

        pub fn probe_unsupported() { kani::unsupported_check(); }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsupported");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unsupported", ChcConfig::default());
        let has_hook = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::UnsupportedCheck))
            } else {
                false
            }
        });
        assert!(has_hook, "MIR should contain UnsupportedCheckHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_unsupported", ChcConfig::default());
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "UnsupportedCheck hook should emit at least one error rule"
        );
    });
}

/// UnsupportedCheck remains fail-closed under `prove_safety_only`.
#[test]
fn test_kani_hook_unsupported_check_prove_safety_only_still_emits_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "UnsupportedCheckHook"]
            pub fn unsupported_check() { panic!("unsupported") }
        }

        pub fn probe_unsupported_prove_safety_only() { kani::unsupported_check(); }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsupported_prove_safety_only");
        let body = instance.body().expect("function body");
        let cfg = ChcConfig { prove_safety_only: true, ..ChcConfig::default() };

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unsupported_prove_safety_only", cfg);
        let has_hook = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::UnsupportedCheck))
            } else {
                false
            }
        });
        assert!(has_hook, "MIR should contain UnsupportedCheckHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_unsupported_prove_safety_only", cfg);
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "UnsupportedCheck must remain fail-closed in prove_safety_only mode"
        );
    });
}

/// Cover hook emits a no-op transition (informational marker only).
#[test]
fn test_kani_hook_cover_emits_passthrough_transition() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "CoverHook"]
            pub fn cover(_cond: bool) {}
        }

        pub fn probe_cover(x: u32) -> u32 { kani::cover(x > 5); x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cover");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cover", ChcConfig::default());
        let has_hook = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Cover))
            } else {
                false
            }
        });
        assert!(has_hook, "MIR should contain CoverHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_cover", ChcConfig::default());
        assert_vc_structure(&vc, "probe_cover", body.blocks.len());
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "Cover should emit passthrough transition rules"
        );
    });
}

/// Offset model generates pointer arithmetic constraint.
#[test]
fn test_kani_model_offset_constrains_dest_to_arithmetic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani_models {
            #[kanitool::fn_marker = "OffsetModel"]
            pub fn offset(base: *const u32, count: isize) -> *const u32 {
                unsafe { base.offset(count) }
            }
        }

        pub fn probe_offset(base: *const u32) -> *const u32 { kani_models::offset(base, 3) }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_offset");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_offset", ChcConfig::default());
        let has_model = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_model(func), Some(KaniModel::Offset))
            } else {
                false
            }
        });
        assert!(has_model, "MIR should contain OffsetModel call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_offset", ChcConfig::default());
        assert_vc_structure(&vc, "probe_offset", body.blocks.len());
        let has_constraints = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && r.head.name != "error")
            .any(|r| !r.body.constraints.is_empty());
        assert!(has_constraints, "Offset model should produce at least one constraint");
    });
}

/// PanicStub model produces a no-op transition.
#[test]
fn test_kani_model_panic_stub_produces_transition() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani_models {
            #[kanitool::fn_marker = "PanicStub"]
            pub fn panic_stub() {}
        }

        pub fn probe_panic_stub() { kani_models::panic_stub(); }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_panic_stub");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_panic_stub", ChcConfig::default());
        let has_model = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_model(func), Some(KaniModel::PanicStub))
            } else {
                false
            }
        });
        assert!(has_model, "MIR should contain PanicStub model call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_panic_stub", ChcConfig::default());
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "PanicStub model should emit at least one transition rule"
        );
    });
}

/// SafetyCheckNoAssume emits error rule but transitions unconditionally.
#[test]
fn test_kani_hook_safety_check_no_assume_emits_error_without_assume() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "SafetyCheckNoAssumeHook"]
            pub fn safety_check_no_assume(cond: bool) {
                if !cond { panic!("safety check no assume") }
            }
        }

        pub fn probe_safety_no_assume(x: u32) -> u32 {
            kani::safety_check_no_assume(x > 0);
            x + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_safety_no_assume");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_safety_no_assume", ChcConfig::default());
        let has_hook = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::SafetyCheckNoAssume))
            } else {
                false
            }
        });
        assert!(has_hook, "MIR should contain SafetyCheckNoAssumeHook call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_safety_no_assume", ChcConfig::default());
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "SafetyCheckNoAssume should emit at least one error rule"
        );
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "SafetyCheckNoAssume should emit transition rules (unconditional continuation)"
        );
    });
}

/// Kani hook dispatch must record diverging-drop metrics when a recognized hook
/// is invoked with `target=None` (#2727).
#[test]
fn test_kani_hook_target_none_records_diverging_drop_count() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(cond: bool) {
                if !cond { panic!("assumption violated") }
            }
        }

        pub fn probe_assume_target_none(x: u32) -> u32 {
            kani::assume(x > 0);
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assume_target_none");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_assume_target_none", ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                    && matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Assume))
                {
                    Some((bb_idx, func, args, destination))
                } else {
                    None
                }
            })
            .expect("expected AssumeHook call terminator");

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();

        let target_none = None;
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_none,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: None,
        };
        let handled = chc_ctx.try_dispatch_call_kani(&dcx);

        assert!(handled, "kani dispatch should claim recognized AssumeHook call");
        assert_eq!(
            chc_ctx.diagnostics.diverging_call_drop.get(),
            1,
            "target=None KaniHook::Assume should record one diverging drop"
        );
    });
}

/// Kani model dispatch must record diverging-drop metrics when a recognized
/// model call is invoked with `target=None` (#2727).
#[test]
fn test_kani_model_target_none_records_diverging_drop_count() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani_models {
            #[kanitool::fn_marker = "OffsetModel"]
            pub fn offset(base: *const u32, count: isize) -> *const u32 {
                unsafe { base.offset(count) }
            }
        }

        pub fn probe_offset_target_none(base: *const u32) -> *const u32 {
            kani_models::offset(base, 3)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_offset_target_none");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_offset_target_none", ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                    && matches!(chc_ctx.detect_kani_model(func), Some(KaniModel::Offset))
                {
                    Some((bb_idx, func, args, destination))
                } else {
                    None
                }
            })
            .expect("expected OffsetModel call terminator");

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();

        let target_none = None;
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_none,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: None,
        };
        let handled = chc_ctx.try_dispatch_call_kani(&dcx);

        assert!(handled, "kani dispatch should claim recognized OffsetModel call");
        assert_eq!(
            chc_ctx.diagnostics.diverging_call_drop.get(),
            1,
            "target=None KaniModel::Offset should record one diverging drop"
        );
    });
}

/// Unmarked `kani::safety_check` calls should still be claimed by the
/// path-based fallback in `try_dispatch_call_kani`.
#[test]
fn test_unmarked_kani_safety_check_path_dispatch_claims_call() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub fn safety_check(cond: bool, _msg: &'static str) {
                if !cond {
                    panic!("safety check");
                }
            }
        }

        pub fn probe_unmarked_safety_check(x: u32) {
            kani::safety_check(x > 0, "x must be positive");
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unmarked_safety_check");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_unmarked_safety_check", ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, args, destination, target, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                let callee_path = chc_ctx.resolve_callee_path(func)?;
                if callee_path.contains("kani::") && callee_path.ends_with("::safety_check") {
                    Some((bb_idx, func, args, destination, target, callee_path))
                } else {
                    None
                }
            })
            .expect("expected unmarked kani::safety_check call terminator");

        assert!(
            chc_ctx.detect_kani_hook(func).is_none(),
            "test fixture must exercise unmarked path fallback, not marker detection"
        );

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: Some(callee_path),
        };

        let handled = chc_ctx.try_dispatch_call_kani(&dcx);
        assert!(handled, "unmarked kani::safety_check should be claimed by path fallback");
        assert!(
            chc_ctx.vc.rules.iter().any(|rule| rule.head.name == "error"),
            "path fallback safety_check should emit an error rule"
        );
        assert!(
            chc_ctx.diagnostics.diverging_call_drop.get() == 0,
            "path fallback safety_check should stay on the normal call path"
        );
    });
}

/// Unmarked `kani::safety_check_no_assume` calls should also be claimed by the
/// path-based fallback in `try_dispatch_call_kani`.
#[test]
fn test_unmarked_kani_safety_check_no_assume_path_dispatch_claims_call() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub fn safety_check_no_assume(cond: bool, _msg: &'static str) {
                if !cond {
                    panic!("safety check");
                }
            }
        }

        pub fn probe_unmarked_safety_check_no_assume(x: u32) {
            kani::safety_check_no_assume(x > 0, "x must be positive");
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unmarked_safety_check_no_assume");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_unmarked_safety_check_no_assume",
            ChcConfig::default(),
        );

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, args, destination, target, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                let callee_path = chc_ctx.resolve_callee_path(func)?;
                if callee_path.contains("kani::")
                    && callee_path.ends_with("::safety_check_no_assume")
                {
                    Some((bb_idx, func, args, destination, target, callee_path))
                } else {
                    None
                }
            })
            .expect("expected unmarked kani::safety_check_no_assume call terminator");

        assert!(
            chc_ctx.detect_kani_hook(func).is_none(),
            "test fixture must exercise unmarked path fallback, not marker detection"
        );

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: Some(callee_path),
        };

        let handled = chc_ctx.try_dispatch_call_kani(&dcx);
        assert!(
            handled,
            "unmarked kani::safety_check_no_assume should be claimed by path fallback"
        );
        assert!(
            chc_ctx.vc.rules.iter().any(|rule| rule.head.name == "error"),
            "path fallback safety_check_no_assume should emit an error rule"
        );
        assert!(
            chc_ctx.diagnostics.diverging_call_drop.get() == 0,
            "path fallback safety_check_no_assume should stay on the normal call path"
        );
    });
}

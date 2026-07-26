// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR-backed production-path tests for `template_check.rs` (TIC).
//!
//! Covers the VC clearing semantics of `apply_template_check()`:
//! - On a detected accumulator pattern, TIC verifies 3 SMT checks (initiation,
//!   consecution, safety) and replaces the VC with a trivially safe system.
//! - On no supported pattern, the VC is unchanged.
//!
//! These tests use the FULL translation pipeline (`mir_to_chc`) which includes
//! TIC, as opposed to `test_lemma_linearize.rs` which stops before TIC.
//!
//! Part of #3644: MIR-backed coverage for loop guidance postpasses.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Source code fixtures (unique names per D5 to avoid registry bleed-through)
// =============================================================================

/// Forward accumulator: `sum += counter; counter += 1; while counter < n`.
const FORWARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_tic_forward(n: u32) -> u32 {
        let mut sum: u32 = 0;
        let mut counter: u32 = 0;
        while counter < n {
            sum += counter;
            counter += 1;
        }
        sum
    }
"#;

/// Countdown accumulator: `sum += n; counter -= 1; while counter > 0`.
/// The detector requires `sum` to be incremented by a loop-INVARIANT variable
/// (`n`, which is not modified in the loop body), and `counter` to be
/// decremented by a constant.
const COUNTDOWN_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_tic_countdown(n: u32) -> u32 {
        let mut sum: u32 = 0;
        let mut counter: u32 = n;
        while counter > 0 {
            sum += n;
            counter -= 1;
        }
        sum
    }
"#;

/// No loop — TIC should not fire.
const NO_LOOP_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_tic_noop(x: u32) -> u32 {
        x + 1
    }
"#;

/// Loop without supported accumulator pattern — TIC should not fire.
const NON_ACCUMULATOR_LOOP_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_tic_non_accum(n: u32) -> u32 {
        let mut x: u32 = 1;
        let mut i: u32 = 0;
        while i < n {
            x = x.wrapping_mul(2);
            i += 1;
        }
        x
    }
"#;

// =============================================================================
// Helper functions
// =============================================================================

/// Generate a VC with int_lift enabled through the FULL translation pipeline
/// (including TIC). If TIC succeeds, rules will be cleared.
fn vc_full_pipeline(source: &str, fn_name: &str) -> trust_mc_core::chc::ChcVc {
    let mut result = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { int_lift: true, ..ChcConfig::default() },
        );
        result = Some(vc);
    });
    result.expect("vc should be produced")
}

/// Generate a VC with int_lift enabled, stopping before TIC.
/// Used to confirm rules exist before TIC would clear them.
fn vc_pre_tic(source: &str, fn_name: &str) -> trust_mc_core::chc::ChcVc {
    let mut result = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_skip_tic(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { int_lift: true, ..ChcConfig::default() },
        );
        result = Some(vc);
    });
    result.expect("vc should be produced")
}

// =============================================================================
// Tests: Forward accumulator
// =============================================================================

#[test]
fn test_template_check_forward_pre_tic_has_rules() {
    // Precondition: before TIC, the forward accumulator VC has rules.
    let vc = vc_pre_tic(FORWARD_SOURCE, "probe_tic_forward");
    assert!(!vc.rules.is_empty(), "pre-TIC forward accumulator VC should have rules, got 0");
}

#[test]
fn test_template_check_forward_clears_rules() {
    // After the full pipeline (including TIC), the forward accumulator
    // should have its VC cleared (TIC success → trivially safe system).
    let vc = vc_full_pipeline(FORWARD_SOURCE, "probe_tic_forward");
    assert!(
        vc.rules.is_empty(),
        "TIC should clear all rules on successful forward accumulator detection, \
         but {} rules remain",
        vc.rules.len()
    );
}

// =============================================================================
// Tests: Countdown accumulator
// =============================================================================

#[test]
fn test_template_check_countdown_pre_tic_has_rules() {
    let vc = vc_pre_tic(COUNTDOWN_SOURCE, "probe_tic_countdown");
    assert!(!vc.rules.is_empty(), "pre-TIC countdown accumulator VC should have rules, got 0");
}

#[test]
fn test_template_check_countdown_clears_rules() {
    let vc = vc_full_pipeline(COUNTDOWN_SOURCE, "probe_tic_countdown");
    assert!(
        vc.rules.is_empty(),
        "TIC should clear all rules on successful countdown accumulator detection, \
         but {} rules remain",
        vc.rules.len()
    );
}

// =============================================================================
// Tests: Negative cases (TIC should NOT fire)
// =============================================================================

#[test]
fn test_template_check_noop_preserves_rules() {
    // No loop → no TIC. VC should have rules.
    let vc = vc_full_pipeline(NO_LOOP_SOURCE, "probe_tic_noop");
    assert!(
        !vc.rules.is_empty(),
        "TIC should not fire on a function without loops — rules should be preserved"
    );
}

#[test]
fn test_template_check_non_accumulator_preserves_rules() {
    // Loop without supported accumulator pattern → TIC should not clear rules.
    let vc_pre = vc_pre_tic(NON_ACCUMULATOR_LOOP_SOURCE, "probe_tic_non_accum");
    let pre_count = vc_pre.rules.len();
    assert!(pre_count > 0, "non-accumulator loop should produce rules");

    let vc_post = vc_full_pipeline(NON_ACCUMULATOR_LOOP_SOURCE, "probe_tic_non_accum");
    assert!(
        !vc_post.rules.is_empty(),
        "TIC should not fire on a non-accumulator loop — rules should be preserved. \
         Pre-TIC had {} rules, post-TIC has {}",
        pre_count,
        vc_post.rules.len()
    );
}

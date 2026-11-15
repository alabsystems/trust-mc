// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A panic arm inside an inlined body is an obligation, not dead code.
//!
//! The inline walker filters a `SwitchInt` arm that diverges into the panic
//! machinery out of the ITE (#4050) so an `Option::unwrap` does not consume
//! SwitchInt depth. Filtering alone assumed the arm untaken: `guard(x)` with
//! `if x > 10 { panic!() }` inlined into a harness proved clean for every `x`.
//! The filtered arm's "not taken" condition is recorded as a check now, on
//! both the side-channel and the value channel, so the host emits the error
//! rule a MIR `Assert` would get. The second probe pins that the recorded
//! obligation is exact: constrained away by the caller, the same check
//! discharges.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

const INLINE_PANIC_ARM_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn guard(x: u32) {
        if x > 10 {
            panic!("x too big");
        }
    }

    // The inlined panic arm is reachable: an error rule, and a reachable one.
    pub fn probe_inlined_panic_arm_reachable(x: u32) {
        guard(x);
    }

    // The caller rules the panic arm out: the obligation is recorded and holds.
    pub fn probe_inlined_panic_arm_discharged(x: u32) {
        if x < 5 {
            guard(x);
        }
    }
"#;

fn translate_probe(tcx: rustc_middle::ty::TyCtxt<'_>, fn_name: &str) -> trust_mc_core::chc::ChcVc {
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
    let (vc, _, _) = chc_ctx.translate_with_diagnostics();
    assert_vc_structure(&vc, fn_name, body.blocks.len());
    vc
}

fn error_rule_count(vc: &trust_mc_core::chc::ChcVc) -> usize {
    vc.rules.iter().filter(|rule| rule.head.name.starts_with("error")).count()
}

#[test]
fn test_inlined_panic_arm_emits_reachable_error_rule() {
    with_test_ay_ctx_for_source(INLINE_PANIC_ARM_SOURCE, |ctx| {
        let fn_name = "probe_inlined_panic_arm_reachable";
        let vc = translate_probe(ctx.tcx, fn_name);
        assert!(
            error_rule_count(&vc) > 0,
            "{fn_name}: the inlined `if x > 10 {{ panic!() }}` arm must emit an error rule; \
             rules={:?}",
            vc.rules.iter().map(|rule| format!("{rule:?}")).collect::<Vec<_>>()
        );
        // `x = 11` panics in Rust: the error must stay reachable.
        assert_z3_result(&emit_chc(&vc).to_string(), "sat");
    });
}

#[test]
fn test_inlined_panic_arm_obligation_discharges_when_unreachable() {
    with_test_ay_ctx_for_source(INLINE_PANIC_ARM_SOURCE, |ctx| {
        let fn_name = "probe_inlined_panic_arm_discharged";
        let vc = translate_probe(ctx.tcx, fn_name);
        assert!(
            error_rule_count(&vc) > 0,
            "{fn_name}: the obligation is recorded even where the caller discharges it"
        );
        // `x < 5` rules the arm out: the recorded check is exact, not a havoc.
        assert_z3_result(&emit_chc(&vc).to_string(), "unsat");
    });
}

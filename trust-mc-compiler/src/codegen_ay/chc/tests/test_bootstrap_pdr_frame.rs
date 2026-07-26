// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for pdr_frame MustSummaries inline encoding.
//!
//! Part of #3836: `MustSummaries::add(...)` was over the 16-block inline budget.
//! Factored into `reject_existing` + `record_true_key` + `push_entry` + small `add`.
//! Each helper fits under the 16-block shared inline gate.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const PDR_FRAME_MUST_SUMMARIES_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    type PredicateId = u32;
    const EXPR_TRUE: u8 = 0;
    const EXPR_FALSE: u8 = 1;

    #[derive(Clone, Copy)]
    struct MustSummaries {
        ent_level: u32,
        ent_pred: PredicateId,
        ent_form: u8,
        has_entry: bool,
        ht_level: u32,
        ht_pred: PredicateId,
        has_true: bool,
    }

    impl MustSummaries {
        fn new() -> Self {
            Self {
                ent_level: 0,
                ent_pred: 0,
                ent_form: 0,
                has_entry: false,
                ht_level: 0,
                ht_pred: 0,
                has_true: false,
            }
        }

        fn has_true_for(&self, level: u32, pred: PredicateId) -> bool {
            self.has_true && self.ht_level == level && self.ht_pred == pred
        }

        fn contains(&self, level: u32, pred: PredicateId, formula: u8) -> bool {
            self.has_entry
                && self.ent_level == level
                && self.ent_pred == pred
                && self.ent_form == formula
        }

        fn reject_existing(&self, level: u32, pred: PredicateId, formula: u8) -> bool {
            formula == EXPR_FALSE
                || self.has_true_for(level, pred)
                || self.contains(level, pred, formula)
        }

        fn record_true_key(&mut self, level: u32, pred: PredicateId) {
            if !self.has_true {
                self.ht_level = level;
                self.ht_pred = pred;
                self.has_true = true;
            }
        }

        fn push_entry(&mut self, level: u32, pred: PredicateId, formula: u8) {
            if !self.has_entry {
                self.ent_level = level;
                self.ent_pred = pred;
                self.ent_form = formula;
                self.has_entry = true;
            }
        }

        fn add(&mut self, level: u32, pred: PredicateId, formula: u8) -> bool {
            if self.reject_existing(level, pred, formula) {
                return false;
            }
            if formula == EXPR_TRUE {
                self.record_true_key(level, pred);
            }
            self.push_entry(level, pred, formula);
            true
        }
    }

    pub fn probe_must_summaries_dedup() {
        let mut summaries = MustSummaries::new();
        let pred: u8 = kani::any();
        kani::assume(pred < 4);
        let pred = pred as PredicateId;
        let level: u8 = kani::any();
        kani::assume(level < 3);
        let level = level as u32;
        let formula: u8 = kani::any();
        kani::assume(formula < 4);
        kani::assume(formula >= 2);

        let _first = summaries.add(level, pred, formula);
        let second = summaries.add(level, pred, formula);

        assert!(!second, "Duplicate formula should be rejected");
    }

    pub fn probe_must_summaries_true_subsumes() {
        let mut summaries = MustSummaries::new();
        let pred: u8 = kani::any();
        kani::assume(pred < 4);
        let pred = pred as PredicateId;

        let added_true = summaries.add(1, pred, EXPR_TRUE);
        kani::assume(added_true);

        let added_int = summaries.add(1, pred, 2);
        assert!(!added_int, "Non-true formula should be rejected after true");
    }
"#;

const PROBE_FN_NAMES: [&str; 2] =
    ["probe_must_summaries_dedup", "probe_must_summaries_true_subsumes"];

fn reset_pdr_frame_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

#[test]
fn test_must_summaries_dedup_no_inferable_predicate() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_pdr_frame_counters();

    with_test_ay_ctx_for_source(PDR_FRAME_MUST_SUMMARIES_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        }

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        assert_eq!(
            inferable_count, 0,
            "probe should not produce inferable_predicate fallbacks, count={inferable_count}"
        );

        // Note: unhandled_call may be non-zero in the unit test context because
        // struct method dispatch is handled by the full driver pipeline, not by
        // mir_to_chc alone. The authoritative check is inferable_predicate=0
        // (above) and the compiletest PROOF verdict (D4).
        let _ = crate::codegen_ay::take_unhandled_call_by_fn();
    });

    reset_pdr_frame_counters();
}

#[test]
fn test_must_summaries_dedup_emits_no_p_inf_rules() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_pdr_frame_counters();

    with_test_ay_ctx_for_source(PDR_FRAME_MUST_SUMMARIES_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");

            let inferable_decls: Vec<_> = vc
                .vars()
                .iter()
                .filter(|decl| decl.name.contains("P_inf_"))
                .map(|decl| decl.name.clone())
                .collect();
            assert!(
                inferable_decls.is_empty(),
                "{fn_name} should not emit P_inf_* declarations: {inferable_decls:?}"
            );

            let has_p_inf = vc.rules.iter().any(|rule| format!("{:?}", rule).contains("P_inf_"));
            assert!(
                !has_p_inf,
                "{fn_name} should not reference P_inf_* summaries in emitted rules"
            );
        }
    });

    reset_pdr_frame_counters();
}

// Note: full unsat verification depends on the compiletest driver (D4), not
// the unit test, because the driver provides additional struct-layout handling
// that mir_to_chc alone does not exercise. The compiletest is the authoritative
// proof check for this harness.

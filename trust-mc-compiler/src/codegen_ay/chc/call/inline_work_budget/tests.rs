// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::chc::call::codegen_call_virtual_inline::translate_virtual_body_inline;
use crate::codegen_ay::chc::call::inline_body::speculative_inline;
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
use crate::codegen_ay::chc::rules::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::rules::codegen_rules_entry::CodegenRulesEntry;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::Expr;
use std::collections::HashMap;

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn chain0(x: u8) -> u8 { chain1(x) }
    fn chain1(x: u8) -> u8 { chain2(x) }
    fn chain2(x: u8) -> u8 { chain3(x) }
    fn chain3(x: u8) -> u8 { chain4(x) }
    fn chain4(x: u8) -> u8 { chain5(x) }
    fn chain5(x: u8) -> u8 { chain6(x) }
    fn chain6(x: u8) -> u8 { chain7(x) }
    fn chain7(x: u8) -> u8 { chain8(x) }
    fn chain8(x: u8) -> u8 { x ^ 3 }

    pub fn branching(n: u8) -> u8 {
        if n == 0 { 1 } else { branching(n - 1).wrapping_add(branching(n - 1)) }
    }

    static mut CELL: i32 = 0;
    struct Concrete;
    impl Drop for Concrete {
        fn drop(&mut self) { unsafe { CELL += 1; } }
    }
    pub fn nested_box_dyn_drop() {
        { let _plain: Box<dyn Send> = Box::new(Concrete {}); }
        unsafe { assert!(CELL == 1); CELL = 0; }
        {
            let inner: Box<dyn Send> = Box::new(Concrete {});
            let _nested: Box<dyn Send> = Box::new(inner);
        }
        unsafe { assert!(CELL == 1); }
    }
"#;

#[test]
fn failed_speculative_attempts_do_not_refund_the_shared_budget() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "chain0").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "rollback_budget", ChcConfig::default());
        chc.inline_work_budget = InlineWorkBudget::with_limit(3);
        let mut attempts = 0;
        for _ in 0..8 {
            let failed = speculative_inline(&mut chc, |_| {
                attempts += 1;
                None::<()>
            });
            assert!(failed.is_none());
        }
        assert_eq!(attempts, 3, "refused attempts must stop before another snapshot or body");
        assert_eq!(chc.inline_work_budget.spent, 3);
        assert!(chc.inline_work_budget.reported);
        assert_eq!(chc.diagnostics.place_translation_drop.get(), 1);
        assert_eq!(fallback_soundness(INLINE_WORK_BUDGET_EXHAUSTED), FallbackSoundness::FailClose);
    });
}

#[test]
fn nested_and_sibling_speculation_share_work_and_keep_refusal_debt() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "chain0").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "nested_budget", ChcConfig::default());
        chc.inline_work_budget = InlineWorkBudget::with_limit(5);
        let mut children = 0;
        let failed = speculative_inline(&mut chc, |chc| {
            for _ in 0..12 {
                let _ = speculative_inline(chc, |_| {
                    children += 1;
                    None::<()>
                });
            }
            None::<()>
        });
        assert!(failed.is_none());
        assert_eq!(children, 4);
        let sibling = speculative_inline(&mut chc, |_| Some(17));
        assert!(sibling.is_none(), "rollback cannot make a sibling clean or executable again");
        assert_eq!(chc.inline_work_budget.spent, 5);
        assert_eq!(chc.diagnostics.place_translation_drop.get(), 1);
    });
}

#[test]
fn actual_nine_body_chain_keeps_its_exact_return_beyond_the_old_depth_four() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "chain0");
        let body = instance.callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "deep_chain", ChcConfig::default());
        let result = translate_virtual_body_inline(
            &mut chc,
            &body,
            &[Expr::bitvec_const(17u8, 8)],
            0,
            &HashMap::new(),
            Some(instance),
            0,
        )
        .expect("an admitted acyclic chain still reaches its real leaf body");
        assert_eq!(
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&result.value),
            Some(Expr::bitvec_const(18u8, 8)),
        );
        assert!(!chc.inline_work_budget.reported);
        assert!(chc.inline_work_budget.spent > 9);
        assert_eq!(chc.diagnostics.place_translation_drop.get(), 0);
    });
}

#[test]
fn actual_branching_recursion_spends_one_cumulative_budget() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "branching");
        let body = instance.callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "branching_budget", ChcConfig::default());
        chc.inline_work_budget = InlineWorkBudget::with_limit(64);
        let _result = translate_virtual_body_inline(
            &mut chc,
            &body,
            &[Expr::bitvec_const(8u8, 8)],
            0,
            &HashMap::new(),
            Some(instance),
            0,
        );
        assert_eq!(chc.inline_work_budget.spent, 64);
        assert!(chc.inline_work_budget.reported);
        assert!(chc.diagnostics.place_translation_drop.get() > 0);
    });
}

#[test]
fn actual_nested_box_dyn_drop_translation_finishes_with_bounded_fail_closed_work() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "nested_box_dyn_drop").callee_body().unwrap();
        let config = ChcConfig {
            track_level: crate::args::ChcTrackLevel::Mem,
            frame_narrowing: false,
            frame_narrowing_flattened: false,
            ..ChcConfig::default()
        };
        let mut chc = ChcCtx::new(ctx.tcx, &body, "nested_box_dyn_drop", config);
        chc.declare_block_relations();
        chc.declare_error_relation();
        chc.emit_entry_rule();
        chc.generate_transition_rules();
        assert!(chc.inline_work_budget.spent > 0, "walk the actual destructor bodies");
        assert!(chc.inline_work_budget.spent <= MAX_INLINE_WORK);
        // A future exact dyn-drop model may finish without exhausting work.
        // If expansion is cut off, its debt must survive every rollback.
        if chc.inline_work_budget.reported {
            assert!(chc.diagnostics.place_translation_drop.get() > 0);
        }
        assert!(
            chc.vc.rules.iter().any(|rule| rule.head.name.as_str().starts_with("error")),
            "bounded refusal cannot erase the source's checks"
        );
    });
}

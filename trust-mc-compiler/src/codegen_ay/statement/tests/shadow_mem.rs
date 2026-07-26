// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for fail-closed BMC shadow-memory fallbacks.

use super::*;
use crate::kani_middle::kani_functions::KaniModel;

const SHADOW_MEM_PROBE: &str = r#"
pub fn shadow_mem_probe() {}
"#;

#[test]
fn untranslatable_shadow_mem_set_fails_closed_without_blessing_state() {
    with_test_ay_ctx_for_source(SHADOW_MEM_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shadow_mem_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        ctx.config.uninit_checks = true;
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        codegen.codegen_shadow_mem_initialize();
        let before_state = codegen.ctx.shadow_mem_exprs().expect("initialized shadow state");
        let before_violations = codegen.ctx.bmc_vc.violations.len();

        // A slice setter requires a pointer and length. Empty operands force
        // the production translation failure path.
        codegen.codegen_shadow_mem_set(KaniModel::SetSlicePtrInitialized, &[]);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            before_violations + 1,
            "an untranslatable shadow-memory update must add a failing property"
        );
        assert!(
            codegen.ctx.unsupported_constructs.contains_key("shadow_mem_set_untranslatable"),
            "the encoding gap must be visible to the verdict demotion pipeline"
        );
        let after_state = codegen.ctx.shadow_mem_exprs().expect("shadow state remains initialized");
        assert_eq!(
            after_state.init.to_string(),
            before_state.init.to_string(),
            "translation failure must not bless or otherwise mutate initialization state"
        );
    });
}

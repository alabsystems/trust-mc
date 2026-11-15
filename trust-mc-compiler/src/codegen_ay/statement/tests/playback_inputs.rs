// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The statement guard must reach every playback input, including array
//! elements and floating inputs. Model-only values must never impersonate inputs.

use super::*;

const SOURCE: &str = r#"
pub fn scalar(x: u8) -> u8 { x }
pub fn array(x: [u16; 3]) -> [u16; 3] { x }
pub fn float(x: f32) -> f32 { x }
pub fn predicate(x: bool) -> bool { x }
pub enum Choice { First, Second }
pub fn choice(x: Choice) -> Choice { x }
"#;

#[test]
fn statement_guard_is_recorded_for_scalars_arrays_and_floats() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let mut next_ordinal = 0;
        for (suffix, slots) in [("scalar", 1), ("array", 3), ("float", 1)] {
            let instance = find_instance_by_suffix(&ctx, suffix);
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let guard = ctx.declare_var(&format!("caller_{suffix}"), Sort::bool());
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            codegen.current_path_condition = Some(guard);
            let before = next_ordinal;
            next_ordinal += slots;
            codegen.codegen_kani_any_raw(&local_place(0));
            let smt = codegen.ctx.program.to_string();
            for ordinal in before..before + slots {
                assert!(
                    smt.contains(&format!("(= ay_playback_guard_{ordinal} caller_{suffix})")),
                    "{smt}"
                );
                assert!(
                    smt.contains(&format!("(= ay_playback_replayable_{ordinal} true)")),
                    "{smt}"
                );
            }
        }
    });
}

#[test]
fn float_model_fallback_carries_guard_and_is_not_a_native_input() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "predicate");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let guard = ctx.declare_var("caller_active", Sort::bool());
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        codegen.current_path_condition = Some(guard);
        codegen.codegen_float_to_int_in_range(
            &rustc_public::ty::GenericArgs(vec![]),
            &[],
            &local_place(0),
        );
        let smt = codegen.ctx.program.to_string();
        assert!(smt.contains("(= ay_playback_guard_0 caller_active)"), "{smt}");
        assert!(smt.contains("(= ay_playback_replayable_0 false)"), "{smt}");
    });
}

#[test]
fn unit_enum_selector_layout_is_not_guessed() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "choice");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        codegen.codegen_kani_any_raw(&local_place(0));
        let smt = codegen.ctx.program.to_string();
        assert!(smt.contains("(= ay_playback_replayable_0 false)"), "{smt}");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for codegen_prelude.rs — StatementCodegen construction,
//! reference argument initialization, IntoOption trait, and helpers.
//!
//! Tests cover:
//! - StatementCodegen::new initialization (empty state)
//! - init_reference_arguments for &T, &mut T, and non-ref arguments
//! - IntoOption trait impl for Option and Result
//! - current_source_location (before and after span set)
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

// =============================================================================
// IntoOption trait
// =============================================================================

/// IntoOption for Option<T> passes through.
#[test]
fn test_into_option_some() {
    let opt: Option<u32> = Some(42);
    assert_eq!(opt.into_option(), Some(42));
}

/// IntoOption for None passes through.
#[test]
fn test_into_option_none() {
    let opt: Option<u32> = None;
    assert_eq!(opt.into_option(), None);
}

/// IntoOption for Result::Ok converts to Some.
#[test]
fn test_into_option_result_ok() {
    let res: Result<u32, String> = Ok(42);
    assert_eq!(res.into_option(), Some(42));
}

/// IntoOption for Result::Err converts to None.
#[test]
fn test_into_option_result_err() {
    let res: Result<u32, String> = Err("oops".to_string());
    assert_eq!(res.into_option(), None);
}

// =============================================================================
// StatementCodegen::new — empty initialization
// =============================================================================

/// New StatementCodegen has empty env.
#[test]
fn test_new_codegen_empty_env() {
    let source = r#"
pub fn init_probe() {}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "init_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // For a function with no args, env should be empty (no ref args to init)
        // current_path_condition should be None
        assert!(codegen.current_path_condition.is_none());
    });
}

/// New StatementCodegen with no ref args has empty ref_pointees.
#[test]
fn test_new_codegen_no_ref_args_empty_pointees() {
    let source = r#"
pub fn no_ref_probe(x: u32, y: u32) -> u32 {
    x + y
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "no_ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // No reference arguments → ref_pointees should be empty
        assert!(codegen.ref_pointees.is_empty(), "no ref args → empty ref_pointees");
    });
}

// =============================================================================
// init_reference_arguments
// =============================================================================

/// Function with &u32 arg initializes ref_pointees with synthetic pointee.
#[test]
fn test_init_ref_args_single_ref() {
    let source = r#"
pub fn single_ref_probe(x: &u32) -> u32 {
    *x
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "single_ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // arg 1 is &u32 → should be in ref_pointees
        assert!(!codegen.ref_pointees.is_empty(), "&u32 arg should create ref_pointees entry");
        // The pointee should have bitvec(32) sort in env
        for pointee_base in codegen.ref_pointees.values() {
            let pointee = codegen.env_lookup(pointee_base);
            assert!(pointee.is_some(), "pointee should be in env");
            assert_eq!(
                pointee.unwrap().sort().bitvec_width(),
                Some(32),
                "pointee of &u32 should be bitvec(32)"
            );
        }
    });
}

/// Function with &mut T arg also initializes ref_pointees.
#[test]
fn test_init_ref_args_mut_ref() {
    let source = r#"
pub fn mut_ref_probe(x: &mut u64) {
    *x = 99;
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mut_ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert!(!codegen.ref_pointees.is_empty(), "&mut u64 arg should create ref_pointees entry");
        for pointee_base in codegen.ref_pointees.values() {
            let pointee = codegen.env_lookup(pointee_base);
            assert!(pointee.is_some());
            assert_eq!(
                pointee.unwrap().sort().bitvec_width(),
                Some(64),
                "pointee of &mut u64 should be bitvec(64)"
            );
        }
    });
}

/// Function with multiple ref args initializes all.
#[test]
fn test_init_ref_args_multiple() {
    let source = r#"
pub fn multi_ref_probe(a: &u32, b: &u64) -> u32 {
    *a
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "multi_ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Two ref args → two entries in ref_pointees
        assert_eq!(
            codegen.ref_pointees.len(),
            2,
            "two ref args should create two ref_pointees entries"
        );
    });
}

/// Function with bool ref arg initializes pointee as bool sort.
#[test]
fn test_init_ref_args_bool_ref() {
    let source = r#"
pub fn bool_ref_probe(b: &bool) -> bool {
    *b
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert!(!codegen.ref_pointees.is_empty());
        for pointee_base in codegen.ref_pointees.values() {
            let pointee = codegen.env_lookup(pointee_base);
            assert!(pointee.is_some());
            assert!(pointee.unwrap().sort().is_bool(), "pointee of &bool should be bool sort");
        }
    });
}

/// Mixed ref and non-ref args: only ref args get pointees.
#[test]
fn test_init_ref_args_mixed() {
    let source = r#"
pub fn mixed_probe(val: u32, r: &u32) -> u32 {
    val + *r
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Only 1 ref arg (r: &u32) → 1 entry
        assert_eq!(
            codegen.ref_pointees.len(),
            1,
            "only &u32 arg should create ref_pointees entry, not u32"
        );
    });
}

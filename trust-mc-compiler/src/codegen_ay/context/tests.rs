// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for AY codegen context.
//!
//! Extracted from context/mod.rs as part of #2836.

use super::*;
use crate::codegen_ay::names::enum_sort;

fn smt_text(program: &AYProgram) -> String {
    program.to_string()
}

// =========================================================================
// AYConfig defaults
// =========================================================================

#[test]
fn test_ay_config_defaults() {
    let config = AYConfig::default();
    assert_eq!(config.unwind_depth, 1);
    assert!(config.unwinding_assertions);
    assert!(!config.use_chc);
    assert!(config.produce_models);
    assert_eq!(config.logic, "QF_AUFBV");
    assert!(!config.logic_override);
    assert!(config.function_inlining);
    assert_eq!(config.inline_depth, 10);
    assert!(!config.use_emit_bmc);
    assert!(!config.ay_wide_mem);
}

// =========================================================================
// declare_var
// =========================================================================

#[test]
fn test_declare_var_creates_fresh_variable() {
    with_test_ay_ctx(|mut ctx| {
        let var = ctx.declare_var("x", Sort::bitvec(32));
        assert_eq!(var.sort().bitvec_width(), Some(32));
        assert_eq!(var, Expr::var("x", Sort::bitvec(32)));
    });
}

#[test]
fn test_declare_var_returns_existing_on_redeclaration() {
    with_test_ay_ctx(|mut ctx| {
        let v1 = ctx.declare_var("x", Sort::bitvec(32));
        let v2 = ctx.declare_var("x", Sort::bitvec(32));
        assert_eq!(v1, v2, "re-declaring same name+sort should return existing");
    });
}

#[test]
fn test_declare_var_cached_returns_original_sort() {
    with_test_ay_ctx(|mut ctx| {
        let v1 = ctx.declare_var("x", Sort::bitvec(32));
        // Re-declaring with different sort returns cached original (var_map hit)
        let v2 = ctx.declare_var("x", Sort::bitvec(64));
        assert_eq!(v1, v2, "var_map cache returns original declaration");
        assert_eq!(v2.sort().bitvec_width(), Some(32), "cached var retains original sort");
    });
}

#[test]
fn test_declare_var_dual_writes_to_bmc_vc() {
    with_test_ay_ctx(|mut ctx| {
        let _ = ctx.declare_var("y", Sort::bool());
        assert!(
            ctx.bmc_vc.decls.iter().any(|d| d.name() == "y"),
            "declare_var should dual-write to bmc_vc"
        );
    });
}

// =========================================================================
// lookup_var
// =========================================================================

#[test]
fn test_lookup_var_returns_none_for_undeclared() {
    with_test_ay_ctx(|ctx| {
        assert!(ctx.lookup_var("nonexistent").is_none());
    });
}

#[test]
fn test_lookup_var_returns_declared_var() {
    with_test_ay_ctx(|mut ctx| {
        let declared = ctx.declare_var("z", Sort::bitvec(8));
        let found = ctx.lookup_var("z");
        assert_eq!(found, Some(&declared));
    });
}

// =========================================================================
// fresh_name
// =========================================================================

#[test]
fn test_fresh_name_generates_unique_names() {
    with_test_ay_ctx(|mut ctx| {
        let n1 = ctx.fresh_name("tmp");
        let n2 = ctx.fresh_name("tmp");
        let n3 = ctx.fresh_name("var");
        assert_ne!(n1, n2, "fresh_name should generate distinct names");
        assert!(n1.starts_with("tmp_"));
        assert!(n2.starts_with("tmp_"));
        assert!(n3.starts_with("var_"));
    });
}

#[test]
fn test_fresh_name_monotonically_increases() {
    with_test_ay_ctx(|mut ctx| {
        let n1 = ctx.fresh_name("x");
        let n2 = ctx.fresh_name("x");
        // Extract numeric suffix
        let s1: u64 = n1.strip_prefix("x_").expect("prefix").parse().expect("digit");
        let s2: u64 = n2.strip_prefix("x_").expect("prefix").parse().expect("digit");
        assert!(s2 > s1, "counters should increase monotonically");
    });
}

// =========================================================================
// set_current_fn / reset_current_fn / current_fn
// =========================================================================

#[test]
fn test_current_fn_initially_none() {
    with_test_ay_ctx(|ctx| {
        assert!(ctx.current_fn().is_none());
    });
}

#[test]
fn test_set_and_reset_current_fn() {
    with_test_ay_ctx_for_source("pub fn my_function() {}", |mut ctx| {
        let instance =
            crate::codegen_ay::test_fixtures::find_instance_by_suffix(ctx.tcx, "my_function");
        ctx.set_current_fn(instance);
        assert!(ctx.current_fn().is_some());
        let name = &ctx.current_fn().expect("current_fn set").name;
        assert!(
            name.contains("my_function"),
            "current_fn name should contain function name, got: {name}"
        );

        ctx.reset_current_fn();
        assert!(ctx.current_fn().is_none());
    });
}

// =========================================================================
// ensure_datatype_declared
// =========================================================================

#[test]
fn test_ensure_datatype_declared_noop_for_primitives() {
    with_test_ay_ctx(|mut ctx| {
        // Primitives should not cause any declarations
        ctx.ensure_datatype_declared(&Sort::bitvec(32));
        ctx.ensure_datatype_declared(&Sort::bool());
        ctx.ensure_datatype_declared(&Sort::int());
        // No panic = success
    });
}

#[test]
fn test_ensure_datatype_declared_adds_to_program() {
    with_test_ay_ctx(|mut ctx| {
        let dt_sort = enum_sort(
            "Pair",
            vec![("Pair_mk", vec![("fst", Sort::bitvec(32)), ("snd", Sort::bitvec(32))])],
        );
        ctx.ensure_datatype_declared(&dt_sort);

        assert!(
            ctx.program.is_datatype_declared("Pair"),
            "declare_datatype should register 'Pair' in program"
        );
        let smt = smt_text(&ctx.program);
        assert!(
            smt.contains("declare-datatype") && smt.contains("Pair"),
            "program SMT output should contain Pair declaration, got: {smt}"
        );
    });
}

#[test]
fn test_ensure_datatype_declared_adds_to_bmc_vc() {
    with_test_ay_ctx(|mut ctx| {
        let dt_sort = enum_sort(
            "Color",
            vec![("Red", Vec::<(&str, Sort)>::new()), ("Green", vec![]), ("Blue", vec![])],
        );
        ctx.ensure_datatype_declared(&dt_sort);

        assert!(
            ctx.bmc_vc.decls.iter().any(|d| d.name() == "Color"),
            "ensure_datatype_declared should dual-write to bmc_vc"
        );
    });
}

#[test]
fn test_ensure_datatype_declared_recurses_into_array_element() {
    with_test_ay_ctx(|mut ctx| {
        let no_fields: Vec<(&str, Sort)> = vec![];
        let inner_dt =
            enum_sort("Status", vec![("Ok", vec![("val", Sort::bitvec(64))]), ("Err", no_fields)]);
        let array_sort = Sort::array(Sort::bitvec(32), inner_dt);
        ctx.ensure_datatype_declared(&array_sort);

        assert!(
            ctx.program.is_datatype_declared("Status"),
            "declaring Array(bv32, Status) should recursively declare Status"
        );
        assert!(
            ctx.bmc_vc.decls.iter().any(|d| d.name() == "Status"),
            "recursive declaration should also appear in bmc_vc"
        );
    });
}

#[test]
fn test_ensure_datatype_declared_idempotent() {
    with_test_ay_ctx(|mut ctx| {
        let dt_sort = enum_sort("Unit", vec![("Unit_mk", Vec::<(&str, Sort)>::new())]);
        ctx.ensure_datatype_declared(&dt_sort);
        let decl_count_after_first = ctx.bmc_vc.decls.len();

        ctx.ensure_datatype_declared(&dt_sort);
        assert_eq!(
            ctx.bmc_vc.decls.len(),
            decl_count_after_first,
            "declaring the same datatype twice should not double-declare in bmc_vc"
        );
    });
}

// =========================================================================
// split / split_emit_bmc
// =========================================================================

#[test]
#[should_panic(expected = "body() called on AYCtx without transformer")]
fn test_body_panics_without_transformer() {
    with_test_ay_ctx(|mut ctx| {
        let instance = crate::codegen_ay::test_fixtures::find_instance_by_suffix(ctx.tcx, "add");
        let _ = ctx.body(instance);
    });
}

#[test]
fn test_split_returns_program_and_diagnostics() {
    with_test_ay_ctx(|mut ctx| {
        ctx.unsupported("inline_asm", "test.rs:1");
        let _ = ctx.declare_var("x", Sort::bitvec(32));
        let (diag, program) = ctx.split();
        assert_eq!(diag.unsupported_constructs.len(), 1);
        let smt = smt_text(&program);
        assert!(smt.contains('x'), "program should contain declared var");
    });
}

#[test]
fn test_split_emit_bmc_generates_program_from_bmc_vc() {
    with_test_ay_ctx(|mut ctx| {
        let _ = ctx.declare_var("a", Sort::bitvec(32));
        ctx.record_property_violation(Expr::bool_const(true), "kani_assert");
        ctx.finalize_emit_bmc();
        let (diag, program) = ctx.split_emit_bmc();
        assert!(diag.unsupported_constructs.is_empty());
        let smt = smt_text(&program);
        assert!(smt.contains('a'), "emit_bmc program should contain declared vars");
    });
}

#[test]
fn test_split_emit_chc_returns_empty_program_without_chc_codegen() {
    with_test_ay_ctx(|ctx| {
        let (diag, program) = ctx.split_emit_chc();
        assert!(diag.unsupported_constructs.is_empty());
        let smt = smt_text(&program);
        // Graceful fallback: returns an empty HORN program instead of panicking.
        // Must specifically be HORN logic (not BMC/QF_BV).
        assert!(smt.contains("HORN"), "fallback should produce a HORN program, got: {smt}");
    });
}

// =========================================================================
// record_chc_local_to_state_idx
// =========================================================================

#[test]
fn test_record_chc_local_to_state_idx() {
    with_test_ay_ctx(|mut ctx| {
        let mut mapping = HashMap::new();
        mapping.insert(0, 0);
        mapping.insert(1, 2);
        ctx.record_chc_local_to_state_idx("test_fn", mapping);
        assert!(ctx.chc_local_to_state_idx.contains_key("test_fn"));
        let m = ctx.chc_local_to_state_idx.get("test_fn").expect("test_fn mapping");
        assert_eq!(m.get(&1), Some(&2));
    });
}

// =========================================================================
// AYConfig::select_logic (original tests)
// =========================================================================

#[test]
fn test_select_logic_chc_mode() {
    // CHC mode always returns HORN, regardless of datatypes
    let config = AYConfig { use_chc: true, ..Default::default() };

    assert_eq!(config.select_logic(false), "HORN");
    assert_eq!(config.select_logic(true), "HORN");
}

#[test]
fn test_select_logic_bmc_no_datatypes() {
    // BMC mode without datatypes uses configured logic (default QF_AUFBV)
    let config = AYConfig::default();
    assert_eq!(config.select_logic(false), "QF_AUFBV");
}

#[test]
fn test_select_logic_bmc_with_datatypes() {
    // BMC mode with datatypes upgrades to ALL
    let config = AYConfig::default();
    assert_eq!(config.select_logic(true), "ALL");
}

#[test]
fn test_select_logic_custom_bmc_logic() {
    // BMC mode without datatypes respects custom logic setting
    let config = AYConfig { logic: "QF_BV".into(), ..Default::default() };

    assert_eq!(config.select_logic(false), "QF_BV");
    // With datatypes, still upgrades to ALL
    assert_eq!(config.select_logic(true), "ALL");
}

#[test]
fn test_select_logic_chc_overrides_custom() {
    // CHC mode overrides custom logic setting
    let config = AYConfig { use_chc: true, logic: "QF_BV".into(), ..Default::default() };

    assert_eq!(config.select_logic(false), "HORN");
    assert_eq!(config.select_logic(true), "HORN");
}

#[test]
fn test_select_logic_user_override_bmc() {
    // User override (--ay-logic) takes precedence in BMC mode (#621)
    let config = AYConfig { logic: "QF_DT".into(), logic_override: true, ..Default::default() };

    // Override applies even with datatypes (bypasses ALL upgrade)
    assert_eq!(config.select_logic(false), "QF_DT");
    assert_eq!(config.select_logic(true), "QF_DT");
}

#[test]
fn test_select_logic_user_override_chc() {
    // User override takes precedence over CHC HORN selection (#621)
    let config = AYConfig {
        use_chc: true,
        logic: "QF_LIA".into(),
        logic_override: true,
        ..Default::default()
    };

    // Override bypasses automatic HORN selection
    assert_eq!(config.select_logic(false), "QF_LIA");
    assert_eq!(config.select_logic(true), "QF_LIA");
}

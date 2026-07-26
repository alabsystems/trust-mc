// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// collect_state_vars tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify that collect_state_vars creates state vars for each MIR local.
#[test]
fn test_collect_state_vars_count() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let local_count = body.locals().len();
        assert!(local_count > 0, "simple_fn should have at least one local");
        // State vars should be created for locals (at least for translatable types)
        assert!(
            !chc_ctx.state_var_mgr.state_vars.is_empty(),
            "collect_state_vars should create at least some state vars"
        );
    });
}

/// Verify that state vars for u32 param get bitvec sort.
#[test]
fn test_collect_state_vars_u32_sort() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // The parameter x: u32 should produce a bv32 state var
        let has_bv32 = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(_, sort)| sort.bitvec_width() == Some(32));
        assert!(has_bv32, "u32 parameter should produce a bv32 state var");
    });
}

/// Verify that mixed types produce the correct sorts.
#[test]
fn test_collect_state_vars_mixed_types() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // i32 → bv32, u64 → bv64, bool → bool sort
        let has_bv32 = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(_, sort)| sort.bitvec_width() == Some(32));
        let has_bv64 = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(_, sort)| sort.bitvec_width() == Some(64));
        let has_bool = chc_ctx.state_var_mgr.state_vars.iter().any(|(_, sort)| sort.is_bool());

        assert!(has_bv32, "i32 should produce bv32 state var");
        assert!(has_bv64, "u64 should produce bv64 state var");
        assert!(has_bool, "bool should produce Bool state var");
    });
}

/// Verify that output state vars are created alongside input vars.
#[test]
fn test_output_state_vars_created() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Output state vars should match input state vars count
        assert_eq!(
            chc_ctx.state_var_mgr.state_vars.len(),
            chc_ctx.state_var_mgr.output_state_vars.len(),
            "input and output state vars should have same count"
        );

        // Output names should have __out suffix
        for (name, _) in &chc_ctx.state_var_mgr.output_state_vars {
            assert!(name.ends_with("__out"), "output state var should end with __out, got: {name}");
        }
    });
}

/// Verify that state var naming follows convention: _fn_idx.
#[test]
fn test_state_var_naming() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Input state vars follow _fn_idx pattern, except heap metadata
        // arrays (obj_valid, obj_size) which are declared unconditionally
        // for dealloc safety checks at all track levels (Fix #2736).
        let heap_metadata = ["obj_valid", "obj_size"];
        for (name, _) in &chc_ctx.state_var_mgr.state_vars {
            if heap_metadata.contains(&&**name) {
                continue;
            }
            assert!(
                name.starts_with("_simple_fn_"),
                "state var should start with _simple_fn_, got: {name}"
            );
        }
    });
}

/// Verify that no-args functions still create state vars for the return local.
#[test]
fn test_no_args_fn_has_return_local_state_var() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "no_args_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "no_args_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Even with no args, local_0 (return place) should have a state var
        assert!(
            !chc_ctx.state_var_mgr.state_vars.is_empty(),
            "no_args_fn should have at least the return local as a state var"
        );
        // Check _no_args_fn_0 exists (return local)
        let has_return_var =
            chc_ctx.state_var_mgr.state_vars.iter().any(|(name, _)| &**name == "_no_args_fn_0");
        assert!(has_return_var, "return local _no_args_fn_0 should be in state vars");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Numeric reference sort mapping tests (Part of #2272)
// ═══════════════════════════════════════════════════════════════════════

const NUMERIC_REF_SORT_SOURCE: &str = r#"
pub struct BigInt(pub u64);
pub struct BigRational(pub u64, pub u64);

pub fn bigint_ref_probe(x: &BigInt) -> u32 {
    let _ = x;
    1
}

pub fn bigrational_ref_probe(x: &BigRational) -> u32 {
    let _ = x;
    2
}

pub fn mixed_numeric_ref_probe(x: &BigInt, y: &BigRational) -> u32 {
    let _ = x;
    let _ = y;
    3
}
"#;

/// Verify BigInt references map to Int sort, not pointer bitvec sort.
#[test]
fn test_collect_state_vars_bigint_ref_uses_int_sort() {
    with_test_ay_ctx_for_source(NUMERIC_REF_SORT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "bigint_ref_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "bigint_ref_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let bigint_ref_sort = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .find(|(name, _)| &**name == "_bigint_ref_probe_1")
            .map(|(_, sort)| sort)
            .expect("missing state var for bigint_ref_probe arg local_1");
        assert!(
            bigint_ref_sort.is_int(),
            "BigInt ref local should use Int sort, got {:?}",
            bigint_ref_sort
        );
        assert!(
            !bigint_ref_sort.is_bitvec(),
            "BigInt ref local should not use pointer bitvec sort, got {:?}",
            bigint_ref_sort
        );

        let bigint_ref_out_sort = chc_ctx
            .state_var_mgr
            .output_state_vars
            .iter()
            .find(|(name, _)| &**name == "_bigint_ref_probe_1__out")
            .map(|(_, sort)| sort)
            .expect("missing output state var for bigint_ref_probe arg local_1");
        assert!(
            bigint_ref_out_sort.is_int(),
            "BigInt ref output local should use Int sort, got {:?}",
            bigint_ref_out_sort
        );
        assert!(
            !bigint_ref_out_sort.is_bitvec(),
            "BigInt ref output local should not use pointer bitvec sort, got {:?}",
            bigint_ref_out_sort
        );
    });
}

/// Verify BigRational references map to Real sort, not pointer bitvec sort.
#[test]
fn test_collect_state_vars_bigrational_ref_uses_real_sort() {
    with_test_ay_ctx_for_source(NUMERIC_REF_SORT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "bigrational_ref_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "bigrational_ref_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let bigrational_ref_sort = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .find(|(name, _)| &**name == "_bigrational_ref_probe_1")
            .map(|(_, sort)| sort)
            .expect("missing state var for bigrational_ref_probe arg local_1");
        assert!(
            bigrational_ref_sort.is_real(),
            "BigRational ref local should use Real sort, got {:?}",
            bigrational_ref_sort
        );
        assert!(
            !bigrational_ref_sort.is_bitvec(),
            "BigRational ref local should not use pointer bitvec sort, got {:?}",
            bigrational_ref_sort
        );

        let bigrational_ref_out_sort = chc_ctx
            .state_var_mgr
            .output_state_vars
            .iter()
            .find(|(name, _)| &**name == "_bigrational_ref_probe_1__out")
            .map(|(_, sort)| sort)
            .expect("missing output state var for bigrational_ref_probe arg local_1");
        assert!(
            bigrational_ref_out_sort.is_real(),
            "BigRational ref output local should use Real sort, got {:?}",
            bigrational_ref_out_sort
        );
        assert!(
            !bigrational_ref_out_sort.is_bitvec(),
            "BigRational ref output local should not use pointer bitvec sort, got {:?}",
            bigrational_ref_out_sort
        );
    });
}

/// Regression guard: mixed numeric references must not regress to pointer bitvec sorts.
#[test]
fn test_collect_state_vars_numeric_refs_not_pointer_bitvec() {
    with_test_ay_ctx_for_source(NUMERIC_REF_SORT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "mixed_numeric_ref_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "mixed_numeric_ref_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let bigint_ref_sort = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .find(|(name, _)| &**name == "_mixed_numeric_ref_probe_1")
            .map(|(_, sort)| sort)
            .expect("missing state var for mixed_numeric_ref_probe BigInt arg local_1");
        let bigrational_ref_sort = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .find(|(name, _)| &**name == "_mixed_numeric_ref_probe_2")
            .map(|(_, sort)| sort)
            .expect("missing state var for mixed_numeric_ref_probe BigRational arg local_2");
        let bigint_ref_out_sort = chc_ctx
            .state_var_mgr
            .output_state_vars
            .iter()
            .find(|(name, _)| &**name == "_mixed_numeric_ref_probe_1__out")
            .map(|(_, sort)| sort)
            .expect("missing output state var for mixed_numeric_ref_probe BigInt arg local_1");
        let bigrational_ref_out_sort = chc_ctx
            .state_var_mgr
            .output_state_vars
            .iter()
            .find(|(name, _)| &**name == "_mixed_numeric_ref_probe_2__out")
            .map(|(_, sort)| sort)
            .expect("missing output state var for mixed_numeric_ref_probe BigRational arg local_2");

        assert!(
            bigint_ref_sort.is_int() && !bigint_ref_sort.is_bitvec(),
            "BigInt ref local should remain Int (not pointer bitvec), got {:?}",
            bigint_ref_sort
        );
        assert!(
            bigrational_ref_sort.is_real() && !bigrational_ref_sort.is_bitvec(),
            "BigRational ref local should remain Real (not pointer bitvec), got {:?}",
            bigrational_ref_sort
        );
        assert!(
            bigint_ref_out_sort.is_int() && !bigint_ref_out_sort.is_bitvec(),
            "BigInt ref output local should remain Int (not pointer bitvec), got {:?}",
            bigint_ref_out_sort
        );
        assert!(
            bigrational_ref_out_sort.is_real() && !bigrational_ref_out_sort.is_bitvec(),
            "BigRational ref output local should remain Real (not pointer bitvec), got {:?}",
            bigrational_ref_out_sort
        );
    });
}

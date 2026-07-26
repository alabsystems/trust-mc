// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Mem-level local type array pre-declaration (#2258)
// ═══════════════════════════════════════════════════════════════════════

fn assert_type_array_declared(
    chc_ctx: &ChcCtx<'_, '_>,
    fn_name: &str,
    type_key: &str,
    elem_sort: Sort,
) {
    let arr_name = format!("_{fn_name}_mem_{type_key}");
    let arr_out_name = format!("{arr_name}__out");
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);

    assert!(
        chc_ctx.heap_state.type_arrays.contains_key(type_key),
        "missing type_arrays entry for {type_key}. keys: {:?}",
        chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
    );

    let state_count = chc_ctx
        .state_var_mgr
        .state_vars
        .iter()
        .filter(|(name, sort)| &**name == arr_name.as_str() && *sort == arr_sort)
        .count();
    assert_eq!(
        state_count,
        1,
        "expected exactly one state var {arr_name} with sort {arr_sort:?}; state_vars: {:?}",
        chc_ctx.state_var_mgr.state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
    );

    let output_count = chc_ctx
        .state_var_mgr
        .output_state_vars
        .iter()
        .filter(|(name, sort)| &**name == arr_out_name.as_str() && *sort == arr_sort)
        .count();
    assert_eq!(
        output_count,
        1,
        "expected exactly one output state var {arr_out_name} with sort {arr_sort:?}; output_state_vars: {:?}",
        chc_ctx.state_var_mgr.output_state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
    );

    assert!(
        chc_ctx
            .vc
            .vars()
            .iter()
            .any(|var| var.name.as_ref() == arr_name.as_str() && var.sort == arr_sort),
        "vc.vars() missing declare-var for {type_key} input array. vars: {:?}",
        chc_ctx.vc.vars().iter().map(|v| &v.name).collect::<Vec<_>>()
    );
    assert!(
        chc_ctx
            .vc
            .vars()
            .iter()
            .any(|var| var.name.as_ref() == arr_out_name.as_str() && var.sort == arr_sort),
        "vc.vars() missing declare-var for {type_key} output array. vars: {:?}",
        chc_ctx.vc.vars().iter().map(|v| &v.name).collect::<Vec<_>>()
    );
}

/// Source with bool locals that trigger mem_bool type array creation at Mem level.
const LOCAL_TYPE_ARRAY_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn bool_local(x: u32) -> bool {
        x > 10
    }

    pub fn multi_type_locals(a: i32, b: bool, c: u64) -> bool {
        if b { a > 0 } else { c < 100 }
    }

    pub fn byte_locals(a: u8, b: i8) -> i16 {
        (a as i16) + (b as i16)
    }
"#;

/// At Mem level, a function with a bool local should pre-declare mem_bool type array.
#[test]
fn test_collect_local_type_arrays_predeclares_bool() {
    with_test_ay_ctx_for_source(LOCAL_TYPE_ARRAY_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "bool_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "bool_local",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        assert_type_array_declared(&chc_ctx, "bool_local", "bool", Sort::bool());
    });
}

/// At Reg level, collect_local_type_arrays should be a no-op.
#[test]
fn test_collect_local_type_arrays_noop_at_reg_level() {
    with_test_ay_ctx_for_source(LOCAL_TYPE_ARRAY_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "bool_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "bool_local", ChcConfig::default());

        chc_ctx.declare_block_relations();

        // At Reg level, no type-indexed arrays should be created
        let has_mem_bool =
            chc_ctx.state_var_mgr.state_vars.iter().any(|(name, _)| name.contains("_mem_bool"));
        assert!(
            !has_mem_bool,
            "Reg-level should NOT produce local type arrays. state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    });
}

/// Multiple non-bv8 local types should each get their own type array.
#[test]
fn test_collect_local_type_arrays_multiple_types() {
    with_test_ay_ctx_for_source(LOCAL_TYPE_ARRAY_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_type_locals");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "multi_type_locals",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        assert_type_array_declared(&chc_ctx, "multi_type_locals", "bool", Sort::bool());
        assert_type_array_declared(&chc_ctx, "multi_type_locals", "i32", Sort::bitvec(32));
        assert_type_array_declared(&chc_ctx, "multi_type_locals", "u64", Sort::bitvec(64));
    });
}

/// Bug 9 regression: bv8-backed scalar types (u8/i8) must be pre-declared as
/// type-indexed memory arrays, not skipped.
#[test]
fn test_collect_local_type_arrays_predeclares_byte_types() {
    with_test_ay_ctx_for_source(LOCAL_TYPE_ARRAY_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "byte_locals");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "byte_locals",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        assert_type_array_declared(&chc_ctx, "byte_locals", "u8", Sort::bitvec(8));
        assert_type_array_declared(&chc_ctx, "byte_locals", "i8", Sort::bitvec(8));
    });
}

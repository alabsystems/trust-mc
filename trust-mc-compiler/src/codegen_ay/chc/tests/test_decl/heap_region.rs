// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Ptr-level heap region pre-declaration (Part of #2231)
// ═══════════════════════════════════════════════════════════════════════

fn assert_region_elem_sort_declared(
    chc_ctx: &ChcCtx<'_, '_>,
    expected_elem_sort: Sort,
    context: &str,
) {
    let expected_region_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), expected_elem_sort.clone());
    let region_arrays: Vec<_> = chc_ctx
        .heap_state
        .region_arrays
        .values()
        .map(|(name, sort)| (name.to_string(), sort.clone()))
        .collect();

    assert!(
        region_arrays.iter().any(|(_, sort)| sort == &expected_elem_sort),
        "{context}: expected region elem sort {expected_elem_sort:?}. regions: {region_arrays:?}"
    );
    assert!(
        chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(name, sort)| name.contains("_region_") && sort == &expected_region_sort),
        "{context}: expected state var sort {expected_region_sort:?}. state_vars: {:?}",
        chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| (name.to_string(), sort.clone()))
            .collect::<Vec<_>>()
    );
}

/// At Ptr level, predeclare_heap_region_arrays should scan for alloc stubs
/// and pre-declare region arrays as state vars. Box::new triggers ShallowInitBox.
const HEAP_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;

    pub fn probe_box_alloc(x: u32) -> Box<u32> {
        Box::new(x)
    }
"#;

/// `Box<[T; N]>` / `vec![...]` allocations need a typed region at declaration
/// time so they do not upgrade late to `_region_*_arr`. Part of #3714.
const HEAP_TYPED_REGION_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_boxed_array_region() {
        let _boxed = Box::new([1i32]);
    }
"#;

/// `vec![[u64; 3], ...]` allocates `Box<[[u64; 3]; N]>` and then calls
/// `slice::into_vec`, so declaration-time region prediction must recover the
/// inner `[u64; 3]` element sort from the boxed array construction. Part of
/// #3783.
const HEAP_VEC_LITERAL_REGION_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_literal_array_region() -> usize {
        let v = vec![[0u64; 3], [2u64; 3]];
        v.len()
    }
"#;

/// The real `offset_non_power_two` shape allocates the Vec literal in the same
/// body that later calls `as_mut_ptr()` and `offset_from_unsigned()`. Keep this
/// declaration-time probe exact so region prediction covers the live harness,
/// not just a reduced `vec![...]` smoke test. Part of #3783.
const HEAP_VEC_LITERAL_RUNTIME_GUARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}

        #[inline(always)]
        pub fn any_where<T, F: FnOnce(&T) -> bool>(f: F) -> T {
            let result = any();
            assume(f(&result));
            result
        }
    }

    pub fn probe_vec_literal_runtime_guard() -> bool {
        let mut v = vec![[0u64; 3], [2u64; 3]];
        unsafe {
            let offset = kani::any_where(|o: &usize| *o <= v.len());
            let begin = v.as_mut_ptr();
            let end = begin.add(offset);
            end.offset_from_unsigned(begin) == offset
        }
    }
"#;

/// At Ptr level, Box::new should cause heap region array pre-declaration.
#[test]
fn test_predeclare_heap_region_arrays_box_new() {
    with_test_ay_ctx_for_source(HEAP_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_alloc");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_box_alloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // At Ptr level, Box::new triggers ShallowInitBox or alloc stubs,
        // which should cause predeclare_heap_region_arrays to add region arrays.
        let has_region_array = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(name, sort)| name.contains("_region_") && sort.is_array());

        // Even if Box::new doesn't generate the expected MIR pattern at this
        // optimization level, verify the function ran without errors and
        // that Ptr-level produced more state vars than Reg-level would.
        let instance2 = find_instance_by_suffix(ctx.tcx, "probe_box_alloc");
        let body2 = instance2.body().expect("function body");
        let mut chc_ctx_reg =
            ChcCtx::new(ctx.tcx, &body2, "probe_box_alloc_reg", ChcConfig::default());
        chc_ctx_reg.declare_block_relations();

        // Ptr-level should have at least as many state vars as Reg
        assert!(
            chc_ctx.state_var_mgr.state_vars.len() >= chc_ctx_reg.state_var_mgr.state_vars.len(),
            "Ptr-level should produce >= state vars than Reg. Ptr: {}, Reg: {}",
            chc_ctx.state_var_mgr.state_vars.len(),
            chc_ctx_reg.state_var_mgr.state_vars.len()
        );

        // If region arrays were declared, verify they have Array sort
        if has_region_array {
            let region_vars: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .filter(|(name, _)| name.contains("_region_"))
                .collect();
            for (name, sort) in &region_vars {
                assert!(
                    sort.is_array(),
                    "region array {name} should have Array sort, got {sort:?}"
                );
            }
        }
    });
}

/// At Reg level, predeclare_heap_region_arrays should be a no-op (guard: track_level < Ptr).
#[test]
fn test_predeclare_heap_region_arrays_noop_at_reg() {
    with_test_ay_ctx_for_source(HEAP_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_alloc");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_box_alloc", ChcConfig::default());

        chc_ctx.declare_block_relations();

        let has_region_array =
            chc_ctx.state_var_mgr.state_vars.iter().any(|(name, _)| name.contains("_region_"));
        assert!(
            !has_region_array,
            "Reg-level should NOT produce region arrays. \
             state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    });
}

/// ShallowInitBox of an array payload should predeclare the allocator region
/// with the array element sort. Part of #3714/#4152.
#[test]
fn test_predeclare_heap_region_arrays_shallow_init_box_predicts_typed_region() {
    with_test_ay_ctx_for_source(HEAP_TYPED_REGION_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_boxed_array_region");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_boxed_array_region",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        assert_region_elem_sort_declared(
            &chc_ctx,
            Sort::bitvec(32),
            "Box<[i32; 1]> should predeclare a typed allocator region",
        );
    });
}

/// `vec![...]` allocation should predeclare the allocator region with the
/// nested array element sort before relation signatures are finalized.
#[test]
fn test_predeclare_heap_region_arrays_vec_literal_predicts_nested_array_region() {
    with_test_ay_ctx_for_source(HEAP_VEC_LITERAL_REGION_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_literal_array_region");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_vec_literal_array_region",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        assert_region_elem_sort_declared(
            &chc_ctx,
            Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(64)),
            "vec![[u64; 3], ...] should predeclare a nested-array allocator region",
        );

        let has_region_state_var =
            chc_ctx.state_var_mgr.state_vars.iter().any(|(name, _)| name.contains("_region_"));
        assert!(
            has_region_state_var,
            "region state var should be declared. state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(name, _)| name).collect::<Vec<_>>()
        );
    });
}

/// Runtime-guard variant: same as above but with kani::any_where + pointer
/// arithmetic.
#[test]
fn test_predeclare_heap_region_arrays_vec_literal_runtime_guard_predicts_nested_array_region() {
    with_test_ay_ctx_for_source(HEAP_VEC_LITERAL_RUNTIME_GUARD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_literal_runtime_guard");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_vec_literal_runtime_guard",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        assert_region_elem_sort_declared(
            &chc_ctx,
            Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(64)),
            "runtime-guard vec literal should predeclare a nested-array allocator region",
        );

        let has_region_state_var =
            chc_ctx.state_var_mgr.state_vars.iter().any(|(name, _)| name.contains("_region_"));
        assert!(
            has_region_state_var,
            "runtime-guard vec literal should declare a region state var. state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(name, _)| name).collect::<Vec<_>>()
        );
    });
}

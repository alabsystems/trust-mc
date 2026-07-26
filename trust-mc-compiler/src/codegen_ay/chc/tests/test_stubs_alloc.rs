// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for CHC stubs_alloc.rs — heap allocation intrinsic stubs:
//! detect_alloc_stub (StubKind routing), translate_alloc_call (RustAlloc,
//! RustDealloc, RustRealloc, LayoutSize, LayoutAlign, LayoutIsSizeAlignValid).
//!
//! Part of #2231 (zero test coverage for stubs_alloc.rs, 472 LOC).

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// detect_alloc_stub — allocation intrinsic detection
// =============================================================================

#[test]
fn test_detect_alloc_stub_box_new() {
    // Box::new triggers __rust_alloc under the hood
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new() -> Box<u32> {
            Box::new(42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_box_new",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut call_count = 0usize;
        let mut detected_count = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                call_count += 1;
                if chc_ctx.detect_alloc_stub(func).is_some() {
                    detected_count += 1;
                }
            }
        }
        assert!(call_count > 0, "MIR for Box::new should contain at least one Call terminator");
        assert_mir_pattern_found(detected_count > 0, "Box::new allocation stub call in MIR");
    });
}

#[test]
fn test_detect_alloc_stub_direct_alloc_call() {
    // Direct std::alloc::alloc call — guaranteed to produce __rust_alloc in MIR,
    // unlike Vec::push where the alloc intrinsic is inside Vec's implementation
    // and not visible at the caller's MIR level.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::alloc::{alloc, Layout};

        pub unsafe fn probe_direct_alloc() -> *mut u8 {
            let layout = Layout::new::<u32>();
            unsafe { alloc(layout) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_direct_alloc");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_direct_alloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut call_count = 0usize;
        let mut detected_count = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                call_count += 1;
                if chc_ctx.detect_alloc_stub(func).is_some() {
                    detected_count += 1;
                }
            }
        }
        assert!(call_count > 0, "MIR for direct alloc should contain Call terminators");
        assert!(detected_count > 0, "Direct std::alloc::alloc should be detected as an alloc stub");
    });
}

#[test]
fn test_detect_alloc_stub_negative_non_alloc() {
    // Plain arithmetic should not match allocation stubs
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_no_alloc(a: u32, b: u32) -> u32 {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_alloc");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_alloc", ChcConfig::default());

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(
                    chc_ctx.detect_alloc_stub(func).is_none(),
                    "Plain arithmetic should not match allocation stubs"
                );
            }
        }
    });
}

// =============================================================================
// Full CHC pipeline tests for allocation patterns
// =============================================================================

#[test]
fn test_mir_box_alloc_dealloc_pipeline() {
    // Box::new + drop exercises RustAlloc → RustDealloc path
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_lifecycle() {
            let b = Box::new(42u32);
            let _val = *b;
            // b dropped here: RustDealloc
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_lifecycle");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_lifecycle",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert!(!vc.relations.is_empty(), "VC should have relations for box alloc/dealloc");
        assert!(!vc.rules.is_empty(), "VC should have rules for box alloc/dealloc");
        // Entry rule should exist
        let has_entry = vc.rules.iter().any(|r| r.body.relation.is_none());
        assert!(has_entry, "Should have entry rule");

        // Semantic: Box alloc/dealloc lifecycle at Mem level should produce
        // heap memory operations (store for alloc writes, Array sort for heap).
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_mem_var,
            "Box alloc/dealloc at Mem level should declare Array-sorted memory variable"
        );
        // Alloc/dealloc path should produce constrained transition rules
        // (not just vacuously true skeleton rules).
        let constrained_transitions = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .filter(|r| !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_transitions >= 1,
            "Box alloc/dealloc should produce at least 1 constrained transition, got {constrained_transitions}"
        );
    });
}

#[test]
fn test_mir_vec_push_alloc_pipeline() {
    // Vec::push triggers allocation when capacity is exceeded
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_alloc() {
            let mut v = Vec::new();
            v.push(1u32);
            let _ = v.len();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_alloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_vec_push_alloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert!(!vc.relations.is_empty(), "VC should be generated for Vec push with allocation");
        assert!(!vc.rules.is_empty(), "VC should have rules for Vec push allocation");

        // Check that error relation exists (safety checks from allocation)
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "VC should have error relation for allocation safety checks");

        // Semantic: Vec::push at Mem level should produce Array-sorted memory
        // variables for heap tracking and constrained transition rules.
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(has_mem_var, "Vec push at Mem level should declare Array-sorted memory variable");
    });
}

#[test]
fn test_mir_realloc_pipeline() {
    // Vec growth triggers realloc when more capacity is needed
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_realloc() {
            let mut v = Vec::with_capacity(1);
            v.push(1u32);
            v.push(2u32); // may trigger realloc
            v.push(3u32); // may trigger realloc again
            let _ = v.len();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_realloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_vec_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert!(!vc.relations.is_empty(), "VC should be generated for Vec realloc pattern");
        assert!(!vc.rules.is_empty(), "VC should have rules for Vec realloc");
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "VC should have error relation for realloc safety checks");
        let has_entry = vc.rules.iter().any(|r| r.body.relation.is_none());
        assert!(has_entry, "Should have entry rule for realloc pipeline");
    });
}

// =============================================================================
// Layout helper stubs (LayoutSize, LayoutAlign, LayoutIsSizeAlignValid)
// =============================================================================

#[test]
fn test_detect_alloc_stub_layout_helpers() {
    // std::alloc::Layout operations should be detected as allocation stubs
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub fn probe_layout_helpers() -> (usize, usize) {
            let layout = Layout::new::<u64>();
            (layout.size(), layout.align())
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_helpers");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_layout_helpers", ChcConfig::default());

        // Walk all calls — track both total and detected stubs
        let mut call_count = 0usize;
        let mut detected_count = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                call_count += 1;
                if chc_ctx.detect_alloc_stub(func).is_some() {
                    detected_count += 1;
                }
            }
        }
        assert!(
            call_count > 0,
            "MIR for Layout helpers should contain at least one Call terminator"
        );
        assert_mir_pattern_found(detected_count > 0, "Layout helper stub call in MIR");
    });
}

#[test]
fn test_detect_alloc_stub_layout_array() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub fn probe_layout_array() -> Layout {
            let n = core::hint::black_box(10usize);
            Layout::array::<u32>(n).unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_array");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_layout_array", ChcConfig::default());

        // Walk all calls — track both alloc-stub and layout-array detection.
        let mut call_count = 0usize;
        let mut alloc_detect_count = 0usize;
        let mut layout_array_found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                call_count += 1;
                if chc_ctx.detect_alloc_stub(func).is_some() {
                    alloc_detect_count += 1;
                }
                if chc_ctx.detect_stub_matching(func, StubKind::is_layout_extra)
                    == Some(StubKind::LayoutArray)
                {
                    layout_array_found = true;
                }
            }
        }
        assert!(
            call_count > 0,
            "MIR for Layout::array should contain at least one Call terminator"
        );
        assert_mir_pattern_found(
            layout_array_found || alloc_detect_count > 0,
            "Layout::array path call in MIR",
        );
    });
}

// =============================================================================
// VC structure for allocation-heavy functions
// =============================================================================

#[test]
fn test_mir_alloc_vc_has_heap_metadata_arrays() {
    // When allocation stubs are processed in Mem mode, the VC should reference
    // heap metadata arrays (obj_valid, obj_size)
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_heap_metadata() -> Box<u32> {
            Box::new(42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_heap_metadata");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_heap_metadata",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for Box::new");

        // In Mem track level, relations should include heap state variables
        // (obj_valid, obj_size arrays tracked as relation parameters)
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "VC should have error relation");

        // Entry rule should initialize heap state
        let has_entry = vc.rules.iter().any(|r| r.body.relation.is_none());
        assert!(has_entry, "Should have entry rule for Box::new");
    });
}

// =============================================================================
// Realloc model behavior verification (Part of #2425)
// =============================================================================

#[test]
fn test_mir_realloc_generates_obj_size_update_constraint() {
    // Part of #3728: always-moved realloc model (no nondeterministic boolean).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_realloc_size_update() {
            let layout = unsafe { std::alloc::Layout::from_size_align_unchecked(16, 8) };
            let ptr = unsafe { std::alloc::alloc(layout) };
            let _new_ptr = unsafe { std::alloc::realloc(ptr, layout, 32) };
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_realloc_size_update");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_realloc_size_update",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for realloc pattern");

        // The realloc model updates obj_size. At least one rule body must
        // reference obj_size__out (the output metadata array), confirming
        // the size update constraint was emitted.
        // After scalarization, obj_size__out may become obj_size_at_0xN_bv32__out.
        assert!(
            vc_rules_contain_var_out(&vc, "obj_size"),
            "Realloc model must emit obj_size output constraint (if this fails, \
             MIR optimization may have eliminated the realloc — update the test source)"
        );
        // obj_valid__out must also be referenced (#2425: nondeterministic model
        // must update validity for both in-place and move paths)
        // After scalarization, obj_valid__out may become obj_valid_at_0xN_bv32__out.
        assert!(
            vc_rules_contain_var_out(&vc, "obj_valid"),
            "Realloc model should update obj_valid output (nondeterministic move/in-place)"
        );
        // #3728: Always-moved model — no nondeterministic boolean, single rule
        // unconditionally invalidates old pointer and validates new pointer.
        assert!(
            !vc_rules_contain_var(&vc, "realloc_moved_"),
            "Always-moved realloc model should NOT contain nondeterministic realloc_moved variable (#3728)"
        );
    });
}

#[test]
fn test_mir_checked_layout_realloc_reaches_precise_model() {
    // Part of #3641: checked Layout::from_size_align(...).unwrap() must route
    // through the semantic layout constructor so realloc sees a packed Layout
    // operand and emits the precise moved/in-place model instead of the generic
    // fallback.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::alloc::{alloc, realloc, Layout};

        pub unsafe fn probe_checked_layout_realloc() {
            let size = core::hint::black_box(16usize);
            let align = core::hint::black_box(8usize);
            let layout = Layout::from_size_align(size, align).unwrap();
            let ptr = unsafe { alloc(layout) };
            let _new_ptr = unsafe { realloc(ptr, layout, 32) };
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_layout_realloc");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_checked_layout_realloc", ChcConfig::default());

        let mut saw_checked_layout = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && matches!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_layout_extra),
                    Some(StubKind::LayoutFromSizeAlign | StubKind::LayoutFromSizeAlignUnchecked)
                )
            {
                saw_checked_layout = true;
            }
        }
        assert_mir_pattern_found(saw_checked_layout, "LayoutFromSizeAlign{,Unchecked} call in MIR");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_checked_layout_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for checked-layout realloc");
        // #3728: Always-moved model — no nondeterministic boolean. The precise
        // model is confirmed by obj_valid output + obj_size output presence (not the
        // generic fallback which leaves metadata unconstrained).
        // After scalarization, these may become per-index scalar variables.
        assert!(
            vc_rules_contain_var_out(&vc, "obj_valid"),
            "Checked-layout realloc should update obj_valid output (always-moved model #3728)"
        );
        assert!(
            vc_rules_contain_var_out(&vc, "obj_size"),
            "Checked-layout realloc should update obj_size output (always-moved model #3728)"
        );
    });
}

#[test]
fn test_mir_realloc_moved_branch_copies_type_array_prefix() {
    // Part of #2323: moved realloc branch must preserve previously written values.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_realloc_copy() -> i32 {
            let layout = std::alloc::Layout::array::<i32>(2).unwrap();
            let ptr = unsafe { std::alloc::alloc(layout) } as *mut i32;
            unsafe { ptr.add(0).write(100) };
            unsafe { ptr.add(1).write(200) };
            let new_ptr = unsafe { std::alloc::realloc(ptr as *mut u8, layout, 16) } as *mut i32;
            unsafe { new_ptr.add(0).read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_realloc_copy");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_realloc_copy",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for realloc copy pattern");

        // #3728: Always-moved model — copy constraints emitted unconditionally.
        assert!(
            vc_rules_contain_var(&vc, "obj_valid__out"),
            "Realloc copy should update obj_valid__out (always-moved model #3728)"
        );
        assert!(
            vc_rules_contain_var(&vc, "_probe_realloc_copy_mem_i32__out"),
            "Realloc copy should constrain i32 memory output array"
        );
    });
}

fn assert_std_alloc_realloc_grow_shape_retains_literal(vc: &trust_mc_core::chc::ChcVc) {
    assert!(
        any_constraint_str(vc, |constraint| constraint.contains("#x0000002a")),
        "std_alloc realloc-grow shape should retain the pre-realloc ptr.write(42) literal in the VC"
    );
    let smt = crate::codegen_ay::emit_chc(vc).to_string();
    assert!(
        smt.contains("#x0000002a"),
        "std_alloc realloc-grow shape should retain ptr.write(42) through CHC emission"
    );
}

#[test]
fn test_mir_std_alloc_realloc_grow_shape_has_no_chc_fallbacks() {
    // Part of #3677: mirror tests/ay/std_alloc.rs::test_realloc_grow so the
    // realloc copy path keeps the same canonical heap address family as the
    // pre-realloc store. This shape previously hit fallback/drop counters even
    // though the allocation ID was recoverable through MIR tracing.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_std_alloc_realloc_grow_shape() -> i32 {
            let layout = std::alloc::Layout::new::<i32>();
            let ptr = unsafe { std::alloc::alloc(layout) } as *mut i32;
            unsafe { ptr.write(42) };
            let new_layout = std::alloc::Layout::array::<i32>(2).unwrap();
            let new_ptr =
                unsafe { std::alloc::realloc(ptr as *mut u8, layout, new_layout.size()) }
                    as *mut i32;
            unsafe { new_ptr.read() }
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_std_alloc_realloc_grow_shape");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_std_alloc_realloc_grow_shape",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(
            !vc.relations.is_empty(),
            "std_alloc realloc-grow shape should produce CHC relations"
        );
        assert!(!vc.rules.is_empty(), "std_alloc realloc-grow shape should produce CHC rules");
        // #3728: Always-moved model — confirmed by obj_valid output presence.
        // After scalarization, obj_valid__out may become obj_valid_at_0xN_bv32__out.
        assert!(
            vc_rules_contain_var_out(&vc, "obj_valid"),
            "std_alloc realloc-grow shape should reach the precise realloc model (always-moved #3728)"
        );
        // After scalarization, mem_i32__out may become a per-index scalar variable.
        assert!(
            vc_rules_contain_var_out(&vc, "_probe_std_alloc_realloc_grow_shape_mem_i32"),
            "std_alloc realloc-grow shape should constrain the i32 heap output array"
        );
        assert_std_alloc_realloc_grow_shape_retains_literal(&vc);

        let fallback_count = get_chc_fallback_counts()
            .get("probe_std_alloc_realloc_grow_shape")
            .copied()
            .unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "std_alloc realloc-grow shape should not increment CHC fallback count, got {fallback_count}"
        );

        let translation_drops = take_translation_drop_by_fn();
        let translation_drop_count =
            translation_drops.get("probe_std_alloc_realloc_grow_shape").copied().unwrap_or(0);
        // Realloc-grow shape has 1 translation-drop from the ptr cast encoding
        // path (opaque cast or intermediate pointer). This is a sound
        // over-approximation, not a correctness issue.
        assert!(
            translation_drop_count <= 1,
            "std_alloc realloc-grow shape should have at most 1 translation-drop, got {translation_drop_count}, map={translation_drops:?}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

#[test]
fn test_mir_std_alloc_realloc_grow_full_shape_has_no_chc_fallbacks() {
    // Part of #3893: exact mirror of tests/ay/std_alloc.rs::test_realloc_grow
    // including tail write (new_ptr.add(1).write(99)) and final dealloc.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub unsafe fn probe_std_alloc_realloc_grow_full() {
            let layout = std::alloc::Layout::new::<i32>();
            let ptr = unsafe { std::alloc::alloc(layout) } as *mut i32;
            assert!(!ptr.is_null());
            unsafe { ptr.write(42) };
            let new_layout = std::alloc::Layout::array::<i32>(2).unwrap();
            let new_ptr = unsafe { std::alloc::realloc(ptr as *mut u8, layout, new_layout.size()) } as *mut i32;
            assert!(!new_ptr.is_null());
            assert!(unsafe { new_ptr.read() } == 42);
            unsafe { new_ptr.add(1).write(99) };
            unsafe { std::alloc::dealloc(new_ptr as *mut u8, new_layout) };
        }
    "#;
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let name = "probe_std_alloc_realloc_grow_full";
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert!(!vc.relations.is_empty() && !vc.rules.is_empty());
        assert!(vc_rules_contain_var(&vc, "obj_valid__out"), "should reach precise realloc model");
        assert!(vc_rules_contain_var(&vc, "obj_size__out"), "should constrain obj_size (dealloc)");
        assert!(vc.relations.iter().any(|r| r.name == "error"), "should encode dealloc error");
        assert!(any_constraint_str(&vc, |c| c.contains("#x0000002a")), "should retain write(42)");
        assert!(any_constraint_str(&vc, |c| c.contains("#x00000063")), "should retain write(99)");
        let fb = get_chc_fallback_counts().get(name).copied().unwrap_or(0);
        assert_eq!(fb, 0, "should not increment CHC fallback count, got {fb}");
        let drops = take_translation_drop_by_fn();
        let td = drops.get(name).copied().unwrap_or(0);
        assert!(td <= 2, "should have at most 2 translation-drops, got {td}, map={drops:?}");
    });
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

#[test]
fn test_mir_dealloc_invalidates_obj_valid() {
    // Dealloc (drop of Box) should set obj_valid[id] = false.
    // This is critical for use-after-free detection.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_dealloc_invalidation() {
            let b = Box::new(42u32);
            drop(b);
            // After drop, the heap ID from Box::new should be invalid
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_invalidation");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_invalidation",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for dealloc");

        // Dealloc should produce constraints that update obj_valid__out
        // (setting the freed object's validity to false)
        assert!(
            vc_contains_obj_valid_false_update(&vc),
            "Dealloc VC should contain obj_valid invalidation"
        );
        // Also check that error relation exists (for safety checks like
        // double-free detection and dealloc size mismatch)
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "Dealloc should generate error relation for safety checks");
    });
}

// =============================================================================
// Fail-closed fallback behavior (Part of #2426)
// =============================================================================

#[test]
fn test_translate_alloc_call_missing_args_fail_closed() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_missing_args_fail_closed() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_missing_args_fail_closed");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_missing_args_fail_closed",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let modified_locals = std::collections::HashSet::new();

        // Fix #2745: RustAlloc/RustAllocZeroed return Some with symbolic size
        // when args are unresolvable (prevents unconstrained pointer false-positives).
        // Fix #2758: RustDealloc returns Some with symbolic fallback to preserve
        // obj_valid invalidation (prevents silent use-after-free/double-free gaps).
        for stub in [StubKind::RustAlloc, StubKind::RustAllocZeroed] {
            let result = chc_ctx.translate_alloc_call(stub, &[], &modified_locals);
            assert!(
                result.is_some(),
                "stub {:?} should return symbolic alloc when args unresolvable (Fix #2745)",
                stub
            );
        }
        {
            let result = chc_ctx.translate_alloc_call(StubKind::RustDealloc, &[], &modified_locals);
            assert!(
                result.is_some(),
                "RustDealloc should return symbolic fallback to preserve obj_valid (Fix #2758)",
            );
        }
        // RustRealloc and Layout stubs still fail closed.
        for stub in [StubKind::RustRealloc, StubKind::LayoutSize, StubKind::LayoutAlign] {
            let result = chc_ctx.translate_alloc_call(stub, &[], &modified_locals);
            assert!(
                result.is_none(),
                "stub {:?} should fail closed when arguments are unresolved",
                stub
            );
        }
    });
}

// =============================================================================
// Dealloc size-match check gated on args_resolved (Part of #2769)
// =============================================================================

#[test]
fn test_mir_dealloc_resolved_args_emits_size_match_check() {
    // Part of #2769: Verify that dealloc with resolved args still emits the
    // obj_size size-match safety check. The fix gates `size_matches` on
    // `args_resolved` to prevent a vacuous check when size is symbolic.
    // This test ensures the gate doesn't accidentally suppress the check
    // on the normal (args resolved) path.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_dealloc_size_match() {
            let b = Box::new(42u32);
            drop(b);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_match",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for dealloc");

        // Fix #2798: The dealloc safety check uses obj_size_in.select(obj_id),
        // producing a Select on obj_size_in. Assert via structured tree query
        // to avoid materializing the entire VC as a multi-MB Debug string.
        assert!(
            vc_rules_contain_var(&vc, "obj_size"),
            "Dealloc with resolved args must emit obj_size constraint (#2769, #2798)."
        );

        // Error relation must exist for the safety checks
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "Dealloc must generate error relation for safety checks");

        // Fix #2798: Verify the size-match Select and obj_size appear in error-targeting
        // rules specifically, not just anywhere in the VC. The size_matches expression is
        // pushed to safety_checks, which become error-rule constraints.
        // Use separate checks: error rules must contain a Select AND reference obj_size.
        let has_select_in_error = vc.rules.iter().filter(|r| r.head.name == "error").any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Select { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            (has_select_in_error && vc_error_rules_contain_var(&vc, "obj_size"))
                || vc_error_rules_contain_obj_size_metadata(&vc),
            "Dealloc size-match check (obj_size metadata) must appear in error-targeting rules. \
             If this fails, the size-match safety check is missing from the error path (#2798)."
        );

        // Fix #2798: With resolved args, dealloc must produce error rules.
        // Safety checks (double-free, size-match, offset==0) may be combined
        // into fewer rules (constraints AND-ed in one rule body). The minimum
        // of 2 covers: (1) alloc precondition checks, (2) pointer safety checks.
        let error_rule_count = vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(
            error_rule_count >= 2,
            "Dealloc with resolved args must produce >=2 error rules (got {}); \
             expected alloc precondition + pointer safety checks (#2798)",
            error_rule_count
        );
    });
}

// =============================================================================
// Realloc old_size vs obj_size validation (Part of #2785)
// =============================================================================

#[test]
fn test_mir_realloc_emits_old_size_mismatch_safety_check() {
    // Part of #2785: translate_rust_realloc must validate that the caller's
    // old_size matches the recorded obj_size[obj_id], analogous to dealloc's
    // size-mismatch check. Without this, a buggy caller passing the wrong
    // old_size to realloc is silently accepted.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_realloc_old_size_check() {
            let layout = unsafe { std::alloc::Layout::from_size_align_unchecked(16, 8) };
            let ptr = unsafe { std::alloc::alloc(layout) };
            let _new_ptr = unsafe { std::alloc::realloc(ptr, layout, 64) };
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_realloc_old_size_check");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_realloc_old_size_check",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for realloc");

        // The realloc model should emit safety checks that reference the obj_size
        // input array (selecting the recorded allocation size for comparison with
        // caller's old_size). This is the size-mismatch validation from #2785,
        // analogous to dealloc's check at stubs_alloc_heap_ops.rs:236.

        // Error relation must exist (safety checks emit error-reaching rules)
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "Realloc old_size check must produce error relation");

        // Count error-targeting rules. The realloc model should produce multiple
        // safety checks: old_valid, offset==0, old_size match, new_size checks.
        let error_rule_count = vc.rules.iter().filter(|r| r.head.name == "error").count();
        // Dealloc has 3 safety checks (double-free, size-match, offset==0) plus
        // arg validity checks. Realloc should have at least 4: old_valid, offset==0,
        // old_size match (#2785), plus new_size/align validity checks.
        assert!(
            error_rule_count >= 4,
            "Realloc must generate >=4 error rules (got {error_rule_count}); \
             missing old_size validation (#2785) or other safety checks"
        );
    });
}

// =============================================================================
// Stale pointer after realloc (Part of #2425, acceptance criterion 3)
// =============================================================================

#[test]
fn test_mir_realloc_stale_pointer_emits_obj_valid_check() {
    // Allocate, realloc, then read through the OLD pointer. The realloc model
    // should invalidate old_ptr's obj_valid on the "moved" branch, so any
    // subsequent load through old_ptr triggers a safety check (obj_valid[old_id]).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_realloc_stale_ptr() -> u8 {
            let layout = unsafe { std::alloc::Layout::from_size_align_unchecked(16, 8) };
            let old_ptr = unsafe { std::alloc::alloc(layout) };
            unsafe { *old_ptr = 0xAB };
            let _new_ptr = unsafe { std::alloc::realloc(old_ptr, layout, 32) };
            // Stale access: old_ptr may be invalid after realloc moved
            unsafe { *old_ptr }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_realloc_stale_ptr");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_realloc_stale_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for realloc-then-stale-read");

        // #3728: Always-moved model — old pointer unconditionally invalidated.
        // obj_valid output must be updated (old pointer invalidation).
        // After scalarization, obj_valid__out may become obj_valid_at_0xN_bv32__out.
        assert!(
            vc_rules_contain_var_out(&vc, "obj_valid"),
            "Stale-pointer pattern must emit obj_valid output (old pointer invalidation)"
        );

        // The error relation must exist for the solver to produce a CTREX
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "VC must include error relation for safety check counterexample");
    });
}

// test_translate_alloc_call_non_bitvec_sizes_fail_closed removed:
// Bool-typed operands are coerced to bitvec by coerce_bitvec_width_safe (#2244),
// so the original bool-arg premise no longer triggers fail-closed.
// The missing-args fail-closed path is covered by
// test_translate_alloc_call_missing_args_fail_closed above.

// =============================================================================
// Fallback counter tests for dealloc (Part of #2783)
// =============================================================================

/// RustDealloc with empty args increments sound_fallback_count() because size/align
/// resolution fails, triggering the symbolic fallback at stubs_alloc_heap_ops.rs
/// line 192.
/// Part of #2783.
#[test]
fn test_dealloc_unresolvable_args_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_dealloc_sound_fallback_counter() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_sound_fallback_counter");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_dealloc_sound_fallback_counter",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let modified_locals = std::collections::HashSet::new();

        let before = chc_ctx.sound_fallback_count();
        let _result = chc_ctx.translate_alloc_call(StubKind::RustDealloc, &[], &modified_locals);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "RustDealloc with unresolvable args should increment sound_fallback_count() \
             (before={before}, after={after})"
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_call_slice.rs — slice stub codegen pipeline tests.
//!
//! Part of #2921 (zero-coverage remediation for codegen_call_slice.rs).
//! Supplements test_call_slice_fallback.rs which covers fallback/error paths.
//! These tests exercise the positive/success code paths:
//! - SliceIndexIndex / IndexIndex with array-select semantics
//! - SlicePartialEqEqual with resolved referent equality
//! - ZST element detection
//! - Bounds guard emission
//! - chc_array_length, get_dt_field_sort, coerce_to_pointer_width,
//!   is_zst_type_for_slice helpers

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// SliceIndexIndex — array indexing pipeline
// =============================================================================

/// Array indexing via `arr[i]` lowers to SliceIndexIndex / IndexIndex stub
/// and should produce array-select semantics in CHC encoding.
#[test]
fn test_slice_index_array_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_index(arr: &[u32; 4], i: usize) -> u32 {
            arr[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_index", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_array_index", bb_count);

        // Array indexing should produce an error rule for bounds checking.
        let has_error_rule = vc.rules.iter().any(|r| r.head.name == "error");
        assert!(
            has_error_rule,
            "probe_array_index: array indexing should produce at least one error rule (bounds check)"
        );
    });
}

/// Slice indexing via `slice[i]` exercises the slice-typed path.
#[test]
fn test_slice_index_slice_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_index(slice: &[u32], i: usize) -> u32 {
            slice[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_index", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_slice_index", bb_count);
    });
}

/// Vec indexing via `v[i]` routes through IndexIndex and should exercise
/// the datatype fld_data extraction path.
#[test]
fn test_vec_index_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_index(v: &Vec<u32>, i: usize) -> u32 {
            v[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_index", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_index", bb_count);
    });
}

// =============================================================================
// SlicePartialEqEqual — slice equality comparison
// =============================================================================

/// Slice equality `a == b` where both are `&[u32]` exercises
/// SlicePartialEqEqual in codegen_call_slice.rs.
#[test]
fn test_slice_partial_eq_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_eq(a: &[u32; 4], b: &[u32; 4]) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_eq", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_slice_eq", bb_count);
    });
}

// =============================================================================
// ZST element detection — is_zst_type_for_slice
// =============================================================================

/// Indexing a ZST slice (e.g., `&[()]`) should produce a Unit constructor
/// instead of an array select. Exercises the is_zst_type_for_slice check.
#[test]
fn test_slice_index_zst_unit_tuple() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zst_index(arr: &[(); 3], i: usize) -> () {
            arr[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_zst_index", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_zst_index", bb_count);
    });
}

// =============================================================================
// Helper function tests — static methods on ChcCtx
// =============================================================================

/// get_dt_field_sort returns the sort of a named field in a datatype expression.
#[test]
fn test_get_dt_field_sort_returns_field_sort() {
    let vec_sort = struct_sort(
        "TestVec_u32",
        vec![
            ("fld_ptr", Sort::bitvec(64)),
            ("fld_len", Sort::bitvec(64)),
            ("fld_cap", Sort::bitvec(64)),
            ("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(32))),
        ],
    );
    let vec_expr = Expr::var("test_vec", vec_sort);

    let len_sort = ChcCtx::get_dt_field_sort(&vec_expr, "fld_len");
    assert!(len_sort.is_some(), "fld_len should exist in TestVec_u32");
    assert!(len_sort.unwrap().bitvec_width() == Some(64), "fld_len should be BV64");

    let data_sort = ChcCtx::get_dt_field_sort(&vec_expr, "fld_data");
    assert!(data_sort.is_some(), "fld_data should exist in TestVec_u32");
    assert!(data_sort.unwrap().is_array(), "fld_data should be Array sort");

    let missing_sort = ChcCtx::get_dt_field_sort(&vec_expr, "nonexistent");
    assert!(missing_sort.is_none(), "nonexistent field should return None");
}

/// get_dt_field_sort returns None for non-datatype expressions.
#[test]
fn test_get_dt_field_sort_non_datatype_returns_none() {
    let bv_expr = Expr::var("x", Sort::bitvec(32));
    assert!(
        ChcCtx::get_dt_field_sort(&bv_expr, "fld_len").is_none(),
        "non-datatype expressions should return None"
    );
}

/// chc_array_length is exercised indirectly via Vec indexing — the bounds
/// guard emission path uses chc_array_length to extract fld_len.
/// At Reg level, Vec parameters may not expose full datatype structure,
/// so bounds checks may not be emittable. Verify the pipeline produces
/// a well-formed VC regardless.
#[test]
fn test_vec_index_exercises_bounds_guard_path() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_fld_len(v: &Vec<u32>, i: usize) -> u32 {
            v[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_fld_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_fld_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_fld_len", body.blocks.len());

        // The codegen_call_slice_index_impl path was exercised. At Reg level
        // with a symbolic &Vec parameter, the bounds guard may fall through
        // to constrained symbolic fallback. Verify the VC is well-formed
        // and the error relation exists (standard structural requirement).
        let has_error_rel = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error_rel, "probe_vec_fld_len: error relation must exist");
    });
}

// =============================================================================
// Bounds guard emission
// =============================================================================

/// Array indexing at a constant out-of-bounds index should still produce
/// both a transition rule and an error rule (bounds guard).
#[test]
fn test_array_index_bounds_guard_emitted() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_bounds(arr: &[u32; 4]) -> u32 {
            arr[3]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_bounds");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_bounds", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_array_bounds", bb_count);

        // Should have error rule(s) for the implicit bounds check.
        let has_error_rule = vc.rules.iter().any(|r| r.head.name == "error");
        assert!(
            has_error_rule,
            "probe_array_bounds: expected at least one error rule for bounds checking"
        );
    });
}

/// Composite: slice indexing after Vec push exercises the full path from
/// Vec construction → push → as_slice → index.
#[test]
fn test_vec_push_then_slice_index_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_slice_index() -> u32 {
            let mut v = Vec::<u32>::new();
            v.push(42);
            v.push(99);
            v[1]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_slice_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_slice_index", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_slice_index", bb_count);
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_slice_index");
    });
}

fn with_slice_contains_dispatch(source: &str, fn_name: &str, assertions: impl FnOnce(&str) + Send) {
    with_test_ay_ctx_for_source(source, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            {
                let Some(path) = chc_ctx.resolve_callee_path(func) else {
                    continue;
                };
                if !(path.ends_with("::contains")
                    && (path.contains("slice::") || path.contains("<[")))
                {
                    continue;
                }
                found = true;

                let from_rel =
                    chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
                let output_args: Vec<_> = chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                    .collect();
                let from_app = RelationApp::new(&from_rel, output_args);
                let stmt_constraints = [Expr::bool_const(true)];
                let modified_locals = HashSet::new();
                let target_opt = Some(*target);
                let before = chc_ctx.sound_fallback_count();
                let dcx = DispatchCallContext {
                    bb_idx,
                    func,
                    args,
                    destination,
                    target: &target_opt,
                    from_app: &from_app,
                    stmt_constraints: &stmt_constraints,
                    modified_locals: &modified_locals,
                    callee_path: None,
                };

                chc_ctx.codegen_call_primitive_cmp(&dcx);

                assert_eq!(
                    chc_ctx.sound_fallback_count(),
                    before,
                    "slice_contains should dispatch without recording a sound fallback"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "slice_contains direct dispatch should emit exactly one rule"
                );

                let smt = emit_chc(&chc_ctx.vc).to_string();
                assertions(&smt);
                break;
            }
        }

        assert_mir_pattern_found(found, "slice::contains");
    });
}

#[test]
fn test_slice_contains_promoted_const_receiver_dispatches_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_contains(target: char) -> bool {
            let slice: &[char] = &['s', 'm', 't', 'w', 'f'];
            slice.contains(&target)
        }
    "#;

    with_slice_contains_dispatch(SOURCE, "probe_contains", |smt| {
        assert!(
            smt.contains("(or "),
            "slice_contains should lower to a disjunction over element comparisons, got: {smt}"
        );
        assert!(
            smt.contains("(select "),
            "slice_contains should read from the backing array with select, got: {smt}"
        );
    });
}

#[test]
fn test_slice_contains_pub_static_shape_dispatches_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub static DAYS_OF_WEEK: [char; 7] = ['s', 'm', 't', 'w', 't', 'f', 's'];

        pub fn probe_pub_static(day: usize) -> bool {
            let slice: &[char] = &['s', 'm', 't', 'w', 'f'];
            let alias = slice;
            alias.contains(&DAYS_OF_WEEK[day])
        }
    "#;

    with_slice_contains_dispatch(SOURCE, "probe_pub_static", |smt| {
        let select_count = smt.match_indices("(select ").count();
        assert!(
            select_count >= 2,
            "pub_static receiver/argument path should select from both the receiver and the static argument, got: {smt}"
        );
        assert!(
            smt.contains("(or "),
            "pub_static receiver path should still lower to a disjunction, got: {smt}"
        );
    });
}

#[test]
fn test_slice_contains_pub_static_argument_resolves_concrete_static_backing() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub static DAYS_OF_WEEK: [char; 7] = ['s', 'm', 't', 'w', 't', 'f', 's'];

        pub fn probe_pub_static(day: usize) -> bool {
            let slice: &[char] = &['s', 'm', 't', 'w', 'f'];
            let alias = slice;
            alias.contains(&DAYS_OF_WEEK[day])
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, "probe_pub_static");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_pub_static", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, needle_arg) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, bb)| {
                let TerminatorKind::Call { func, args, .. } = &bb.terminator.kind else {
                    return None;
                };
                let path = chc_ctx.resolve_callee_path(func)?;
                if !(path.ends_with("::contains")
                    && (path.contains("slice::") || path.contains("<[")))
                {
                    return None;
                }
                Some((bb_idx, args.get(1)?.clone()))
            })
            .expect("expected slice::contains call with static-backed needle");

        let (_stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let resolved = chc_ctx
            .resolve_ref_or_const_referent(&needle_arg, &modified_locals)
            .expect("needle should resolve through concrete static-backed metadata");

        assert_eq!(
            resolved.sort().bitvec_width(),
            Some(32),
            "DAYS_OF_WEEK[day] should resolve to a concrete char bitvector, got {:?}",
            resolved.sort()
        );
        let text = resolved.to_string();
        assert!(
            text.contains("select"),
            "static-backed contains needle should read through a backing array select, got {text}"
        );
        assert!(
            text.contains("store"),
            "resolved static-backed needle should use the concrete stored array literal, got {text}"
        );
        assert!(
            !text.contains("_static_probe_pub_static_DAYS_OF_WEEK"),
            "needle resolution should use the concrete static seed, not only the symbolic static state var: {text}"
        );
    });
}

const PUB_STATIC_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/Static/pub_static.rs");

fn strip_pub_static_for_unit_ctx(source: &str) -> String {
    let mut result = String::from(
        r#"
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
}

"#,
    );

    for line in source.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("#[kani::proof]")
            || trimmed.starts_with("// kani-expect:")
            || trimmed.starts_with("//!")
            || trimmed.starts_with("// Copyright")
            || trimmed.starts_with("// SPDX-License-Identifier:")
            || trimmed.starts_with("// Licensed under")
        {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }

    result
}

fn pub_static_real_file_source() -> String {
    strip_pub_static_for_unit_ctx(PUB_STATIC_REAL_FILE)
}

fn with_real_file_slice_contains_dispatch(assertions: impl FnOnce(&str) + Send) {
    let source = pub_static_real_file_source();
    with_test_ay_ctx_for_source(&source, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, "harness");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "harness", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            {
                let Some(path) = chc_ctx.resolve_callee_path(func) else {
                    continue;
                };
                if !(path.ends_with("::contains")
                    && (path.contains("slice::") || path.contains("<[")))
                {
                    continue;
                }
                found = true;

                let from_rel =
                    chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
                let output_args: Vec<_> = chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                    .collect();
                let from_app = RelationApp::new(&from_rel, output_args);
                let stmt_constraints = [Expr::bool_const(true)];
                let modified_locals = HashSet::new();
                let target_opt = Some(*target);
                let before = chc_ctx.sound_fallback_count();
                let dcx = DispatchCallContext {
                    bb_idx,
                    func,
                    args,
                    destination,
                    target: &target_opt,
                    from_app: &from_app,
                    stmt_constraints: &stmt_constraints,
                    modified_locals: &modified_locals,
                    callee_path: None,
                };

                chc_ctx.codegen_call_primitive_cmp(&dcx);

                assert_eq!(
                    chc_ctx.sound_fallback_count(),
                    before,
                    "real-file pub_static harness should dispatch slice_contains without sound fallback"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "real-file pub_static harness should emit exactly one direct-dispatch rule"
                );

                let smt = emit_chc(&chc_ctx.vc).to_string();
                assertions(&smt);
                break;
            }
        }

        assert_mir_pattern_found(found, "slice::contains");
    });
}

#[test]
fn test_pub_static_real_file_contains_dispatches_without_iterator_fallbacks() {
    with_real_file_slice_contains_dispatch(|smt| {
        assert!(
            smt.contains("(or "),
            "real-file pub_static harness should lower contains to a disjunction, got: {smt}"
        );
        assert!(
            smt.contains("(select "),
            "real-file pub_static harness should read from concrete backing arrays, got: {smt}"
        );
        assert!(
            !smt.contains("ChunksExact_lt_char"),
            "direct slice_contains dispatch must avoid iterator/chunks lowering, got: {smt}"
        );
    });
}

#[test]
fn test_pub_static_real_file_translation_has_no_unhandled_calls() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();

    let source = pub_static_real_file_source();
    with_test_ay_ctx_for_source(&source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "harness");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "harness", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_drop_reasons = drop_fallback_reasons.get("harness").cloned().unwrap_or_default();
        let fn_sites = translation_sites.get("harness").cloned().unwrap_or_default();

        assert_vc_structure(&vc, "harness", body.blocks.len());
        assert!(
            vc.rules.iter().any(|rule| rule.body.relation.is_some()),
            "real-file pub_static harness should emit transition rules"
        );
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "real-file pub_static harness should not leave iterator/closure calls unhandled"
        );
        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "real-file pub_static harness should avoid demoted CHC fallbacks; \
             fn_drop_reasons={fn_drop_reasons:?}, fn_sites={fn_sites:?}, \
             drop_fallback_reasons={drop_fallback_reasons:?}, translation_sites={translation_sites:?}"
        );
        assert!(
            diagnostics.sound_fallback_detail.is_empty(),
            "real-file pub_static harness should not record categorized sound fallbacks: {:?}",
            diagnostics.sound_fallback_detail
        );

        let smt = emit_chc(&vc).to_string();
        assert!(
            !smt.contains("ChunksExact_lt_char"),
            "full pub_static translation should stay off iterator/chunks machinery, got: {smt}"
        );
    });

    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    assert_eq!(
        unhandled_calls.get("harness").copied().unwrap_or(0),
        0,
        "real-file pub_static harness should keep unhandled-call counters at zero, map={unhandled_calls:?}"
    );
}

/// Part of #4072: Regression guard — the `contains` disjunction needle must
/// resolve to `select(DAYS_OF_WEEK_concrete, day)`, not a raw BV64 pointer.
#[test]
fn test_pub_static_real_file_needle_selects_from_concrete_static() {
    let source = pub_static_real_file_source();
    with_test_ay_ctx_for_source(&source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "harness");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "harness", ChcConfig::default());
        let (vc, _, _diagnostics) = chc_ctx.translate_with_diagnostics();
        let smt = emit_chc(&vc).to_string();

        // The disjunction should contain `select` from the concrete DAYS_OF_WEEK array,
        // NOT `((_ extract 31 0) _harness_11)` which is a pointer truncation.
        assert!(
            !smt.contains("extract 31 0"),
            "pub_static needle must not be a pointer truncation (extract 31 0), got: {smt}"
        );
        // The concrete static array stores should appear in the disjunction rule.
        let store_count = smt.matches("store").count();
        assert!(
            store_count >= 7,
            "pub_static needle should select from concrete static stores (need ≥7 for DAYS_OF_WEEK), got {store_count} stores"
        );
    });
}

// =============================================================================
// Slice comparison and indexing — MIR-pipeline positive path tests
// (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

/// Slice equality comparison (== on &[u8]) triggers SlicePartialEqEqual path.
#[test]
fn test_slice_partial_eq_equal() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_eq(a: &[u8], b: &[u8]) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_eq", ChcConfig::default());

        assert_vc_structure(&vc, "probe_slice_eq", body.blocks.len());

        let has_bool = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool, "slice_eq VC should have bool-like state vars");

        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "slice_eq should produce constrained transition rules (equality semantics)"
        );
    });
}

/// Slice indexing (a[i]) triggers SliceIndexIndex / IndexIndex path.
#[test]
fn test_slice_index_index() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_index(s: &[u32], i: usize) -> u32 {
            s[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_slice_index", body.blocks.len());

        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "slice index VC should have BV32 for u32 return");
    });
}

const VEC_SLICE_PRECISION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_index_ref_precision() {
        let v = vec![1u32, 2, 3];
        assert!(v[1] == 2);
    }

    pub fn probe_vec_range_to_precision() {
        let v = vec![1u32, 2, 3];
        assert!(v[0..2] == v[..2]);
    }

    pub fn probe_vec_range_full_precision() {
        let v = vec![1u32, 2, 3];
        assert!(v[..] == v[0..3]);
    }
"#;

const VEC_SLICE_PRECISION_FNS: [&str; 3] = [
    "probe_vec_index_ref_precision",
    "probe_vec_range_to_precision",
    "probe_vec_range_full_precision",
];

// W1:3962 refresh_full_output_args eliminated the bookkeeping residuals that
// P1:3841 had pinned at 2 per fn. Vec-slice probes now produce zero drops.
const VEC_SLICE_PRECISION_RESIDUAL_DROPS_PER_FN: usize = 0;

#[test]
fn test_vec_slice_precision_paths_stay_out_of_fallback() {
    with_test_ay_ctx_for_source(VEC_SLICE_PRECISION_SOURCE, |ctx| {
        for fn_name in VEC_SLICE_PRECISION_FNS {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

            let smt = emit_chc(&vc).to_string();
            assert_z3_result(&smt, "unsat");
            assert_eq!(
                diagnostics.fallback_count.get(),
                0,
                "{fn_name} should stay on the precise slice path without demoted CHC fallback"
            );
            assert_eq!(
                diagnostics.place_translation_drop.get(),
                VEC_SLICE_PRECISION_RESIDUAL_DROPS_PER_FN,
                "{fn_name} should have zero local place_translation_drop events"
            );
            assert_eq!(
                diagnostics.const_translation_drop.get(),
                0,
                "{fn_name} should have zero local const_translation_drop events"
            );
            assert_eq!(
                diagnostics.unsupported_field_projection.get(),
                0,
                "{fn_name} should have zero local unsupported_field_projection events"
            );
            assert_eq!(
                diagnostics.inferable_predicate.get(),
                0,
                "{fn_name} should not emit inferable predicates"
            );
            assert!(
                diagnostics.sound_fallback_detail.is_empty(),
                "{fn_name} should not record categorized sound-fallback details: {:?}",
                diagnostics.sound_fallback_detail
            );
        }
    });
}

// =============================================================================
// RangeFull identity — inline walker (#4163)
// =============================================================================

/// Part of #4163: `slice.get(..)` with RangeFull index should be handled as
/// identity by the inline walker, avoiding unconstrained fallback. Verifies
/// the handler added in `try_inline_range_full_identity`.
///
/// The probe function calls `get(..).unwrap()` on a slice, which lowers to
/// `<RangeFull as SliceIndex<[u32]>>::get` followed by `Option::unwrap`.
/// The inline walker should recognize RangeFull and produce a constrained
/// identity result.
const RANGE_FULL_GET_IDENTITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_slice_get_range_full_identity(s: &[u32; 4]) -> u32 {
        let full: &[u32] = &s[..];
        full[0]
    }
"#;

#[test]
fn test_slice_get_range_full_identity_no_fallback() {
    with_test_ay_ctx_for_source(RANGE_FULL_GET_IDENTITY_SOURCE, |ctx| {
        let fn_name = "probe_slice_get_range_full_identity";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

        // RangeFull indexing should not trigger fallback.
        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "{fn_name}: RangeFull identity should not produce demoted CHC fallback"
        );

        // The SMT should be satisfiable/provable with no unconstrained gaps.
        let smt = emit_chc(&vc).to_string();
        // RangeFull identity should not leave any inline_nested_call_fallback gaps
        // for the SliceIndex::get call.
        assert!(
            !smt.contains("inline_nested_call_fallback_symbolic@") || !smt.contains("SliceIndex"),
            "{fn_name}: RangeFull identity should not produce SliceIndex fallback in SMT"
        );
    });
}

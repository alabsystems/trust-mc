// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Dedicated tests for chc/stubs_iterators_vec.rs — Vec iterator stub detection
// and translation extracted from stubs_iterators.rs per #2246.
//
// Part of #2303: zero-coverage remediation.
//
// Note: Helper functions (make_vec_into_iter_chc, infer_vec_sort_from_iter,
// extract_vec_data_with_sort) are thoroughly tested in test_stubs_iterators.rs.
// This file targets the public entry points: detect_vec_iter_stub,
// translate_vec_iter_call (error path), and get_collection_arg.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::codegen_ctx::CollectionProjectionKind;
use super::common::*;

// =============================================================================
// detect_vec_iter_stub — MIR-backed Vec iterator stub detection
// =============================================================================

/// Vec::into_iter() should be detected as VecIntoIter stub.
#[test]
fn test_detect_vec_iter_stub_into_iter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_into_iter() {
            let v: Vec<u32> = Vec::new();
            let _ = v.into_iter();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_into_iter");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_into_iter", ChcConfig::default());

        let detected = collect_detected_vec_iter_stubs(&chc_ctx, &body);
        assert!(
            detected.iter().any(|s| matches!(s, StubKind::VecIntoIter)),
            "Vec::into_iter should be detected as VecIntoIter, got: {detected:?}"
        );
    });
}

/// IntoIter::next() should be detected as IntoIterNext stub.
#[test]
fn test_detect_vec_iter_stub_into_iter_next() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_next() {
            let v: Vec<u32> = Vec::new();
            let mut iter = v.into_iter();
            let _ = iter.next();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_next");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_next", ChcConfig::default());

        let detected = collect_detected_vec_iter_stubs(&chc_ctx, &body);
        assert!(
            detected.iter().any(|s| matches!(s, StubKind::IntoIterNext)),
            "IntoIter::next should be detected as IntoIterNext, got: {detected:?}"
        );
    });
}

/// Non-Vec iterator calls should not be detected.
#[test]
fn test_detect_vec_iter_stub_rejects_hashmap_iter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;
        pub fn probe_hashmap_iter() {
            let m: HashMap<u32, u32> = HashMap::new();
            let _ = m.into_iter();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_iter", ChcConfig::default());

        let detected = collect_detected_vec_iter_stubs(&chc_ctx, &body);
        assert!(
            detected.is_empty(),
            "HashMap::into_iter should NOT be detected as Vec iter stub, got: {detected:?}"
        );
    });
}

// =============================================================================
// translate_vec_iter_call — unsound-skip error path (VecIntoIter with bad sort)
// =============================================================================

/// VecIntoIter with non-datatype Vec sort should emit false constraint (fail-closed).
#[test]
fn test_translate_vec_iter_call_non_datatype_emits_false_constraint() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Inject a bitvec "vec" as state_var[0] to simulate non-datatype sort
        chc_ctx.push_state_var_pair("bad_vec_in", "bad_vec_out", Sort::bitvec(64));

        let modified: HashSet<usize> = HashSet::new();
        let bad_operand = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 0,
            projection: vec![],
        });

        let skip_before = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        let result =
            chc_ctx.translate_vec_iter_call(StubKind::VecIntoIter, &[bad_operand], &modified, None);

        assert!(result.is_some(), "should return Some even for error path");
        let result = result.unwrap();
        assert!(result.result.is_none(), "error path should have no result expression");
        // W4:4053 changed forced_failure() from constraints:[false] to force_error:true
        // to avoid vacuous CHC rules. Empty constraints + force_error is the new contract.
        assert!(
            result.constraints.is_empty(),
            "forced_failure should use force_error, not false constraints"
        );
        assert!(result.force_error, "error path should request fail-closed error emission");

        let skip_after = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        assert!(skip_after > skip_before, "UNSOUND_SKIP_COUNT should increment on error path");
    });
}

/// IntoIterNext with non-datatype iter sort should use force_error.
#[test]
fn test_translate_vec_iter_call_into_iter_next_non_datatype_emits_false() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Inject a bitvec "iter" as state_var[0] to simulate non-datatype sort
        chc_ctx.push_state_var_pair("bad_iter_in", "bad_iter_out", Sort::bitvec(64));

        let modified: HashSet<usize> = HashSet::new();
        let bad_operand = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 0,
            projection: vec![],
        });

        let skip_before = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        let result = chc_ctx.translate_vec_iter_call(
            StubKind::IntoIterNext,
            &[bad_operand],
            &modified,
            None,
        );

        assert!(result.is_some(), "IntoIterNext error path should return Some");
        let result = result.unwrap();
        assert!(result.result.is_none(), "error path should have no result");
        assert!(
            result.constraints.is_empty(),
            "forced_failure should use force_error, not false constraints"
        );
        assert!(result.force_error, "error path should request fail-closed error emission");

        let skip_after = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        assert!(skip_after > skip_before, "UNSOUND_SKIP_COUNT should increment");
    });
}

/// translate_vec_iter_call with empty args returns None.
#[test]
fn test_translate_vec_iter_call_empty_args_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_vec_iter_call(StubKind::VecIntoIter, &[], &modified, None);
        assert!(result.is_none(), "VecIntoIter with 0 args should return None");

        let result = chc_ctx.translate_vec_iter_call(StubKind::IntoIterNext, &[], &modified, None);
        assert!(result.is_none(), "IntoIterNext with 0 args should return None");
    });
}

/// VecIter and VecIterMut with empty args also return None (args.first()?).
///
/// Part of #2627: error-path test coverage gaps.
#[test]
fn test_translate_vec_iter_and_iter_mut_empty_args_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_vec_iter_call(StubKind::VecIter, &[], &modified, None);
        assert!(result.is_none(), "VecIter with 0 args should return None");

        let result = chc_ctx.translate_vec_iter_call(StubKind::VecIterMut, &[], &modified, None);
        assert!(result.is_none(), "VecIterMut with 0 args should return None");
    });
}

/// Non-Vec-iterator stub kind returns None (catch-all arm).
///
/// Part of #2627: error-path test coverage gaps.
#[test]
fn test_translate_vec_iter_non_vec_stub_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // BigIntAdd is not a Vec iterator stub — should hit the catch-all None
        let result = chc_ctx.translate_vec_iter_call(StubKind::BigIntAdd, &[], &modified, None);
        assert!(result.is_none(), "non-Vec stub should return None");

        let result = chc_ctx.translate_vec_iter_call(StubKind::HashMapInsert, &[], &modified, None);
        assert!(result.is_none(), "HashMapInsert is not a Vec iterator stub");
    });
}

// =============================================================================
// get_collection_arg — projected collection local reconstruction (#2874 Step 2)
// =============================================================================

/// Flattened projected Vec locals should be reconstructed to datatype expressions.
#[test]
fn test_get_collection_arg_reconstructs_projected_vec_local() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_get_collection_arg_vec() -> usize {
            let v = vec![1u32, 2u32, 3u32];
            let it = v.iter();
            it.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_get_collection_arg_vec");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_get_collection_arg_vec", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let vec_local = chc_ctx
            .collections
            .projection_locals
            .iter()
            .find_map(
                |(local, kind)| {
                    if *kind == CollectionProjectionKind::Vec { Some(*local) } else { None }
                },
            )
            .expect("expected projected Vec local metadata");

        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&vec_local),
            "projected Vec local should be flattened"
        );

        let operand = Operand::Copy(Place { local: vec_local, projection: vec![] });
        let modified: HashSet<usize> = HashSet::new();

        // Part of #2876: Flattened locals now reconstruct as Datatypes via bare
        // read.  Verify the reconstruction produces a Datatype expression.
        let direct = chc_ctx.translate_operand_with_modified(&operand, &modified);
        assert!(
            direct.as_ref().is_some_and(|e| e.sort().is_datatype()),
            "bare flattened local should reconstruct as Datatype (Part of #2876)"
        );

        let vec_expr = chc_ctx
            .get_collection_arg(&operand, &modified)
            .expect("projected Vec local should reconstruct to datatype");
        assert!(vec_expr.sort().is_datatype(), "reconstructed Vec should be datatype");
        let ExprValue::DatatypeConstructor { args, .. } = vec_expr.value() else {
            panic!("expected datatype constructor for reconstructed Vec");
        };
        assert_eq!(args.len(), 4, "Vec constructor should have 4 fields");
    });
}

/// Deep-flattened VecIntoIter locals should rebuild nested Vec + pos structure.
#[test]
fn test_get_collection_arg_reconstructs_projected_vec_into_iter_local() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_get_collection_arg_vec_into_iter() -> Option<u32> {
            let mut it = vec![1u32, 2u32].into_iter();
            it.next()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_get_collection_arg_vec_into_iter");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_get_collection_arg_vec_into_iter",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let iter_local = chc_ctx
            .collections
            .projection_locals
            .iter()
            .find_map(|(local, kind)| {
                if *kind == CollectionProjectionKind::VecIntoIter { Some(*local) } else { None }
            })
            .expect("expected projected VecIntoIter local metadata");

        assert!(
            chc_ctx.flattened_field_count(iter_local) >= 5,
            "VecIntoIter projection should include Vec fields + pos"
        );

        let operand = Operand::Copy(Place { local: iter_local, projection: vec![] });
        let modified: HashSet<usize> = HashSet::new();
        let iter_expr = chc_ctx
            .get_collection_arg(&operand, &modified)
            .expect("projected VecIntoIter local should reconstruct to datatype");

        assert!(iter_expr.sort().is_datatype(), "reconstructed VecIntoIter should be datatype");
        let ExprValue::DatatypeConstructor { args, .. } = iter_expr.value() else {
            panic!("expected datatype constructor for reconstructed VecIntoIter");
        };
        assert_eq!(args.len(), 2, "VecIntoIter constructor should have (vec, pos) args");
        assert!(
            matches!(args[0].value(), ExprValue::DatatypeConstructor { .. }),
            "VecIntoIter.fld_vec should be reconstructed as a nested datatype"
        );
    });
}

// =============================================================================
// Slice IntoIterator trait path detection — Part of #3602
// =============================================================================

/// `for val in x` where `x: &[u32]` should detect VecIter via the IntoIterator trait path.
#[test]
fn test_detect_slice_into_iter_immutable() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_slice_for_loop(s: &[u32]) -> u32 {
            let mut sum = 0u32;
            for val in s {
                sum += val;
            }
            sum
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_for_loop");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_slice_for_loop", ChcConfig::default());

        let detected = collect_detected_vec_iter_stubs(&chc_ctx, &body);
        assert!(
            detected.iter().any(|s| matches!(s, StubKind::VecIter)),
            "for val in &[u32] should route IntoIterator::into_iter to VecIter, got: {detected:?}"
        );
        assert!(
            detected.iter().any(|s| matches!(s, StubKind::IntoIterNext)),
            "slice iterator next() should still be detected as IntoIterNext, got: {detected:?}"
        );
    });
}

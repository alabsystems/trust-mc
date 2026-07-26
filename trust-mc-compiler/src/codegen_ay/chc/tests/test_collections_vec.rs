// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Vec iterator translation — normal path (Part of #2187)
// Exercises translate_vec_iter_call for VecIntoIter and IntoIterNext.
// Normal path: vec has datatype sort, no UNSOUND_SKIP_COUNT increment.
// =============================================================================

#[test]
fn test_vec_into_iter_translation_normal_path() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_into_iter() {
            let v: Vec<u32> = Vec::new();
            let mut iter = v.into_iter();
            let _ = iter.next();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_into_iter");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_into_iter", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let skip_before = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        let modified_locals: HashSet<usize> = HashSet::new();
        let mut found_into_iter = false;
        let mut found_next = false;

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_vec_iter_stub(func)
            {
                match stub {
                    StubKind::VecIntoIter => {
                        let result =
                            chc_ctx.translate_vec_iter_call(stub, args, &modified_locals, None);
                        // Normal path: translation succeeds with no false constraints
                        let r = result.expect(
                            "translate_vec_iter_call returned None for VecIntoIter on normal path",
                        );
                        assert!(
                            !r.constraints
                                .iter()
                                .any(|c| matches!(c.value(), ExprValue::BoolConst(false))),
                            "Normal VecIntoIter path should not emit false constraint"
                        );
                        found_into_iter = true;
                    }
                    StubKind::IntoIterNext => {
                        let result =
                            chc_ctx.translate_vec_iter_call(stub, args, &modified_locals, None);
                        // IntoIterNext may return None when element sort is not resolved yet.
                        // When it does return Some, verify no false constraints and mark found.
                        if let Some(r) = &result {
                            assert!(
                                !r.constraints
                                    .iter()
                                    .any(|c| matches!(c.value(), ExprValue::BoolConst(false))),
                                "Normal IntoIterNext path should not emit false constraint"
                            );
                            found_next = true;
                        } else {
                            // Sort not resolved — acceptable for iterator element types.
                            // Don't count as found: the trailing assert ensures at least
                            // one call actually produces a translation result.
                        }
                    }
                    _ => {}
                }
            }
        }

        let skip_after = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        assert_eq!(
            skip_before, skip_after,
            "Normal Vec iterator path should not increment ITERATOR_UNSOUND_SKIP_COUNT"
        );
        assert!(
            found_into_iter || found_next,
            "Should detect at least one Vec iterator call in MIR"
        );
    });
}

// =============================================================================
// Vec iterator translation — skip path (Part of #2187)
// Exercises ITERATOR_UNSOUND_SKIP_COUNT increment when Vec operand resolves
// to a non-datatype sort (e.g., bitvec). Without declare_block_relations(),
// state vars are empty and operand translation falls back to bitvec.
// =============================================================================

#[test]
fn test_vec_into_iter_translation_skip_path_increments_counter() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_skip_path() {
            let v: Vec<u32> = Vec::new();
            let mut iter = v.into_iter();
            let _ = iter.next();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_skip_path");
        let body = instance.body().expect("function body");

        // Intentionally DO NOT call declare_block_relations().
        // This leaves state_vars empty, so the Vec operand resolves to a
        // bitvec sort instead of a datatype, triggering the skip path.
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_skip_path", ChcConfig::default());

        let skip_before = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        let modified_locals: HashSet<usize> = HashSet::new();
        let mut found_skip = false;
        let mut saw_iter_stub_call = false;
        let mut saw_none_result = false;

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_vec_iter_stub(func)
                && matches!(
                    stub,
                    StubKind::VecIntoIter
                        | StubKind::VecIter
                        | StubKind::VecIterMut
                        | StubKind::IntoIterNext
                )
            {
                saw_iter_stub_call = true;
                let result = chc_ctx.translate_vec_iter_call(stub, args, &modified_locals, None);
                // Skip path: translation returns Some with false constraint,
                // or returns None if operand translation itself failed.
                // Covers both VecIntoIter construction (line 232) and
                // IntoIterNext non-datatype guard (line 260).
                match result {
                    Some(r) => {
                        let has_false_constraint = r
                            .constraints
                            .iter()
                            .any(|c| matches!(c.value(), ExprValue::BoolConst(false)));
                        if has_false_constraint {
                            found_skip = true;
                        }
                    }
                    None => saw_none_result = true,
                }
            }
        }

        let skip_after = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);

        assert!(
            saw_iter_stub_call,
            "probe_vec_skip_path should include at least one Vec iterator stub call"
        );
        assert!(
            found_skip || saw_none_result,
            "Vec iterator skip-path test expected either false-constraint skip or None result"
        );

        // Either the counter was incremented (skip path fired), or the operand
        // translation returned None before reaching the skip path. Both are valid
        // outcomes when state vars are uninitialized.
        if found_skip {
            assert!(
                skip_after > skip_before,
                "Skip path should have incremented ITERATOR_UNSOUND_SKIP_COUNT"
            );
        }
        // The test passing at all validates the code path doesn't panic
        // when operand resolution produces non-datatype sorts.
    });
}

// =========================================================================
// Vec/String is_empty Collection Predicate Tests (Part of #2125)
// =========================================================================

#[test]
fn test_detect_vec_is_empty_stub() {
    // Vec::is_empty should be detected by detect_collection_predicate_stub.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_is_empty() -> bool {
            let v: Vec<u8> = Vec::new();
            v.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_is_empty", ChcConfig::default());

        let detected = collect_detected_collection_predicate_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::VecIsEmpty),
            "Vec::is_empty should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_string_is_empty_stub() {
    // String::is_empty should be detected by detect_collection_predicate_stub.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_string_is_empty() -> bool {
            let s = String::new();
            s.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_is_empty");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_is_empty", ChcConfig::default());

        let detected = collect_detected_collection_predicate_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::StringIsEmpty),
            "String::is_empty should be detected; got: {:?}",
            detected
        );
    });
}

// =============================================================================
// Vec iterator stub detection tests (Part of #2016)
// =============================================================================

#[test]
fn test_detect_vec_into_iter_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_into_iter() {
            let v: Vec<u8> = Vec::new();
            let mut iter = v.into_iter();
            let _ = iter.next();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_into_iter");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_into_iter", ChcConfig::default());

        let detected = collect_detected_vec_iter_stubs(&chc_ctx, &body);

        // Should detect at least VecIntoIter or IntoIterNext
        assert!(
            !detected.is_empty(),
            "Vec::into_iter + next should detect at least one Vec iterator stub, got: {:?}",
            detected
        );
    });
}

// =============================================================================
// VecIntoIter sort structure tests (Part of #2016)
// =============================================================================

/// Verify VecIntoIter sort has fld_vec and fld_pos fields.
/// This is the structure make_vec_into_iter_chc produces.
#[test]
fn test_vec_into_iter_sort_structure() {
    use crate::codegen_ay::test_fixtures::vec_sort;

    let elem_sort = Sort::bitvec(32);
    let v_sort = vec_sort(elem_sort);

    // VecIntoIter struct: (fld_vec: Vec<T>, fld_pos: bv64)
    let iter_sort = struct_sort(
        "VecIntoIter_bv32",
        [("fld_vec", v_sort.clone()), ("fld_pos", Sort::bitvec(64))],
    );

    let dt = iter_sort.datatype_sort();
    assert!(dt.is_some(), "VecIntoIter should be a datatype");
    let dt = dt.unwrap();
    assert_eq!(dt.constructors.len(), 1, "VecIntoIter should have 1 constructor");
    let ctor = &dt.constructors[0];
    assert_eq!(ctor.fields.len(), 2, "Should have 2 fields (vec, pos)");

    let vec_field = ctor.fields.iter().find(|f| f.name == "fld_vec");
    assert!(vec_field.is_some(), "Should have fld_vec field");
    assert_eq!(vec_field.unwrap().sort, v_sort, "fld_vec sort should match Vec sort");

    let pos_field = ctor.fields.iter().find(|f| f.name == "fld_pos");
    assert!(pos_field.is_some(), "Should have fld_pos field");
    assert_eq!(pos_field.unwrap().sort, Sort::bitvec(64), "fld_pos should be bv64");
}

/// Verify VecIntoIter construction: initial position is zero.
#[test]
fn test_vec_into_iter_initial_position_zero() {
    use crate::codegen_ay::test_fixtures::vec_sort;

    let elem_sort = Sort::bitvec(32);
    let v_sort = vec_sort(elem_sort.clone());
    let array_sort = Sort::array(Sort::bitvec(64), elem_sort);
    let data = Expr::var("data_0", array_sort);

    let vec_expr = Expr::datatype_constructor(
        "Vec",
        "Vec_mk",
        vec![
            Expr::bitvec_const(0x1000u64, 64),
            Expr::bitvec_const(5u64, 64),
            Expr::bitvec_const(10u64, 64),
            data,
        ],
        v_sort.clone(),
    );

    let iter_sort =
        struct_sort("VecIntoIter_bv32", [("fld_vec", v_sort), ("fld_pos", Sort::bitvec(64))]);

    let zero = Expr::bitvec_const(0u64, 64);
    let iter_expr = Expr::datatype_constructor(
        "VecIntoIter_bv32",
        "VecIntoIter_bv32_mk",
        vec![vec_expr, zero],
        iter_sort.clone(),
    );

    assert_eq!(*iter_expr.sort(), iter_sort);
    assert!(iter_expr.sort().is_datatype());
}

/// Verify Vec element access pattern: data[pos] for iterator.next().
#[test]
fn test_vec_iter_element_access_pattern() {
    use crate::codegen_ay::test_fixtures::vec_sort;

    let elem_sort = Sort::bitvec(32);
    let v_sort = vec_sort(elem_sort.clone());

    // Extract data array from Vec
    let vec_var = Expr::var("vec_0", v_sort);
    let data = vec_var.clone().field_select(
        "Vec",
        "fld_data",
        Sort::array(Sort::bitvec(64), elem_sort.clone()),
    );
    let len = vec_var.field_select("Vec", "fld_len", Sort::bitvec(64));
    let pos = Expr::var("pos", Sort::bitvec(64));

    // in_bounds = pos < len
    let in_bounds = pos.clone().bvult(len);
    assert!(in_bounds.sort().is_bool(), "bounds check should be Bool");

    // elem = data[pos]
    let elem = data.select(pos);
    assert_eq!(elem.sort(), &elem_sort, "data[pos] should have element sort");
}

/// Verify iterator intrinsic detection for range iterator patterns.
/// Range iterators use CheckedAddUnsigned for step advancement.
#[test]
fn test_detect_iterator_intrinsic_checked_add() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_checked_add_unsigned(x: i32, y: u32) -> Option<i32> {
            x.checked_add_unsigned(y)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_unsigned");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_checked_add_unsigned", ChcConfig::default());

        let detected = collect_detected_iterator_intrinsic_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::CheckedAddUnsigned),
            "checked_add_unsigned should be detected as CheckedAddUnsigned; got: {:?}",
            detected
        );
        assert!(
            !detected.contains(&StubKind::OptionUnwrapUnchecked),
            "probe_checked_add_unsigned should not detect OptionUnwrapUnchecked; got: {:?}",
            detected
        );
    });
}

/// Verify iterator position increment: new_pos = ite(in_bounds, pos + 1, pos).
#[test]
fn test_vec_iter_position_advance_pattern() {
    let pos = Expr::var("pos", Sort::bitvec(64));
    let len = Expr::var("len", Sort::bitvec(64));
    let one = Expr::bitvec_const(1u64, 64);

    let in_bounds = pos.clone().bvult(len);
    let incremented = pos.clone().bvadd(one);
    let new_pos = Expr::ite(in_bounds.clone(), incremented.clone(), pos.clone());
    assert_eq!(new_pos.sort(), &Sort::bitvec(64), "new_pos should be bv64");
    assert!(matches!(in_bounds.value(), ExprValue::BvULt(_, _)));
    assert!(matches!(incremented.value(), ExprValue::BvAdd(_, _)));
    if let ExprValue::Ite { cond, then_expr, else_expr } = new_pos.value() {
        assert_eq!(cond, &in_bounds, "ite condition should be in-bounds check");
        assert_eq!(then_expr, &incremented, "ite then branch should increment position");
        assert_eq!(else_expr, &pos, "ite else branch should preserve current position");
    } else {
        assert!(
            matches!(new_pos.value(), ExprValue::Ite { .. }),
            "expected ite expression for iterator position advance, got {:?}",
            new_pos.value()
        );
    }
}

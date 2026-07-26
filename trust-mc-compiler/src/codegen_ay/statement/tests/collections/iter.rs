// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Iterator collection stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;

/// Return the number of emitted constraints so far.
fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

/// Return the latest emitted constraint expression.
fn latest_constraint(codegen: &StatementCodegen<'_, '_, '_>) -> Expr {
    codegen.ctx.bmc_vc.constraints.last().expect("expected at least one emitted constraint").clone()
}

// -----------------------------------------------------------------------------
// BMC unsound skip counter (collections/iter.rs)
// Part of #2016: test coverage for unsoundness tracking.
// -----------------------------------------------------------------------------

/// Test get_bmc_iterator_unsound_skip_count public accessor.
/// collections/iter.rs: get_bmc_iterator_unsound_skip_count returns atomic count.
#[test]
fn test_bmc_iterator_unsound_skip_counter() {
    use crate::codegen_ay::statement::collections::get_bmc_iterator_unsound_skip_count;

    // Verify the accessor returns a valid count (non-negative)
    let count = get_bmc_iterator_unsound_skip_count();
    // Counter value depends on test execution order; just verify it's callable
    assert!(count < usize::MAX);
}

// =============================================================================
// Iterator adapter stub tests (Part of #2016)
// =============================================================================
// IterFold, IterSum, MapNext, FilterNext — the 4 untested StubKind arms in
// iter.rs. These stubs return symbolic results since closures are opaque.

/// Test IterFold with empty args returns target (symbolic result path).
/// iter.rs: IterFold branch — returns codegen_symbolic_result.
#[test]
fn test_codegen_iter_stub_fold_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_iter_stub(
            StubKind::IterFold,
            &[],
            &dest,
            Some(1),
            "core::iter::Iterator::fold",
        );
        assert_eq!(result, Some(1));
    });
}

/// Test IterSum with empty args returns target (symbolic result path).
/// iter.rs: IterSum branch — returns codegen_symbolic_result.
#[test]
fn test_codegen_iter_stub_sum_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_iter_stub(
            StubKind::IterSum,
            &[],
            &dest,
            Some(2),
            "core::iter::Iterator::sum",
        );
        assert_eq!(result, Some(2));
    });
}

/// Test IterFold preserves init value on exhausted iterator.
/// iter.rs: IterFold branch — ITE(non_empty, symbolic, init).
#[test]
fn test_codegen_iter_stub_fold_exhausted_iter_uses_init_branch() {
    use crate::codegen_ay::stubs::StubKind;
    use ay_bindings::ExprValue;
    use rustc_public::mir::{Rvalue, StatementKind};

    with_test_ay_ctx_for_source(
        r#"
        pub fn fold_init_probe(x: u32) -> u32 {
            let init = 99u32;
            x.wrapping_add(init)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "fold_init_probe");
            let body = instance.body().expect("function body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let elem_sort = Sort::bitvec(32);
            let vec_sort = vec_sort(elem_sort.clone());
            let vec_iter_sort = struct_sort(
                "VecIntoIter_FoldProbe",
                [("fld_vec", vec_sort.clone()), ("fld_pos", Sort::bitvec(POINTER_WIDTH))],
            );

            let ptr = Expr::var("fold_ptr", Sort::bitvec(POINTER_WIDTH));
            let len = Expr::bitvec_const(3u64, POINTER_WIDTH);
            let cap = Expr::bitvec_const(3u64, POINTER_WIDTH);
            let default = Expr::var("fold_default", elem_sort);
            let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), default);
            let vec = vec_expr(ptr, len, cap, data, vec_sort);
            let exhausted_pos = Expr::bitvec_const(3u64, POINTER_WIDTH);
            let iter = Expr::datatype_constructor(
                "VecIntoIter_FoldProbe",
                "VecIntoIter_FoldProbe_mk",
                vec![vec, exhausted_pos],
                vec_iter_sort,
            );

            let iter_op = seed_collections_local(&mut codegen, 1, iter);

            // Pull an actual MIR constant operand for the fold init argument.
            let (init_op, init_expr) = body
                .blocks
                .iter()
                .flat_map(|bb| bb.statements.iter())
                .find_map(|stmt| {
                    if let StatementKind::Assign(_, Rvalue::Use(op @ Operand::Constant(_))) =
                        &stmt.kind
                    {
                        let expr = codegen.codegen_operand(op)?;
                        return (expr.sort().bitvec_width() == Some(32))
                            .then_some((op.clone(), expr));
                    }
                    None
                })
                .expect("fold_init_probe should include a u32 constant operand");

            let dest = Place { local: 0, projection: vec![] };
            let before = constraint_count(&codegen);
            let result = codegen.codegen_iter_stub(
                StubKind::IterFold,
                &[iter_op, init_op],
                &dest,
                Some(9),
                "core::iter::Iterator::fold",
            );

            assert_eq!(result, Some(9));
            assert!(
                constraint_count(&codegen) > before,
                "IterFold should emit an assignment constraint"
            );

            let emitted = latest_constraint(&codegen);
            let rhs = match emitted.value() {
                ExprValue::Eq(_, rhs) => rhs,
                other => panic!("expected Eq assignment constraint, got {other:?}"),
            };

            match rhs.value() {
                ExprValue::Ite { else_expr, .. } => {
                    assert_eq!(
                        else_expr.value(),
                        init_expr.value(),
                        "IterFold exhausted branch should use init value"
                    );
                }
                ExprValue::BitVecConst { .. } => {
                    assert_eq!(
                        rhs.value(),
                        init_expr.value(),
                        "expected fold init result for exhausted iterator"
                    );
                }
                other => panic!("expected ITE/init constant for IterFold, got {other:?}"),
            }
        },
    );
}

/// Test IterSum preserves numeric zero on exhausted iterator.
/// iter.rs: IterSum branch — ITE(non_empty, symbolic, zero).
#[test]
fn test_codegen_iter_stub_sum_exhausted_iter_uses_zero_branch() {
    use crate::codegen_ay::stubs::StubKind;
    use ay_bindings::ExprValue;
    use num_bigint::BigInt;

    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let elem_sort = Sort::bitvec(32);
        let vec_sort = vec_sort(elem_sort.clone());
        let vec_iter_sort = struct_sort(
            "VecIntoIter_SumProbe",
            [("fld_vec", vec_sort.clone()), ("fld_pos", Sort::bitvec(POINTER_WIDTH))],
        );

        let ptr = Expr::var("sum_ptr", Sort::bitvec(POINTER_WIDTH));
        let len = Expr::bitvec_const(2u64, POINTER_WIDTH);
        let cap = Expr::bitvec_const(2u64, POINTER_WIDTH);
        let default = Expr::var("sum_default", elem_sort);
        let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), default);
        let vec = vec_expr(ptr, len, cap, data, vec_sort);
        let exhausted_pos = Expr::bitvec_const(2u64, POINTER_WIDTH);
        let iter = Expr::datatype_constructor(
            "VecIntoIter_SumProbe",
            "VecIntoIter_SumProbe_mk",
            vec![vec, exhausted_pos],
            vec_iter_sort,
        );

        let iter_op = seed_collections_local(&mut codegen, 1, iter);

        let dest = Place { local: 0, projection: vec![] };
        let before = constraint_count(&codegen);
        let result = codegen.codegen_iter_stub(
            StubKind::IterSum,
            &[iter_op],
            &dest,
            Some(10),
            "core::iter::Iterator::sum",
        );

        assert_eq!(result, Some(10));
        assert!(
            constraint_count(&codegen) > before,
            "IterSum should emit an assignment constraint"
        );

        let emitted = latest_constraint(&codegen);
        let rhs = match emitted.value() {
            ExprValue::Eq(_, rhs) => rhs,
            other => panic!("expected Eq assignment constraint, got {other:?}"),
        };

        match rhs.value() {
            ExprValue::Ite { else_expr, .. } => {
                assert!(
                    matches!(
                        else_expr.value(),
                        ExprValue::BitVecConst { value, width }
                            if *value == BigInt::from(0u32) && *width == 32
                    ),
                    "IterSum exhausted branch should use zero, got {:?}",
                    else_expr.value()
                );
            }
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(value, &BigInt::from(0u32), "expected sum empty identity result");
                assert_eq!(*width, 32, "expected sum identity width");
            }
            other => panic!("expected ITE/zero constant for IterSum, got {other:?}"),
        }
    });
}

/// Test MapNext with empty args returns target (early-return warn path).
/// iter.rs: MapNext branch — requires args, returns target on empty.
#[test]
fn test_codegen_iter_stub_map_next_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_iter_stub(
            StubKind::MapNext,
            &[],
            &dest,
            Some(3),
            "core::iter::adapters::map::Map::next",
        );
        // MapNext with empty args hits warn path, returns target directly
        assert_eq!(result, Some(3));
    });
}

/// Test FilterNext with empty args returns target (early-return warn path).
/// iter.rs: FilterNext branch — requires args, returns target on empty.
#[test]
fn test_codegen_iter_stub_filter_next_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_iter_stub(
            StubKind::FilterNext,
            &[],
            &dest,
            Some(4),
            "core::iter::adapters::filter::Filter::next",
        );
        // FilterNext with empty args hits warn path, returns target directly
        assert_eq!(result, Some(4));
    });
}

/// Test MapNext with seeded Map iterator advances inner state.
/// iter.rs: MapNext branch — full path with wrapped iterator.
#[test]
fn test_codegen_iter_stub_map_next_with_seeded_iter() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a Map iterator in the env at local_1
        // Map has fld_iter (inner iterator) — use a simple Vec into_iter sort
        let elem_sort = Sort::bitvec(32);
        let vec_sort = struct_sort(
            "VecIntoIter",
            [
                ("fld_vec", Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort)),
                ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ],
        );
        let inner_iter = Expr::var("inner_iter_0", vec_sort.clone());
        let map_sort = struct_sort("MapIter", [("fld_iter", vec_sort)]);
        let map_iter =
            Expr::datatype_constructor("MapIter", "MapIter_mk", vec![inner_iter], map_sort);

        let _op = seed_collections_local(&mut codegen, 1, map_iter);

        let op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let before = constraint_count(&codegen);
        let result = codegen.codegen_iter_stub(
            StubKind::MapNext,
            &[op],
            &dest,
            Some(5),
            "core::iter::adapters::map::Map::next",
        );

        assert_eq!(result, Some(5));
        assert!(
            constraint_count(&codegen) > before,
            "MapNext should emit an assignment constraint"
        );

        // New behavior (Part of #1751): result preserves Option shape and
        // propagates inner iterator exhaustion via an `is Some` tester.
        let emitted = latest_constraint(&codegen);
        let rhs = match emitted.value() {
            ay_bindings::ExprValue::Eq(_, rhs) => rhs,
            other => panic!("expected Eq assignment constraint, got {other:?}"),
        };
        match rhs.value() {
            ay_bindings::ExprValue::Ite { cond, .. } => {
                assert!(
                    matches!(
                        cond.value(),
                        ay_bindings::ExprValue::DatatypeTester { constructor_name, .. }
                            if constructor_name.starts_with("Some")
                    ),
                    "MapNext should gate result on inner Option::Some, got {:?}",
                    cond.value()
                );
            }
            other => panic!("expected ITE in MapNext assignment, got {other:?}"),
        }
    });
}

/// Test FilterNext with seeded Filter iterator advances inner state.
/// iter.rs: FilterNext branch — full path with wrapped iterator.
#[test]
fn test_codegen_iter_stub_filter_next_with_seeded_iter() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a Filter iterator in the env at local_1
        let elem_sort = Sort::bitvec(32);
        let vec_sort = struct_sort(
            "VecIntoIter",
            [
                ("fld_vec", Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort)),
                ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ],
        );
        let inner_iter = Expr::var("inner_iter_0", vec_sort.clone());
        let filter_sort = struct_sort("FilterIter", [("fld_iter", vec_sort)]);
        let filter_iter = Expr::datatype_constructor(
            "FilterIter",
            "FilterIter_mk",
            vec![inner_iter],
            filter_sort,
        );

        let _op = seed_collections_local(&mut codegen, 1, filter_iter);

        let op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let before = constraint_count(&codegen);
        let result = codegen.codegen_iter_stub(
            StubKind::FilterNext,
            &[op],
            &dest,
            Some(6),
            "core::iter::adapters::filter::Filter::next",
        );

        assert_eq!(result, Some(6));
        assert!(
            constraint_count(&codegen) > before,
            "FilterNext should emit an assignment constraint"
        );

        // New behavior (Part of #1751): top-level result is gated by inner
        // iterator exhaustion (`is Some` on inner Option result).
        let emitted = latest_constraint(&codegen);
        let rhs = match emitted.value() {
            ay_bindings::ExprValue::Eq(_, rhs) => rhs,
            other => panic!("expected Eq assignment constraint, got {other:?}"),
        };
        match rhs.value() {
            ay_bindings::ExprValue::Ite { cond, .. } => {
                assert!(
                    matches!(
                        cond.value(),
                        ay_bindings::ExprValue::DatatypeTester { constructor_name, .. }
                            if constructor_name.starts_with("Some")
                    ),
                    "FilterNext should gate result on inner Option::Some, got {:?}",
                    cond.value()
                );
            }
            other => panic!("expected ITE in FilterNext assignment, got {other:?}"),
        }
    });
}

/// Test IterMap with operand creates Map iterator wrapper.
/// iter.rs: IterMap branch — wraps inner iterator in MapIter.
#[test]
fn test_codegen_iter_stub_map_creates_wrapper() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a simple iterator value at local_1
        let iter_val = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let op = seed_collections_local(&mut codegen, 1, iter_val);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_iter_stub(
            StubKind::IterMap,
            &[op],
            &dest,
            Some(7),
            "core::iter::Iterator::map",
        );
        assert_eq!(result, Some(7));
    });
}

/// Test IterMap with empty args returns target (early-return warn path).
#[test]
fn test_codegen_iter_stub_map_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_iter_stub(
            StubKind::IterMap,
            &[],
            &dest,
            Some(8),
            "core::iter::Iterator::map",
        );
        // IterMap with empty args hits warn path, returns target
        assert_eq!(result, Some(8));
    });
}

/// Test IterFilter with empty args returns target (early-return warn path).
#[test]
fn test_codegen_iter_stub_filter_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_iter_stub(
            StubKind::IterFilter,
            &[],
            &dest,
            Some(9),
            "core::iter::Iterator::filter",
        );
        // IterFilter with empty args hits warn path, returns target
        assert_eq!(result, Some(9));
    });
}

// =============================================================================
// BMC UNSOUND_SKIP_COUNT skip-path tests (Part of #2187)
// Exercise the 6 BMC_ITERATOR_UNSOUND_SKIP_COUNT increment sites when
// iterator expressions have non-datatype sort (bitvec instead of struct).
//
// Fix #2500: These tests serialize via SKIP_COUNTER_MUTEX because they
// read/assert on a global atomic counter that can be drained or incremented
// by concurrent tests (including reset_statement_session_counters).
// =============================================================================

// SKIP_COUNTER_MUTEX is defined in the parent tests/mod.rs so that both
// this module and operand.rs (which drains the counter via
// reset_statement_session_counters) share the same lock.
use super::super::SKIP_COUNTER_MUTEX;

/// Test IntoIterNext skip path (iter.rs:69): non-datatype sort triggers
/// BMC_ITERATOR_UNSOUND_SKIP_COUNT increment and record_violation_guarded.
#[test]
fn test_bmc_into_iter_next_skip_path_non_datatype() {
    use crate::codegen_ay::statement::collections::get_bmc_iterator_unsound_skip_count;
    use crate::codegen_ay::stubs::StubKind;

    let _guard = SKIP_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a bitvec (non-datatype) expression as the iterator — triggers skip
        let non_dt_iter = Expr::var("fake_iter", Sort::bitvec(64));
        let op = seed_collections_local(&mut codegen, 1, non_dt_iter);

        let dest = Place { local: 0, projection: vec![] };
        let skip_before = get_bmc_iterator_unsound_skip_count();

        let result = codegen.codegen_iter_stub(
            StubKind::IntoIterNext,
            &[op],
            &dest,
            Some(1),
            "alloc::vec::IntoIter::next",
        );

        let skip_after = get_bmc_iterator_unsound_skip_count();

        // Skip path should fire: non-datatype sort → counter increment
        assert!(
            skip_after > skip_before,
            "IntoIterNext skip path should increment BMC_ITERATOR_UNSOUND_SKIP_COUNT; \
             before={}, after={}",
            skip_before,
            skip_after
        );
        // codegen_iter_stub returns target on skip path
        assert_eq!(result, Some(1));
    });
}

/// Test HashMapIterNext skip path (iter.rs:247): non-datatype sort triggers
/// BMC_ITERATOR_UNSOUND_SKIP_COUNT increment.
#[test]
fn test_bmc_hashmap_iter_next_skip_path_non_datatype() {
    use crate::codegen_ay::statement::collections::get_bmc_iterator_unsound_skip_count;
    use crate::codegen_ay::stubs::StubKind;

    let _guard = SKIP_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a bitvec (non-datatype) expression as the iterator
        let non_dt_iter = Expr::var("fake_hashmap_iter", Sort::bitvec(64));
        let op = seed_collections_local(&mut codegen, 1, non_dt_iter);

        let dest = Place { local: 0, projection: vec![] };
        let skip_before = get_bmc_iterator_unsound_skip_count();

        let result = codegen.codegen_iter_stub(
            StubKind::HashMapIterNext,
            &[op],
            &dest,
            Some(2),
            "std::collections::hash_map::IntoIter::next",
        );

        let skip_after = get_bmc_iterator_unsound_skip_count();

        assert!(
            skip_after > skip_before,
            "HashMapIterNext skip path should increment BMC_ITERATOR_UNSOUND_SKIP_COUNT; \
             before={}, after={}",
            skip_before,
            skip_after
        );
        assert_eq!(result, Some(2));
    });
}

/// Test BTreeSetIterNext skip path (iter.rs:362): non-datatype sort triggers
/// BMC_ITERATOR_UNSOUND_SKIP_COUNT increment.
#[test]
fn test_bmc_set_iter_next_skip_path_non_datatype() {
    use crate::codegen_ay::statement::collections::get_bmc_iterator_unsound_skip_count;
    use crate::codegen_ay::stubs::StubKind;

    let _guard = SKIP_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a bitvec (non-datatype) expression as the iterator
        let non_dt_iter = Expr::var("fake_set_iter", Sort::bitvec(64));
        let op = seed_collections_local(&mut codegen, 1, non_dt_iter);

        let dest = Place { local: 0, projection: vec![] };
        let skip_before = get_bmc_iterator_unsound_skip_count();

        let result = codegen.codegen_iter_stub(
            StubKind::BTreeSetIterNext,
            &[op],
            &dest,
            Some(3),
            "alloc::collections::btree::set::IntoIter::next",
        );

        let skip_after = get_bmc_iterator_unsound_skip_count();

        assert!(
            skip_after > skip_before,
            "BTreeSetIterNext skip path should increment BMC_ITERATOR_UNSOUND_SKIP_COUNT; \
             before={}, after={}",
            skip_before,
            skip_after
        );
        assert_eq!(result, Some(3));
    });
}

/// Test vec_iter_next_from_expr skip path (iter_helpers.rs:266): non-datatype
/// sort triggers BMC_ITERATOR_UNSOUND_SKIP_COUNT and returns None.
#[test]
fn test_bmc_vec_iter_next_from_expr_skip_path() {
    use crate::codegen_ay::statement::collections::get_bmc_iterator_unsound_skip_count;

    let _guard = SKIP_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_dt_iter = Expr::var("fake_vec_iter", Sort::bitvec(64));
        let skip_before = get_bmc_iterator_unsound_skip_count();

        let result = codegen.vec_iter_next_from_expr(&non_dt_iter, None);

        let skip_after = get_bmc_iterator_unsound_skip_count();

        assert!(
            skip_after > skip_before,
            "vec_iter_next_from_expr skip path should increment BMC_ITERATOR_UNSOUND_SKIP_COUNT; \
             before={}, after={}",
            skip_before,
            skip_after
        );
        assert!(result.is_none(), "Skip path should return None");
    });
}

/// Test codegen_iter_collect_vec skip path (iter_helpers.rs:331): non-datatype
/// sort triggers BMC_ITERATOR_UNSOUND_SKIP_COUNT and returns None.
#[test]
fn test_bmc_codegen_iter_collect_vec_skip_path() {
    use crate::codegen_ay::statement::collections::get_bmc_iterator_unsound_skip_count;

    let _guard = SKIP_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_dt_iter = Expr::var("fake_collect_iter", Sort::bitvec(64));
        let skip_before = get_bmc_iterator_unsound_skip_count();

        let result = codegen.codegen_iter_collect_vec(&non_dt_iter);

        let skip_after = get_bmc_iterator_unsound_skip_count();

        assert!(
            skip_after > skip_before,
            "codegen_iter_collect_vec skip path should increment BMC_ITERATOR_UNSOUND_SKIP_COUNT; \
             before={}, after={}",
            skip_before,
            skip_after
        );
        assert!(result.is_none(), "Skip path should return None");
    });
}

/// Test codegen_iter_flatten_from_vec_iter skip path (iter_helpers.rs:365):
/// non-datatype sort triggers BMC_ITERATOR_UNSOUND_SKIP_COUNT and returns None.
#[test]
fn test_bmc_codegen_iter_flatten_skip_path() {
    use crate::codegen_ay::statement::collections::get_bmc_iterator_unsound_skip_count;

    let _guard = SKIP_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_dt_iter = Expr::var("fake_flatten_iter", Sort::bitvec(64));
        let skip_before = get_bmc_iterator_unsound_skip_count();

        let result = codegen.codegen_iter_flatten_from_vec_iter(&non_dt_iter);

        let skip_after = get_bmc_iterator_unsound_skip_count();

        assert!(
            skip_after > skip_before,
            "codegen_iter_flatten_from_vec_iter skip path should increment \
             BMC_ITERATOR_UNSOUND_SKIP_COUNT; before={}, after={}",
            skip_before,
            skip_after
        );
        assert!(result.is_none(), "Flatten skip path should return None");
    });
}

// =============================================================================
// iter_helpers.rs: Direct unit tests for iterator helper methods
// (Part of #2016, #2192)
//
// These tests exercise the helper functions in collections/iter_helpers.rs
// through a MIR-driven context, verifying datatype construction, field
// extraction, and sort inference.
// =============================================================================

/// Test make_map_iterator creates Map wrapper with fld_iter field.
/// iter_helpers.rs:41 — make_map_iterator.
#[test]
fn test_make_map_iterator_sort_and_field() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let inner_sort = struct_sort(
            "VecIntoIter",
            [("fld_vec", Sort::bitvec(POINTER_WIDTH)), ("fld_pos", Sort::bitvec(POINTER_WIDTH))],
        );
        let inner_iter = Expr::var("inner", inner_sort);
        let map_iter = codegen.make_map_iterator(inner_iter);

        // Verify sort structure
        assert!(map_iter.sort().is_datatype());
        let dt = map_iter.sort().datatype_sort().unwrap();
        assert!(dt.name.starts_with("Map_"));
        assert_eq!(dt.constructors.len(), 1);
        assert_eq!(dt.constructors[0].fields.len(), 1);
        assert_eq!(dt.constructors[0].fields[0].name, "fld_iter");
        assert!(dt.constructors[0].fields[0].sort.is_datatype());
    });
}

/// Test make_filter_iterator creates Filter wrapper with fld_iter field.
/// iter_helpers.rs:55 — make_filter_iterator.
#[test]
fn test_make_filter_iterator_sort_and_field() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let inner_sort = struct_sort("VecIntoIter", [("fld_pos", Sort::bitvec(POINTER_WIDTH))]);
        let inner_iter = Expr::var("inner", inner_sort);
        let filter_iter = codegen.make_filter_iterator(inner_iter);

        assert!(filter_iter.sort().is_datatype());
        let dt = filter_iter.sort().datatype_sort().unwrap();
        assert!(dt.name.starts_with("Filter_"));
        assert_eq!(dt.constructors[0].fields[0].name, "fld_iter");
    });
}

/// Test update_wrapped_iterator reconstructs wrapper with new inner.
/// iter_helpers.rs:103 — update_wrapped_iterator.
#[test]
fn test_update_wrapped_iterator_preserves_sort() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let inner_sort = struct_sort("InnerIter", [("fld_pos", Sort::bitvec(POINTER_WIDTH))]);
        let wrapper_sort = struct_sort("Map_InnerIter", [("fld_iter", inner_sort.clone())]);
        let ctor_name = wrapper_sort
            .datatype_default_constructor()
            .map_or_else(|| "Map_InnerIter_mk".to_string(), str::to_string);

        let old_inner = Expr::var("old_inner", inner_sort.clone());
        let wrapper =
            Expr::datatype_constructor("Map_InnerIter", &ctor_name, vec![old_inner], wrapper_sort);

        let new_inner = Expr::var("new_inner", inner_sort);
        let updated = codegen.update_wrapped_iterator(&wrapper, new_inner);

        assert_eq!(updated.sort().datatype_name(), wrapper.sort().datatype_name());
    });
}

/// Test make_tuple creates Tuple2 with fld_0 and fld_1 fields.
/// iter_helpers.rs:197 — make_tuple.
#[test]
fn test_make_tuple_creates_two_field_struct() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let first = Expr::bitvec_const(42u64, 64);
        let second = Expr::bitvec_const(7u32, 32);
        let tuple = codegen.make_tuple(first, second);

        assert!(tuple.sort().is_datatype());
        let dt = tuple.sort().datatype_sort().unwrap();
        assert!(dt.name.starts_with("Tuple2_"));
        assert_eq!(dt.constructors[0].fields.len(), 2);
        assert_eq!(dt.constructors[0].fields[0].name, "fld_0");
        assert_eq!(dt.constructors[0].fields[0].sort.bitvec_width(), Some(64));
        assert_eq!(dt.constructors[0].fields[1].name, "fld_1");
        assert_eq!(dt.constructors[0].fields[1].sort.bitvec_width(), Some(32));
    });
}

/// Test infer_iter_vec_sort extracts fld_vec sort from VecIntoIter.
/// iter_helpers.rs:223 — infer_iter_vec_sort.
#[test]
fn test_infer_iter_vec_sort_from_datatype() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_inner_sort = struct_sort(
            "Vec_bv32",
            [("fld_ptr", Sort::bitvec(POINTER_WIDTH)), ("fld_len", Sort::bitvec(POINTER_WIDTH))],
        );
        let iter_sort = struct_sort(
            "VecIntoIter",
            [("fld_vec", vec_inner_sort.clone()), ("fld_pos", Sort::bitvec(POINTER_WIDTH))],
        );
        let ctor = iter_sort
            .datatype_default_constructor()
            .map_or_else(|| "VecIntoIter_mk".to_string(), str::to_string);
        let iter = Expr::datatype_constructor(
            "VecIntoIter",
            &ctor,
            vec![Expr::var("vec", vec_inner_sort), Expr::bitvec_const(0u64, POINTER_WIDTH)],
            iter_sort,
        );

        let inferred = codegen.infer_iter_vec_sort(&iter);
        assert!(inferred.is_datatype());
        assert_eq!(inferred.datatype_name(), Some("Vec_bv32"));
    });
}

/// Test infer_iter_vec_sort fallback for non-datatype sort.
/// iter_helpers.rs:234 — fallback returns Vec_bv32 sort.
#[test]
fn test_infer_iter_vec_sort_fallback_for_non_datatype() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_dt = Expr::var("not_iter", Sort::bitvec(64));
        let inferred = codegen.infer_iter_vec_sort(&non_dt);
        assert!(inferred.is_datatype());
        let dt = inferred.datatype_sort().unwrap();
        assert!(dt.name.starts_with("Vec_"));
        assert_eq!(dt.constructors[0].fields.len(), 4);
    });
}

/// Test datatype_field_info extracts correct info.
/// iter_helpers.rs:249 — datatype_field_info.
#[test]
fn test_datatype_field_info_returns_correct_tuple() {
    let dt_sort =
        struct_sort("MyStruct", [("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(64))]);
    let ctor = dt_sort
        .datatype_default_constructor()
        .map_or_else(|| "MyStruct_mk".to_string(), str::to_string);
    let expr = Expr::datatype_constructor(
        "MyStruct",
        &ctor,
        vec![Expr::bitvec_const(1u32, 32), Expr::bitvec_const(2u64, 64)],
        dt_sort,
    );

    let sort_ref = expr.sort().clone();
    let info = StatementCodegen::datatype_field_info(&sort_ref, "fld_x");
    assert!(info.is_some());
    let (dt_name, ctor_name, field_sort) = info.unwrap();
    assert_eq!(dt_name, "MyStruct");
    assert!(!ctor_name.is_empty());
    assert_eq!(field_sort.bitvec_width(), Some(32));
}

/// Test datatype_field_info returns None for missing field.
#[test]
fn test_datatype_field_info_returns_none_for_missing() {
    let dt_sort = struct_sort("MyStruct", [("fld_x", Sort::bitvec(32))]);
    let ctor = dt_sort
        .datatype_default_constructor()
        .map_or_else(|| "MyStruct_mk".to_string(), str::to_string);
    let expr =
        Expr::datatype_constructor("MyStruct", &ctor, vec![Expr::bitvec_const(1u32, 32)], dt_sort);
    let sort_ref = expr.sort().clone();
    assert!(StatementCodegen::datatype_field_info(&sort_ref, "fld_missing").is_none());
}

/// Test datatype_field_info returns None for non-datatype.
#[test]
fn test_datatype_field_info_returns_none_for_non_datatype() {
    let bv = Expr::var("x", Sort::bitvec(64));
    let sort_ref = bv.sort().clone();
    assert!(StatementCodegen::datatype_field_info(&sort_ref, "fld_x").is_none());
}

/// Test make_vec_into_iter creates VecIntoIter with fld_vec and fld_pos.
/// iter_helpers.rs:461 — make_vec_into_iter.
#[test]
fn test_make_vec_into_iter_creates_iter_sort() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let vec_sort = struct_sort(
            "Vec_bv32",
            [("fld_ptr", Sort::bitvec(POINTER_WIDTH)), ("fld_len", Sort::bitvec(POINTER_WIDTH))],
        );
        let ctor = vec_sort
            .datatype_default_constructor()
            .map_or_else(|| "Vec_bv32_mk".to_string(), str::to_string);
        let vec = Expr::datatype_constructor(
            "Vec_bv32",
            &ctor,
            vec![Expr::bitvec_const(0u64, POINTER_WIDTH), Expr::bitvec_const(3u64, POINTER_WIDTH)],
            vec_sort,
        );

        let iter = codegen.make_vec_into_iter(vec);
        assert!(iter.sort().is_datatype());
        let dt = iter.sort().datatype_sort().unwrap();
        assert!(dt.name.starts_with("VecIntoIter_"));
        assert_eq!(dt.constructors[0].fields.len(), 2);
        assert_eq!(dt.constructors[0].fields[0].name, "fld_vec");
        assert_eq!(dt.constructors[0].fields[1].name, "fld_pos");
        assert_eq!(dt.constructors[0].fields[1].sort.bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test make_flatten_iter creates Flatten wrapper with fld_iter.
/// iter_helpers.rs:478 — make_flatten_iter.
#[test]
fn test_make_flatten_iter_creates_wrapper() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let inner_sort = struct_sort("VecIntoIter", [("fld_pos", Sort::bitvec(POINTER_WIDTH))]);
        let inner = Expr::var("inner", inner_sort);
        let flatten = codegen.make_flatten_iter(inner);

        assert!(flatten.sort().is_datatype());
        let dt = flatten.sort().datatype_sort().unwrap();
        assert!(dt.name.starts_with("Flatten_"));
        assert_eq!(dt.constructors[0].fields[0].name, "fld_iter");
    });
}

#[test]
fn test_make_option_is_some_returns_bool() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_name = "Option_bv32";
        let none_name = crate::codegen_ay::names::option_none_constructor_name(option_name);
        let some_name = crate::codegen_ay::names::option_some_constructor_name(option_name);
        let option_sort = enum_sort(
            option_name,
            [(none_name, vec![]), (some_name.clone(), vec![("value", Sort::bitvec(32))])],
        );
        let some_val = Expr::datatype_constructor(
            option_name,
            &some_name,
            vec![Expr::bitvec_const(42u32, 32)],
            option_sort,
        );

        let result = codegen.make_option_is_some(&some_val);
        assert!(result.sort().is_bool());
        let smt = format!("{:?}", result);
        assert!(
            smt.contains("is") || smt.contains(&some_name),
            "should produce an is-constructor check, got: {}",
            smt
        );
    });
}

#[test]
fn test_make_option_is_some_fallback_non_option() {
    use ay_bindings::ExprValue;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_option = Expr::var("x", Sort::bitvec(32));
        let result = codegen.make_option_is_some(&non_option);
        assert!(result.sort().is_bool());
        assert!(
            !matches!(result.value(), ExprValue::BoolConst(_)),
            "fallback must stay symbolic, not a constant bool"
        );
        assert!(
            matches!(result.value(), ExprValue::Var { name } if name.contains("option_is_some_fallback")),
            "fallback should produce a dedicated symbolic var, got: {:?}",
            result.value()
        );
    });
}

#[test]
fn test_make_set_contains_returns_bool() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let key_sort = Sort::bitvec(64);
        let set = Expr::var("set", Sort::array(key_sort.clone(), Sort::bool()));
        let key = Expr::var("key", key_sort);
        let result = codegen.make_set_contains(&set, &key);
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_extract_option_value_from_some() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = enum_sort(
            "Option_bv32",
            [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])],
        );
        let some_val = Expr::datatype_constructor(
            "Option_bv32",
            "Some",
            vec![Expr::bitvec_const(42u32, 32)],
            option_sort,
        );

        let extracted = codegen.extract_option_value(&some_val);
        assert_eq!(extracted.sort().bitvec_width(), Some(32));
    });
}

/// Test extract_option_value fallback for non-option sort.
/// iter_helpers.rs:191 — fallback returns symbolic bitvec.
#[test]
fn test_extract_option_value_fallback_non_option() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_option = Expr::var("x", Sort::bitvec(32));
        let extracted = codegen.extract_option_value(&non_option);
        assert_eq!(extracted.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test option_sort_for_value uses expected sort when datatype.
/// iter_helpers.rs:306 — option_sort_for_value.
#[test]
fn test_option_sort_for_value_uses_expected_when_datatype() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let expected = enum_sort(
            "Option_bv32",
            [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])],
        );
        let result = codegen.option_sort_for_value(&Sort::bitvec(32), Some(expected));
        assert!(result.is_datatype());
        assert_eq!(result.datatype_name(), Some("Option_bv32"));
    });
}

/// Test option_sort_for_value creates fresh sort when no expected.
/// iter_helpers.rs:313 — fallback creates option sort.
#[test]
fn test_option_sort_for_value_creates_fresh_when_none() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.option_sort_for_value(&Sort::bitvec(32), None);
        assert!(result.is_datatype());
        let dt = result.datatype_sort().expect("Option should be datatype");
        assert!(
            dt.constructors
                .iter()
                .any(|ctor| crate::codegen_ay::names::is_none_constructor(&ctor.name))
        );
        assert!(
            dt.constructors
                .iter()
                .any(|ctor| crate::codegen_ay::names::is_some_constructor(&ctor.name))
        );
    });
}

/// Test make_vec_from_parts creates Vec with 4 fields.
/// iter_helpers.rs:431 — make_vec_from_parts.
#[test]
fn test_make_vec_from_parts_creates_vec_sort() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let elem_sort = Sort::bitvec(32);
        let data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort.clone());
        let len = Expr::bitvec_const(5u64, POINTER_WIDTH);
        let data = Expr::var("data", data_sort);

        let vec = codegen.make_vec_from_parts(elem_sort, len, data);
        assert!(vec.sort().is_datatype());
        let dt = vec.sort().datatype_sort().unwrap();
        assert!(dt.name.starts_with("Vec_"));
        assert_eq!(dt.constructors[0].fields.len(), 4);
        assert_eq!(dt.constructors[0].fields[0].name, "fld_ptr");
        assert_eq!(dt.constructors[0].fields[1].name, "fld_len");
        assert_eq!(dt.constructors[0].fields[2].name, "fld_cap");
        assert_eq!(dt.constructors[0].fields[3].name, "fld_data");
    });
}

/// Test set_iter_field_select extracts field from set iterator.
/// iter_helpers.rs:118 — set_iter_field_select.
#[test]
fn test_set_iter_field_select_extracts_field() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let key_sort = Sort::bitvec(64);
        let set_sort = Sort::array(key_sort.clone(), Sort::bool());
        let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);
        let iter_sort = struct_sort(
            "SetIter",
            [
                ("fld_set", set_sort),
                ("fld_keys", keys_sort),
                ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ],
        );
        let ctor = iter_sort
            .datatype_default_constructor()
            .map_or_else(|| "SetIter_mk".to_string(), str::to_string);
        let iter = Expr::datatype_constructor(
            "SetIter",
            &ctor,
            vec![
                Expr::var("set", Sort::array(Sort::bitvec(64), Sort::bool())),
                Expr::var("keys", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(64))),
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                Expr::bitvec_const(5u64, POINTER_WIDTH),
            ],
            iter_sort,
        );

        let pos = codegen.set_iter_field_select(&iter, "SetIter", "fld_pos");
        assert_eq!(pos.sort().bitvec_width(), Some(POINTER_WIDTH));

        let set = codegen.set_iter_field_select(&iter, "SetIter", "fld_set");
        assert!(set.sort().is_array());
    });
}

/// Test set_iter_field_select fallback for non-datatype sort.
/// iter_helpers.rs:132 — fallback creates symbolic value.
#[test]
fn test_set_iter_field_select_fallback() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_dt = Expr::var("not_iter", Sort::bitvec(64));

        let set_fallback = codegen.set_iter_field_select(&non_dt, "SetIter", "fld_set");
        assert!(set_fallback.sort().is_array());

        let keys_fallback = codegen.set_iter_field_select(&non_dt, "SetIter", "fld_keys");
        assert!(keys_fallback.sort().is_array());

        let pos_fallback = codegen.set_iter_field_select(&non_dt, "SetIter", "fld_pos");
        assert_eq!(pos_fallback.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test hashmap_iter_field_select extracts field from hashmap iterator.
/// iter_helpers.rs:146 — hashmap_iter_field_select.
#[test]
fn test_hashmap_iter_field_select_extracts_field() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // DT-free encoding (#3057, #3106): fld_data + fld_present
        let key_sort = Sort::bitvec(64);
        let val_sort = Sort::bitvec(32);
        let data_sort = Sort::array(key_sort.clone(), val_sort);
        let present_sort = Sort::array(key_sort.clone(), Sort::bool());
        let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);
        let iter_sort = struct_sort(
            "HashMapIter",
            [
                ("fld_data", data_sort),
                ("fld_present", present_sort),
                ("fld_keys", keys_sort),
                ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ],
        );
        let ctor = iter_sort
            .datatype_default_constructor()
            .map_or_else(|| "HashMapIter_mk".to_string(), str::to_string);
        let iter = Expr::datatype_constructor(
            "HashMapIter",
            &ctor,
            vec![
                Expr::var("data", Sort::array(Sort::bitvec(64), Sort::bitvec(32))),
                Expr::const_array(Sort::bool(), Expr::bool_const(true)),
                Expr::var("keys", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(64))),
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                Expr::bitvec_const(3u64, POINTER_WIDTH),
            ],
            iter_sort,
        );

        let data_field = codegen.hashmap_iter_field_select(&iter, "HashMapIter", "fld_data");
        assert!(data_field.sort().is_array());

        let pos_field = codegen.hashmap_iter_field_select(&iter, "HashMapIter", "fld_pos");
        assert_eq!(pos_field.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test hashmap_iter_field_select fallback for non-datatype sort.
/// iter_helpers.rs:160 — fallback creates symbolic value.
#[test]
fn test_hashmap_iter_field_select_fallback() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_dt = Expr::var("not_iter", Sort::bitvec(64));

        let data_fallback = codegen.hashmap_iter_field_select(&non_dt, "HashMapIter", "fld_data");
        assert!(data_fallback.sort().is_array());

        let pos_fallback = codegen.hashmap_iter_field_select(&non_dt, "HashMapIter", "fld_pos");
        assert_eq!(pos_fallback.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test advance_wrapped_iterator returns None for non-datatype wrapper.
/// iter_helpers.rs:77 — early return for non-datatype.
#[test]
fn test_advance_wrapped_iterator_non_datatype_returns_none() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let non_dt = Expr::var("not_wrapper", Sort::bitvec(64));
        let result = codegen.advance_wrapped_iterator(&non_dt, "fld_iter");
        assert!(result.is_none());
    });
}

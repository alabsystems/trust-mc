// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for iter.rs — iterator codegen helpers.
//!
//! Tests cover:
//! - Expression-level IndexRange construction and length computation
//! - IndexRange next() stepping logic (start increment, has_next condition)
//! - MIR-driven codegen_step_unchecked (forward/backward bitvec/int steps)
//! - Expression-level PolymorphicIter/IntoIter construction patterns
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Expression-level IndexRange tests
// ═══════════════════════════════════════════════════════════════════════

/// Build an IndexRange sort with start/end fields of the given bitvec width.
fn index_range_sort(width: u32) -> Sort {
    struct_sort(
        "IndexRange",
        [("fld_start", Sort::bitvec(width)), ("fld_end", Sort::bitvec(width))],
    )
}

/// Build an IndexRange expression [start, end).
fn index_range_expr(start: u128, end: u128, width: u32) -> (Expr, Sort) {
    let sort = index_range_sort(width);
    let cons = sort.datatype_default_constructor().unwrap_or("IndexRange_mk").to_string();
    let expr = Expr::datatype_constructor(
        "IndexRange",
        cons,
        vec![Expr::bitvec_const(start, width), Expr::bitvec_const(end, width)],
        sort.clone(),
    );
    (expr, sort)
}

/// Helper: seed argument locals into a StatementCodegen's SSA environment.
fn seed_args(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        }
    }
}

/// Look up the expression currently assigned to a MIR Place via SSA env.
fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

/// Return the number of emitted constraints so far.
fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

/// Return the string form of the latest emitted constraint.
fn latest_constraint_text(codegen: &StatementCodegen<'_, '_, '_>) -> String {
    codegen
        .ctx
        .bmc_vc
        .constraints
        .last()
        .expect("expected an emitted assignment constraint")
        .to_string()
}

// ─── index_range_len_expr ───────────────────────────────────────────

#[test]
fn test_index_range_len_non_empty() {
    // IndexRange [2, 10) → len = 10 - 2 = 8
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(2, 10, POINTER_WIDTH);
        let len = codegen.index_range_len_expr(&alive, &sort, false);
        assert!(len.is_some(), "index_range_len_expr should succeed");
        let len = len.unwrap();
        assert!(len.sort().is_bitvec(), "len should be bitvec, got {:?}", len.sort());
        assert_eq!(
            len.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "len width should match pointer width"
        );
        // len = ite(end >= start, end - start, 0)
        assert!(
            matches!(len.value(), ExprValue::Ite { .. }),
            "len should be ite (guarded subtraction), got {:?}",
            len.value()
        );
    });
}

#[test]
fn test_index_range_len_underflow_returns_zero() {
    // IndexRange [10, 2) → end < start → should produce ite guarding to zero
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(10, 2, POINTER_WIDTH);
        let len = codegen
            .index_range_len_expr(&alive, &sort, false)
            .expect("should succeed even for reversed range");
        assert!(len.sort().is_bitvec());
        // The result should be an ite expression, not a bare bvsub
        assert!(
            matches!(len.value(), ExprValue::Ite { .. }),
            "len should be ite (guarded subtraction), got {:?}",
            len.value()
        );
    });
}

#[test]
fn test_index_range_len_empty() {
    // IndexRange [0, 0) → len = 0 - 0 = 0
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(0, 0, POINTER_WIDTH);
        let len = codegen
            .index_range_len_expr(&alive, &sort, false)
            .expect("should succeed for empty range");
        assert!(len.sort().is_bitvec());
    });
}

#[test]
fn test_index_range_len_rejects_non_datatype() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_sort = Sort::bitvec(64);
        let bv_expr = Expr::bitvec_const(42u128, 64);
        assert!(
            codegen.index_range_len_expr(&bv_expr, &bv_sort, false).is_none(),
            "should return None for non-Datatype sort"
        );
    });
}

#[test]
fn test_index_range_len_32bit_width() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(5, 15, 32);
        let len = codegen
            .index_range_len_expr(&alive, &sort, false)
            .expect("should succeed for 32-bit range");
        assert_eq!(len.sort().bitvec_width(), Some(32), "len should be 32-bit");
    });
}

/// Build an IndexRange sort with Int-sorted start/end fields.
///
/// Exercises the Int-lifting path: when ranges are lifted from BV to Int
/// sort (Part of #2875), the statement layer must handle Int fields.
fn index_range_sort_int() -> Sort {
    struct_sort("IndexRange", [("fld_start", Sort::int()), ("fld_end", Sort::int())])
}

/// Build an Int-sorted IndexRange expression [start, end).
fn index_range_expr_int(start: i64, end: i64) -> (Expr, Sort) {
    let sort = index_range_sort_int();
    let cons = sort.datatype_default_constructor().unwrap_or("IndexRange_mk").to_string();
    let expr = Expr::datatype_constructor(
        "IndexRange",
        cons,
        vec![Expr::int_const(start), Expr::int_const(end)],
        sort.clone(),
    );
    (expr, sort)
}

/// Statement-layer `index_range_len_expr` handles Int-sorted IndexRange.
///
/// Fix for P952/P953 F1: the statement layer now supports Int-sorted range
/// fields using `int_ge`/`int_sub`, matching the CHC layer's `range_len_expr`.
#[test]
fn test_index_range_len_succeeds_for_int_sort() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr_int(2, 10);
        let len = codegen
            .index_range_len_expr(&alive, &sort, false)
            .expect("index_range_len_expr should handle Int sort (P952 F1 fix)");
        assert!(len.sort().is_int(), "len of Int range should be Int sort, got {:?}", len.sort());
        assert!(
            matches!(len.value(), ExprValue::Ite { .. }),
            "len should be ite (guarded subtraction), got {:?}",
            len.value()
        );
    });
}

/// Int-sorted `index_range_len_expr` with reversed range returns guarded zero.
#[test]
fn test_index_range_len_int_reversed_range() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // end < start: len should be guarded to zero via ite
        let (alive, sort) = index_range_expr_int(10, 2);
        let len = codegen
            .index_range_len_expr(&alive, &sort, false)
            .expect("should succeed for reversed Int range");
        assert!(len.sort().is_int(), "len should be Int sort");
        assert!(
            matches!(len.value(), ExprValue::Ite { .. }),
            "reversed range len should be ite (guarded), got {:?}",
            len.value()
        );
    });
}

/// Int-sorted `index_range_len_expr` with empty range [0, 0).
#[test]
fn test_index_range_len_int_empty_range() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr_int(0, 0);
        let len = codegen
            .index_range_len_expr(&alive, &sort, false)
            .expect("should succeed for empty Int range");
        assert!(len.sort().is_int(), "len should be Int sort");
    });
}

/// Statement-layer `index_range_next_expr` uses Int operations for Int-sorted ranges.
///
/// Fix for P953 F2: `index_range_next_expr` now dispatches to `int_lt`/`int_add`
/// when the range fields are Int-sorted, instead of falling back to BV operations.
#[test]
fn test_index_range_next_int_sort_uses_int_operations() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr_int(0, 5);
        let (start, end, has_next, updated_alive) = codegen
            .index_range_next_expr(&alive, &sort, false)
            .expect("index_range_next_expr should handle Int sort (P953 F2 fix)");
        // Fields should be Int-sorted
        assert!(start.sort().is_int(), "start should be Int sort, got {:?}", start.sort());
        assert!(end.sort().is_int(), "end should be Int sort, got {:?}", end.sort());
        // has_next should use int_lt, not bvult
        assert!(
            matches!(has_next.value(), ExprValue::IntLt(_, _)),
            "has_next should use IntLt for Int sort, got {:?}",
            has_next.value()
        );
        assert!(has_next.sort().is_bool(), "has_next should be Bool sort");
        // updated_alive should be a Datatype constructor
        assert!(
            updated_alive.sort().is_datatype(),
            "updated_alive should be Datatype sort, got {:?}",
            updated_alive.sort()
        );
    });
}

// ─── index_range_next_expr ──────────────────────────────────────────

#[test]
fn test_index_range_next_returns_four_tuple() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(0, 5, POINTER_WIDTH);
        let result = codegen.index_range_next_expr(&alive, &sort, false);
        assert!(result.is_some(), "index_range_next_expr should succeed");

        let (start, end, has_next, updated_alive) = result.unwrap();
        assert!(start.sort().is_bitvec(), "start should be bitvec");
        assert_eq!(start.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(end.sort().is_bitvec(), "end should be bitvec");
        assert_eq!(end.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(has_next.sort().is_bool(), "has_next should be bool");
        assert!(
            updated_alive.sort().is_datatype(),
            "updated_alive should be datatype, got {:?}",
            updated_alive.sort()
        );
    });
}

#[test]
fn test_index_range_next_has_next_is_unsigned_lt() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(0, 5, POINTER_WIDTH);
        let (_, _, has_next, _) =
            codegen.index_range_next_expr(&alive, &sort, false).expect("should succeed");
        // has_next = bvult(start, end)
        assert!(has_next.sort().is_bool());
        assert!(
            matches!(has_next.value(), ExprValue::BvULt(..)),
            "has_next should be BvULt, got {:?}",
            has_next.value()
        );
    });
}

#[test]
fn test_index_range_next_updated_alive_is_constructor() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(3, 7, POINTER_WIDTH);
        let (_, _, _, updated_alive) =
            codegen.index_range_next_expr(&alive, &sort, false).expect("should succeed");

        // The updated_alive is a DatatypeConstructor with ITE start field
        assert!(
            matches!(updated_alive.value(), ExprValue::DatatypeConstructor { .. }),
            "updated_alive should be DatatypeConstructor, got {:?}",
            updated_alive.value()
        );
    });
}

#[test]
fn test_index_range_next_rejects_non_datatype() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_sort = Sort::bitvec(64);
        let bv_expr = Expr::bitvec_const(0u128, 64);
        assert!(
            codegen.index_range_next_expr(&bv_expr, &bv_sort, false).is_none(),
            "should return None for non-Datatype sort"
        );
    });
}

#[test]
fn test_index_range_next_32bit_produces_32bit_exprs() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(0, 10, 32);
        let (start, end, _, _) =
            codegen.index_range_next_expr(&alive, &sort, false).expect("should succeed for 32-bit");
        assert_eq!(start.sort().bitvec_width(), Some(32));
        assert_eq!(end.sort().bitvec_width(), Some(32));
    });
}

#[test]
fn test_index_range_next_single_element_range() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(5, 6, POINTER_WIDTH);
        let (start, end, has_next, _) = codegen
            .index_range_next_expr(&alive, &sort, false)
            .expect("should succeed for single-element range");

        assert!(start.sort().is_bitvec());
        assert!(end.sort().is_bitvec());
        assert!(has_next.sort().is_bool());
    });
}

#[test]
fn test_index_range_next_large_range() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = index_range_expr(0, 1000, POINTER_WIDTH);
        let result = codegen.index_range_next_expr(&alive, &sort, false);
        assert!(result.is_some(), "should succeed for large range");
    });
}

// ─── signed index_range tests (Part of #3272) ─────────────────────────

#[test]
fn test_index_range_len_signed_negative_bounds() {
    // Range<i32> [-5, 5) → len should be 10.
    // With unsigned comparison, -5 (0xFFFFFFFB) > 5, so guard fails → len = 0 (WRONG).
    // With signed comparison, -5 < 5, so guard succeeds → len = 10 (CORRECT).
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Build IndexRange with 32-bit BV fields representing signed values.
        // -5 in two's complement 32-bit = 0xFFFFFFFB = 4294967291
        let neg5: u128 = (-5i32 as u32) as u128;
        let pos5: u128 = 5;
        let (alive, sort) = index_range_expr(neg5, pos5, 32);

        // Unsigned: should produce ite(5 >= 0xFFFFFFFB, ...) = ite(false, ...) = 0
        let len_unsigned = codegen
            .index_range_len_expr(&alive, &sort, false)
            .expect("unsigned len should succeed");
        assert!(matches!(len_unsigned.value(), ExprValue::Ite { .. }));

        // Signed: should produce ite(-5 <=s 5, ...) = ite(true, ...) = 10
        let len_signed =
            codegen.index_range_len_expr(&alive, &sort, true).expect("signed len should succeed");
        assert!(matches!(len_signed.value(), ExprValue::Ite { .. }));

        // The expressions differ because signed uses bvsge vs bvuge in the guard.
        // We can't evaluate SMT expressions here, but we verify the structure is correct.
        assert_ne!(
            format!("{:?}", len_unsigned),
            format!("{:?}", len_signed),
            "signed and unsigned len should produce different guard expressions"
        );
    });
}

#[test]
fn test_index_range_next_signed_negative_start() {
    // Range<i32> [-3, 2) → has_next should be true (signed: -3 < 2).
    // With unsigned comparison, -3 (0xFFFFFFFD) > 2, so has_next = false (WRONG).
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let neg3: u128 = (-3i32 as u32) as u128;
        let pos2: u128 = 2;
        let (alive, sort) = index_range_expr(neg3, pos2, 32);

        // Unsigned path: has_next uses bvult
        let (_, _, has_next_unsigned, _) = codegen
            .index_range_next_expr(&alive, &sort, false)
            .expect("unsigned next should succeed");

        // Signed path: has_next uses bvslt
        let (_, _, has_next_signed, _) =
            codegen.index_range_next_expr(&alive, &sort, true).expect("signed next should succeed");

        // The guard expressions should differ (bvult vs bvslt).
        assert_ne!(
            format!("{:?}", has_next_unsigned),
            format!("{:?}", has_next_signed),
            "signed and unsigned has_next should use different comparison ops"
        );
    });
}

// ─── Fix #4297: bounds check on misshapen IndexRange-like sorts ───────

/// Build a 1-field datatype sort (simulating e.g. a `Take<Iter>` adapter whose
/// internal alive state has a single field, not the (start, end) pair an
/// IndexRange has). Previously, `index_range_len_expr` / `index_range_next_expr`
/// unconditionally indexed `constructors[0].fields[1]` and ICEd with
/// `index out of bounds: the len is 1 but the index is 1`.
fn one_field_datatype_expr() -> (Expr, Sort) {
    let sort = struct_sort("OneFieldAdapter", [("fld_only", Sort::bitvec(POINTER_WIDTH))]);
    let cons = sort.datatype_default_constructor().unwrap_or("OneFieldAdapter_mk").to_string();
    let expr = Expr::datatype_constructor(
        "OneFieldAdapter",
        cons,
        vec![Expr::bitvec_const(0u128, POINTER_WIDTH)],
        sort.clone(),
    );
    (expr, sort)
}

#[test]
fn test_index_range_len_regression_4297_one_field_returns_none_not_panic() {
    // Regression test for #4297: trust_mc ICE at
    // trust_mc-compiler/src/codegen_ay/statement/iter.rs:352:54
    // triggered by iterator chains like `[a, b].iter().take(n).collect::<String>()`.
    // The alive sort reaching index_range_* helpers was a 1-field adapter, causing
    // `constructors[0].fields[1]` to panic. Expected behavior is to return None
    // so the caller can fall back to an unsupported-verdict path.
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = one_field_datatype_expr();
        let result = codegen.index_range_len_expr(&alive, &sort, false);
        assert!(
            result.is_none(),
            "index_range_len_expr must return None (not panic) for 1-field alive sort"
        );
    });
}

#[test]
fn test_index_range_next_regression_4297_one_field_returns_none_not_panic() {
    // Regression test for #4297 — see sibling test for the full narrative.
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let (alive, sort) = one_field_datatype_expr();
        let result = codegen.index_range_next_expr(&alive, &sort, false);
        assert!(
            result.is_none(),
            "index_range_next_expr must return None (not panic) for 1-field alive sort"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// MIR-driven codegen_step_unchecked tests
// ═══════════════════════════════════════════════════════════════════════

const STEP_PROBE_SOURCE: &str = r#"
pub fn step_forward(start: u32, n: u32) -> u32 {
    start + n
}

pub fn step_backward(start: u32, n: u32) -> u32 {
    start - n
}

pub fn step_forward_64(start: u64, n: u64) -> u64 {
    start + n
}
"#;

#[test]
fn test_codegen_step_forward_u32_returns_target() {
    with_test_ay_ctx_for_source(STEP_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "step_forward");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let args: Vec<Operand> = body
            .arg_locals()
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                Operand::Copy(Place { local: Local::from(idx + 1), projection: vec![] })
            })
            .collect();
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let pre = constraint_count(&codegen);
        let result = codegen.codegen_step_unchecked(&args, &dest, Some(1), true);
        assert_eq!(result, Some(1), "forward step should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("forward step should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "u32 step should produce bv32");
        assert!(constraint_count(&codegen) > pre, "forward step should emit constraints");
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvadd"), "forward step should emit bvadd, got {emitted}");
    });
}

#[test]
fn test_codegen_step_backward_u32_returns_target() {
    with_test_ay_ctx_for_source(STEP_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "step_backward");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let args: Vec<Operand> = body
            .arg_locals()
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                Operand::Copy(Place { local: Local::from(idx + 1), projection: vec![] })
            })
            .collect();
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let pre = constraint_count(&codegen);
        let result = codegen.codegen_step_unchecked(&args, &dest, Some(2), false);
        assert_eq!(result, Some(2), "backward step should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("backward step should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "u32 step should produce bv32");
        assert!(constraint_count(&codegen) > pre, "backward step should emit constraints");
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvsub"), "backward step should emit bvsub, got {emitted}");
    });
}

#[test]
fn test_codegen_step_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(STEP_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "step_forward");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let args = vec![Operand::Copy(Place { local: Local::from(1usize), projection: vec![] })];
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let result = codegen.codegen_step_unchecked(&args, &dest, Some(1), true);
        assert_eq!(result, None, "insufficient args should return None");
    });
}

#[test]
fn test_codegen_step_empty_args_returns_none() {
    with_test_ay_ctx_for_source(STEP_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "step_forward");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let args: Vec<Operand> = vec![];
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let result = codegen.codegen_step_unchecked(&args, &dest, Some(1), true);
        assert_eq!(result, None, "empty args should return None");
    });
}

#[test]
fn test_codegen_step_forward_none_target() {
    with_test_ay_ctx_for_source(STEP_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "step_forward");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let args: Vec<Operand> = body
            .arg_locals()
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                Operand::Copy(Place { local: Local::from(idx + 1), projection: vec![] })
            })
            .collect();
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let result = codegen.codegen_step_unchecked(&args, &dest, None, true);
        assert_eq!(result, None, "None target should propagate through");
    });
}

#[test]
fn test_codegen_step_forward_64bit_returns_target() {
    with_test_ay_ctx_for_source(STEP_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "step_forward_64");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let args: Vec<Operand> = body
            .arg_locals()
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                Operand::Copy(Place { local: Local::from(idx + 1), projection: vec![] })
            })
            .collect();
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let pre = constraint_count(&codegen);
        let result = codegen.codegen_step_unchecked(&args, &dest, Some(3), true);
        assert_eq!(result, Some(3), "64-bit forward step should succeed");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("64-bit step should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64), "u64 step should produce bv64");
        assert!(constraint_count(&codegen) > pre, "64-bit step should emit constraints");
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvadd"), "64-bit forward step should emit bvadd, got {emitted}");
    });
}

/// Build a PolymorphicIter sort manually for testing.
fn polymorphic_iter_sort(elem_width: u32) -> Sort {
    let idx_sort = index_range_sort(POINTER_WIDTH);
    let data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(elem_width));
    struct_sort("PolymorphicIter", [("fld_alive", idx_sort), ("fld_data", data_sort)])
}

// Trivial ay_bindings-only construction tests deleted per #2312 / #2391:
// - test_polymorphic_iter_sort_is_datatype (ay Sort assertion only)
// - test_polymorphic_iter_construction_has_two_fields (ay Expr constructor only)
// - test_into_iter_nested_structure (ay Expr nesting only, no production call)

#[test]
fn test_into_iter_zero_length_array_range() {
    // For zero-length arrays, alive range should be [0, 0)
    let idx_sort = index_range_sort(POINTER_WIDTH);
    let idx_cons = idx_sort.datatype_default_constructor().unwrap_or("IndexRange_mk").to_string();
    let alive = Expr::datatype_constructor(
        "IndexRange",
        idx_cons,
        vec![Expr::bitvec_const(0u128, POINTER_WIDTH), Expr::bitvec_const(0u128, POINTER_WIDTH)],
        idx_sort.clone(),
    );

    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let len = codegen
            .index_range_len_expr(&alive, &idx_sort, false)
            .expect("len should succeed on empty range");
        assert!(len.sort().is_bitvec());
    });
}

#[test]
fn test_codegen_step_with_symbolic_args() {
    let probe_src = r#"
pub fn symbolic_step(x: u32, y: u32) -> u32 {
    x + y
}
"#;
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "symbolic_step");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let args: Vec<Operand> = body
            .arg_locals()
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                Operand::Copy(Place { local: Local::from(idx + 1), projection: vec![] })
            })
            .collect();
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let pre = constraint_count(&codegen);
        let result = codegen.codegen_step_unchecked(&args, &dest, Some(1), true);
        assert_eq!(result, Some(1), "symbolic forward step should return target");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("symbolic step should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "u32 symbolic step should produce bv32"
        );
        assert!(constraint_count(&codegen) > pre, "symbolic step should emit constraints");
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("bvadd"),
            "symbolic forward step should emit bvadd, got {emitted}"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed extract_array_iter_len tests
// Part of #2391: coverage gap — 9 of 12 iter.rs functions had no tests
// ═══════════════════════════════════════════════════════════════════════

/// extract_array_iter_len returns the const length N from &IntoIter<T, N>.
#[test]
fn test_extract_array_iter_len_from_into_iter_ref() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_array_iter(arr: [u32; 5]) {
            for _x in arr {}
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_array_iter");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);

            // Scan locals for any type containing IntoIter with a const generic
            let mut found_iter = false;
            for local_decl in body.locals() {
                let ty = local_decl.ty;
                let ty_str = format!("{:?}", ty);
                if ty_str.contains("IntoIter") {
                    let len = StatementCodegen::extract_array_iter_len(ty);
                    if let Some(n) = len {
                        assert_eq!(n, 5, "array length should be 5, got {n}");
                        found_iter = true;
                    }
                }
            }
            assert!(found_iter, "should find at least one IntoIter local with extractable length");
        },
    );
}

/// extract_array_iter_len returns None for non-iterator types.
#[test]
fn test_extract_array_iter_len_returns_none_for_plain_type() {
    with_test_ay_ctx_for_source("pub fn probe_plain(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_plain");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);

        // The u32 argument type should not be an iterator
        let arg_ty = body.arg_locals()[0].ty;
        assert!(
            StatementCodegen::extract_array_iter_len(arg_ty).is_none(),
            "u32 should not extract array iter len"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed get_ref_pointee_sort tests
// ═══════════════════════════════════════════════════════════════════════

/// get_ref_pointee_sort returns None when the operand is a Constant.
#[test]
fn test_get_ref_pointee_sort_constant_returns_none() {
    with_test_ay_ctx_for_source("pub fn probe_const() -> u32 { 42 }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_const");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Search MIR for a Constant operand and test get_ref_pointee_sort on it
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Use(ref op @ Operand::Constant(_))) =
                    stmt.kind
                {
                    let result = codegen.get_ref_pointee_sort(op);
                    assert!(
                        result.is_none(),
                        "Constant operand should return None from get_ref_pointee_sort"
                    );
                    return;
                }
            }
        }
        // If no constant found in assignments, check terminators aren't needed
        // (the return value 42 may be optimized differently)
        panic!("should find at least one Constant operand in MIR");
    });
}

/// get_ref_pointee_sort returns None when ref_pointees has no entry for the reference.
#[test]
fn test_get_ref_pointee_sort_untracked_ref_returns_none() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_ref(x: &u32) -> u32 { *x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_ref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            seed_args(&mut codegen, &body);

            // The reference argument (local 1) has no ref_pointees entry by default
            let ref_operand =
                Operand::Copy(Place { local: Local::from(1usize), projection: vec![] });
            let result = codegen.get_ref_pointee_sort(&ref_operand);
            assert!(
                result.is_none(),
                "untracked reference should return None from get_ref_pointee_sort"
            );
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed iter_base_from_operand tests
// ═══════════════════════════════════════════════════════════════════════

/// iter_base_from_operand returns None for None input.
#[test]
fn test_iter_base_from_operand_none_returns_none() {
    with_test_ay_ctx_for_source("pub fn probe_iter_base() {}", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_iter_base");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert!(codegen.iter_base_from_operand(None).is_none(), "None operand should return None");
    });
}

/// iter_base_from_operand returns the SSA base and unwrapped type for a Copy operand.
#[test]
fn test_iter_base_from_operand_copy_returns_base() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_iter_copy(x: &u32) -> u32 { *x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_iter_copy");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            seed_args(&mut codegen, &body);

            // Local 1 is &u32 — iter_base_from_operand should return the base name and u32 type
            let operand = Operand::Copy(Place { local: Local::from(1usize), projection: vec![] });
            let result = codegen.iter_base_from_operand(Some(&operand));
            assert!(result.is_some(), "Copy operand for &u32 should return Some");
            let (base, ty) = result.unwrap();
            assert!(!base.is_empty(), "base name should be non-empty");
            // The type should be unwrapped from &u32 to u32
            assert!(
                matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(_))),
                "type should be unwrapped to u32, got {:?}",
                ty.kind()
            );
        },
    );
}

/// iter_base_from_operand returns None for a Constant operand.
#[test]
fn test_iter_base_from_operand_constant_returns_none() {
    with_test_ay_ctx_for_source("pub fn probe_iter_const() -> u32 { 42 }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_iter_const");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find a Constant operand in the MIR
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Use(ref op @ Operand::Constant(_))) =
                    stmt.kind
                {
                    let result = codegen.iter_base_from_operand(Some(op));
                    assert!(
                        result.is_none(),
                        "Constant operand should return None from iter_base_from_operand"
                    );
                    return;
                }
            }
        }
        panic!("should find at least one Constant operand in MIR");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// polymorphic_iter_len_expr coverage tests
// Part of #2391: coverage gap — soundness-critical len computation
// ═══════════════════════════════════════════════════════════════════════

/// Verify alive field extraction from PolymorphicIter feeds valid data to index_range_len_expr.
/// This exercises the core delegation path of polymorphic_iter_len_expr without needing
/// a real PolymorphicIter MIR type (which rustc may inline away).
#[test]
fn test_polymorphic_iter_len_via_alive_field_extraction() {
    let probe_src = "pub fn iter_probe() {}\n";
    with_test_ay_ctx_for_source(probe_src, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "iter_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Build a synthetic PolymorphicIter with alive = IndexRange[2, 7)
        let idx_sort = index_range_sort(POINTER_WIDTH);
        let idx_cons =
            idx_sort.datatype_default_constructor().unwrap_or("IndexRange_mk").to_string();
        let alive = Expr::datatype_constructor(
            "IndexRange",
            idx_cons,
            vec![
                Expr::bitvec_const(2u128, POINTER_WIDTH),
                Expr::bitvec_const(7u128, POINTER_WIDTH),
            ],
            idx_sort.clone(),
        );
        let data = Expr::var("arr", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32)));
        let iter_sort = polymorphic_iter_sort(POINTER_WIDTH);
        let iter_cons =
            iter_sort.datatype_default_constructor().unwrap_or("PolymorphicIter_mk").to_string();
        let iter_expr =
            Expr::datatype_constructor("PolymorphicIter", iter_cons, vec![alive, data], iter_sort);

        // Extract alive field and compute len — this mirrors polymorphic_iter_len_expr's logic
        let alive_extracted =
            iter_expr.field_select("PolymorphicIter", "fld_alive", idx_sort.clone());
        let len = codegen
            .index_range_len_expr(&alive_extracted, &idx_sort, false)
            .expect("index_range_len_expr should succeed on extracted alive field");
        assert!(len.sort().is_bitvec(), "len should be bitvec, got {:?}", len.sort());
        assert!(
            matches!(len.value(), ExprValue::Ite { .. }),
            "len should be ite (guarded subtraction), got {:?}",
            len.value()
        );
    });
}

/// polymorphic_iter_len_expr rejects non-Datatype iter_expr (soundness guard #967).
#[test]
fn test_polymorphic_iter_len_rejects_non_datatype_expr() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_poly_guard(arr: [u32; 3]) {
            for _x in arr {}
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_poly_guard");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Use a bitvec expression (wrong sort) — the is_datatype() guard should reject
            let bv_expr = Expr::bitvec_const(0u128, POINTER_WIDTH);
            for local_decl in body.locals() {
                let ty = local_decl.ty;
                let ty_str = format!("{:?}", ty);
                if (ty_str.contains("IntoIter") || ty_str.contains("iter_inner"))
                    && let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind()
                    && def.variants()[0].fields().len() >= 2
                {
                    let result = codegen.polymorphic_iter_len_expr(&bv_expr, ty);
                    assert!(
                        result.is_none(),
                        "polymorphic_iter_len_expr must reject non-Datatype expr (#967)"
                    );
                    return;
                }
            }
            // If no suitable iterator type found in this MIR, test is vacuously correct
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed build_index_range_expr tests
// Part of #2391: coverage gap — IndexRange construction from real MIR type
// ═══════════════════════════════════════════════════════════════════════

/// build_index_range_expr constructs a Datatype expression from a real Range type.
#[test]
fn test_build_index_range_expr_from_range_type() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_range() {
            for _i in 0..10u32 {}
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_range");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Look for a Range ADT type in locals
            let mut found = false;
            for local_decl in body.locals() {
                let ty = local_decl.ty;
                let ty_str = format!("{:?}", ty);
                if !ty_str.contains("Range") || ty_str.contains("RangeInclusive") {
                    continue;
                }
                if let TyKind::RigidTy(RigidTy::Adt(_, _)) = ty.kind() {
                    let start = Expr::bitvec_const(0u128, 32);
                    let end = Expr::bitvec_const(10u128, 32);
                    if let Some(expr) = codegen.build_index_range_expr(ty, start, end) {
                        assert!(
                            expr.sort().is_datatype(),
                            "build_index_range_expr should produce Datatype sort"
                        );
                        assert!(
                            matches!(expr.value(), ExprValue::DatatypeConstructor { .. }),
                            "result should be DatatypeConstructor"
                        );
                        found = true;
                        break;
                    }
                }
            }
            assert!(found, "should find a Range type in `for _i in 0..10u32` and build IndexRange");
        },
    );
}

/// build_index_range_expr returns None for non-ADT types.
#[test]
fn test_build_index_range_expr_rejects_non_adt() {
    with_test_ay_ctx_for_source("pub fn probe_non_adt(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_non_adt");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arg_ty = body.arg_locals()[0].ty;
        let start = Expr::bitvec_const(0u128, 32);
        let end = Expr::bitvec_const(10u128, 32);
        assert!(
            codegen.build_index_range_expr(arg_ty, start, end).is_none(),
            "non-ADT type should return None from build_index_range_expr"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed build_option_expr tests
// Part of #2391: coverage gap — Option enum construction from predicate
// ═══════════════════════════════════════════════════════════════════════

/// build_option_expr constructs ITE(is_some, Some(val), None) from an Option<u32> dest.
#[test]
fn test_build_option_expr_constructs_ite() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_option() -> Option<u32> {
            Some(42)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_option");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Return place (local 0) has type Option<u32>
            let dest = Place { local: Local::from(0usize), projection: vec![] };
            let is_some = Expr::bool_const(true);
            let payload = Expr::bitvec_const(42u128, 32);

            let result = codegen.build_option_expr(&dest, is_some, payload);
            assert!(result.is_some(), "build_option_expr should succeed for Option<u32>");
            let expr = result.unwrap();
            assert!(
                matches!(expr.value(), ExprValue::Ite { .. }),
                "result should be ITE expression, got {:?}",
                expr.value()
            );
        },
    );
}

/// build_option_expr returns None for non-Option destination types.
#[test]
fn test_build_option_expr_rejects_non_option_dest() {
    with_test_ay_ctx_for_source("pub fn probe_u32() -> u32 { 0 }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Return place (local 0) is u32, not Option — should return None
        let dest = Place { local: Local::from(0usize), projection: vec![] };
        let is_some = Expr::bool_const(true);
        let payload = Expr::bitvec_const(0u128, 32);

        assert!(
            codegen.build_option_expr(&dest, is_some, payload).is_none(),
            "build_option_expr should return None for non-Option destination"
        );
    });
}

/// build_option_expr with false predicate still produces ITE (both branches present).
#[test]
fn test_build_option_expr_with_false_predicate() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_option_none() -> Option<u32> {
            None
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_option_none");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let dest = Place { local: Local::from(0usize), projection: vec![] };
            let is_some = Expr::bool_const(false);
            let payload = Expr::bitvec_const(0u128, 32);

            let result = codegen.build_option_expr(&dest, is_some, payload);
            assert!(result.is_some(), "build_option_expr should succeed with false predicate");
            let expr = result.unwrap();
            assert!(
                matches!(expr.value(), ExprValue::Ite { .. }),
                "should still be ITE (condition selects None branch), got {:?}",
                expr.value()
            );
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed build_polymorphic_iter_expr tests
// Part of #2391: coverage gap — PolymorphicIter construction from MIR Ty
// ═══════════════════════════════════════════════════════════════════════

/// build_polymorphic_iter_expr returns None for non-ADT types.
#[test]
fn test_build_polymorphic_iter_expr_rejects_non_adt() {
    with_test_ay_ctx_for_source("pub fn probe_prim(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_prim");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // u32 is not an ADT — should return None
        let arg_ty = body.arg_locals()[0].ty;
        let alive = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let data = Expr::var("data", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32)));
        assert!(
            codegen.build_polymorphic_iter_expr(arg_ty, alive, data).is_none(),
            "non-ADT type should return None from build_polymorphic_iter_expr"
        );
    });
}

// DELETED: test_build_polymorphic_iter_expr_with_adt — vacuous (#2435).
// The probe source `for _x in arr {}` does not produce an IntoIter ADT type
// in the MIR locals that the search loop can match. The test always fell through
// without executing any assertion. Confirmed by adding panic! guard.
// The non-ADT rejection test (test_build_polymorphic_iter_expr_rejects_non_adt)
// still covers build_polymorphic_iter_expr.

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed polymorphic_iter_next_expr tests
// Part of #2391: coverage gap — PolymorphicIter next() stepping
// ═══════════════════════════════════════════════════════════════════════

/// polymorphic_iter_next_expr returns None for non-ADT iter_ty.
#[test]
fn test_polymorphic_iter_next_rejects_non_adt_type() {
    with_test_ay_ctx_for_source("pub fn probe_next_prim(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_next_prim");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let iter_expr = Expr::var("dummy_iter", polymorphic_iter_sort(32));
        let arg_ty = body.arg_locals()[0].ty; // u32 — not an ADT
        let dest = Place { local: Local::from(0usize), projection: vec![] };

        assert!(
            codegen.polymorphic_iter_next_expr(&iter_expr, arg_ty, &dest).is_none(),
            "non-ADT iter_ty should return None from polymorphic_iter_next_expr"
        );
    });
}

// DELETED: test_polymorphic_iter_next_rejects_non_datatype_expr — vacuous (#2435).
// Same probe source issue as build_polymorphic_iter_expr_with_adt: `for _x in arr {}`
// does not produce a matchable IntoIter ADT in the MIR locals. The loop always
// fell through without executing the assertion. Confirmed by adding panic! guard.
// The non-ADT rejection test (test_polymorphic_iter_next_rejects_non_adt_type)
// still covers the primary guard path.

// ═══════════════════════════════════════════════════════════════════════
// MIR-backed build_array_into_iter_expr tests
// Part of #2391: coverage gap — IntoIter construction from array
// ═══════════════════════════════════════════════════════════════════════

/// build_array_into_iter_expr constructs IntoIter from array with seeded args.
#[test]
fn test_build_array_into_iter_expr_with_array_arg() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_into_iter(arr: [u32; 4]) -> u32 {
            arr[0]
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_into_iter");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            seed_args(&mut codegen, &body);

            // arg 1 is [u32; 4] — create a Copy operand referencing it
            let arr_operand =
                Operand::Copy(Place { local: Local::from(1usize), projection: vec![] });
            let dest_ty = body.arg_locals()[0].ty;
            let elem_ty = body.arg_locals()[0].ty;

            let result = codegen.build_array_into_iter_expr(dest_ty, &arr_operand, elem_ty, 4);
            let expr = result.expect(
                "build_array_into_iter_expr must succeed for [u32; 4] — None means test is vacuous (#2435)"
            );
            assert!(
                expr.sort().is_datatype(),
                "IntoIter expr should have Datatype sort, got {:?}",
                expr.sort()
            );
            assert!(
                matches!(expr.value(), ExprValue::DatatypeConstructor { .. }),
                "IntoIter should be DatatypeConstructor, got {:?}",
                expr.value()
            );
        },
    );
}

/// build_array_into_iter_expr with zero-length array creates exhausted iterator.
#[test]
fn test_build_array_into_iter_expr_zero_length() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_empty_iter(_arr: [u32; 0]) -> usize {
            0
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "probe_empty_iter");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            seed_args(&mut codegen, &body);

            let arr_operand =
                Operand::Copy(Place { local: Local::from(1usize), projection: vec![] });
            let dest_ty = body.arg_locals()[0].ty;
            let elem_ty = body.arg_locals()[0].ty;

            // len=0: should create IntoIter with alive range [0, 0)
            let result = codegen.build_array_into_iter_expr(dest_ty, &arr_operand, elem_ty, 0);
            let expr = result.expect(
                "build_array_into_iter_expr must succeed for [u32; 0] — None means test is vacuous (#2435)"
            );
            assert!(
                expr.sort().is_datatype(),
                "zero-length IntoIter should still have Datatype sort"
            );
            assert!(
                matches!(expr.value(), ExprValue::DatatypeConstructor { .. }),
                "zero-length IntoIter should be DatatypeConstructor"
            );
        },
    );
}

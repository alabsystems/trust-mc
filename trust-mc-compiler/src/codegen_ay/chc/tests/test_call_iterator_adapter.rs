// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_iterator_adapter.rs` — iterator adapter CHC helpers.
//!
//! Part of #2303 (codegen_call_iterator_adapter.rs, 375 LOC, zero dedicated coverage).
//! Covers:
//! - `adapter_zero_expr_for_sort`: identity element construction
//! - `adapter_pos_lt_len`: width-normalizing position < length comparison
//! - `adapter_option_payload_sort`: Option payload extraction
//! - `fresh_adapter_symbol`: symbolic variable generation
//! - `rebuild_datatype_with_field`: field replacement on datatype exprs

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_iterator_adapter::CallIteratorAdapter;
use super::common::*;
use ay_bindings::{Expr, ExprValue, Sort};

// =============================================================================
// adapter_zero_expr_for_sort — identity elements
// =============================================================================

#[test]
fn test_adapter_zero_bool() {
    let result = ChcCtx::adapter_zero_expr_for_sort(&Sort::bool());
    assert!(result.is_some(), "Bool should have a zero expression");
    let expr = result.unwrap();
    assert!(expr.sort().is_bool());
    assert_eq!(expr.to_string(), "false");
}

#[test]
fn test_adapter_zero_bv32() {
    let result = ChcCtx::adapter_zero_expr_for_sort(&Sort::bitvec(32));
    assert!(result.is_some(), "BV32 should have a zero expression");
    let expr = result.unwrap();
    assert!(expr.sort().is_bitvec());
    assert_eq!(expr.sort().bitvec_width(), Some(32));
}

#[test]
fn test_adapter_zero_bv64() {
    let result = ChcCtx::adapter_zero_expr_for_sort(&Sort::bitvec(64));
    assert!(result.is_some());
    let expr = result.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(64));
}

#[test]
fn test_adapter_zero_int() {
    let result = ChcCtx::adapter_zero_expr_for_sort(&Sort::int());
    assert!(result.is_some(), "Int should have a zero expression");
    let expr = result.unwrap();
    assert!(expr.sort().is_int());
}

#[test]
fn test_adapter_zero_real() {
    let result = ChcCtx::adapter_zero_expr_for_sort(&Sort::real());
    assert!(result.is_some(), "Real should have a zero expression");
    let expr = result.unwrap();
    assert!(expr.sort().is_real());
}

#[test]
fn test_adapter_zero_array_returns_none() {
    let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let result = ChcCtx::adapter_zero_expr_for_sort(&array_sort);
    assert!(result.is_none(), "Array sorts should not have a zero expression");
}

#[test]
fn test_adapter_zero_datatype_returns_none() {
    let dt_sort = struct_sort("TestDT", [("fld_x", Sort::bitvec(32))]);
    let result = ChcCtx::adapter_zero_expr_for_sort(&dt_sort);
    assert!(result.is_none(), "Datatype sorts should not have a zero expression");
}

// =============================================================================
// adapter_pos_lt_len — width-normalizing position < length comparison
// =============================================================================

#[test]
fn test_adapter_pos_lt_len_same_width() {
    let pos = Expr::var("pos", Sort::bitvec(32));
    let len = Expr::var("len", Sort::bitvec(32));
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "same-width BV pos < len should succeed");
    let (has_remaining, pos_out) = result.unwrap();
    assert!(has_remaining.sort().is_bool(), "has_remaining should be Bool");
    assert_eq!(pos_out.sort().bitvec_width(), Some(32));
}

#[test]
fn test_adapter_pos_lt_len_pos_narrower() {
    // pos is BV16, len is BV32 — should normalize to BV32
    let pos = Expr::var("pos", Sort::bitvec(16));
    let len = Expr::var("len", Sort::bitvec(32));
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "narrow pos should be coerced to wider width");
    let (has_remaining, pos_out) = result.unwrap();
    assert!(has_remaining.sort().is_bool());
    assert_eq!(pos_out.sort().bitvec_width(), Some(32));
}

#[test]
fn test_adapter_pos_lt_len_len_narrower() {
    // pos is BV64, len is BV32 — should normalize to BV64
    let pos = Expr::var("pos", Sort::bitvec(64));
    let len = Expr::var("len", Sort::bitvec(32));
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "narrow len should be coerced to wider width");
    let (has_remaining, pos_out) = result.unwrap();
    assert!(has_remaining.sort().is_bool());
    assert_eq!(pos_out.sort().bitvec_width(), Some(64));
}

#[test]
fn test_adapter_pos_lt_len_non_bitvec_returns_none() {
    let pos = Expr::var("pos", Sort::int());
    let len = Expr::var("len", Sort::int());
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_none(), "Int sorts should not have bitvec_width");
}

#[test]
fn test_adapter_pos_lt_len_bv8() {
    let pos = Expr::var("pos", Sort::bitvec(8));
    let len = Expr::var("len", Sort::bitvec(8));
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some());
    let (_, pos_out) = result.unwrap();
    assert_eq!(pos_out.sort().bitvec_width(), Some(8));
}

#[test]
fn test_adapter_pos_lt_len_signed_uses_signed_comparison() {
    let pos = Expr::var("pos", Sort::bitvec(32));
    let len = Expr::var("len", Sort::bitvec(32));
    let result = ChcCtx::adapter_pos_lt_len_with_signedness(pos, len, true);
    assert!(result.is_some(), "signed comparison should be supported for bitvectors");
    let (has_remaining, _) = result.unwrap();
    assert!(
        matches!(has_remaining.value(), ExprValue::BvSLt(_, _)),
        "signed range comparison should use bvslt, got {:?}",
        has_remaining.value()
    );
}

// =============================================================================
// adapter_option_payload_sort — Option payload extraction
// =============================================================================

#[test]
fn test_adapter_option_payload_sort_enum_option() {
    // Standard enum-encoded Option: constructors Some(payload), None
    let option_sort = option_datatype_sort(Sort::bitvec(32));
    let result = ChcCtx::adapter_option_payload_sort(&option_sort);
    assert!(result.is_some(), "enum-encoded Option should yield payload sort");
    let payload = result.unwrap();
    assert!(payload.is_bitvec());
    assert_eq!(payload.bitvec_width(), Some(32));
}

#[test]
fn test_adapter_option_payload_sort_struct_encoding() {
    // Struct-encoded Option: single constructor with (is_some: Bool, value: T)
    let struct_sort =
        struct_sort("FlatOption_u64", [("is_some", Sort::bool()), ("value", Sort::bitvec(64))]);
    let result = ChcCtx::adapter_option_payload_sort(&struct_sort);
    assert!(result.is_some(), "struct-encoded Option should yield payload sort");
    let payload = result.unwrap();
    assert_eq!(payload.bitvec_width(), Some(64));
}

#[test]
fn test_adapter_option_payload_sort_non_option_returns_none() {
    // A plain struct that doesn't look like Option (no is_some field, no enum variant)
    let plain_sort = struct_sort("Point", [("x", Sort::bitvec(32)), ("y", Sort::bitvec(32))]);
    let result = ChcCtx::adapter_option_payload_sort(&plain_sort);
    assert!(result.is_none(), "non-Option struct should return None");
}

#[test]
fn test_adapter_option_payload_sort_bitvec_returns_none() {
    let result = ChcCtx::adapter_option_payload_sort(&Sort::bitvec(32));
    assert!(result.is_none(), "BV sort is not an Option");
}

// =============================================================================
// fresh_adapter_symbol — symbolic variable generation
// =============================================================================

const ADAPTER_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn adapter_probe(x: u32) -> u32 { x }
"#;

#[test]
fn test_fresh_adapter_symbol_produces_unique_names() {
    with_test_ay_ctx_for_source(ADAPTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "adapter_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "adapter_probe", ChcConfig::default());

        let sym1 = chc_ctx.fresh_adapter_symbol("test_sym", Sort::bitvec(32));
        let sym2 = chc_ctx.fresh_adapter_symbol("test_sym", Sort::bitvec(32));

        assert_ne!(
            sym1.to_string(),
            sym2.to_string(),
            "successive symbols should have different names"
        );
        assert!(sym1.sort().is_bitvec());
        assert!(sym2.sort().is_bitvec());
    });
}

#[test]
fn test_fresh_adapter_symbol_preserves_sort() {
    with_test_ay_ctx_for_source(ADAPTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "adapter_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "adapter_probe", ChcConfig::default());

        let bool_sym = chc_ctx.fresh_adapter_symbol("filter_keep", Sort::bool());
        assert!(bool_sym.sort().is_bool(), "Bool sort should be preserved");

        let int_sym = chc_ctx.fresh_adapter_symbol("fold_acc", Sort::int());
        assert!(int_sym.sort().is_int(), "Int sort should be preserved");
    });
}

// =============================================================================
// rebuild_datatype_with_field — field replacement on datatype exprs
// =============================================================================

#[test]
fn test_rebuild_datatype_with_field_replaces_named_field() {
    with_test_ay_ctx_for_source(ADAPTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "adapter_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "adapter_probe", ChcConfig::default());

        let iter_sort = struct_sort(
            "VecIter_u32",
            [("fld_pos", Sort::bitvec(64)), ("fld_len", Sort::bitvec(64))],
        );

        let base = Expr::var("iter_state", iter_sort.clone());
        let new_pos = Expr::bitvec_const(42u64, 64);

        let rebuilt = chc_ctx.rebuild_datatype_with_field(&base, "fld_pos", new_pos);
        assert!(rebuilt.is_some(), "rebuild should succeed for a valid field name");
        let rebuilt_expr = rebuilt.unwrap();
        assert_eq!(
            rebuilt_expr.sort(),
            &iter_sort,
            "rebuilt expr should have the same sort as the original"
        );
    });
}

#[test]
fn test_rebuild_datatype_with_field_nonexistent_field() {
    with_test_ay_ctx_for_source(ADAPTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "adapter_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "adapter_probe", ChcConfig::default());

        let dt_sort = struct_sort("Simple", [("fld_x", Sort::bitvec(32))]);

        let base = Expr::var("s", dt_sort);
        let replacement = Expr::bitvec_const(0u64, 32);

        // "nonexistent" doesn't match any field — all fields pass through unchanged
        let rebuilt = chc_ctx.rebuild_datatype_with_field(&base, "nonexistent", replacement);
        assert!(rebuilt.is_some(), "rebuild with non-matching field still constructs");
    });
}

#[test]
fn test_rebuild_datatype_non_datatype_sort_returns_none() {
    with_test_ay_ctx_for_source(ADAPTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "adapter_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "adapter_probe", ChcConfig::default());

        let non_dt = Expr::var("x", Sort::bitvec(32));
        let replacement = Expr::bitvec_const(0u64, 32);
        let result = chc_ctx.rebuild_datatype_with_field(&non_dt, "fld_pos", replacement);
        assert!(result.is_none(), "non-datatype sort should return None");
    });
}

// =============================================================================
// advance_range_iterator_expr — flattened Range path
// =============================================================================

const RANGE_ADVANCE_UNSIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_unsigned_range_advance(n: u32) -> u32 {
        let r = 0u32..n;
        r.start
    }
"#;

const RANGE_ADVANCE_SIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_signed_range_advance(n: i32) -> i32 {
        let r = -2i32..n;
        r.start
    }
"#;

fn find_range_local(body: &rustc_public::mir::Body) -> usize {
    body.local_decls()
        .find_map(|(local_idx, local_decl)| match local_decl.ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Range" => {
                Some(local_idx)
            }
            _ => None, // external enum: TyKind
        })
        .expect("expected at least one Range local in MIR")
}

fn range_spec_next_path_counts()
-> super::super::codegen_call_iterator_adapter::RangeSpecNextPathCounts {
    super::super::codegen_call_iterator_adapter::get_range_spec_next_path_counts()
}

/// Range fields use native BV sorts. The flattened path should use bvult for
/// unsigned comparison, matching the element type's bitvector width.
#[test]
fn test_advance_range_iterator_expr_flattened_unsigned_uses_bvult() {
    with_test_ay_ctx_for_source(RANGE_ADVANCE_UNSIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned_range_advance");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_unsigned_range_advance", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let range_local = find_range_local(&body);
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&range_local),
            "Range local should be flattened"
        );
        let modified_locals: HashSet<usize> = HashSet::new();
        let iter_expr = Expr::var("dummy_iter", Sort::bitvec(32));
        let before_counts = range_spec_next_path_counts();

        let result =
            chc_ctx.advance_range_iterator_expr(&iter_expr, Some(range_local), &modified_locals);
        assert!(result.is_some(), "flattened unsigned Range advancement should succeed");
        let (_next_start, has_remaining, current_item) = result.unwrap();
        assert!(
            matches!(has_remaining.value(), ExprValue::BvULt(_, _)),
            "unsigned Range comparison should use bvult, got {:?}",
            has_remaining.value()
        );
        assert!(current_item.sort().is_bitvec(), "current item for Range<u32> should be BV");
        let after_counts = range_spec_next_path_counts();
        assert!(
            after_counts.flattened > before_counts.flattened,
            "flattened path telemetry should increment: before={before_counts:?}, after={after_counts:?}"
        );
    });
}

/// Signed Range types use bvslt for flattened field comparison, preserving
/// correct signed ordering for negative range bounds.
#[test]
fn test_advance_range_iterator_expr_flattened_signed_uses_bvslt() {
    with_test_ay_ctx_for_source(RANGE_ADVANCE_SIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed_range_advance");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_signed_range_advance", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let range_local = find_range_local(&body);
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&range_local),
            "Range local should be flattened"
        );
        let modified_locals: HashSet<usize> = HashSet::new();
        let iter_expr = Expr::var("dummy_iter", Sort::bitvec(32));
        let before_counts = range_spec_next_path_counts();

        let result =
            chc_ctx.advance_range_iterator_expr(&iter_expr, Some(range_local), &modified_locals);
        assert!(result.is_some(), "flattened signed Range advancement should succeed");
        let (_next_start, has_remaining, current_item) = result.unwrap();
        assert!(
            matches!(has_remaining.value(), ExprValue::BvSLt(_, _)),
            "signed Range comparison should use bvslt, got {:?}",
            has_remaining.value()
        );
        assert!(current_item.sort().is_bitvec(), "current item for Range<i32> should be BV");
        let after_counts = range_spec_next_path_counts();
        assert!(
            after_counts.flattened > before_counts.flattened,
            "flattened path telemetry should increment: before={before_counts:?}, after={after_counts:?}"
        );
    });
}

/// When iter_local is None, signedness fallback should use the centralized
/// signedness_fallback() (comparison kind → signed) instead of hardcoded false.
/// This ensures signed ranges like (-5i32..5i32) use bvslt, not bvult.
/// Part of #2842.
#[test]
fn test_advance_range_iterator_expr_none_local_uses_signed_fallback() {
    with_test_ay_ctx_for_source(RANGE_ADVANCE_UNSIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned_range_advance");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_unsigned_range_advance", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified_locals: HashSet<usize> = HashSet::new();
        // Build a datatype Range expression so the datatype path is taken
        let start_sort = Sort::bitvec(32);
        let range_sort = enum_sort(
            "Range_bv32",
            [(
                "Range_bv32_ctor",
                vec![("fld_start", start_sort.clone()), ("fld_end", start_sort.clone())],
            )],
        );
        let iter_expr = Expr::datatype_constructor(
            "Range_bv32",
            "Range_bv32_ctor",
            vec![Expr::var("start_val", start_sort.clone()), Expr::var("end_val", start_sort)],
            range_sort,
        );
        let before_counts = range_spec_next_path_counts();

        // Pass None for iter_local to trigger fallback
        let result = chc_ctx.advance_range_iterator_expr(&iter_expr, None, &modified_locals);
        assert!(result.is_some(), "datatype Range advancement with None local should succeed");
        let (_next, has_remaining, _current) = result.unwrap();
        // With centralized fallback (comparison kind), default is signed → bvslt
        assert!(
            matches!(has_remaining.value(), ExprValue::BvSLt(_, _)),
            "Range comparison with unknown signedness should use signed (bvslt) fallback, got {:?}",
            has_remaining.value()
        );
        let after_counts = range_spec_next_path_counts();
        assert!(
            after_counts.datatype > before_counts.datatype,
            "datatype path telemetry should increment: before={before_counts:?}, after={after_counts:?}"
        );
    });
}

// =============================================================================
// codegen_call_iterator_adapter — RangeSpecNext fail-closed fallback
// =============================================================================

const RANGE_SPEC_NEXT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_range_spec_next(n: u32) -> Option<u32> {
        let r = 0u32..n;
        if r.start < r.end { Some(r.start) } else { None }
    }
"#;

#[test]
fn test_range_spec_next_modeling_failure_emits_error_rule_without_symbolic_fallback() {
    with_test_ay_ctx_for_source(RANGE_SPEC_NEXT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_spec_next");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_range_spec_next", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_bb = 0;
        let target = 0;
        let destination = rustc_public::mir::Place { local: 0, projection: vec![] };
        let from_rel =
            chc_ctx.block_relations.get(&from_bb).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        let before_rules = chc_ctx.vc.rules.len();
        let before_counts = range_spec_next_path_counts();

        // Force RangeSpecNext modeling failure: omit receiver args.
        let empty_args: Vec<rustc_public::mir::Operand> = Vec::new();
        let cx = ChcCallContext {
            stub: StubKind::RangeSpecNext,
            args: &empty_args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_iterator_adapter(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        let rule = chc_ctx.vc.rules.last().expect("RangeSpecNext should emit one fallback rule");
        assert_eq!(rule.head.name, "error", "RangeSpecNext fallback must be fail-closed");
        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "fail-closed error rule should preserve statement constraints"
        );
        assert!(
            !rule.body.constraints.iter().any(|c| c.to_string().contains("iter_adapter_result")),
            "RangeSpecNext fallback must not emit symbolic iter_adapter_result assignment"
        );

        let after_counts = range_spec_next_path_counts();
        assert!(
            after_counts.fail_closed > before_counts.fail_closed,
            "RangeSpecNext fail-closed telemetry should increment: before={before_counts:?}, after={after_counts:?}"
        );
    });
}

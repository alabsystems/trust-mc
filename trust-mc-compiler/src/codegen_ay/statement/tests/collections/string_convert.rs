// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for collections/string_convert.rs: String equality and conversion stubs.
//!
//! Covers codegen_string_convert_stub paths for:
//! - StringEq: quantified content comparison (forall i. i < len => l[i] == r[i])
//! - CowToString: pass-through/symbolic string
//! - DisplayToString: symbolic string creation
//! - FmtFormat: symbolic string creation
//! - create_symbolic_string: helper for symbolic String values
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use crate::codegen_ay::names::RUST_STRING_SORT;
use crate::codegen_ay::stubs::StubKind;
use std::sync::Arc;

fn with_string_codegen<F>(callback: F)
where
    F: FnOnce(&mut StatementCodegen<'_, '_, '_>) + Send,
{
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        callback(&mut codegen);
    });
}

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

fn make_test_string(codegen: &mut StatementCodegen<'_, '_, '_>, prefix: &str) -> Expr {
    codegen.create_symbolic_string(prefix)
}

// =============================================================================
// create_symbolic_string — unit tests
// =============================================================================

/// Test create_symbolic_string produces a RustString datatype.
/// string_convert.rs: create_symbolic_string.
#[test]
fn test_create_symbolic_string_produces_rust_string_sort() {
    with_string_codegen(|codegen| {
        let string = codegen.create_symbolic_string("test");
        assert!(string.sort().is_datatype());
        assert_eq!(
            string.sort().datatype_name(),
            Some(RUST_STRING_SORT),
            "create_symbolic_string should produce RustString datatype"
        );
    });
}

/// Test create_symbolic_string emits cap >= len constraint.
/// string_convert.rs: create_symbolic_string (constraint assertion).
#[test]
fn test_create_symbolic_string_emits_cap_ge_len_constraint() {
    with_string_codegen(|codegen| {
        let before = codegen.ctx.bmc_vc.constraints.len();
        let _string = codegen.create_symbolic_string("cap_test");
        let after = codegen.ctx.bmc_vc.constraints.len();
        assert!(
            after > before,
            "create_symbolic_string should emit at least one constraint (cap >= len)"
        );
    });
}

// =============================================================================
// StringEq — MIR-driven tests
// =============================================================================

/// Test StringEq with two seeded String operands produces boolean result.
/// string_convert.rs: StringEq branch — quantified content comparison.
#[test]
fn test_codegen_string_eq_with_two_strings_produces_bool() {
    with_string_codegen(|codegen| {
        let lhs_string = make_test_string(codegen, "eq_lhs");
        let rhs_string = make_test_string(codegen, "eq_rhs");

        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());

        // Seed strings in env and set up references
        let lhs_base = format!("{}::local_2", fn_name);
        codegen.env_update(lhs_base.clone(), lhs_string);
        let rhs_base = format!("{}::local_3", fn_name);
        codegen.env_update(rhs_base.clone(), rhs_string);

        // Set up ref_pointees so get_map_base_from_ref resolves
        let lhs_ref_base = format!("{}::local_4", fn_name);
        let rhs_ref_base = format!("{}::local_5", fn_name);
        codegen.env_update(lhs_ref_base.clone(), Expr::bitvec_const(0x100u64, POINTER_WIDTH));
        codegen.env_update(rhs_ref_base.clone(), Expr::bitvec_const(0x200u64, POINTER_WIDTH));
        codegen.ref_pointees.insert(Arc::from(lhs_ref_base), Arc::from(lhs_base));
        codegen.ref_pointees.insert(Arc::from(rhs_ref_base), Arc::from(rhs_base));

        let lhs_op = Operand::Copy(Place { local: 4, projection: vec![] });
        let rhs_op = Operand::Copy(Place { local: 5, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_string_stub(
            StubKind::StringEq,
            &[lhs_op, rhs_op],
            &dest,
            Some(1),
            "core::cmp::PartialEq::eq",
        );
        assert_eq!(result, Some(1));

        let dest_expr =
            assigned_expr_for_place(codegen, &dest).expect("StringEq should assign destination");
        assert!(
            dest_expr.sort().is_bool(),
            "StringEq should produce Bool sort, got {:?}",
            dest_expr.sort()
        );
    });
}

/// Test StringEq with insufficient args returns None (fail-closed #2497).
/// string_convert.rs: StringEq branch — fail-closed path.
#[test]
fn test_codegen_string_eq_insufficient_args_symbolic_fallback() {
    with_string_codegen(|codegen| {
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::StringEq,
            &[],
            &dest,
            Some(2),
            "core::cmp::PartialEq::eq",
        );
        assert_eq!(result, None, "StringEq with insufficient args must fail-closed (#2497)");
        assert!(
            assigned_expr_for_place(codegen, &dest).is_none(),
            "StringEq fail-closed path should not assign destination"
        );
    });
}

// =============================================================================
// CowToString — MIR-driven tests
// =============================================================================

/// Test CowToString with seeded Cow (modeled as String) passes through.
/// string_convert.rs: CowToString branch — pass-through path.
#[test]
fn test_codegen_cow_to_string_with_ref_passes_through() {
    with_string_codegen(|codegen| {
        let cow_string = make_test_string(codegen, "cow");

        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let cow_base = format!("{}::local_2", fn_name);
        codegen.env_update(cow_base.clone(), cow_string);

        let ref_base = format!("{}::local_1", fn_name);
        codegen.env_update(ref_base.clone(), Expr::bitvec_const(0x300u64, POINTER_WIDTH));
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(cow_base));

        let ref_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_string_stub(
            StubKind::CowToString,
            &[ref_op],
            &dest,
            Some(3),
            "<Cow<str> as ToString>::to_string",
        );
        assert_eq!(result, Some(3));

        let dest_expr =
            assigned_expr_for_place(codegen, &dest).expect("CowToString should assign destination");
        assert_eq!(
            dest_expr.sort().datatype_name(),
            Some(RUST_STRING_SORT),
            "CowToString should produce RustString sort"
        );
    });
}

/// Test CowToString with empty args returns None (fail-closed #2497).
/// string_convert.rs: CowToString branch — fail-closed path.
#[test]
fn test_codegen_cow_to_string_empty_args_symbolic() {
    with_string_codegen(|codegen| {
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::CowToString,
            &[],
            &dest,
            Some(4),
            "<Cow<str> as ToString>::to_string",
        );
        assert_eq!(result, None, "CowToString with empty args must fail-closed (#2497)");
        assert!(
            assigned_expr_for_place(codegen, &dest).is_none(),
            "CowToString fail-closed path should not assign destination"
        );
    });
}

// =============================================================================
// DisplayToString — MIR-driven tests
// =============================================================================

/// Test DisplayToString with empty args returns None (fail-closed #2497).
/// string_convert.rs: DisplayToString requires 1 arg (self).
#[test]
fn test_codegen_display_to_string_empty_args_fail_closed() {
    with_string_codegen(|codegen| {
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::DisplayToString,
            &[],
            &dest,
            Some(5),
            "<u32 as ToString>::to_string",
        );
        assert_eq!(result, None, "DisplayToString with empty args must fail-closed (#2497)");
    });
}

// =============================================================================
// FmtFormat — MIR-driven tests
// =============================================================================

/// Test FmtFormat produces symbolic RustString.
/// string_convert.rs: FmtFormat branch.
#[test]
fn test_codegen_fmt_format_produces_symbolic_string() {
    with_string_codegen(|codegen| {
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_string_stub(
            StubKind::FmtFormat,
            &[],
            &dest,
            Some(6),
            "std::fmt::format",
        );
        assert_eq!(result, Some(6));

        let dest_expr =
            assigned_expr_for_place(codegen, &dest).expect("FmtFormat should assign destination");
        assert_eq!(
            dest_expr.sort().datatype_name(),
            Some(RUST_STRING_SORT),
            "FmtFormat should produce RustString sort"
        );
    });
}

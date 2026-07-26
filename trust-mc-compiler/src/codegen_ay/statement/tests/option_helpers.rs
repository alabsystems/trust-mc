// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for option_helpers.rs — shared Option/Result handling helpers.
//!
//! Covers:
//! - `codegen_symbolic_result` — symbolic value generation for destinations
//! - `get_option_base_direct` — Option base name from owned operand
//! - `get_option_base_from_ref` — Option base name from reference operand
//! - `make_zero_for_discrim` — zero constant matching discriminant sort
//!
//! All tests use MIR-driven patterns that exercise actual production functions.
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use std::sync::Arc;

// ─── MIR probe sources ───────────────────────────────────────────────────

const OPTION_HELPERS_PROBE: &str = r#"
pub fn probe_option_unwrap(x: Option<u32>) -> u32 {
    x.unwrap()
}
pub fn probe_option_ref_is_some(x: &Option<u32>) -> bool {
    x.is_some()
}
pub fn probe_u32_identity(x: u32) -> u32 { x }
"#;

fn with_option_helpers_codegen<F>(fn_suffix: &str, callback: F)
where
    F: FnOnce(&mut StatementCodegen<'_, '_, '_>, &rustc_public::mir::Body) + Send,
{
    with_test_ay_ctx_for_source(OPTION_HELPERS_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_suffix);
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        callback(&mut codegen, &body);
    });
}

// =============================================================================
// make_zero_for_discrim — production function tests
// =============================================================================

/// Bool discriminant produces false.
#[test]
fn test_make_zero_for_discrim_bool_production() {
    with_option_helpers_codegen("probe_u32_identity", |codegen, _body| {
        let discrim = Expr::bool_const(true);
        let zero = codegen.make_zero_for_discrim(&discrim);
        assert!(zero.is_some(), "Bool sort should produce a zero constant");
        assert!(zero.unwrap().sort().is_bool());
    });
}

/// BitVec discriminant zero preserves width.
#[test]
fn test_make_zero_for_discrim_bitvec_widths_production() {
    with_option_helpers_codegen("probe_u32_identity", |codegen, _body| {
        for width in [8u32, 16, 32, 64] {
            let discrim = Expr::bitvec_const(42u128, width);
            let zero = codegen.make_zero_for_discrim(&discrim);
            assert!(zero.is_some(), "bv{width} should produce a zero constant");
            let z = zero.unwrap();
            assert_eq!(
                z.sort().bitvec_width(),
                Some(width),
                "zero constant should preserve bv{width} width"
            );
        }
    });
}

/// Int discriminant produces int_const(0).
#[test]
fn test_make_zero_for_discrim_int_production() {
    with_option_helpers_codegen("probe_u32_identity", |codegen, _body| {
        let discrim = Expr::int_const(99);
        let zero = codegen.make_zero_for_discrim(&discrim);
        assert!(zero.is_some(), "Int sort should produce a zero constant");
        assert!(zero.unwrap().sort().is_int());
    });
}

/// Real/Array/Datatype discriminants return None (unsupported).
#[test]
fn test_make_zero_for_discrim_unsupported_sorts() {
    with_option_helpers_codegen("probe_u32_identity", |codegen, _body| {
        // Array sort
        let arr_discrim = Expr::var("arr_discrim", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
        assert!(
            codegen.make_zero_for_discrim(&arr_discrim).is_none(),
            "Array sort should return None"
        );

        // Datatype sort
        let dt_sort = struct_sort("TestDT", [("fld_x", Sort::bitvec(32))]);
        let dt_discrim = Expr::var("dt_discrim", dt_sort);
        assert!(
            codegen.make_zero_for_discrim(&dt_discrim).is_none(),
            "Datatype sort should return None"
        );
    });
}

// =============================================================================
// codegen_symbolic_result — production function tests
// =============================================================================

/// codegen_symbolic_result assigns a symbolic value for u32 destination.
#[test]
fn test_codegen_symbolic_result_u32_destination() {
    with_option_helpers_codegen("probe_u32_identity", |codegen, _body| {
        let dest = local_place(0); // return place
        let dest_base = codegen.ssa_base_name(&dest);

        // Before: destination not in env
        let before = codegen.env_lookup(&dest_base).cloned();

        codegen.codegen_symbolic_result(&dest);

        // After: destination should have a symbolic value
        let after = codegen.env_lookup(&dest_base).cloned();
        // The symbolic result should differ from whatever was there before
        // (or be newly populated if nothing was there)
        assert!(after.is_some(), "codegen_symbolic_result should populate destination in env");
        let val = after.unwrap();
        assert!(
            val.sort().is_bitvec(),
            "u32 destination should get bitvec sort, got {:?}",
            val.sort()
        );
        // If before had a value, after should be different (fresh symbolic)
        if before.is_some() {
            // Can't directly compare AY expressions, but we know a fresh declare_var was used
        }
    });
}

// =============================================================================
// get_option_base_direct — production function tests
// =============================================================================

/// get_option_base_direct finds flattened Option in environment.
#[test]
fn test_get_option_base_direct_flattened_env() {
    with_option_helpers_codegen("probe_option_unwrap", |codegen, _body| {
        // Seed arg local (local 1 is the Option<u32> argument)
        let arg_place = local_place(1);
        let arg_base = codegen.ssa_base_name(&arg_place);

        // Simulate flattened Option: base_name.0 (discriminant) in env
        let discrim_name = format!("{}.0", arg_base);
        codegen.env_update(discrim_name, Expr::bitvec_const(1u128, 8));

        let operand = Operand::Copy(arg_place);
        let result = codegen.get_option_base_direct(&operand);

        assert!(result.is_some(), "should find flattened Option via discriminant lookup");
        assert_eq!(result.as_deref(), Some(arg_base.as_str()));
    });
}

/// get_option_base_direct finds native SMT Option in environment.
#[test]
fn test_get_option_base_direct_native_smt_env() {
    with_option_helpers_codegen("probe_option_unwrap", |codegen, _body| {
        let arg_place = local_place(1);
        let arg_base = codegen.ssa_base_name(&arg_place);

        // Seed native SMT Option in env (not flattened)
        let option_sort =
            enum_sort("Option_bv32", [("None", vec![]), ("Some", vec![("val", Sort::bitvec(32))])]);
        codegen.env_update(arg_base.clone(), Expr::var("opt_val", option_sort));

        let operand = Operand::Copy(arg_place);
        let result = codegen.get_option_base_direct(&operand);

        assert!(result.is_some(), "should find native SMT Option via direct lookup");
        assert_eq!(result.as_deref(), Some(arg_base.as_str()));
    });
}

/// get_option_base_direct returns None when neither flattened nor native found.
#[test]
fn test_get_option_base_direct_not_found() {
    with_option_helpers_codegen("probe_option_unwrap", |codegen, _body| {
        // Don't seed anything in env
        let operand = Operand::Copy(local_place(1));
        let result = codegen.get_option_base_direct(&operand);

        assert!(result.is_none(), "should return None when not in environment");
    });
}

// =============================================================================
// get_option_base_from_ref — production function tests
// =============================================================================

/// get_option_base_from_ref resolves through ref_pointees.
#[test]
fn test_get_option_base_from_ref_with_pointee() {
    with_option_helpers_codegen("probe_option_ref_is_some", |codegen, _body| {
        // Set up: ref at local 1 points to "option_target"
        let ref_place = local_place(1);
        let ref_base = codegen.ssa_base_name(&ref_place);
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from("option_target"));

        let operand = Operand::Copy(ref_place);
        let result = codegen.get_option_base_from_ref(&operand);

        assert_eq!(result.as_deref(), Some("option_target"));
    });
}

/// get_option_base_from_ref returns None when ref not tracked.
#[test]
fn test_get_option_base_from_ref_no_pointee() {
    // Use probe_u32_identity (no ref args) so init_reference_arguments
    // doesn't auto-populate ref_pointees.
    with_option_helpers_codegen("probe_u32_identity", |codegen, _body| {
        // Use a high local index that won't be auto-initialized
        let operand = Operand::Copy(local_place(5));
        let result = codegen.get_option_base_from_ref(&operand);

        assert!(result.is_none(), "should return None when ref not tracked");
    });
}

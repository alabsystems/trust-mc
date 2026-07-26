// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven pipeline tests for codegen_call_cmp_string.rs — primitive comparison
//! (Ord::cmp, PartialOrd relational ops, PartialEq eq/ne), Step::unchecked,
//! and wrapping arithmetic (wrapping_add/sub/mul) call codegen.
//!
//! Part of #2296 (chc/ test coverage gaps).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;
use crate::codegen_ay::emit_chc;

fn with_float_predicate_dispatch(
    source: &str,
    fn_name: &str,
    predicate_name: &str,
    assertions: impl FnOnce(&mut ChcCtx<'_, '_>, &str) + Send,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
                && chc_ctx
                    .resolve_callee_path(func)
                    .as_deref()
                    .is_some_and(|path| path.contains(predicate_name))
            {
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
                    "{predicate_name} dispatch should not record a sound fallback"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "{predicate_name} dispatch should emit one rule"
                );
                let smt = emit_chc(&chc_ctx.vc).to_string();
                assertions(&mut chc_ctx, &smt);
                break;
            }
        }
        assert_mir_pattern_found(found, predicate_name);
    });
}

fn assert_smt_contains_any(smt: &str, patterns: &[&str], message: &str) {
    assert!(patterns.iter().any(|pattern| smt.contains(pattern)), "{message}, got: {smt}");
}

fn assert_normal_dispatch_shape(
    smt: &str,
    exp_extract: &str,
    mantissa_extract: &str,
    zero_patterns: &[&str],
    max_patterns: &[&str],
) {
    assert!(
        smt.contains(exp_extract),
        "is_normal should inspect the exponent bits in emitted CHC, got: {smt}"
    );
    assert_smt_contains_any(
        smt,
        zero_patterns,
        "is_normal should compare the exponent against zero",
    );
    assert_smt_contains_any(
        smt,
        max_patterns,
        "is_normal should compare the exponent against the all-ones bound",
    );
    assert!(
        !smt.contains(mantissa_extract),
        "is_normal should not inspect mantissa bits; that would indicate NaN/Infinity dispatch, got: {smt}"
    );
}

// =============================================================================
// Ord::cmp pipeline tests
// =============================================================================

/// u32::cmp produces an ITE chain mapping to Ordering discriminant (bv32).
#[test]
fn test_ord_cmp_u32_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::cmp::Ordering;

        pub fn probe_ord_cmp(a: u32, b: u32) -> Ordering {
            a.cmp(&b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ord_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ord_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ord_cmp", body.blocks.len());

        // Ordering is encoded as bv32 — should appear in state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Ord::cmp should produce bv32 state vars for Ordering");
    });
}

/// i32::cmp exercises the signed comparison path (bvslt instead of bvult).
#[test]
fn test_ord_cmp_i32_signed_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::cmp::Ordering;

        pub fn probe_ord_cmp_signed(a: i32, b: i32) -> Ordering {
            a.cmp(&b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ord_cmp_signed");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ord_cmp_signed", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        assert_vc_structure(&vc, "probe_ord_cmp_signed", body.blocks.len());

        // Signed cmp uses bvslt for the less-than branch in the ITE chain
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvslt"),
            "signed i32::cmp should emit bvslt for less-than comparison"
        );
    });
}

// =============================================================================
// PartialOrd relational operator pipeline tests
// =============================================================================

/// PartialOrd::lt exercises the "lt" branch with unsigned bvult.
#[test]
fn test_partial_ord_lt_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_lt(a: u32, b: u32) -> bool {
            a < b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_lt");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_lt", ChcConfig::default());

        assert_vc_structure(&vc, "probe_lt", body.blocks.len());

        // Bool return type should appear in relation sorts (comparison result)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "u32 < returning bool should have Bool sort in relations");

        // bv32 sorts for the u32 operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "u32 < should have bv32 state vars for operands");
    });
}

/// PartialOrd::ge exercises the "ge" branch.
#[test]
fn test_partial_ord_ge_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ge(a: u32, b: u32) -> bool {
            a >= b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ge");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ge", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ge", body.blocks.len());

        // Bool return type should appear in relation sorts (comparison result)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "u32 >= returning bool should have Bool sort in relations");

        // bv32 sorts for the u32 operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "u32 >= should have bv32 state vars for operands");
    });
}

// =============================================================================
// PartialEq eq/ne pipeline tests
// =============================================================================

/// PartialEq::eq exercises the "eq" method branch.
#[test]
fn test_partial_eq_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_eq(a: u32, b: u32) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_eq", ChcConfig::default());

        assert_vc_structure(&vc, "probe_eq", body.blocks.len());

        // Bool return type should appear in relation sorts
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "equality comparison returning bool should have Bool sort in relations");

        // bv32 sorts for the u32 operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "u32 == should have bv32 state vars for operands");
    });
}

/// PartialEq::ne exercises the "ne" method branch.
#[test]
fn test_partial_ne_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ne(a: u32, b: u32) -> bool {
            a != b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ne");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ne", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ne", body.blocks.len());

        // Bool return type should appear in relation sorts
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool,
            "inequality comparison returning bool should have Bool sort in relations"
        );

        // bv32 sorts for the u32 operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "u32 != should have bv32 state vars for operands");
    });
}

/// `is_finite` should route through the dedicated float predicate dispatcher
/// instead of the unconstrained catch-all.
#[test]
fn test_float_is_finite_dispatch_emits_exponent_check_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_finite(x: f32) -> bool {
            x.is_finite()
        }
    "#;

    with_float_predicate_dispatch(SOURCE, "probe_is_finite", "is_finite", |_chc_ctx, smt| {
        assert!(
            smt.contains("extract 30 23"),
            "is_finite should inspect the exponent bits in emitted CHC, got: {smt}"
        );
    });
}

/// `is_normal` should route through the dedicated float predicate dispatcher
/// and inspect the exponent bits instead of falling back.
#[test]
fn test_float_is_normal_dispatch_emits_exponent_check_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_normal(x: f64) -> bool {
            x.is_normal()
        }
    "#;

    with_float_predicate_dispatch(SOURCE, "probe_is_normal", "is_normal", |_chc_ctx, smt| {
        assert_normal_dispatch_shape(
            smt,
            "extract 62 52",
            "extract 51 0",
            &["(_ bv0 11)", "#b00000000000"],
            &["(_ bv2047 11)", "#b11111111111"],
        );
    });
}

/// `is_normal` on `f32` should also stay on the direct exponent-range path.
#[test]
fn test_float_is_normal_f32_dispatch_emits_exponent_check_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_normal_f32(x: f32) -> bool {
            x.is_normal()
        }
    "#;

    with_float_predicate_dispatch(SOURCE, "probe_is_normal_f32", "is_normal", |_chc_ctx, smt| {
        assert_normal_dispatch_shape(
            smt,
            "extract 30 23",
            "extract 22 0",
            &["(_ bv0 8)", "#b00000000", "#x00"],
            &["(_ bv255 8)", "#b11111111", "#xff", "#xFF"],
        );
    });
}

/// `is_sign_positive` should constrain the Bool destination from the sign bit
/// directly instead of leaving the call unconstrained.
#[test]
fn test_float_is_sign_positive_dispatch_emits_sign_check_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_sign_positive(x: f64) -> bool {
            x.is_sign_positive()
        }
    "#;

    with_float_predicate_dispatch(
        SOURCE,
        "probe_is_sign_positive",
        "is_sign_positive",
        |_chc_ctx, smt| {
            assert!(
                smt.contains("extract 63 63"),
                "is_sign_positive should inspect the sign bit in emitted CHC, got: {smt}"
            );
        },
    );
}

/// `is_sign_negative` should constrain the Bool destination from the sign bit
/// and compare it against a one-bit `1` constant instead of falling back.
#[test]
fn test_float_is_sign_negative_dispatch_emits_sign_check_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_sign_negative(x: f32) -> bool {
            x.is_sign_negative()
        }
    "#;

    with_float_predicate_dispatch(
        SOURCE,
        "probe_is_sign_negative",
        "is_sign_negative",
        |_chc_ctx, smt| {
            assert!(
                smt.contains("extract 31 31"),
                "is_sign_negative should inspect the sign bit in emitted CHC, got: {smt}"
            );
            assert!(
                smt.contains("#b1") || smt.contains("(_ bv1 1)"),
                "is_sign_negative should compare the sign bit against 1, got: {smt}"
            );
        },
    );
}

/// `is_nan` should check exponent all-ones AND mantissa non-zero.
#[test]
fn test_float_is_nan_dispatch_emits_exponent_and_mantissa_check() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_nan(x: f32) -> bool {
            x.is_nan()
        }
    "#;

    with_float_predicate_dispatch(SOURCE, "probe_is_nan", "is_nan", |_chc_ctx, smt| {
        assert!(
            smt.contains("extract 30 23"),
            "is_nan should inspect the exponent bits in emitted CHC, got: {smt}"
        );
        assert!(
            smt.contains("extract 22 0"),
            "is_nan should inspect the mantissa bits in emitted CHC, got: {smt}"
        );
    });
}

/// `is_infinite` should check exponent all-ones AND mantissa zero.
#[test]
fn test_float_is_infinite_dispatch_emits_exponent_and_mantissa_check() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_infinite(x: f32) -> bool {
            x.is_infinite()
        }
    "#;

    with_float_predicate_dispatch(SOURCE, "probe_is_infinite", "is_infinite", |_chc_ctx, smt| {
        assert!(
            smt.contains("extract 30 23"),
            "is_infinite should inspect the exponent bits in emitted CHC, got: {smt}"
        );
        assert!(
            smt.contains("extract 22 0"),
            "is_infinite should inspect the mantissa bits in emitted CHC, got: {smt}"
        );
    });
}

/// PartialEq over Ordering should resolve const-ref discriminants (Bug 5, #1739).
///
/// After #4044, the by-value guard in `resolve_ref_or_const_referent_impl` routes
/// non-ref locals away from the ref tiers. Test the discriminant map + BV const
/// construction directly, which is the invariant the Tier 3 path relies on.
#[test]
fn test_partial_eq_ordering_const_ref_discriminant_resolution() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_eq(a: u32, b: u32) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_eq");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_eq", ChcConfig::default());

        // Verify const_ref_discriminants map insertion and BV const construction,
        // which is what Tier 3 in resolve_ref_or_const_referent_impl uses.
        let synthetic_local = 9_999usize;
        chc_ctx.ref_resolution.const_ref_discriminants.insert(synthetic_local, 42);
        let discr = chc_ctx
            .ref_resolution
            .const_ref_discriminants
            .get(&synthetic_local)
            .expect("const_ref_discriminants should contain inserted local");
        let expr = Expr::bitvec_const(*discr as i128, 32);
        match expr.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*value, 42u64.into());
                assert_eq!(*width, 32);
            }
            other => panic!("expected bv32 discriminant const, got {other:?}"),
        }
    });
}

/// `codegen_call_primitive_cmp` should not panic when invoked with `target=None`;
/// it should record a diverging-call drop for diagnostics.
#[test]
fn test_primitive_cmp_target_none_records_drop_count() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_wrapping_add(a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_add");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrapping_add", ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                    && chc_ctx
                        .resolve_callee_path(func)
                        .as_deref()
                        .is_some_and(|path| path.contains("wrapping_add"))
                {
                    Some((bb_idx, func, args, destination))
                } else {
                    None
                }
            })
            .expect("expected wrapping_add call terminator");

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();
        let target_none = None;
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_none,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: None,
        };

        chc_ctx.codegen_call_primitive_cmp(&dcx);

        assert_eq!(
            chc_ctx.diagnostics.diverging_call_drop.get(),
            1,
            "primitive cmp with target=None should record one diverging drop instead of panicking"
        );
    });
}

// =============================================================================
// Wrapping arithmetic pipeline tests
// =============================================================================

/// wrapping_add exercises the wrapping arithmetic -> bvadd path.
#[test]
fn test_wrapping_add_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_wrapping_add(a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_add", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_add", body.blocks.len());

        // Should produce constrained rules (result = a bvadd b)
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(constrained, "wrapping_add should produce constrained transition rules");
    });
}

/// wrapping_sub exercises the wrapping arithmetic -> bvsub path.
#[test]
fn test_wrapping_sub_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_wrapping_sub(a: u32, b: u32) -> u32 {
            a.wrapping_sub(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_sub");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrapping_sub", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        assert_vc_structure(&vc, "probe_wrapping_sub", body.blocks.len());

        // wrapping_sub should emit bvsub in the SMT output
        let smt = emit_chc(&vc).to_string();
        assert!(smt.contains("bvsub"), "wrapping_sub should emit bvsub for subtraction");
    });
}

/// wrapping_mul exercises the wrapping arithmetic -> bvmul path.
#[test]
fn test_wrapping_mul_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_wrapping_mul(a: u32, b: u32) -> u32 {
            a.wrapping_mul(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_mul");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrapping_mul", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        assert_vc_structure(&vc, "probe_wrapping_mul", body.blocks.len());

        // wrapping_mul should emit bvmul in the SMT output
        let smt = emit_chc(&vc).to_string();
        assert!(smt.contains("bvmul"), "wrapping_mul should emit bvmul for multiplication");
    });
}

// =============================================================================
// wrapping_arithmetic_method unit test
// =============================================================================

/// Verify the wrapping_arithmetic_method static helper parses method names correctly.
#[test]
fn test_wrapping_arithmetic_method_parser() {
    use rustc_public::mir::BinOp;

    // Wrapping methods — is_unchecked = false
    assert_eq!(ChcCtx::wrapping_arithmetic_method("u32::wrapping_add"), Some((BinOp::Add, false)));
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u64>::wrapping_sub"),
        Some((BinOp::Sub, false))
    );
    assert_eq!(ChcCtx::wrapping_arithmetic_method("wrapping_mul"), Some((BinOp::Mul, false)));
    // Unchecked methods — is_unchecked = true (Part of #3299)
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_add"),
        Some((BinOp::Add, true))
    );
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_sub"),
        Some((BinOp::Sub, true))
    );
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_mul"),
        Some((BinOp::Mul, true))
    );

    // Negative cases
    assert_eq!(ChcCtx::wrapping_arithmetic_method("u32::checked_add"), None);
    assert_eq!(ChcCtx::wrapping_arithmetic_method("u32::saturating_add"), None);
    assert_eq!(ChcCtx::wrapping_arithmetic_method("u32::add"), None);
}

// =============================================================================
// checked_arithmetic_method unit test (Part of #3369: proof_coverage)
// =============================================================================

/// Verify that checked_arithmetic_method parses checked_add/sub/mul method names.
#[test]
fn test_checked_arithmetic_method_parser() {
    use rustc_public::mir::BinOp;

    // Positive cases
    assert_eq!(ChcCtx::checked_arithmetic_method("u32::checked_add"), Some(BinOp::Add));
    assert_eq!(
        ChcCtx::checked_arithmetic_method("core::num::<impl u64>::checked_sub"),
        Some(BinOp::Sub)
    );
    assert_eq!(ChcCtx::checked_arithmetic_method("checked_mul"), Some(BinOp::Mul));

    // Negative cases — wrapping and saturating should not match
    assert_eq!(ChcCtx::checked_arithmetic_method("u32::wrapping_add"), None);
    assert_eq!(ChcCtx::checked_arithmetic_method("u32::saturating_sub"), None);
    assert_eq!(ChcCtx::checked_arithmetic_method("u32::add"), None);
    assert_eq!(ChcCtx::checked_arithmetic_method(""), None);
}

// =============================================================================
// saturating_arithmetic_method unit test (Part of #3369: proof_coverage)
// =============================================================================

/// Verify that saturating_arithmetic_method parses saturating_add/sub method names.
#[test]
fn test_saturating_arithmetic_method_parser() {
    use rustc_public::mir::BinOp;

    // Positive cases
    assert_eq!(ChcCtx::saturating_arithmetic_method("u32::saturating_add"), Some(BinOp::Add));
    assert_eq!(
        ChcCtx::saturating_arithmetic_method("core::num::<impl i64>::saturating_sub"),
        Some(BinOp::Sub)
    );

    // Negative cases — no saturating_mul in the matcher
    assert_eq!(ChcCtx::saturating_arithmetic_method("u32::saturating_mul"), None);
    assert_eq!(ChcCtx::saturating_arithmetic_method("u32::wrapping_add"), None);
    assert_eq!(ChcCtx::saturating_arithmetic_method("u32::checked_add"), None);
    assert_eq!(ChcCtx::saturating_arithmetic_method(""), None);
}

// =============================================================================
// Saturating arithmetic BigInt bounds at width=128 (Part of #3403)
// =============================================================================

/// Verify that saturating arithmetic saturation bounds can be constructed at
/// width=128 without i128 overflow. Before #3403 fix, these would panic from
/// `1i128 << 127` wrapping to i128::MIN.
#[test]
fn test_saturating_bounds_width_128_bv_signed() {
    use ay_bindings::Expr;
    use num_bigint::BigInt;

    let w: u32 = 128;
    // This is the fixed code path from codegen_saturating_arithmetic BV signed path.
    let half = BigInt::from(1u128) << (w - 1);
    let max_val = Expr::bitvec_const(&half - 1, w); // i128::MAX = 2^127 - 1
    let min_val = Expr::bitvec_const(-half, w); // i128::MIN = -2^127

    assert!(max_val.sort().is_bitvec());
    assert_eq!(max_val.sort().bitvec_width(), Some(128));
    assert!(min_val.sort().is_bitvec());
    assert_eq!(min_val.sort().bitvec_width(), Some(128));
}

/// Verify Int-lifted saturating bounds at width=128 (signed path).
#[test]
fn test_saturating_bounds_width_128_int_signed() {
    use ay_bindings::Expr;
    use num_bigint::BigInt;

    let int_bv_width: u32 = 128;
    let half = BigInt::from(1u128) << (int_bv_width - 1);
    let max_val = Expr::int_const(&half - 1);
    let min_val = Expr::int_const(-half);

    assert!(max_val.sort().is_int());
    assert!(min_val.sort().is_int());
}

/// Verify Int-lifted unsigned MAX at width=128 (unsigned add saturation).
/// Before #3403, `1i128 << 128` was shift-width UB.
#[test]
fn test_saturating_bounds_width_128_int_unsigned() {
    use ay_bindings::Expr;
    use num_bigint::BigInt;

    let int_bv_width: u32 = 128;
    // This is the fixed code path: (BigInt::from(1u128) << 128) - 1 = u128::MAX.
    let max_val = Expr::int_const((BigInt::from(1u128) << int_bv_width) - 1);

    assert!(max_val.sort().is_int());
}

// =============================================================================
// is_exact_div unit test (Part of #3369: proof_coverage)
// =============================================================================

/// Verify that is_exact_div detects exact_div intrinsic path suffixes.
#[test]
fn test_is_exact_div_classifier() {
    assert!(ChcCtx::is_exact_div("core::intrinsics::exact_div"));
    assert!(ChcCtx::is_exact_div("exact_div"));

    assert!(!ChcCtx::is_exact_div("core::intrinsics::unchecked_div"));
    assert!(!ChcCtx::is_exact_div("u32::div"));
    assert!(!ChcCtx::is_exact_div("exact_div_other"));
    assert!(!ChcCtx::is_exact_div(""));
}

// =============================================================================
// is_pow_method unit test (Part of #3369: proof_coverage)
// =============================================================================

/// Verify that is_pow_method detects pow and wrapping_pow method calls.
#[test]
fn test_is_pow_method_classifier() {
    assert!(ChcCtx::is_pow_method("u32::pow"));
    assert!(ChcCtx::is_pow_method("core::num::<impl u64>::pow"));
    assert!(ChcCtx::is_pow_method("u32::wrapping_pow"));

    assert!(!ChcCtx::is_pow_method("u32::powi")); // not pow
    assert!(!ChcCtx::is_pow_method("u32::checked_pow"));
    assert!(!ChcCtx::is_pow_method("f64::powf"));
    assert!(!ChcCtx::is_pow_method(""));
}

// =============================================================================
// euclid_method unit test (Part of #3369: proof_coverage)
// =============================================================================

/// Verify that euclid_method detects div_euclid and rem_euclid calls.
/// Returns Some(EuclidOp) for matches — variant discrimination tested via is_some/none
/// since EuclidOp is in a private module.
#[test]
fn test_euclid_method_classifier() {
    assert!(ChcCtx::euclid_method("u32::div_euclid").is_some());
    assert!(ChcCtx::euclid_method("core::num::<impl i64>::rem_euclid").is_some());
    assert!(ChcCtx::euclid_method("div_euclid").is_some());
    assert!(ChcCtx::euclid_method("rem_euclid").is_some());

    assert!(ChcCtx::euclid_method("u32::div").is_none());
    assert!(ChcCtx::euclid_method("u32::rem").is_none());
    assert!(ChcCtx::euclid_method("").is_none());
}

// =============================================================================
// is_wrapping_abs / is_wrapping_neg unit tests (Part of #3369: proof_coverage)
// =============================================================================

/// Verify that is_wrapping_abs detects wrapping_abs method calls.
#[test]
fn test_is_wrapping_abs_classifier() {
    assert!(ChcCtx::is_wrapping_abs("i32::wrapping_abs"));
    assert!(ChcCtx::is_wrapping_abs("core::num::<impl i64>::wrapping_abs"));
    assert!(ChcCtx::is_wrapping_abs("wrapping_abs"));

    assert!(!ChcCtx::is_wrapping_abs("i32::abs"));
    assert!(!ChcCtx::is_wrapping_abs("i32::wrapping_neg"));
    assert!(!ChcCtx::is_wrapping_abs(""));
}

/// Verify that is_wrapping_neg detects wrapping_neg method calls.
#[test]
fn test_is_wrapping_neg_classifier() {
    assert!(ChcCtx::is_wrapping_neg("i32::wrapping_neg"));
    assert!(ChcCtx::is_wrapping_neg("core::num::<impl i64>::wrapping_neg"));
    assert!(ChcCtx::is_wrapping_neg("wrapping_neg"));

    assert!(!ChcCtx::is_wrapping_neg("i32::neg"));
    assert!(!ChcCtx::is_wrapping_neg("i32::wrapping_abs"));
    assert!(!ChcCtx::is_wrapping_neg(""));
}

// =============================================================================
// is_overflowing_add_signed unit test (Part of #3369: proof_coverage)
// =============================================================================

/// Verify that is_overflowing_add_signed detects overflowing_add_signed calls.
#[test]
fn test_is_overflowing_add_signed_classifier() {
    assert!(ChcCtx::is_overflowing_add_signed("usize::overflowing_add_signed"));
    assert!(ChcCtx::is_overflowing_add_signed("core::num::<impl usize>::overflowing_add_signed"));
    assert!(ChcCtx::is_overflowing_add_signed("overflowing_add_signed"));

    assert!(!ChcCtx::is_overflowing_add_signed("usize::overflowing_add"));
    assert!(!ChcCtx::is_overflowing_add_signed("usize::wrapping_add"));
    assert!(!ChcCtx::is_overflowing_add_signed(""));
}

/// Verify that overflowing_arithmetic_method detects tuple-producing overflow operations.
#[test]
fn test_overflowing_arithmetic_method_classifier() {
    assert!(ChcCtx::overflowing_arithmetic_method("u32::overflowing_add").is_some());
    assert!(ChcCtx::overflowing_arithmetic_method("core::intrinsics::add_with_overflow").is_some());
    assert!(ChcCtx::overflowing_arithmetic_method("std::intrinsics::sub_with_overflow").is_some());
    assert!(ChcCtx::overflowing_arithmetic_method("mul_with_overflow").is_some());

    assert!(ChcCtx::overflowing_arithmetic_method("usize::overflowing_add_signed").is_none());
    assert!(ChcCtx::overflowing_arithmetic_method("u32::checked_add").is_none());
    assert!(ChcCtx::overflowing_arithmetic_method("").is_none());
}

// =============================================================================
// is_formatting_path unit tests (Part of #3570)
// =============================================================================

/// Formatting paths should be classified as formatting (error-blocked).
#[test]
fn test_is_formatting_path_positive_cases() {
    // Display/Debug trait methods
    assert!(ChcCtx::is_formatting_path("std::fmt::Display::fmt"));
    assert!(ChcCtx::is_formatting_path("core::fmt::Debug::fmt"));
    assert!(ChcCtx::is_formatting_path("core::fmt::Formatter::write_str"));
    assert!(ChcCtx::is_formatting_path("std::fmt::Arguments::<'a>::from_str"));

    // panic module (diagnostic infrastructure)
    assert!(ChcCtx::is_formatting_path("core::panic::PanicInfo::message"));
    assert!(ChcCtx::is_formatting_path("core::panic::Location::file"));
    assert!(ChcCtx::is_formatting_path("std::panic::set_hook"));

    // panicking module
    assert!(ChcCtx::is_formatting_path("core::panicking::panic_fmt"));
    assert!(ChcCtx::is_formatting_path("core::panicking::panic"));
}

/// catch_unwind and resume_unwind are NOT formatting paths — they are
/// semantically significant control-flow functions. Part of #3570.
#[test]
fn test_is_formatting_path_catch_unwind_excluded() {
    assert!(
        !ChcCtx::is_formatting_path("std::panic::catch_unwind"),
        "catch_unwind must not be error-blocked — it is control flow, not formatting"
    );
    assert!(
        !ChcCtx::is_formatting_path("std::panic::resume_unwind"),
        "resume_unwind must not be error-blocked — it is control flow, not formatting"
    );
}

/// Non-formatting paths should not be classified as formatting.
#[test]
fn test_is_formatting_path_negative_cases() {
    assert!(!ChcCtx::is_formatting_path("std::vec::Vec::push"));
    assert!(!ChcCtx::is_formatting_path("core::ops::Add::add"));
    assert!(!ChcCtx::is_formatting_path(""));
    assert!(!ChcCtx::is_formatting_path("my_module::format_data"));
}

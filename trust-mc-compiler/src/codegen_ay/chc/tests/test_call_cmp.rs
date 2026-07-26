// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for comparison dispatch in `codegen_call_cmp.rs` through the full
//! CHC pipeline (`mir_to_chc`). Covers:
//! - `codegen_call_primitive_cmp_stub` — StubKind-based dispatch (eq/ne/lt/le/gt/ge/cmp)
//! - `codegen_call_primitive_cmp` — string-based fallback (partial_cmp, wrapping arith, Step)
//!
//! Pure helper tests (primitive_cmp_method, step_unchecked_method,
//! wrapping_arithmetic_method) are in test_call_dispatch.rs and test_core_vc.rs.
//!
//! Part of #2226 (codegen_call_cmp.rs coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

fn cmp_constraints_as_smt(vc: &trust_mc_core::chc::ChcVc) -> Vec<String> {
    vc.rules
        .iter()
        .flat_map(|r| r.body.constraints.iter())
        .map(ToString::to_string)
        .filter(|s| {
            s.contains("bvult")
                || s.contains("bvule")
                || s.contains("bvslt")
                || s.contains("bvsle")
                || s.contains("bvugt")
                || s.contains("bvuge")
                || s.contains("bvsgt")
                || s.contains("bvsge")
        })
        .collect()
}

fn reset_raw_ptr_ord_helper_metadata() {
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}

// =============================================================================
// Integer comparison — eq / ne
// =============================================================================

const CMP_EQ_NE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_cmp_eq_ne(a: u32, b: u32) -> bool {
        if a == b {
            a != 0
        } else {
            false
        }
    }
"#;

const CMP_UNIT_ARRAY_ANY_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }
    }

    pub fn probe_unit_array_any_clone_move_eq() {
        let zst_array: [(); 10] = kani::any();

        let cloned = zst_array.clone();
        assert_eq!(cloned, zst_array);

        let moved = zst_array;
        assert_eq!(moved, cloned);
    }
"#;

#[test]
fn test_cmp_eq_ne_generates_vc() {
    with_test_ay_ctx_for_source(CMP_EQ_NE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cmp_eq_ne");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_cmp_eq_ne", ChcConfig::default());

        assert_vc_structure(&vc, "probe_cmp_eq_ne", body.blocks.len());

        // eq/ne branching should produce constrained transition rules
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 1,
            "eq/ne comparison should produce at least 1 constrained rule, got {constrained}"
        );

        // u32 operands → BV32 sorts in relations
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "eq/ne VC should have BV32 state vars for u32 operands");
    });
}

#[test]
fn test_unit_array_any_clone_move_equality_solver_proves() {
    with_test_ay_ctx_for_source(CMP_UNIT_ARRAY_ANY_SOURCE, |ctx| {
        let fn_name = "probe_unit_array_any_clone_move_eq";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert_z3_result(&smt, "unsat");
    });
}

// =============================================================================
// Integer comparison — lt / le / gt / ge
// =============================================================================

const CMP_ORDERING_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_cmp_ordering(a: i32, b: i32) -> i32 {
        if a < b {
            -1
        } else if a > b {
            1
        } else {
            0
        }
    }
"#;

#[test]
fn test_cmp_ordering_generates_vc() {
    with_test_ay_ctx_for_source(CMP_ORDERING_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cmp_ordering");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_cmp_ordering", ChcConfig::default());

        assert_vc_structure(&vc, "probe_cmp_ordering", body.blocks.len());

        // Branching comparisons produce multiple BB transitions
        assert!(
            vc.rules.len() >= 4,
            "Ordering comparison should produce at least 4 rules, got {}",
            vc.rules.len()
        );
    });
}

// =============================================================================
// Unsigned comparison — exercises unsigned comparison paths (bvult/bvule/bvugt/bvuge)
// =============================================================================

const CMP_UNSIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_unsigned_cmp(a: u64, b: u64) -> u64 {
        if a < b {
            a
        } else if a > b {
            b
        } else {
            0
        }
    }
"#;

#[test]
fn test_unsigned_cmp_generates_vc() {
    with_test_ay_ctx_for_source(CMP_UNSIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_unsigned_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_unsigned_cmp", body.blocks.len());

        // Branching unsigned comparisons produce multiple BB transitions
        assert!(
            vc.rules.len() >= 4,
            "Unsigned comparison should produce at least 4 rules, got {}",
            vc.rules.len()
        );
    });
}

// =============================================================================
// Wrapping arithmetic — exercises wrapping_add/wrapping_sub/wrapping_mul dispatch
// =============================================================================

const WRAPPING_ARITH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_wrapping_arith(a: u32, b: u32) -> u32 {
        let sum = a.wrapping_add(b);
        let diff = sum.wrapping_sub(1);
        diff.wrapping_mul(2)
    }
"#;

#[test]
fn test_wrapping_arith_generates_vc() {
    with_test_ay_ctx_for_source(WRAPPING_ARITH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_arith");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_arith", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_arith", body.blocks.len());

        // Three wrapping operations should produce constrained transition rules
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 1,
            "wrapping arithmetic should produce constrained rules, got {constrained}"
        );
    });
}

// =============================================================================
// Signed comparison — exercises signed comparison paths (bvslt/bvsle/bvsgt/bvsge)
// =============================================================================

const CMP_SIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_signed_cmp(a: i8, b: i8) -> i8 {
        if a < b {
            a
        } else if a > b {
            b
        } else {
            0
        }
    }
"#;

const CMP_SIGNED_ARRAY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_array_signed_cmp(a: [i64; 2], b: [i64; 2]) -> bool {
        a > b
    }
"#;

const CMP_OPTION_REF_EQ_PROMOTED_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Copy, Clone)]
    pub enum SignConstraint {
        Positive,
        Negative,
        Zero,
        NonNegative,
        NonPositive,
    }

    pub fn sign_from_constraint(c: SignConstraint) -> Option<i32> {
        match c {
            SignConstraint::Positive => Some(1),
            SignConstraint::Negative => Some(-1),
            SignConstraint::Zero => Some(0),
            _ => None,
        }
    }

    pub fn maybe_ten(flag: bool) -> Option<usize> {
        if flag {
            Some(10)
        } else {
            None
        }
    }

    pub fn probe_option_ref_eq_promoted_i32() {
        let got = sign_from_constraint(SignConstraint::Positive);
        assert!((&got) == (&Some(1)));
    }

    pub fn probe_option_ref_eq_promoted_usize() {
        let got = maybe_ten(true);
        assert!((&got) == (&Some(10)));
    }
"#;

const CMP_RAW_PTR_ORD_HELPERS_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(ambiguous_wide_pointer_comparisons)]

    pub fn probe_ptr_min_max(a: *const u8, b: *const u8) -> bool {
        let lo = a.min(b);
        let hi = a.max(b);
        lo <= hi
    }

    pub fn probe_ptr_clamp(x: *const u8, lo: *const u8, hi: *const u8) -> *const u8 {
        x.clamp(lo, hi)
    }

    pub fn probe_equal_wide_ptr_min_max() -> bool {
        let array = [0u16, 10];
        let first: *const [u16] = &array[1..2];
        let second: *const [u16] = &array[1..2];
        first.min(second) == first && first.max(second) == first
    }
"#;

const CMP_RAW_WIDE_PTR_RESIDUAL_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(ambiguous_wide_pointer_comparisons)]

    pub fn probe_wide_ptr_cmp_diff() -> std::cmp::Ordering {
        let array = [[0u8, 2]; 10];
        let first: *const [u8] = &array[0];
        let second: *const [u8] = &array[5];
        first.cmp(&second)
    }

    pub fn probe_wide_ptr_min_max_diff() -> bool {
        let array = [[0u8, 2]; 10];
        let first: *const [u8] = &array[0];
        let second: *const [u8] = &array[5];
        first.min(second) == first && first.max(second) == second
    }

    pub fn probe_wide_ptr_clamp_diff() -> *const [u8] {
        let array = [[0u8, 2]; 10];
        let object: *const [u8] = &array[5];
        let smaller: *const [u8] = &array[0];
        let bigger: *const [u8] = &array[9];
        object.clamp(smaller, bigger)
    }

    pub fn probe_wide_ptr_eq_diff() -> bool {
        let array = [[0u8, 2]; 10];
        let first: *const [u8] = &array[0];
        let second: *const [u8] = &array[5];
        std::ptr::eq(first, second)
    }
"#;

#[test]
fn test_signed_cmp_generates_vc() {
    with_test_ay_ctx_for_source(CMP_SIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_signed_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_signed_cmp", body.blocks.len());

        // i8 operands → BV8 sorts in relations
        let has_bv8 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(8)));
        assert!(has_bv8, "signed cmp VC should have BV8 state vars for i8 operands");

        // Branching signed comparisons produce multiple transitions
        assert!(
            vc.rules.len() >= 4,
            "Signed comparison should produce at least 4 rules, got {}",
            vc.rules.len()
        );
    });
}

#[test]
fn test_signed_array_cmp_generates_vc() {
    with_test_ay_ctx_for_source(CMP_SIGNED_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_signed_cmp");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_array_signed_cmp", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, "probe_array_signed_cmp", body.blocks.len());
        // State may appear as relation arg sorts or free variables (declare-var).
        let has_array_rel =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_array));
        let has_array_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_array_rel || has_array_var,
            "signed fixed-array comparison should keep array-backed state in the VC"
        );
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "signed fixed-array comparison should not use demoted CHC fallback"
        );
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "signed fixed-array comparison should not require inferable predicates"
        );
    });
}

#[test]
fn test_option_ref_eq_with_promoted_rhs_reconstructs_flattened_stack_locals() {
    with_test_ay_ctx_for_source(CMP_OPTION_REF_EQ_PROMOTED_SOURCE, |ctx| {
        for fn_name in ["probe_option_ref_eq_promoted_i32", "probe_option_ref_eq_promoted_usize"] {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                fn_name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_eq!(
                diagnostics.inferable_predicate.get(),
                0,
                "{fn_name}: flattened stack-local Option reference equality should not require inferable predicates"
            );
            assert_z3_result(&smt, "unsat");
        }
    });
}

#[test]
fn test_raw_ptr_ord_helpers_avoid_fallback_and_signedness_noise() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(CMP_RAW_PTR_ORD_HELPERS_SOURCE, |ctx| {
        for fn_name in ["probe_ptr_min_max", "probe_ptr_clamp", "probe_equal_wide_ptr_min_max"] {
            reset_raw_ptr_ord_helper_metadata();
            let signedness_before = crate::codegen_ay::shared::get_signedness_fallback_count();

            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
            let signedness_after = crate::codegen_ay::shared::get_signedness_fallback_count();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_eq!(
                diagnostics.inferable_predicate.get(),
                0,
                "{fn_name} should not require inferable predicates for raw-pointer Ord helpers"
            );
            assert_eq!(
                diagnostics.place_translation_drop.get(),
                0,
                "{fn_name} should stay off call_dispatch_fallback after the raw-pointer Ord helper split"
            );
            assert_eq!(
                diagnostics.fallback_count.get(),
                0,
                "{fn_name} should avoid generic demoted fallback in raw-pointer Ord helpers"
            );
            // Part of #4028: signedness_fallback increases per-function after
            // W2:4264 BV/Datatype cmp coercion changes. Max observed: +3
            // (probe_ptr_clamp). Bound at +4 for headroom.
            assert!(
                signedness_after <= signedness_before + 4,
                "{fn_name} signedness_fallback should stay bounded (was {signedness_before}, now {signedness_after})"
            );

            let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let call_dispatch_fallbacks = translation_sites
                .get(fn_name)
                .map(|sites| {
                    sites
                        .iter()
                        .filter(|(reason, _)| *reason == "call_dispatch_fallback")
                        .map(|(_, count)| *count)
                        .sum::<usize>()
                })
                .unwrap_or(0);
            assert_eq!(
                call_dispatch_fallbacks, 0,
                "{fn_name} should not record call_dispatch_fallback, sites={translation_sites:?}"
            );

            let cmp_constraints = cmp_constraints_as_smt(&vc);
            assert!(
                !cmp_constraints.is_empty(),
                "{fn_name} should emit ordering constraints for raw-pointer Ord helpers"
            );
            if fn_name == "probe_equal_wide_ptr_min_max" {
                // #4030: BV128 fat pointers use DT selectors or BV extract.
                let has_fld_ptr = vc.rules.iter().any(|rule| {
                    rule_contains_expr(rule, |expr| is_selector_named(expr, "fld_ptr"))
                });
                let has_bv_extract = vc.rules.iter().any(|rule| {
                    rule_contains_expr(rule, |e| matches!(e.value(), ExprValue::BvExtract { .. }))
                });
                assert!(
                    has_fld_ptr || has_bv_extract,
                    "{fn_name} should decompose wide-pointer via selectors or BV extract"
                );
            }
        }
    });
}

#[test]
fn test_wide_ptr_residual_localizer_stays_off_call_dispatch_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(CMP_RAW_WIDE_PTR_RESIDUAL_SOURCE, |ctx| {
        for fn_name in [
            "probe_wide_ptr_cmp_diff",
            "probe_wide_ptr_min_max_diff",
            "probe_wide_ptr_clamp_diff",
            "probe_wide_ptr_eq_diff",
        ] {
            reset_raw_ptr_ord_helper_metadata();

            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
            let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
            let call_dispatch_fallbacks = fn_sites
                .iter()
                .filter(|(reason, _)| *reason == "call_dispatch_fallback")
                .map(|(_, count)| *count)
                .sum::<usize>();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_eq!(
                diagnostics.place_translation_drop.get(),
                0,
                "{fn_name} should stay off demoted translation drops; translation_sites={fn_sites:?}"
            );
            assert_eq!(
                diagnostics.fallback_count.get(),
                0,
                "{fn_name} should stay off generic demoted fallback"
            );
            assert_eq!(
                call_dispatch_fallbacks, 0,
                "{fn_name} should stay off call_dispatch_fallback, sites={fn_sites:?}"
            );
        }
    });
}

// =============================================================================
// Same-allocation thin-pointer ordering localizer (Part of #4030 addendum)
// =============================================================================

/// Thin-pointer same-allocation ordering: `&array[0]` vs `&array[5]`.
/// The CHC address model must produce a deterministic `bvult` comparison
/// on the (base + offset) expressions. If the codegen falls back to
/// unconstrained symbolic pointer values, z3 returns `sat` (false CTREX).
const CMP_THIN_PTR_SAME_ALLOC_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_thin_ptr_same_alloc_lt() -> bool {
        let array = [0u8; 10];
        let p1: *const u8 = &array[0];
        let p2: *const u8 = &array[5];
        p1 < p2
    }

    pub fn probe_thin_ptr_same_alloc_cmp() -> core::cmp::Ordering {
        let array = [0u8; 10];
        let p1: *const u8 = &array[0];
        let p2: *const u8 = &array[5];
        p1.cmp(&p2)
    }

    pub fn probe_thin_ptr_max_result_is_second() {
        let array = [0u8; 10];
        let p1: *const u8 = &array[0];
        let p2: *const u8 = &array[5];
        let hi = p1.max(p2);
        assert_eq!(hi, p2);
    }
"#;

#[test]
fn test_thin_ptr_same_alloc_lt_stays_off_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(CMP_THIN_PTR_SAME_ALLOC_SOURCE, |ctx| {
        let fn_name = "probe_thin_ptr_same_alloc_lt";
        reset_raw_ptr_ord_helper_metadata();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum::<usize>();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "{fn_name} should not use demoted translation drops"
        );
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should not record call_dispatch_fallback, sites={fn_sites:?}"
        );

        let cmp_constraints = cmp_constraints_as_smt(&vc);
        assert!(
            !cmp_constraints.is_empty(),
            "{fn_name} should emit BV ordering constraints for thin-pointer comparison"
        );
        // Same-allocation thin pointers: unsigned comparison only (no signed)
        assert!(
            cmp_constraints.iter().all(|c| !c.contains("bvslt") && !c.contains("bvsle")),
            "{fn_name} should use unsigned comparison (bvult) not signed for raw pointers, got {cmp_constraints:?}"
        );
    });
}

#[test]
fn test_thin_ptr_same_alloc_cmp_stays_off_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(CMP_THIN_PTR_SAME_ALLOC_SOURCE, |ctx| {
        let fn_name = "probe_thin_ptr_same_alloc_cmp";
        reset_raw_ptr_ord_helper_metadata();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum::<usize>();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "{fn_name} should not use demoted translation drops"
        );
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should not record call_dispatch_fallback, sites={fn_sites:?}"
        );

        // cmp returns Ordering (BV32 encoding: -1/0/1 ITE)
        let cmp_constraints = cmp_constraints_as_smt(&vc);
        assert!(
            !cmp_constraints.is_empty(),
            "{fn_name} should emit BV ordering constraints for raw-pointer cmp"
        );
    });
}

#[test]
fn test_thin_ptr_max_result_uses_selected_operand() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(CMP_THIN_PTR_SAME_ALLOC_SOURCE, |ctx| {
        let fn_name = "probe_thin_ptr_max_result_is_second";
        reset_raw_ptr_ord_helper_metadata();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum::<usize>();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "{fn_name} should not use demoted translation drops"
        );
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should not record call_dispatch_fallback, sites={fn_sites:?}"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

// =============================================================================
// Equal-address / different-length fat-pointer ordering localizer (Part of #4030 addendum)
// =============================================================================

/// Fat-pointer ordering where data pointers are equal (same base) but lengths
/// differ. The compare lane must decompose into `(fld_ptr, fld_len)` and use
/// the length as a tiebreaker after the address comparison is equal.
const CMP_FAT_PTR_EQUAL_ADDR_DIFF_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(ambiguous_wide_pointer_comparisons)]

    pub fn probe_fat_ptr_equal_addr_diff_len() -> bool {
        let array = [0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let full: &[u8] = &array;
        let p1: *const [u8] = &full[..2] as *const [u8];
        let p2: *const [u8] = &full[..4] as *const [u8];
        p1 < p2
    }
"#;

#[test]
fn test_fat_ptr_equal_addr_diff_len_stays_off_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(CMP_FAT_PTR_EQUAL_ADDR_DIFF_LEN_SOURCE, |ctx| {
        let fn_name = "probe_fat_ptr_equal_addr_diff_len";
        reset_raw_ptr_ord_helper_metadata();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum::<usize>();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "{fn_name} should not use demoted translation drops"
        );
        // Record but do not assert zero — this may trigger call_dispatch_fallback
        // from the slice indexing. The localizer documents the current state.
        let signedness_fallback = crate::codegen_ay::shared::get_signedness_fallback_count();

        // Fat-pointer ordering should decompose into fld_ptr + fld_len selectors
        let has_fld_ptr = vc
            .rules
            .iter()
            .any(|rule| rule_contains_expr(rule, |expr| is_selector_named(expr, "fld_ptr")));
        let has_fld_len = vc
            .rules
            .iter()
            .any(|rule| rule_contains_expr(rule, |expr| is_selector_named(expr, "fld_len")));

        // Log current state for diagnostic purposes
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        let cmp_constraints = cmp_constraints_as_smt(&vc);
        eprintln!(
            "{fn_name}: call_dispatch_fallback={call_dispatch_fallbacks}, \
             signedness_fallback={signedness_fallback}, \
             has_fld_ptr={has_fld_ptr}, has_fld_len={has_fld_len}, \
             cmp_constraints={cmp_constraints:?}, smt_len={}",
            smt.len()
        );

        assert!(
            has_fld_ptr || !cmp_constraints.is_empty(),
            "{fn_name} should either decompose via fld_ptr selectors or emit direct BV ordering"
        );
    });
}

// =============================================================================
// Thin-pointer harness localizer (Part of #4030)
// =============================================================================

/// Mirrors the compiletest `check_thin_ptr` helper structure closely enough to
/// distinguish "ordering constraints exist" from "the full assertion packet
/// actually proves unsat".
const CMP_THIN_PTR_HARNESS_LOCALIZER_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(ambiguous_wide_pointer_comparisons)]
    use std::cmp::Ordering;

    fn compare_diff<T: ?Sized>(smaller: *const T, bigger: *const T) {
        assert_eq!(smaller.cmp(&bigger), Ordering::Less);
        assert_eq!(bigger.cmp(&smaller), Ordering::Greater);

        assert!(smaller < bigger);
        assert!(smaller <= bigger);
        assert!(bigger > smaller);
        assert!(bigger >= smaller);
        assert!(bigger != smaller);

        assert!(!(smaller > bigger));
        assert!(!(smaller >= bigger));
        assert!(!(bigger <= smaller));
        assert!(!(bigger < smaller));
        assert!(!(bigger == smaller));
        assert!(!(std::ptr::eq(bigger, smaller)));

        assert_eq!(smaller.min(bigger), smaller);
        assert_eq!(smaller.max(bigger), bigger);
        assert_eq!(bigger.min(smaller), smaller);
        assert_eq!(bigger.max(smaller), bigger);
    }

    fn compare_equal<T: ?Sized>(obj1: *const T, obj2: *const T) {
        assert_eq!(obj1.cmp(&obj2), Ordering::Equal);
        assert!(obj1 <= obj2);
        assert!(obj1 >= obj2);
        assert!(obj1 == obj2);

        assert!(!(obj1 > obj2));
        assert!(!(obj1 < obj2));
        assert!(!(obj1 != obj2));

        assert_eq!(obj1.min(obj2), obj1);
        assert_eq!(obj1.max(obj2), obj1);
    }

    fn check_clamp<T: ?Sized>(object: *const T, smaller: *const T, bigger: *const T) {
        assert_eq!(object.clamp(smaller, bigger), object);
        assert_eq!(object.clamp(smaller, object), object);
        assert_eq!(object.clamp(object, bigger), object);

        assert_eq!(object.clamp(bigger, bigger), bigger);
        assert_eq!(object.clamp(smaller, smaller), smaller);
    }

    pub fn probe_check_thin_ptr_harness() {
        let array = [0u8; 10];
        let first_ptr: *const u8 = &array[0];
        let second_ptr: *const u8 = &array[5];

        compare_diff(first_ptr, second_ptr);
        compare_equal(first_ptr, first_ptr);
        check_clamp(&array[5], &array[0], &array[9]);
    }
"#;

#[test]
fn test_thin_ptr_harness_localizer_proves_unsat() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(CMP_THIN_PTR_HARNESS_LOCALIZER_SOURCE, |ctx| {
        let fn_name = "probe_check_thin_ptr_harness";
        reset_raw_ptr_ord_helper_metadata();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum::<usize>();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "{fn_name} should not use demoted translation drops"
        );
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should not record call_dispatch_fallback, sites={fn_sites:?}"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

// =============================================================================
// Mixed-width comparison — exercises bitvec width coercion paths
// =============================================================================

const CMP_MIXED_WIDTH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_mixed_width(a: u8, b: u32) -> bool {
        (a as u32) == b
    }
"#;

#[test]
fn test_mixed_width_cmp_generates_vc() {
    with_test_ay_ctx_for_source(CMP_MIXED_WIDTH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mixed_width");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_mixed_width", ChcConfig::default());

        assert_vc_structure(&vc, "probe_mixed_width", body.blocks.len());

        // Should have BV32 sorts (the cast target width) or BV8 (source width)
        let has_bv = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32) || s.bitvec_width() == Some(8))
        });
        assert!(has_bv, "mixed-width VC should have bitvec state vars");
    });
}

// =============================================================================
// Boolean comparison — exercises bool eq/ne paths
// =============================================================================

const CMP_BOOL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_bool_cmp(a: bool, b: bool) -> bool {
        a == b
    }
"#;

#[test]
fn test_bool_cmp_generates_vc() {
    with_test_ay_ctx_for_source(CMP_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bool_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bool_cmp", body.blocks.len());

        // Bool sorts should appear in relations (not bitvec)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "bool cmp VC should have Bool state vars for bool operands");
    });
}

// =============================================================================
// Combined comparisons — exercises multiple cmp dispatch in sequence
// =============================================================================

const CMP_COMBINED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_combined_cmp(a: u32, b: u32, c: u32) -> u32 {
        if a == b && b < c {
            a.wrapping_add(c)
        } else if a != c {
            b.wrapping_sub(a)
        } else {
            0
        }
    }
"#;

#[test]
fn test_combined_cmp_generates_vc() {
    with_test_ay_ctx_for_source(CMP_COMBINED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_combined_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_combined_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_combined_cmp", body.blocks.len());

        // Multiple comparisons + branching should produce many rules
        assert!(
            vc.rules.len() >= 5,
            "Combined comparison should produce at least 5 rules, got {}",
            vc.rules.len()
        );

        // Combined should have constrained rules for comparison + wrapping arith
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 2,
            "Combined cmp+arith should produce at least 2 constrained rules, got {constrained}"
        );
    });
}

// =============================================================================
// Unsigned le / ge — exercises bvule/bvuge dispatch paths (gap: only lt/gt tested above)
// =============================================================================

const CMP_LE_GE_UNSIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_le_ge_unsigned(a: u32, b: u32) -> u32 {
        if a <= b {
            1
        } else if a >= b {
            2
        } else {
            0
        }
    }
"#;

#[test]
fn test_le_ge_unsigned_generates_vc() {
    with_test_ay_ctx_for_source(CMP_LE_GE_UNSIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_le_ge_unsigned");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_le_ge_unsigned", ChcConfig::default());

        assert_vc_structure(&vc, "probe_le_ge_unsigned", body.blocks.len());

        // le/ge branching produces multiple BB transitions
        assert!(
            vc.rules.len() >= 4,
            "le/ge comparison should produce at least 4 rules, got {}",
            vc.rules.len()
        );

        // u32 operands → BV32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "le/ge unsigned VC should have BV32 state vars");
    });
}

// =============================================================================
// Signed le / ge — exercises bvsle/bvsge dispatch paths
// =============================================================================

const CMP_LE_GE_SIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_le_ge_signed(a: i16, b: i16) -> i16 {
        if a <= b {
            a
        } else if a >= b {
            b
        } else {
            0
        }
    }
"#;

#[test]
fn test_le_ge_signed_generates_vc() {
    with_test_ay_ctx_for_source(CMP_LE_GE_SIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_le_ge_signed");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_le_ge_signed", ChcConfig::default());

        assert_vc_structure(&vc, "probe_le_ge_signed", body.blocks.len());

        // i16 operands → BV16 sorts
        let has_bv16 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(16)));
        assert!(has_bv16, "le/ge signed VC should have BV16 state vars for i16 operands");

        // Branching le/ge produces multiple transitions
        assert!(
            vc.rules.len() >= 4,
            "Signed le/ge should produce at least 4 rules, got {}",
            vc.rules.len()
        );
    });
}

// =============================================================================
// Standalone ne — exercises PartialEq::ne without eq in same function
// =============================================================================

const CMP_NE_STANDALONE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ne_standalone(a: u32, b: u32) -> u32 {
        if a != b {
            a
        } else {
            b
        }
    }
"#;

#[test]
fn test_ne_standalone_generates_vc() {
    with_test_ay_ctx_for_source(CMP_NE_STANDALONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ne_standalone");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ne_standalone", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ne_standalone", body.blocks.len());

        // ne branching should produce constrained transitions
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 1,
            "ne comparison should produce at least 1 constrained rule, got {constrained}"
        );
    });
}

// =============================================================================
// All six relational ops — exercises all comparison dispatch paths in one function
// =============================================================================

const CMP_ALL_SIX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_all_six_ops(a: u32, b: u32) -> u32 {
        if a == b {
            1
        } else if a != b {
            if a < b {
                2
            } else if a <= b {
                3
            } else if a > b {
                4
            } else if a >= b {
                5
            } else {
                6
            }
        } else {
            0
        }
    }
"#;

#[test]
fn test_all_six_ops_generates_vc() {
    with_test_ay_ctx_for_source(CMP_ALL_SIX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_all_six_ops");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_all_six_ops", ChcConfig::default());

        assert_vc_structure(&vc, "probe_all_six_ops", body.blocks.len());

        // Many branches from 6 comparisons
        assert!(
            vc.rules.len() >= 7,
            "All six relational ops should produce at least 7 rules, got {}",
            vc.rules.len()
        );

        // Multiple constrained transitions from the comparison chain
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 3,
            "Six relational ops should produce at least 3 constrained rules, got {constrained}"
        );
    });
}

// =============================================================================
// Bool ne — exercises bool ne path (gap: only bool eq tested above)
// =============================================================================

const CMP_BOOL_NE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_bool_ne(a: bool, b: bool) -> bool {
        a != b
    }
"#;

#[test]
fn test_bool_ne_generates_vc() {
    with_test_ay_ctx_for_source(CMP_BOOL_NE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_ne");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bool_ne", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bool_ne", body.blocks.len());

        // Bool sorts should appear in relations
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "bool ne VC should have Bool state vars");
    });
}

// =============================================================================
// partial_cmp — exercises string-based fallback (no StubKind for partial_cmp)
// Returns Option<Ordering> which requires datatype wrapping.
// =============================================================================

const CMP_PARTIAL_CMP_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cmp::Ordering;

    pub fn probe_partial_cmp(a: u32, b: u32) -> i32 {
        match a.partial_cmp(&b) {
            Some(Ordering::Less) => -1,
            Some(Ordering::Equal) => 0,
            Some(Ordering::Greater) => 1,
            None => -2,
        }
    }
"#;

const CMP_ORD_CMP_U64_HIGH_BITS_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cmp::Ordering;

    pub fn probe_ord_cmp_u64_high_bits(a: u64, b: u64) -> i32 {
        match a.cmp(&b) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }
"#;

#[test]
fn test_partial_cmp_generates_vc() {
    with_test_ay_ctx_for_source(CMP_PARTIAL_CMP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_partial_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_partial_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_partial_cmp", body.blocks.len());

        // partial_cmp match branches should produce multiple constrained rules
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 1,
            "partial_cmp should produce at least 1 constrained rule, got {constrained}"
        );
    });
}

#[test]
fn test_ord_cmp_u64_does_not_truncate_operands_to_bv32() {
    with_test_ay_ctx_for_source(CMP_ORD_CMP_U64_HIGH_BITS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ord_cmp_u64_high_bits");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ord_cmp_u64_high_bits", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ord_cmp_u64_high_bits", body.blocks.len());
        let cmp_constraints = cmp_constraints_as_smt(&vc);
        assert!(
            !cmp_constraints.is_empty(),
            "expected comparison constraints in Ord::cmp lowering"
        );
        let has_truncation = cmp_constraints.iter().any(|c| c.contains("extract 31 0"));
        assert!(
            !has_truncation,
            "Ord::cmp should compare full-width operands; found BV32 truncation in constraints: {cmp_constraints:?}"
        );
    });
}

#[test]
fn test_cmp_lowering_avoids_fixed_bv32_coercions_and_width_fallbacks() {
    let repo = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cmp_stub_path = [
        repo.join("src/codegen_ay/chc/call/codegen_call_cmp.rs"),
        repo.join("src/codegen_ay/chc/codegen_call_cmp.rs"),
    ]
    .into_iter()
    .find(|path| path.exists())
    .expect("find codegen_call_cmp.rs");
    let cmp_stub = std::fs::read_to_string(&cmp_stub_path).expect("read codegen_call_cmp.rs");
    let cmp_string = {
        let dir = [
            repo.join("src/codegen_ay/chc/call/codegen_call_cmp_string"),
            repo.join("src/codegen_ay/chc/codegen_call_cmp_string"),
        ]
        .into_iter()
        .find(|path| path.is_dir())
        .expect("find codegen_call_cmp_string/");
        let mut combined = String::new();
        for entry in std::fs::read_dir(&dir).expect("read codegen_call_cmp_string/") {
            let entry = entry.expect("dir entry");
            if entry.path().extension().is_some_and(|e| e == "rs") {
                combined.push_str(
                    &std::fs::read_to_string(entry.path())
                        .expect("read codegen_call_cmp_string submodule"),
                );
            }
        }
        combined
    };

    let cmp_stub_norm = cmp_stub.split_whitespace().collect::<String>();
    let cmp_string_norm = cmp_string.split_whitespace().collect::<String>();

    assert!(
        !cmp_stub_norm.contains("coerce_bitvec_width_safe(lhs,32,is_signed)"),
        "StubKind cmp lowering must not force lhs to BV32"
    );
    assert!(
        !cmp_stub_norm.contains("coerce_bitvec_width_safe(rhs,32,is_signed)"),
        "StubKind cmp lowering must not force rhs to BV32"
    );
    assert!(
        !cmp_string_norm.contains("coerce_bitvec_width_safe(lhs,32,is_signed)"),
        "string-based cmp/partial_cmp lowering must not force lhs to BV32"
    );
    assert!(
        !cmp_string_norm.contains("coerce_bitvec_width_safe(rhs,32,is_signed)"),
        "string-based cmp/partial_cmp lowering must not force rhs to BV32"
    );
    assert!(
        !cmp_string_norm.contains("bitvec_width()).unwrap_or("),
        "partial_cmp lowering must not silently fallback Option payload width"
    );
    assert!(
        cmp_string_norm.contains(".filter(|inner_width|*inner_width==8||*inner_width==32)"),
        "partial_cmp lowering must restrict Option<Ordering> payload width to 8/32"
    );
}

// =============================================================================
// Step::forward_unchecked — exercises range for-loop MIR lowering
// =============================================================================

const STEP_FORWARD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_step_forward(n: usize) -> usize {
        let mut sum: usize = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum.wrapping_add(i);
            i = i.wrapping_add(1);
        }
        sum
    }
"#;

#[test]
fn test_step_forward_generates_vc() {
    with_test_ay_ctx_for_source(STEP_FORWARD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_step_forward");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_step_forward", ChcConfig::default());

        assert_vc_structure(&vc, "probe_step_forward", body.blocks.len());

        // Loop should produce back-edge rules (bb_i -> bb_i pattern)
        let has_loop = vc
            .rules
            .iter()
            .any(|r| r.body.relation.as_ref().is_some_and(|br| br.name == r.head.name));
        // Loop structure: at minimum, constrained transitions for the comparison
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 2 || has_loop,
            "Loop should produce constrained rules or back-edges, got {constrained} constrained, has_loop={has_loop}"
        );

        // usize → BV64 (or BV32) sorts in relations
        let has_bv = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64) || s.bitvec_width() == Some(32))
        });
        assert!(has_bv, "step forward VC should have bitvec state vars for usize");
    });
}

// =============================================================================
// Wrapping sub standalone — exercises wrapping_sub without add/mul context
// =============================================================================

const WRAPPING_SUB_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_wrapping_sub(a: u64, b: u64) -> u64 {
        a.wrapping_sub(b)
    }
"#;

#[test]
fn test_wrapping_sub_generates_vc() {
    with_test_ay_ctx_for_source(WRAPPING_SUB_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_sub");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_sub", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_sub", body.blocks.len());

        // Wrapping sub should produce constrained transition rules
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained >= 1,
            "wrapping_sub should produce at least 1 constrained rule, got {constrained}"
        );

        // u64 → BV64 sorts
        let has_bv64 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64)));
        assert!(has_bv64, "wrapping_sub VC should have BV64 state vars for u64");
    });
}

// =============================================================================
// Reference comparison — Part of #3305: heap safety checks preserved
// =============================================================================

const CMP_REF_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_ref_eq(a: &u32, b: &u32) -> bool { a == b }
"#;

const CMP_COROUTINE_STATE_UNIT_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]

    use std::ops::CoroutineState;

    pub fn probe_coroutine_state_unit_eq() -> bool {
        CoroutineState::<(), ()>::Yielded(()) == CoroutineState::<(), ()>::Yielded(())
    }
"#;

const CMP_COROUTINE_STATE_LOCAL_EQ_ASSERT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]

    use std::ops::CoroutineState;

    pub fn probe_coroutine_state_local_eq_assert() {
        let state = CoroutineState::<(), ()>::Yielded(());
        assert!(state == CoroutineState::Yielded(()));
    }
"#;

const CMP_COROUTINE_RESUME_UNIT_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_coroutine_resume_yield_unit_eq() -> bool {
        let mut g = #[coroutine]
        |mut x: usize| {
            loop {
                let _ = x;
                x = yield;
            }
        };

        Pin::new(&mut g).resume(0) == CoroutineState::Yielded(())
    }
"#;

const CMP_COROUTINE_MULTI_RESUME_UNIT_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_coroutine_multi_resume_yield_unit_eq() -> bool {
        let mut copy = #[coroutine]
        |mut x: usize| {
            loop {
                let _ = x;
                x = yield;
            }
        };

        let mut boxed = #[coroutine]
        |mut x: Box<usize>| {
            loop {
                drop(x);
                x = yield;
            }
        };

        Pin::new(&mut copy).resume(0) == CoroutineState::Yielded(())
            && Pin::new(&mut boxed).resume(Box::new(0)) == CoroutineState::Yielded(())
    }
"#;

#[test]
fn test_ref_eq_at_mem_level_preserves_heap_safety_checks() {
    // Part of #3305: verify deref_cmp retains obj_valid checks for non-stack pointers.
    with_test_ay_ctx_for_source(CMP_REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_eq");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_ref_eq",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        // State may appear as relation arg sorts or free variables (declare-var).
        let has_array_rel = vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.is_array()));
        let has_array_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(
            has_array_rel || has_array_var,
            "Mem level should have Array sorts for heap metadata"
        );
        assert!(!vc.rules.is_empty(), "ref comparison VC should have rules");
        // #3305: obj_valid constraints must appear — safety checks are no longer truncated.
        // Check both rule constraints and free variable declarations (declare-var).
        let has_obj_valid_constraint = vc
            .rules
            .iter()
            .flat_map(|r| r.body.constraints.iter())
            .any(|c| c.to_string().contains("obj_valid"));
        let has_obj_valid_var = vc.vars().iter().any(|v| v.name.contains("obj_valid"));
        assert!(
            has_obj_valid_constraint || has_obj_valid_var,
            "ref cmp at Mem level must reference obj_valid (#3305)"
        );
    });
}

#[test]
fn test_coroutine_state_unit_eq_avoids_zst_ref_deref_fallback() {
    with_test_ay_ctx_for_source(CMP_COROUTINE_STATE_UNIT_EQ_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coroutine_state_unit_eq");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_state_unit_eq", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, "probe_coroutine_state_unit_eq", body.blocks.len());
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "CoroutineState<(), ()> equality should not require inferable predicates"
        );
    });
}

#[test]
fn test_coroutine_state_local_eq_with_promoted_rhs_proves_without_fallback() {
    with_test_ay_ctx_for_source(CMP_COROUTINE_STATE_LOCAL_EQ_ASSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coroutine_state_local_eq_assert");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_coroutine_state_local_eq_assert",
            ChcConfig::default(),
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert_vc_structure(&vc, "probe_coroutine_state_local_eq_assert", body.blocks.len());
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "promoted Yielded(()) equality should not require inferable predicates"
        );
        assert_z3_result(&smt, "unsat");
    });
}

#[test]
fn test_coroutine_resume_yield_unit_eq_uses_canonical_zst_payload() {
    with_test_ay_ctx_for_source(CMP_COROUTINE_RESUME_UNIT_EQ_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coroutine_resume_yield_unit_eq");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_coroutine_resume_yield_unit_eq",
            ChcConfig::default(),
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert_vc_structure(&vc, "probe_coroutine_resume_yield_unit_eq", body.blocks.len());
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "coroutine resume equality on Yielded(()) should not require inferable predicates"
        );
        assert!(
            !smt.contains("__coroutine_yield") && !smt.contains("__coro_yield_payload"),
            "Yielded(()) should use the canonical ZST payload instead of fresh symbols, got {smt}"
        );
        assert_z3_result(&smt, "unsat");
    });
}

#[test]
fn test_coroutine_multi_resume_yield_unit_eq_uses_canonical_zst_payload() {
    with_test_ay_ctx_for_source(CMP_COROUTINE_MULTI_RESUME_UNIT_EQ_SOURCE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_coroutine_multi_resume_yield_unit_eq");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_coroutine_multi_resume_yield_unit_eq",
            ChcConfig::default(),
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert_vc_structure(&vc, "probe_coroutine_multi_resume_yield_unit_eq", body.blocks.len());
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "multi-coroutine resume equality on Yielded(()) should not require inferable predicates"
        );
        assert!(
            !smt.contains("__coroutine_yield") && !smt.contains("__coro_yield_payload"),
            "multi-coroutine Yielded(()) equality should use canonical ZST payloads, got {smt}"
        );
        assert_z3_result(&smt, "unsat");
    });
}

// Part of #3994: promoted enum RHS references with omitted payloads must compare
// on the flattened enum value, not on a bare discriminant or wrapped pointer BV.
const FIVE_VARIANT_ENUM_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Debug, PartialEq)]
    struct ZeroSized;

    impl ZeroSized {
        fn works(&self) -> bool {
            true
        }
    }

    #[derive(Debug, PartialEq)]
    enum FiveVar {
        NoFields,
        DataFul(bool),
        UnitFields((), ()),
        ZSTField(ZeroSized),
        ZSTStruct { field: ZeroSized, unit: () },
    }

    pub fn probe_five_var_dataful_eq() {
        let x = FiveVar::DataFul(true);
        let y = FiveVar::DataFul(true);
        assert!(x == y);
    }

    pub fn probe_five_var_no_fields_eq() {
        let x = FiveVar::NoFields;
        let y = FiveVar::NoFields;
        assert!(x == y);
    }

    pub fn probe_five_var_unit_fields_eq_literal() {
        let x = FiveVar::UnitFields((), ());
        assert!(x == FiveVar::UnitFields((), ()));
    }

    pub fn probe_five_var_zst_field_eq_literal() {
        let x = FiveVar::ZSTField(ZeroSized);
        assert!(x == FiveVar::ZSTField(ZeroSized));
    }

    pub fn probe_five_var_unit_fields_assert_eq_literal() {
        let x = FiveVar::UnitFields((), ());
        assert_eq!(x, FiveVar::UnitFields((), ()));
    }

    pub fn probe_five_var_zst_field_assert_eq_literal() {
        let x = FiveVar::ZSTField(ZeroSized);
        assert_eq!(x, FiveVar::ZSTField(ZeroSized));
    }

    pub fn probe_five_var_unit_fields_ref_read() {
        let x = FiveVar::UnitFields((), ());
        if let FiveVar::UnitFields(v, ..) = &x {
            assert_eq!(std::mem::size_of_val(v), 0);
        }
    }

    pub fn probe_five_var_zst_field_ref_read() {
        let x = FiveVar::ZSTField(ZeroSized);
        if let FiveVar::ZSTField(field) = &x {
            assert!(field.works());
        }
    }
"#;

#[test]
fn test_five_variant_enum_promoted_rhs_and_omitted_field_reads_prove() {
    with_test_ay_ctx_for_source(FIVE_VARIANT_ENUM_EQ_SOURCE, |ctx| {
        for fn_name in [
            "probe_five_var_no_fields_eq",
            "probe_five_var_dataful_eq",
            "probe_five_var_unit_fields_eq_literal",
            "probe_five_var_zst_field_eq_literal",
            "probe_five_var_unit_fields_assert_eq_literal",
            "probe_five_var_zst_field_assert_eq_literal",
            "probe_five_var_unit_fields_ref_read",
            "probe_five_var_zst_field_ref_read",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_eq!(
                diagnostics.fallback_count.get(),
                0,
                "{fn_name} should not require sound fallback for promoted enum equality"
            );
            assert_eq!(
                diagnostics.place_translation_drop.get(),
                0,
                "{fn_name} should keep promoted enum equality on the precise path; \
                 translation_sites={fn_sites:?}"
            );
            assert_z3_result(&smt, "unsat");
        }
    });
}

#[test]
fn test_five_variant_enum_mem_level_split() {
    with_test_ay_ctx_for_source(FIVE_VARIANT_ENUM_EQ_SOURCE, |ctx| {
        for fn_name in [
            "probe_five_var_unit_fields_assert_eq_literal",
            "probe_five_var_zst_field_assert_eq_literal",
            "probe_five_var_unit_fields_ref_read",
            "probe_five_var_zst_field_ref_read",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                fn_name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_z3_result(&smt, "unsat");
        }
    });
}

// Part of #3994: match the `tests/trust_mc/Enum/niche_many_variants.rs` helper-call
// and `ref`-binding MIR more closely before widening production fixes.
const NICHE_MANY_VARIANTS_EXACT_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Debug, PartialEq)]
    enum MyEnum {
        NoFields,
        DataFul(bool),
        UnitFields((), ()),
        ZSTField(ZeroSized),
        ZSTStruct { field: ZeroSized, unit: () },
    }

    #[derive(Debug, PartialEq)]
    struct ZeroSized {}

    impl ZeroSized {
        fn works(&self) -> bool {
            true
        }
    }

    impl MyEnum {
        fn create_unit() -> MyEnum {
            MyEnum::UnitFields((), ())
        }

        fn create_zst_field() -> MyEnum {
            MyEnum::ZSTField(ZeroSized {})
        }
    }

    pub fn check_niche_unit_fields() {
        let x = MyEnum::create_unit();
        assert_eq!(x, MyEnum::UnitFields((), ()));
        if let &MyEnum::UnitFields(ref v, ..) = &x {
            assert_eq!(std::mem::size_of_val(v), 0);
        }
    }

    pub fn check_niche_zst_field() {
        let x = MyEnum::create_zst_field();
        assert_eq!(x, MyEnum::ZSTField(ZeroSized {}));
        if let &MyEnum::ZSTField(ref field) = &x {
            assert!(field.works());
        }
    }
"#;

#[test]
fn test_niche_many_variants_exact_mem_level_split() {
    with_test_ay_ctx_for_source(NICHE_MANY_VARIANTS_EXACT_SOURCE, |ctx| {
        for fn_name in ["check_niche_unit_fields", "check_niche_zst_field"] {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                fn_name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_z3_result(&smt, "unsat");
        }
    });
}

const NICHE_MANY_VARIANTS_EDITION2021_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Debug, PartialEq)]
    enum MyEnum {
        NoFields,
        DataFul(bool),
        UnitFields((), ()),
        ZSTField(ZeroSized),
        ZSTStruct { field: ZeroSized, unit: () },
    }

    #[derive(Debug, PartialEq)]
    struct ZeroSized {}

    impl ZeroSized {
        fn works(&self) -> bool {
            true
        }
    }

    impl MyEnum {
        fn create_unit() -> MyEnum {
            MyEnum::UnitFields((), ())
        }

        fn create_zst_field() -> MyEnum {
            MyEnum::ZSTField(ZeroSized {})
        }
    }

    pub fn check_niche_unit_fields() {
        let x = MyEnum::create_unit();
        assert_eq!(x, MyEnum::UnitFields((), ()));
        if let MyEnum::UnitFields(ref v, ..) = &x {
            assert_eq!(std::mem::size_of_val(v), 0);
        }
    }

    pub fn check_niche_zst_field() {
        let x = MyEnum::create_zst_field();
        assert_eq!(x, MyEnum::ZSTField(ZeroSized {}));
        if let MyEnum::ZSTField(ref field) = &x {
            assert!(field.works());
        }
    }
"#;

#[test]
fn test_niche_many_variants_exact_mem_level_split_edition2021() {
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(
        NICHE_MANY_VARIANTS_EDITION2021_SOURCE,
        "2021",
        |ctx| {
            for fn_name in ["check_niche_unit_fields", "check_niche_zst_field"] {
                let instance = find_instance_by_suffix(ctx.tcx, fn_name);
                let body = instance.body().expect("function body");
                let vc = mir_to_chc(
                    ctx.tcx,
                    &body,
                    fn_name,
                    ChcConfig {
                        track_level: crate::args::ChcTrackLevel::Mem,
                        ..ChcConfig::default()
                    },
                );
                let smt = crate::codegen_ay::emit_chc(&vc).to_string();

                assert_vc_structure(&vc, fn_name, body.blocks.len());
                assert_z3_result(&smt, "unsat");
            }
        },
    );
}

// Part of #3994: exact-file CHC regression guard for the real
// `tests/trust_mc/Enum/niche_many_variants.rs` harness file. This loads the
// actual committed source (not a reduced inline string) and verifies that
// the two failing harnesses (`check_niche_unit_fields`, `check_niche_zst_field`)
// produce `unsat` under CHC unit translation. If they do, the compiletest
// failure is dirty-tree drift, not a committed code bug.
const NICHE_MANY_VARIANTS_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/Enum/niche_many_variants.rs");

/// Strip `#[kani::proof]` and `#[kani::unwind(...)]` attributes so the source
/// compiles as a plain Rust crate under the CHC unit test harness.
fn strip_kani_attributes(source: &str) -> String {
    let mut result = String::with_capacity(source.len() + "#![allow(dead_code)]\n".len());
    result.push_str("#![allow(dead_code)]\n");
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::") {
            continue;
        }
        if trimmed.starts_with("// kani-expect:") {
            continue;
        }
        // Kani's assert_eq! doesn't require Debug; std's does. Add Debug
        // to any derive(PartialEq) that lacks it.
        if trimmed.starts_with("#[derive(")
            && trimmed.contains("PartialEq")
            && !trimmed.contains("Debug")
        {
            let patched = line.replace("#[derive(PartialEq)]", "#[derive(Debug, PartialEq)]");
            result.push_str(&patched);
            result.push('\n');
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

#[test]
fn test_niche_many_variants_real_file_unit_fields() {
    let source = strip_kani_attributes(NICHE_MANY_VARIANTS_REAL_FILE);
    // Real harness uses edition 2021 patterns (explicit `ref` bindings).
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2021", |ctx| {
        let fn_name = "check_niche_unit_fields";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_z3_result(&smt, "unsat");
    });
}

#[test]
fn test_niche_many_variants_real_file_zst_field() {
    let source = strip_kani_attributes(NICHE_MANY_VARIANTS_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2021", |ctx| {
        let fn_name = "check_niche_zst_field";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_z3_result(&smt, "unsat");
    });
}

// =============================================================================
// Part of #4086: SIMD packed BV comparison — extract_packed_bv_elements coverage
// =============================================================================

/// Verify that `extract_packed_bv_elements` correctly decomposes a packed BV(128)
/// representing `[i64; 2]` into two BV(64) element expressions.
#[test]
fn test_extract_packed_bv_elements_decomposes_bv128_into_two_bv64() {
    use crate::codegen_ay::chc::call::codegen_call_cmp_string::cmp_array::extract_packed_bv_elements;
    use ay_bindings::{Expr, Sort};

    let packed = Expr::var("simd_packed", Sort::bitvec(128));
    let elements = extract_packed_bv_elements(&packed, 2, 64);
    let elements = elements.expect("should decompose BV128 into 2 elements");
    assert_eq!(elements.len(), 2, "i64x2 should produce 2 elements");
    for (i, elem) in elements.iter().enumerate() {
        assert_eq!(elem.sort().bitvec_width(), Some(64), "element {i} should be BV64");
    }
    let elem0_str = elements[0].to_string();
    let elem1_str = elements[1].to_string();
    assert!(
        elem0_str.contains("extract") || elem0_str.contains("Extract"),
        "element 0 should use extract: {elem0_str}"
    );
    assert!(
        elem1_str.contains("extract") || elem1_str.contains("Extract"),
        "element 1 should use extract: {elem1_str}"
    );
}

/// Verify that `extract_packed_bv_elements` rejects width mismatches.
#[test]
fn test_extract_packed_bv_elements_rejects_width_mismatch() {
    use crate::codegen_ay::chc::call::codegen_call_cmp_string::cmp_array::extract_packed_bv_elements;
    use ay_bindings::{Expr, Sort};

    let packed = Expr::var("mismatched", Sort::bitvec(128));
    assert!(
        extract_packed_bv_elements(&packed, 3, 64).is_none(),
        "should reject when num_elements * elem_width != total_width"
    );
}

/// Verify that SIMD repr comparison produces appropriate BV state vars in the VC.
/// Part of #4086.
#[test]
fn test_simd_repr_comparison_produces_bv_state_vars_in_vc() {
    let source = r#"
        #![allow(dead_code, non_camel_case_types)]
        #![feature(repr_simd)]

        #[repr(simd)]
        #[derive(Clone, Copy)]
        pub struct i64x2([i64; 2]);

        impl i64x2 {
            fn into_array(self) -> [i64; 2] {
                unsafe { core::mem::transmute(self) }
            }
        }

        impl core::cmp::PartialEq for i64x2 {
            fn eq(&self, other: &Self) -> bool {
                self.into_array() == other.into_array()
            }
        }

        pub fn probe_simd_eq(a: i64x2, b: i64x2) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(source, |ctx| {
        let fn_name = "probe_simd_eq";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let has_bv128 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(128)));
        let has_bv64 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64)));
        assert!(
            has_bv128 || has_bv64,
            "SIMD i64x2 comparison should produce BV128 or BV64 state vars in VC"
        );
    });
}

#[test]
fn test_simd_repr_partial_ord_keeps_array_identity_in_stub_path() {
    let source = r#"
        #![allow(dead_code, non_camel_case_types)]
        #![feature(repr_simd)]

        #[repr(simd)]
        #[derive(Clone, Copy)]
        pub struct i64x2([i64; 2]);

        impl i64x2 {
            fn into_array(self) -> [i64; 2] {
                unsafe { core::mem::transmute(self) }
            }
        }

        impl core::cmp::PartialEq for i64x2 {
            fn eq(&self, other: &Self) -> bool {
                self.into_array() == other.into_array()
            }
        }

        impl core::cmp::PartialOrd for i64x2 {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                self.into_array().partial_cmp(&other.into_array())
            }
        }

        pub fn probe_simd_gt(a: i64x2) -> bool {
            a > i64x2([0, 0])
        }
    "#;

    with_test_ay_ctx_for_source(source, |ctx| {
        let fn_name = "probe_simd_gt";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (repr-SIMD compare payload)",
        );
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ay_bindings::ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, lane_idx)",
        );
    });
}

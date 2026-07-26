// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for codegen_stmt_aggregate_discr.rs — translate_discriminant paths.
// Covers: flattened Option/Result discriminant ITE encoding,
// allocation-related type forcing, unit enum discriminant extraction,
// and Option-like two-variant enum extraction.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use super::test_coroutine_root_map::COROUTINE_RESUME_LIVE_ACROSS_YIELD_SOURCE;
use crate::rustc_public_bridge::IndexedVal;

// =============================================================================
// Flattened Option discriminant: true → 1 (Some), false → 0 (None)
// =============================================================================

const OPTION_DISCR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_discriminant(x: Option<u32>) -> isize {
        match x {
            Some(_) => 1,
            None => 0,
        }
    }
"#;

#[test]
fn test_translate_discriminant_flattened_option_returns_ite() {
    with_test_ay_ctx_for_source(OPTION_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a flattened Option local (should have Bool fld0 for is_some)
        let option_local = chc_ctx.flatten.flattened_tuple_locals.iter().copied().find(|&idx| {
            let vec_idx = chc_ctx.state_idx_for_local(idx);
            chc_ctx.state_var_mgr.state_vars.get(vec_idx).is_some_and(|(_, sort)| sort.is_bool())
        });

        let option_local =
            option_local.expect("should find a flattened Option local with Bool fld0");
        let place = rustc_public::mir::Place { local: option_local, projection: vec![] };

        let discr = chc_ctx.translate_discriminant(&place, &HashSet::new());
        assert!(discr.is_some(), "flattened Option local should produce a discriminant expression");

        let discr_expr = discr.unwrap();
        // The result should be an ITE: ite(bool_var, 1, 0) for Option
        // (true_val=1 for Some, false_val=0 for None)
        let smt = discr_expr.to_string();
        assert!(smt.contains("ite"), "Option discriminant should be ITE expression, got: {smt}");
    });
}

#[test]
fn test_translate_discriminant_option_discr_mapping_is_1_0() {
    with_test_ay_ctx_for_source(OPTION_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Verify Option discriminant mapping: (1, 0) — true=Some(1), false=None(0)
        let has_option_discr = chc_ctx
            .flatten
            .flattened_enum_discr
            .values()
            .any(|&(true_val, false_val)| true_val == 1 && false_val == 0);

        assert!(
            has_option_discr,
            "Option should have discriminant mapping (1, 0) = (Some, None), found: {:?}",
            chc_ctx.flatten.flattened_enum_discr
        );
    });
}

// =============================================================================
// Flattened Result discriminant: true → 0 (Ok), false → 1 (Err)
// =============================================================================

const RESULT_DISCR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_discriminant(x: Result<u32, u32>) -> isize {
        match x {
            Ok(_) => 0,
            Err(_) => 1,
        }
    }
"#;

#[test]
fn test_translate_discriminant_flattened_result_returns_ite() {
    with_test_ay_ctx_for_source(RESULT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_result_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a flattened Result local (should have Bool fld0 for is_ok)
        let result_local = chc_ctx.flatten.flattened_tuple_locals.iter().copied().find(|&idx| {
            let vec_idx = chc_ctx.state_idx_for_local(idx);
            chc_ctx.state_var_mgr.state_vars.get(vec_idx).is_some_and(|(_, sort)| sort.is_bool())
        });

        let result_local =
            result_local.expect("should find a flattened Result local with Bool fld0");
        let place = rustc_public::mir::Place { local: result_local, projection: vec![] };

        let discr = chc_ctx.translate_discriminant(&place, &HashSet::new());
        assert!(discr.is_some(), "flattened Result local should produce a discriminant expression");

        let discr_expr = discr.unwrap();
        let smt = discr_expr.to_string();
        assert!(smt.contains("ite"), "Result discriminant should be ITE expression, got: {smt}");
    });
}

#[test]
fn test_translate_discriminant_result_discr_mapping_is_0_1() {
    with_test_ay_ctx_for_source(RESULT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_result_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Verify Result discriminant mapping: (0, 1) — true=Ok(0), false=Err(1)
        let has_result_discr = chc_ctx
            .flatten
            .flattened_enum_discr
            .values()
            .any(|&(true_val, false_val)| true_val == 0 && false_val == 1);

        assert!(
            has_result_discr,
            "Result should have discriminant mapping (0, 1) = (Ok, Err), found: {:?}",
            chc_ctx.flatten.flattened_enum_discr
        );
    });
}

// =============================================================================
// Option vs Result polarity: verify they produce DIFFERENT ITE encodings
// =============================================================================

const OPTION_RESULT_POLARITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_polarity(x: Option<u32>) -> u32 {
        x.unwrap_or(0)
    }

    pub fn probe_result_polarity(x: Result<u32, u32>) -> u32 {
        x.unwrap_or(0)
    }
"#;

#[test]
fn test_option_and_result_have_opposite_polarity() {
    with_test_ay_ctx_for_source(OPTION_RESULT_POLARITY_SOURCE, |ctx| {
        // Check Option
        let opt_instance = find_instance_by_suffix(ctx.tcx, "probe_option_polarity");
        let opt_body = opt_instance.body().expect("function body");
        let mut opt_ctx =
            ChcCtx::new(ctx.tcx, &opt_body, "probe_option_polarity", ChcConfig::default());
        opt_ctx.declare_block_relations();

        let opt_mappings: Vec<_> = opt_ctx.flatten.flattened_enum_discr.values().copied().collect();

        // Check Result
        let res_instance = find_instance_by_suffix(ctx.tcx, "probe_result_polarity");
        let res_body = res_instance.body().expect("function body");
        let mut res_ctx =
            ChcCtx::new(ctx.tcx, &res_body, "probe_result_polarity", ChcConfig::default());
        res_ctx.declare_block_relations();

        let res_mappings: Vec<_> = res_ctx.flatten.flattened_enum_discr.values().copied().collect();

        // Option should have (1, 0), Result should have (0, 1) — opposite polarity
        assert!(
            opt_mappings.contains(&(1, 0)),
            "Option should have (1, 0) mapping, found: {opt_mappings:?}"
        );
        assert!(
            res_mappings.contains(&(0, 1)),
            "Result should have (0, 1) mapping, found: {res_mappings:?}"
        );
    });
}

// =============================================================================
// Unit enum discriminant: value IS the discriminant
// =============================================================================

const UNIT_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    pub enum Color { Red, Green, Blue }

    pub fn probe_unit_enum_discr(c: Color) -> u32 {
        match c {
            Color::Red => 0,
            Color::Green => 1,
            Color::Blue => 2,
        }
    }
"#;

#[test]
fn test_translate_discriminant_unit_enum_produces_bitvec() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unit_enum_discr");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_unit_enum_discr", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_unit_enum_discr", bb_count);

        // Unit enum should produce bitvec sort for the discriminant
        let has_bv_sort =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width().is_some()));
        assert!(has_bv_sort, "unit enum discriminant should produce bitvec sort in CHC relations");

        // MIR may optimize unit enum matches; verify rules are well-formed
        let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
        for rule in &vc.rules {
            assert!(
                declared.contains(rule.head.name.as_str()),
                "rule head '{}' references undeclared relation",
                rule.head.name
            );
        }
    });
}

// =============================================================================
// Single-variant unit enum: discriminant is the only variant's value
// =============================================================================

const SINGLE_VARIANT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Single { Only }

    pub fn probe_single_variant(s: Single) -> u32 {
        match s {
            Single::Only => 42,
        }
    }
"#;

#[test]
fn test_translate_discriminant_single_variant_unit_enum() {
    with_test_ay_ctx_for_source(SINGLE_VARIANT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_single_variant");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_single_variant", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_single_variant", bb_count);

        // Single-variant enum: the match has only one arm, so the VC should
        // have at most 1 transition rule per block (no discriminant branching).
        // Count rules with non-entry bodies (excluding the init rule).
        let non_init_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        // With a single arm, there should be no discriminant-guarded branching:
        // each block transitions to at most one successor.
        assert!(
            non_init_rules.len() <= bb_count,
            "single-variant enum should not produce discriminant-guarded branching \
             (got {} non-init rules for {} blocks)",
            non_init_rules.len(),
            bb_count
        );
    });
}

const SINGLE_VARIANT_EXPLICIT_AGGREGATE_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[repr(u8)]
    pub enum SingleExplicit { Only = 42 }

    pub fn probe_single_variant_explicit_aggregate() -> SingleExplicit {
        SingleExplicit::Only
    }
"#;

#[test]
fn test_translate_aggregate_single_variant_explicit_unit_enum_is_scalar() {
    with_test_ay_ctx_for_source(SINGLE_VARIANT_EXPLICIT_AGGREGATE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_single_variant_explicit_aggregate");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_single_variant_explicit_aggregate",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let mut aggregate = None;
        for block in &body.blocks {
            for statement in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    rustc_public::mir::Rvalue::Aggregate(
                        rustc_public::mir::AggregateKind::Adt(def, variant_idx, args, _, _),
                        operands,
                    ),
                ) = &statement.kind
                    && def.variants()[variant_idx.to_index()].name() == "Only"
                {
                    aggregate = Some((*def, *variant_idx, args.clone(), operands.clone()));
                }
            }
        }
        let (def, variant_idx, args, operands) =
            aggregate.expect("probe should contain a SingleExplicit::Only aggregate");
        let expr = chc_ctx
            .translate_adt_aggregate(def, variant_idx, &args, &operands, &HashSet::new())
            .expect("single-variant explicit aggregate should translate");

        assert_eq!(
            expr.sort().bitvec_width(),
            Some(32),
            "single-variant explicit unit enum aggregate must match scalar unit-enum sort, got {:?}",
            expr.sort()
        );
    });
}

// =============================================================================
// Result match — VC structure
// =============================================================================

const RESULT_MATCH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_match(r: Result<u32, u32>) -> u32 {
        match r {
            Ok(v) => v,
            Err(e) => e + 1,
        }
    }
"#;

#[test]
fn test_translate_discriminant_result_match_produces_guarded_transitions() {
    with_test_ay_ctx_for_source(RESULT_MATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_match", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_result_match", bb_count);

        // Result match should have at least 2 transition rules (Ok/Err arms)
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "Result match should have >= 2 transition rules, got {}",
            transition_rules.len()
        );

        // At least one rule should have guard constraints from discriminant read
        let guarded = transition_rules.iter().filter(|r| !r.body.constraints.is_empty()).count();
        assert!(guarded >= 1, "Result match should have >= 1 guarded transition rule");
    });
}

// =============================================================================
// Modified-locals path: discriminant reads output_state_vars when local is modified
// =============================================================================

const MODIFIED_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(unused_assignments)]

    pub fn probe_modified_option(x: u32) -> u32 {
        let mut opt: Option<u32> = Some(x);
        opt = None;
        match opt {
            Some(v) => v,
            None => 0,
        }
    }
"#;

#[test]
fn test_translate_discriminant_modified_option_local() {
    with_test_ay_ctx_for_source(MODIFIED_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_modified_option");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_modified_option", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_modified_option", bb_count);

        // Modified-local path: `opt` is reassigned (`opt = None`), so the
        // discriminant read should reference output state vars (`__out`).
        // Verify the VC contains __out variables, proving the modified-local
        // path was exercised rather than the input state path.
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert!(
            smt.contains("__out"),
            "modified Option local should use __out state variables in CHC rules"
        );
    });
}

// =============================================================================
// Strategy 6: symbolic fallback for 3+ variant enums with payloads
// (Part of #2353)
// =============================================================================

const THREEVARIANT_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Ast {
        Num(i32),
        Neg(i32),
        Add(i32, i32),
    }

    pub fn probe_three_variant_match(a: Ast) -> i32 {
        match a {
            Ast::Num(n) => n,
            Ast::Neg(n) => -n,
            Ast::Add(l, r) => l + r,
        }
    }
"#;

/// 3-variant enum with payloads triggers the symbolic fallback (Strategy 6):
/// translate_discriminant returns a fresh symbolic bitvec variable.
/// This is sound (over-approximation) but lets solver explore all branches.
///
/// Part of #2353 AC 6: test symbolic fallback.
#[test]
fn test_translate_discriminant_three_variant_enum_pipeline() {
    with_test_ay_ctx_for_source(THREEVARIANT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_three_variant_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_three_variant_match", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_three_variant_match", bb_count);

        // 3-variant match produces transition rules for each arm.
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 3,
            "3-variant match should have >= 3 transition rules, got {}",
            transition_rules.len()
        );
    });
}

/// Test that translate_discriminant on a 3-variant enum with payloads
/// uses is_constructor ITE chain when the expression has Datatype sort,
/// connecting the discriminant to the actual enum value.
///
/// Part of #2353 AC 6. Updated: was symbolic fallback, now ITE chain.
#[test]
fn test_translate_discriminant_three_variant_uses_ite_chain() {
    with_test_ay_ctx_for_source(THREEVARIANT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_three_variant_match");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_three_variant_match", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (discr_place, _target) = find_discriminant_local(&body)
            .expect("probe_three_variant_match should contain a Discriminant rvalue");
        let result = chc_ctx.translate_discriminant(&discr_place, &HashSet::new());
        assert!(result.is_some(), "3-variant enum discriminant should return Some");
        let expr = result.unwrap();
        assert!(expr.sort().is_bitvec(), "discriminant should be bitvec, got {:?}", expr.sort());
        let smt = expr.to_string();
        // Three valid discriminant encoding paths:
        // 1. ADT Datatype sort: ITE chain with `(_ is Constructor)` tests
        // 2. BV-flattened sort: ITE chain with `(= tag #bNN)` BV equality tests
        // 3. Symbolic fallback: `__discr_*` variable for non-flattenable sorts
        if smt.contains("ite") {
            // ITE chain path (ADT or BV-flattened).
            // ADT path uses `(_ is <ctor>)`, BV path uses `(= tag_var #bNN)`.
            assert!(
                smt.contains("(_ is") || smt.contains("= "),
                "ITE chain discriminant should contain is-constructor or BV equality tests, got: {smt}"
            );
        } else {
            // Symbolic fallback: non-Datatype, non-flattenable sort
            match expr.value() {
                ExprValue::Var { name } => {
                    assert!(
                        name.starts_with("__discr_"),
                        "symbolic discriminant should use __discr_* naming, got {name}"
                    );
                }
                other => panic!("expected either ITE chain or symbolic variable, got {other:?}"),
            }
        }
    });
}

// =============================================================================
// Strategy 3a: custom Option-like 2-variant enum with is_constructor path
// (Part of #2353)
// =============================================================================

const CUSTOM_OPTION_LIKE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum MaybeVal {
        Empty,
        Filled(u32),
    }

    pub fn probe_custom_option_like(m: MaybeVal) -> u32 {
        match m {
            MaybeVal::Empty => 0,
            MaybeVal::Filled(v) => v,
        }
    }
"#;

/// Custom Option-like enum (one empty, one payload variant) exercises
/// the is_constructor-based discriminant extraction path.
/// This differs from `Option<T>` which may use flattened enum mapping.
///
/// Part of #2353 AC 3: test is-constructor tester path.
#[test]
fn test_translate_discriminant_custom_option_like_pipeline() {
    with_test_ay_ctx_for_source(CUSTOM_OPTION_LIKE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_option_like");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_custom_option_like", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_custom_option_like", bb_count);

        // 2-variant match should produce at least 2 transition rules.
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "2-variant match should have >= 2 transition rules, got {}",
            transition_rules.len()
        );
    });
}

/// Directly test translate_discriminant on custom Option-like enum.
/// Should produce ITE(is_constructor(Filled), 1, 0).
///
/// Part of #2353 AC 3.
#[test]
fn test_translate_discriminant_custom_option_like_returns_ite() {
    with_test_ay_ctx_for_source(CUSTOM_OPTION_LIKE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_option_like");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_custom_option_like", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (discr_place, _target) = find_discriminant_local(&body)
            .expect("probe_custom_option_like should contain a Discriminant rvalue");
        let result = chc_ctx.translate_discriminant(&discr_place, &HashSet::new());
        assert!(result.is_some(), "custom Option-like enum discriminant should return Some");
        let expr = result.unwrap();
        assert!(
            expr.sort().is_bitvec(),
            "Option-like discriminant should be bitvec, got {:?}",
            expr.sort()
        );
        let smt = expr.to_string();
        assert!(
            smt.contains("ite"),
            "Option-like discriminant should use ITE encoding, got: {smt}"
        );
    });
}

// =============================================================================
// Strategy 1: allocation-related Result discriminant is symbolic
// (Part of #2353)
// =============================================================================

const ALLOC_RESULT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(allocator_api)]

    use std::alloc::{Allocator, Global, Layout};

    pub fn probe_alloc_discriminant() -> u32 {
        let layout = Layout::new::<u32>();
        let result = Global.allocate(layout);
        let result_ref = &result;
        match result_ref {
            Ok(_ptr) => 1,
            Err(_e) => 0,
        }
    }
"#;

/// Fix #2618: allocation Result discriminant is symbolic (not forced to 0).
/// This allows the solver to explore both Ok and Err(AllocError) paths.
///
/// Part of #2353 AC 1, updated for #2618.
#[test]
fn test_translate_discriminant_alloc_result_returns_symbolic() {
    with_test_ay_ctx_for_source(ALLOC_RESULT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_alloc_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (discr_place, _target) = find_discriminant_local_where(&body, |place| {
            matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref))
        })
        .expect("probe_alloc_discriminant should contain a deref Discriminant place");
        let discr = chc_ctx
            .translate_discriminant(&discr_place, &HashSet::new())
            .expect("allocation Result discriminant should translate");

        assert_eq!(
            discr.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "symbolic discriminant should be pointer-width bitvec, got {:?}",
            discr.sort()
        );
        match discr.value() {
            ExprValue::Var { name } => {
                assert!(
                    name.starts_with("__alloc_discr_"),
                    "symbolic alloc discriminant should use __alloc_discr_* naming, got {name}"
                );
            }
            other => panic!("expected symbolic discriminant variable (#2618), got {other:?}"),
        }
    });
}

// =============================================================================
// Strategy 3b: 2-variant enum where BOTH variants have payloads
// (Part of #2353)
// =============================================================================

const EITHER_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Either {
        Left(u32),
        Right(i64),
    }

    pub fn probe_either_match(e: Either) -> i64 {
        match e {
            Either::Left(v) => v as i64,
            Either::Right(v) => v,
        }
    }
"#;

/// A 2-variant enum where both variants have payloads does not match the
/// Option-like path. It should use is_constructor(variant_0) discriminant logic.
///
/// Part of #2353 AC 3: test is-constructor tester path (2-variant).
#[test]
fn test_translate_discriminant_both_payload_variants_pipeline() {
    with_test_ay_ctx_for_source(EITHER_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_either_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_either_match", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_either_match", bb_count);

        // 2-variant match should produce at least 2 transition rules.
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "2-variant both-payload match should have >= 2 transition rules, got {}",
            transition_rules.len()
        );
    });
}

/// Directly test translate_discriminant on 2-variant both-payload enum.
/// Should produce is_constructor(Left) -> ITE(is_Left, 0, 1).
///
/// Part of #2353 AC 3.
#[test]
fn test_translate_discriminant_both_payload_returns_ite() {
    with_test_ay_ctx_for_source(EITHER_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_either_match");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_either_match", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (discr_place, _target) = find_discriminant_local(&body)
            .expect("probe_either_match should contain a Discriminant rvalue");
        let result = chc_ctx.translate_discriminant(&discr_place, &HashSet::new());
        assert!(result.is_some(), "2-variant both-payload enum discriminant should return Some");
        let expr = result.unwrap();
        assert!(
            expr.sort().is_bitvec(),
            "both-payload discriminant should be bitvec, got {:?}",
            expr.sort()
        );
        let smt = expr.to_string();
        assert!(
            smt.contains("ite"),
            "both-payload discriminant should use ITE encoding, got: {smt}"
        );
    });
}

// =============================================================================
// Non-enum discriminants: return the semantic zero constant
// Coverage: codegen_stmt_aggregate_discr.rs non-enum catch-all
// =============================================================================

const NON_ADT_DISCR_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]

    use std::intrinsics::discriminant_value;

    pub enum MyError {
        Error1(i32),
        Error2(&'static str),
        Error3 { description: String, code: u32 },
    }

    pub fn probe_non_adt_value() -> u8 {
        discriminant_value(&2)
    }

    pub fn probe_non_adt_ctor() -> u8 {
        discriminant_value(&MyError::Error1)
    }
"#;

const COROUTINE_DISCR_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_coroutine_resume_once() -> bool {
        let mut add_one = #[coroutine]
        |mut resume: u8| {
            loop {
                resume = yield resume.saturating_add(1);
            }
        };
        let keep_ref = &mut add_one;
        let _ = keep_ref;

        match Pin::new(&mut add_one).resume(0) {
            CoroutineState::Yielded(value) => value == 1,
            CoroutineState::Complete(_) => false,
        }
    }
"#;

const COROUTINE_PIN_LOOP_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_coroutine_loop() -> bool {
        let mut add_one = #[coroutine]
        |mut resume: u8| {
            loop {
                resume = yield resume.saturating_add(1);
            }
        };
        for _ in 0..2 {
            let res = Pin::new(&mut add_one).resume(1);
            match res {
                CoroutineState::Yielded(value) if value == 2 => {}
                _ => return false,
            }
        }
        true
    }
"#;

/// `discriminant_value(&2)` lowers to `Rvalue::Discriminant` on a primitive
/// referent in current rustc. The CHC translator must return the semantic zero
/// constant instead of dropping the assignment to fallback.
///
/// Part of #2391 AC: coverage gaps.
#[test]
fn test_translate_discriminant_non_adt_returns_zero() {
    with_test_ay_ctx_for_source(NON_ADT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_adt_value");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_adt_value", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (place, _) = find_discriminant_local(&body)
            .expect("probe_non_adt_value should contain Discriminant");
        let ty = place.ty(body.locals()).expect("discriminant place type");
        assert!(
            !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(_, _))),
            "discriminant_value(&2) should target a non-enum referent, got {:?}",
            ty
        );

        let result = chc_ctx
            .translate_discriminant(&place, &HashSet::new())
            .expect("non-enum discriminant should translate to zero");
        assert_eq!(
            result.to_string(),
            Expr::bitvec_const(0u64, POINTER_WIDTH).to_string(),
            "non-enum discriminant should encode as zero, got {:?}",
            result
        );
    });
}

/// Constructor-function references like `&MyError::Error1` are also non-enum
/// referents. They should take the same zero-discriminant path as primitives.
#[test]
fn test_translate_discriminant_non_adt_ctor_returns_zero() {
    with_test_ay_ctx_for_source(NON_ADT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_adt_ctor");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_adt_ctor", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (place, _) =
            find_discriminant_local(&body).expect("probe_non_adt_ctor should contain Discriminant");
        let ty = place.ty(body.locals()).expect("discriminant place type");
        assert!(
            !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(_, _))),
            "constructor reference should lower through a non-enum referent, got {:?}",
            ty
        );

        let result = chc_ctx
            .translate_discriminant(&place, &HashSet::new())
            .expect("constructor-function discriminant should translate to zero");
        assert_eq!(
            result.to_string(),
            Expr::bitvec_const(0u64, POINTER_WIDTH).to_string(),
            "constructor-function discriminant should encode as zero, got {:?}",
            result
        );
    });
}

/// Coroutine discriminant reads on `*_ref` should resolve to the referent local's
/// direct coroutine root, not fall back through the reference local.
#[test]
fn test_translate_discriminant_coroutine_deref_uses_referent_local() {
    with_test_ay_ctx_for_source(COROUTINE_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coroutine_resume_once");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_resume_once", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (ref_local, target_local) =
            find_coroutine_ref_local(&chc_ctx, &body).expect("body should contain a coroutine ref");
        let place = rustc_public::mir::Place {
            local: ref_local,
            projection: vec![rustc_public::mir::ProjectionElem::Deref],
        };
        let target_expr = chc_ctx
            .resolve_local_expr(target_local, &HashSet::new())
            .expect("target coroutine local should resolve to a root expr");
        let expected = crate::codegen_ay::types::coroutine_discriminant_select(target_expr)
            .expect("target coroutine expr should expose a discriminant field");

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let result = chc_ctx
            .translate_discriminant(&place, &HashSet::new())
            .expect("coroutine deref discriminant should translate");

        assert_eq!(
            result.sort().bitvec_width(),
            Some(crate::codegen_ay::types::POINTER_WIDTH),
            "coroutine discriminant should normalize to pointer-width bitvec"
        );
        assert!(
            result.to_string().contains(&expected.to_string()),
            "Discriminant(*_{ref_local}) should read from referent local {target_local}, got {result}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine deref discriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine deref discriminant should avoid aggregate-encoding gaps"
        );
    });
}

/// Coroutine discriminant reads should also resolve through the auxiliary
/// arg-pointee slot when `ref_targets` is unavailable.
#[test]
fn test_translate_discriminant_coroutine_deref_uses_arg_pointee_slot() {
    with_test_ay_ctx_for_source(COROUTINE_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coroutine_resume_once");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_resume_once", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (ref_local, target_local) =
            find_coroutine_ref_local(&chc_ctx, &body).expect("body should contain a coroutine ref");
        let target_expr = chc_ctx
            .resolve_local_expr(target_local, &HashSet::new())
            .expect("target coroutine local should resolve to a root expr");
        let expected = crate::codegen_ay::types::coroutine_discriminant_select(target_expr.clone())
            .expect("target coroutine expr should expose a discriminant field");

        let pointee_vec_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair(
            "probe_coroutine_arg_pointee",
            "probe_coroutine_arg_pointee__out",
            target_expr.sort().clone(),
        );
        let track_key = usize::MAX - pointee_vec_idx;
        chc_ctx.ref_resolution.ref_targets.remove(&ref_local);
        chc_ctx.ref_resolution.ref_arg_pointee_idx.insert(ref_local, pointee_vec_idx);
        chc_ctx.encode.local_expr_env.insert(track_key, target_expr);

        let place = rustc_public::mir::Place {
            local: ref_local,
            projection: vec![rustc_public::mir::ProjectionElem::Deref],
        };
        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let result = chc_ctx
            .translate_discriminant(&place, &HashSet::new())
            .expect("coroutine arg-pointee discriminant should translate");

        assert_eq!(
            result.sort().bitvec_width(),
            Some(crate::codegen_ay::types::POINTER_WIDTH),
            "coroutine discriminant should normalize to pointer-width bitvec"
        );
        assert!(
            result.to_string().contains(&expected.to_string()),
            "Discriminant(*_{ref_local}) should read from arg-pointee slot, got {result}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine arg-pointee discriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine arg-pointee discriminant should avoid aggregate-encoding gaps"
        );
    });
}

fn find_coroutine_ref_local(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> Option<(usize, usize)> {
    chc_ctx.ref_resolution.ref_targets.iter().find_map(|(&ref_local, ref_target)| {
        let target_ty = body.locals().get(ref_target.local).map(|decl| decl.ty);
        (ref_target.projections.is_empty()
            && matches!(
                target_ty.map(|ty| ty.kind()),
                Some(TyKind::RigidTy(RigidTy::Coroutine(..)))
            ))
        .then_some((ref_local, ref_target.local))
    })
}

fn find_coroutine_closure_body(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    suffix: &str,
) -> rustc_public::mir::Body {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path.contains(suffix) && path.contains("{closure#0}")
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing closure for '{suffix}'"),
        [single] => single.body().expect("closure body should exist"),
        many => panic!("ambiguous closure for '{suffix}': {many:?}"),
    }
}

fn find_coroutine_discriminant_place(
    body: &rustc_public::mir::Body,
) -> Option<rustc_public::mir::Place> {
    use rustc_public::mir::StatementKind;

    body.blocks.iter().find_map(|bb| {
        bb.statements.iter().find_map(|stmt| {
            let StatementKind::Assign(_, rhs) = &stmt.kind else {
                return None;
            };
            let rustc_public::mir::Rvalue::Discriminant(place) = rhs else {
                return None;
            };
            place
                .ty(body.locals())
                .ok()
                .filter(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))))
                .map(|_| place.clone())
        })
    })
}

fn find_resume_result_discriminant_place(
    body: &rustc_public::mir::Body,
    chc_ctx: &ChcCtx<'_, '_>,
) -> Option<rustc_public::mir::Place> {
    use rustc_public::mir::{ProjectionElem, StatementKind};

    body.blocks.iter().find_map(|bb| {
        bb.statements.iter().find_map(|stmt| {
            let StatementKind::Assign(_, rhs) = &stmt.kind else {
                return None;
            };
            let rustc_public::mir::Rvalue::Discriminant(place) = rhs else {
                return None;
            };
            if !(place.projection.len() == 1
                && matches!(place.projection[0], ProjectionElem::Deref))
            {
                return None;
            }
            let ref_target = chc_ctx.ref_resolution.ref_targets.get(&place.local)?;
            if !ref_target.projections.is_empty() {
                return None;
            }
            let target_local = ref_target.local;
            (chc_ctx.flatten.flattened_tuple_locals.contains(&target_local)
                || chc_ctx.flatten.enum_bv_layouts.contains_key(&target_local))
            .then_some(place.clone())
        })
    })
}

#[test]
fn test_translate_discriminant_coroutine_pin_wrapper_uses_arg_pointee_slot() {
    with_test_ay_ctx_for_source(COROUTINE_PIN_LOOP_SOURCE, |ctx| {
        let body = find_coroutine_closure_body(ctx.tcx, "probe_coroutine_loop");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_loop::{closure#0}", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let place = find_coroutine_discriminant_place(&body)
            .expect("closure body should contain a coroutine discriminant read");
        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&place.local)
            .expect("Pin<&mut Coroutine> field copy should inherit arg-pointee state");

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let result = chc_ctx
            .translate_discriminant(&place, &HashSet::new())
            .expect("coroutine Pin deref discriminant should translate");

        assert_eq!(
            result.sort().bitvec_width(),
            Some(crate::codegen_ay::types::POINTER_WIDTH),
            "coroutine discriminant should normalize to pointer-width bitvec"
        );
        assert!(
            !matches!(result.value(), ExprValue::Var { .. }),
            "coroutine Pin deref discriminant should not fall back to a symbolic var, got {result}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine Pin deref discriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine Pin deref discriminant should avoid aggregate-encoding gaps"
        );
        assert!(
            !chc_ctx.encode.modified_state_indices.contains(&pointee_vec_idx),
            "discriminant read should not mark pointee idx {pointee_vec_idx} modified"
        );
    });
}

#[test]
fn test_translate_discriminant_coroutine_ref_target_uses_arg_pointee_slot() {
    with_test_ay_ctx_for_source(COROUTINE_PIN_LOOP_SOURCE, |ctx| {
        let body = find_coroutine_closure_body(ctx.tcx, "probe_coroutine_loop");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_loop::{closure#0}", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let place = find_coroutine_discriminant_place(&body)
            .expect("closure body should contain a coroutine discriminant read");
        let ref_local = place.local;
        assert!(
            chc_ctx.ref_resolution.ref_arg_pointee_idx.contains_key(&ref_local),
            "Pin<&mut Coroutine> field copy should inherit arg-pointee state"
        );
        chc_ctx.ref_resolution.ref_targets.insert(
            ref_local,
            crate::codegen_ay::chc::RefTarget::with_projections(ref_local, vec![]),
        );

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let result = chc_ctx
            .translate_discriminant(&place, &HashSet::new())
            .expect("coroutine discriminant should resolve through synthetic ref_target");

        assert!(
            !matches!(result.value(), ExprValue::Var { .. }),
            "coroutine ref_target discriminant should not fall back to a symbolic var, got {result}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine ref_target discriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine ref_target discriminant should avoid aggregate-encoding gaps"
        );
    });
}

#[test]
fn test_translate_discriminant_resume_result_deref_uses_flattened_state_local() {
    with_test_ay_ctx_for_source(COROUTINE_RESUME_LIVE_ACROSS_YIELD_SOURCE, |ctx| {
        let body = find_coroutine_closure_body(ctx.tcx, "probe_resume_live_across_yield");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_resume_live_across_yield::{closure#0}",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let place = find_resume_result_discriminant_place(&body, &chc_ctx)
            .expect("resume-live-across-yield should contain a CoroutineState discriminant read");
        let ref_target = chc_ctx
            .ref_resolution
            .ref_targets
            .get(&place.local)
            .cloned()
            .expect("CoroutineState discriminant read should resolve through ref_targets");
        assert!(
            ref_target.projections.is_empty(),
            "resume result discriminant deref should resolve to a direct local"
        );
        let target_local = ref_target.local;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&target_local),
            "resume result local {target_local} should be flattened"
        );

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let result = chc_ctx
            .translate_discriminant(&place, &HashSet::new())
            .expect("resume result discriminant should translate through flattened local");

        assert!(
            !matches!(result.value(), ExprValue::Var { .. }),
            "resume result discriminant should avoid symbolic fallback, got {result}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "resume result discriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "resume result discriminant should avoid aggregate-encoding gaps"
        );
    });
}

// =============================================================================
// Discriminant range constraints (soundness)
// =============================================================================

/// Verify 3-variant enum discriminant behavior:
/// - Datatype sort: uses is_constructor ITE chain, no range constraint needed
/// - Non-Datatype sort: uses symbolic + bvult(3) range constraint
#[test]
fn test_translate_discriminant_three_variant_constraint_behavior() {
    with_test_ay_ctx_for_source(THREEVARIANT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_three_variant_match");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_three_variant_match", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.heap_state.pending_updates.clear();

        let (discr_place, _target) = find_discriminant_local(&body)
            .expect("probe_three_variant_match should contain a Discriminant rvalue");
        let result = chc_ctx.translate_discriminant(&discr_place, &HashSet::new());
        assert!(result.is_some(), "3-variant enum discriminant should return Some");

        let expr = result.unwrap();
        let smt = expr.to_string();
        if smt.contains("(_ is") || (smt.contains("ite") && smt.contains("= ")) {
            // ITE chain path (ADT or BV-flattened): no range constraint needed —
            // is_constructor tests or BV tag equality tests already constrain the
            // discriminant to valid variant indices.
            // pending_updates may or may not be empty depending on other side effects.
        } else {
            // Symbolic fallback path: range constraint is required.
            let constraints = &chc_ctx.heap_state.pending_updates;
            assert!(
                !constraints.is_empty(),
                "symbolic discriminant should add range constraint to pending_updates"
            );
            assert!(
                constraint_tree_contains(&constraints[0], &|e| matches!(
                    e.value(),
                    ExprValue::BvULt(..)
                )),
                "range constraint should contain a BvULt"
            );
        }
    });
}

/// Verify allocation Result symbolic discriminants emit a range constraint.
#[test]
fn test_translate_discriminant_alloc_result_has_range_constraint() {
    with_test_ay_ctx_for_source(ALLOC_RESULT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_alloc_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.heap_state.pending_updates.clear();

        let (discr_place, _target) = find_discriminant_local_where(&body, |place| {
            matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref))
        })
        .expect("probe_alloc_discriminant should contain a deref Discriminant place");
        let discr = chc_ctx
            .translate_discriminant(&discr_place, &HashSet::new())
            .expect("allocation Result discriminant should translate");

        assert!(
            matches!(discr.value(), ExprValue::Var { .. }),
            "allocation Result discriminant should be symbolic, got {:?}",
            discr.value()
        );

        let constraints = &chc_ctx.heap_state.pending_updates;
        assert!(
            !constraints.is_empty(),
            "allocation Result symbolic discriminant should add range constraint to pending_updates"
        );
    });
}

/// Helper: find a Discriminant rvalue in MIR, returning (place, target_local).
fn find_discriminant_local(
    body: &rustc_public::mir::Body,
) -> Option<(rustc_public::mir::Place, usize)> {
    find_discriminant_local_where(body, |_| true)
}

fn find_discriminant_local_where<F>(
    body: &rustc_public::mir::Body,
    mut predicate: F,
) -> Option<(rustc_public::mir::Place, usize)>
where
    F: FnMut(&rustc_public::mir::Place) -> bool,
{
    for block in &body.blocks {
        for stmt in &block.statements {
            if let rustc_public::mir::StatementKind::Assign(target, rvalue) = &stmt.kind
                && let rustc_public::mir::Rvalue::Discriminant(place) = rvalue
                && predicate(place)
            {
                return Some((place.clone(), target.local));
            }
        }
    }
    None
}

// =============================================================================
// D1 diagnostic: MyEnum with ZST fields reaches enum_bv_layouts (#3994)
// =============================================================================

const MY_ENUM_ZST_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(PartialEq)]
    struct ZeroSized {}

    #[derive(PartialEq)]
    enum MyEnum {
        NoFields,
        DataFul(bool),
        UnitFields((), ()),
        ZSTField(ZeroSized),
        ZSTStruct { field: ZeroSized, unit: () },
    }

    fn probe_my_enum_discriminant(x: MyEnum) -> isize {
        match x {
            MyEnum::NoFields => 0,
            MyEnum::DataFul(_) => 1,
            MyEnum::UnitFields(_, _) => 2,
            MyEnum::ZSTField(_) => 3,
            MyEnum::ZSTStruct { .. } => 4,
        }
    }
"#;

/// Part of #3994 D1: Verify that a 5-variant enum with ZST fields
/// populates `enum_bv_layouts` after the ZST detection broadening.
#[test]
fn test_my_enum_zst_populates_enum_bv_layouts() {
    with_test_ay_ctx_for_source(MY_ENUM_ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_my_enum_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_my_enum_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the MyEnum local via Discriminant read in MIR.
        let enum_local = body.blocks.iter().find_map(|bb| {
            bb.statements.iter().find_map(|stmt| {
                if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                    && let rustc_public::mir::Rvalue::Discriminant(place) = rvalue
                    && place.projection.is_empty()
                {
                    Some(place.local)
                } else {
                    None
                }
            })
        });
        let enum_local = enum_local.expect("MIR should contain a Discriminant read on MyEnum");

        // Core assertion: the local must be in enum_bv_layouts.
        let layout = chc_ctx
            .flatten
            .enum_bv_layouts
            .get(&enum_local)
            .expect("MyEnum should populate enum_bv_layouts (ZST detection broadened)");

        assert_eq!(layout.num_constructors, 5, "MyEnum has 5 variants");
        assert_eq!(layout.max_payload_slots, 1, "only DataFul(bool) contributes a leaf");
        assert_eq!(layout.payload_slot(1, 0), Some(0), "DataFul(bool) keeps payload slot 0");
        assert_eq!(layout.payload_slot(2, 0), None, "UnitFields.0 is omitted");
        assert_eq!(layout.payload_slot(2, 1), None, "UnitFields.1 is omitted");
        assert_eq!(layout.payload_slot(3, 0), None, "ZSTField payload is omitted");
        assert_eq!(layout.payload_slot(4, 0), None, "ZSTStruct.field is omitted");
        assert_eq!(layout.payload_slot(4, 1), None, "ZSTStruct.unit is omitted");

        // translate_discriminant should produce a concrete ITE chain, not a fallback.
        let place = rustc_public::mir::Place { local: enum_local, projection: vec![] };
        let discr = chc_ctx.translate_discriminant(&place, &HashSet::new());
        assert!(discr.is_some(), "translate_discriminant should succeed on BV-flattened MyEnum");
    });
}

// =============================================================================
// D1 diagnostic: Shape with nested struct payload reaches enum_bv_layouts (#3994)
// =============================================================================

const SHAPE_NESTED_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone)]
    pub struct Point { x: i32, y: i32 }

    #[derive(Clone)]
    pub enum Shape {
        Empty,
        WithPoint(Point),
        WithCoords(i32, i32),
    }

    pub fn probe_shape_discriminant(s: Shape) -> i32 {
        match s {
            Shape::Empty => 0,
            Shape::WithPoint(p) => p.x + p.y,
            Shape::WithCoords(x, y) => x + y,
        }
    }
"#;

/// Part of #3994 D1: Verify that Shape (nested struct payload) populates
/// `enum_bv_layouts` and that downcast+nested field projection resolves.
#[test]
fn test_shape_nested_struct_populates_enum_bv_layouts() {
    with_test_ay_ctx_for_source(SHAPE_NESTED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shape_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_shape_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the Shape local via Discriminant read.
        let enum_local = body.blocks.iter().find_map(|bb| {
            bb.statements.iter().find_map(|stmt| {
                if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                    && let rustc_public::mir::Rvalue::Discriminant(place) = rvalue
                    && place.projection.is_empty()
                {
                    Some(place.local)
                } else {
                    None
                }
            })
        });
        let enum_local = enum_local.expect("MIR should contain a Discriminant read on Shape");

        let layout = chc_ctx
            .flatten
            .enum_bv_layouts
            .get(&enum_local)
            .expect("Shape should populate enum_bv_layouts");

        assert_eq!(layout.num_constructors, 3, "Shape has 3 variants");
        assert_eq!(
            layout.max_payload_slots, 2,
            "WithPoint(Point) and WithCoords both have 2 leaves"
        );

        // Verify ctor_field_slot for WithPoint: one field (Point) starting at leaf 0
        assert_eq!(layout.ctor_field_slot[1].len(), 1, "WithPoint has 1 field");
        assert_eq!(layout.ctor_field_slot[1][0], 0, "Point starts at payload slot 0");

        // Verify ctor_field_slot for WithCoords: two fields at positions 0 and 1
        assert_eq!(layout.ctor_field_slot[2].len(), 2, "WithCoords has 2 fields");
        assert_eq!(layout.ctor_field_slot[2][0], 0);
        assert_eq!(layout.ctor_field_slot[2][1], 1);

        // translate_discriminant should produce a concrete ITE chain.
        let place = rustc_public::mir::Place { local: enum_local, projection: vec![] };
        let discr = chc_ctx.translate_discriminant(&place, &HashSet::new());
        assert!(discr.is_some(), "translate_discriminant should succeed on BV-flattened Shape");
    });
}

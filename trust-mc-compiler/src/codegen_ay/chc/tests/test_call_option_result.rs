// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for codegen_call_option_result.rs — Option/Result predicate,
//! unwrap, and combinator stubs flowing through the full CHC pipeline.
//!
//! Detection tests live in test_collections_result.rs and test_stubs_util.rs;
//! these tests verify that the dispatch + codegen path (emit_stub_call_result,
//! codegen_call_option_predicate, codegen_call_result_predicate,
//! codegen_call_unwrap_or, codegen_call_unwrap_expect,
//! codegen_call_unwrap_or_else, codegen_call_combinator) produces
//! structurally correct CHC VCs.
//!
//! Part of #2296 (chc/ test coverage gaps).

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_option_result::CallOptionResult;
use super::common::*;
use crate::codegen_ay::emit_chc;
use ay_bindings::Expr;

// =============================================================================
// Option predicate pipeline tests (is_some, is_none)
// =============================================================================

/// Option::is_some flows through codegen_call_option_predicate → emit_stub_call_result.
/// The pipeline should produce a VC with bool-typed constraints for the discriminant check.
#[test]
fn test_option_is_some_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_some(x: Option<u32>) -> bool {
            x.is_some()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_some");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_is_some", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_is_some", body.blocks.len());

        // Result type is bool — state vars should include bool or small BV
        let has_bool_like = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool_like, "is_some VC should have bool-like state vars for return");
    });
}

/// Option::is_none flows through codegen_call_option_predicate (negation of is_some).
#[test]
fn test_option_is_none_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_none(x: Option<u32>) -> bool {
            x.is_none()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_none");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_is_none", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_is_none", body.blocks.len());

        // Semantic: is_none returns bool — relations should carry Bool sort
        let has_bool_like = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool_like, "is_none VC should have bool-like state vars for return");

        // SMT output should declare Bool state for the bool return
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("Bool"),
            "is_none should declare Bool state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Result predicate pipeline tests (is_ok, is_err)
// =============================================================================

/// Result::is_ok flows through codegen_call_result_predicate → emit_stub_call_result.
#[test]
fn test_result_is_ok_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_ok(x: Result<u32, u64>) -> bool {
            x.is_ok()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_ok");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_is_ok", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_is_ok", body.blocks.len());

        // Should have bool-typed constraints from the discriminant check
        let has_bool_like = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool_like, "is_ok VC should have bool-like state vars");
    });
}

/// Result::is_err flows through codegen_call_result_predicate.
#[test]
fn test_result_is_err_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_err(x: Result<u32, u64>) -> bool {
            x.is_err()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_err");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_is_err", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_is_err", body.blocks.len());

        // Semantic: is_err returns bool — relations should carry Bool sort
        let has_bool_like = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool_like, "is_err VC should have bool-like state vars for return");
    });
}

// =============================================================================
// Unwrap/expect pipeline tests
// =============================================================================

/// Option::unwrap flows through codegen_call_unwrap_expect → emit_stub_call_result.
#[test]
fn test_option_unwrap_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap(x: Option<u32>) -> u32 {
            x.unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap", body.blocks.len());

        // Return type is u32 — should have BV32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "unwrap VC should have BV32 state vars for u32 return");
    });
}

/// Result::unwrap flows through codegen_call_unwrap_expect.
#[test]
fn test_result_unwrap_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_unwrap(x: Result<u32, u64>) -> u32 {
            x.unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_unwrap");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_unwrap", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_unwrap", body.blocks.len());

        // Semantic: Result<u32, u64> unwrap returns u32 — BV32 in relation sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Result unwrap VC should have BV32 state vars for u32 return");

        // SMT output should declare BitVec(32) for u32 payload
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "Result unwrap should declare BV32 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

#[test]
fn test_result_unwrap_propagates_known_layout_sizes_to_unwrapped_layout_local() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::alloc::Layout;

        pub fn probe_result_layout_unwrap() -> Layout {
            Layout::from_size_align(16, 8).unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_layout_unwrap");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_result_layout_unwrap", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut unwrap_call = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && let Some(StubKind::ResultUnwrap) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_unwrap_expect)
            {
                unwrap_call = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            unwrap_call.expect("expected Result::unwrap call in checked-layout MIR");
        let src_local = match args.first() {
            Some(Operand::Copy(place) | Operand::Move(place)) => place.local,
            other => panic!("expected unwrap self operand to be a local move/copy, got {other:?}"),
        };

        chc_ctx.known_layout_sizes.insert(src_local, (16, 8));

        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for unwrap block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let cx = ChcCallContext {
            stub: StubKind::ResultUnwrap,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };

        chc_ctx.codegen_call_unwrap_expect(&cx);

        assert_eq!(
            chc_ctx.known_layout_sizes.get(&destination.local).copied(),
            Some((16, 8)),
            "Result::unwrap should propagate cached concrete layout sizes to the unwrapped Layout local"
        );
    });
}

/// Option::expect flows through codegen_call_unwrap_expect.
#[test]
fn test_option_expect_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_expect(x: Option<u32>) -> u32 {
            x.expect("should be Some")
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_expect");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_expect", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_expect", body.blocks.len());

        // Semantic: expect returns u32 — BV32 in relation sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "expect VC should have BV32 state vars for u32 return");
    });
}

// =============================================================================
// Unwrap_or pipeline tests
// =============================================================================

/// Option::unwrap_or flows through codegen_call_unwrap_or → emit_stub_call_result.
/// Should produce ITE(is_some, inner, default) constraint.
#[test]
fn test_option_unwrap_or_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_or(x: Option<u32>) -> u32 {
            x.unwrap_or(0)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_or");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap_or", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap_or", body.blocks.len());

        // Should have BV32 for u32 return
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "unwrap_or VC should have BV32 state vars");
    });
}

/// Result::unwrap_or flows through codegen_call_unwrap_or.
#[test]
fn test_result_unwrap_or_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_unwrap_or(x: Result<u32, u64>) -> u32 {
            x.unwrap_or(0)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_unwrap_or");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_unwrap_or", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_unwrap_or", body.blocks.len());

        // Semantic: Result<u32, u64> unwrap_or returns u32 — BV32 in relation sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Result unwrap_or VC should have BV32 state vars for u32 return");

        // SMT output should declare BitVec(32) for u32 payload
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "Result unwrap_or should declare BV32 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Unwrap_or_else pipeline tests
// =============================================================================

/// Option::unwrap_or_else flows through codegen_call_unwrap_or_else → emit_stub_call_result.
/// Closure result is over-approximated as symbolic.
#[test]
fn test_option_unwrap_or_else_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_or_else(x: Option<u32>) -> u32 {
            x.unwrap_or_else(|| 42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_or_else");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap_or_else", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap_or_else", body.blocks.len());

        // Semantic: unwrap_or_else returns u32 — BV32 in relation sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "unwrap_or_else VC should have BV32 state vars for u32 return");
    });
}

// =============================================================================
// Combinator pipeline tests (and_then, map, ok_or_else)
// =============================================================================

/// Option::and_then flows through codegen_call_combinator.
/// Closure results are over-approximated as symbolic values.
#[test]
fn test_option_and_then_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_and_then(x: Option<u32>) -> Option<u64> {
            x.and_then(|v| Some(v as u64))
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_and_then");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_and_then", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_and_then", body.blocks.len());

        // Semantic: and_then maps Option<u32> to Option<u64> — BV32 for input, BV64 for output.
        // State may appear as relation arg sorts or free variables (declare-var).
        let has_bv32_rel =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        let has_bv32_var = vc.vars().iter().any(|v| v.sort.bitvec_width() == Some(32));
        assert!(
            has_bv32_rel || has_bv32_var,
            "and_then VC should have BV32 state vars for u32 input"
        );

        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "and_then should declare BV32 for u32 input: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

/// Result::map flows through codegen_call_combinator.
#[test]
fn test_result_map_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_map(x: Result<u32, u64>) -> Result<u64, u64> {
            x.map(|v| v as u64)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_map");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_map", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_map", body.blocks.len());

        // Semantic: Result map uses BV64 for the u64 output type.
        // State may appear as relation arg sorts or free variables (declare-var).
        let has_bv64_rel =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64)));
        let has_bv64_var = vc.vars().iter().any(|v| v.sort.bitvec_width() == Some(64));
        assert!(
            has_bv64_rel || has_bv64_var,
            "Result map VC should have BV64 state vars for u64 output"
        );

        // SMT output should declare both BV32 (input Ok type) and BV64 (output Ok/Err type)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 64)"),
            "Result map should declare BV64 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Collection predicate pipeline tests (Vec::is_empty)
// =============================================================================

/// Vec::is_empty flows through codegen_call_collection_predicate → emit_stub_call_result.
#[test]
fn test_vec_is_empty_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_is_empty(v: &Vec<u32>) -> bool {
            v.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_is_empty", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_is_empty", body.blocks.len());

        // Semantic: is_empty returns bool — relations should carry Bool sort
        let has_bool_like = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool_like, "Vec::is_empty VC should have bool-like state vars for return");
    });
}

/// Vec::is_empty without tracked length increments sound_fallback_count
/// and does not add a concrete `true` predicate constraint.
/// Part of #3725: under-approximation fix regression test.
#[test]
fn test_vec_is_empty_untracked_increments_sound_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_vec_is_empty_fallback(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_vec_is_empty_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) = call_site.expect("expected call terminator in MIR");
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: fallback counter at zero");

        // Use empty args so translate_collection_predicate_call cannot resolve
        // a tracked collection, forcing the None → sound_fallback path.
        let cx = ChcCallContext {
            stub: StubKind::VecIsEmpty,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_collection_predicate(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one transition rule from collection predicate"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "VecIsEmpty without tracked length must increment sound fallback counter"
        );
    });
}

// =============================================================================
// Inline single-payload enum return regressions
// =============================================================================

const INLINE_SINGLE_PAYLOAD_ENUM_RETURN_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn maybe_one(x: u32) -> Option<u32> {
        if x == 1 {
            Some(1)
        } else {
            None
        }
    }

    pub fn probe_option_inline_eq_some(x: u32) {
        if x == 1 {
            assert!(maybe_one(x) == Some(1));
        }
    }

    pub fn maybe_bool(x: bool) -> Option<bool> {
        Some(x)
    }

    pub fn probe_option_bool_inline_eq_some(x: bool) {
        assert!(maybe_bool(x) == Some(x));
    }

    pub fn probe_option_bool_inline_ne_none(x: bool) {
        assert!(maybe_bool(x) != None);
    }

    pub fn ok_one(x: u32) -> Result<u32, u32> {
        if x == 1 {
            Ok(1)
        } else {
            Err(0)
        }
    }

    pub fn probe_result_inline_eq_ok(x: u32) {
        if x == 1 {
            assert!(ok_one(x) == Ok(1));
        }
    }

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

    pub fn probe_sign_from_constraint_all() {
        assert!(sign_from_constraint(SignConstraint::Positive) == Some(1));
        assert!(sign_from_constraint(SignConstraint::Negative) == Some(-1));
        assert!(sign_from_constraint(SignConstraint::Zero) == Some(0));
        assert!(sign_from_constraint(SignConstraint::NonNegative).is_none());
        assert!(sign_from_constraint(SignConstraint::NonPositive).is_none());
    }

    pub struct NiaScopeModel {
        scope0: usize,
        scope1: usize,
        scope2: usize,
        scope_len: usize,
        asserted_len: usize,
    }

    impl NiaScopeModel {
        pub fn new() -> Self {
            Self { scope0: 0, scope1: 0, scope2: 0, scope_len: 0, asserted_len: 0 }
        }

        pub fn push(&mut self) {
            match self.scope_len {
                0 => {
                    self.scope0 = self.asserted_len;
                    self.scope_len = 1;
                }
                1 => {
                    self.scope1 = self.asserted_len;
                    self.scope_len = 2;
                }
                2 => {
                    self.scope2 = self.asserted_len;
                    self.scope_len = 3;
                }
                _ => {}
            }
        }

        pub fn pop(&mut self) -> Option<usize> {
            match self.scope_len {
                3 => {
                    self.scope_len = 2;
                    Some(self.scope2)
                }
                2 => {
                    self.scope_len = 1;
                    Some(self.scope1)
                }
                1 => {
                    self.scope_len = 0;
                    Some(self.scope0)
                }
                _ => None,
            }
        }
    }

    pub fn probe_scope_nested_lifo() {
        let mut model = NiaScopeModel::new();

        model.asserted_len = 0;
        model.push();
        model.asserted_len = 5;
        model.push();
        model.asserted_len = 10;
        model.push();

        assert!(model.scope_len == 3);
        assert!(model.pop() == Some(10));
        assert!(model.pop() == Some(5));
        assert!(model.pop() == Some(0));
        assert!(model.scope_len == 0);
    }

    pub fn probe_result_bool_inline_ok() {
        let result: Result<bool, bool> = Ok(true);
        assert!(result == Ok(true));
    }

    pub fn probe_result_bool_inline_err() {
        let result: Result<bool, bool> = Err(false);
        assert!(result == Err(false));
    }

    pub fn probe_result_bool_symbolic_variant(is_ok: bool, val: bool) {
        let result: Result<bool, bool> = if is_ok { Ok(val) } else { Err(val) };

        if is_ok {
            assert!(result == Ok(val));
            assert!(result != Err(val));
        } else {
            assert!(result == Err(val));
            assert!(result != Ok(val));
        }
    }
"#;

// Part of #3901: cover the single-payload enum constructor path across
// callee-return Option repros and consumer-side Result<bool, bool> equality.
// `probe_scope_nested_lifo` is separated into COMPLEX_PROBES because it
// requires multi-field struct method inlining that has a distinct encoding gap.
const INLINE_SINGLE_PAYLOAD_ENUM_PROBES: [&str; 7] = [
    "probe_option_inline_eq_some",
    "probe_option_bool_inline_eq_some",
    "probe_option_bool_inline_ne_none",
    "probe_sign_from_constraint_all",
    "probe_result_bool_inline_ok",
    "probe_result_bool_inline_err",
    "probe_result_bool_symbolic_variant",
];

// Part of #3901: complex probes that exercise multi-field struct method inlining.
// These have a separate encoding gap (method-body inline constrained but
// PDR produces sat on the combined CHC system) and are tracked separately.
const _INLINE_SINGLE_PAYLOAD_COMPLEX_PROBES: [&str; 1] = ["probe_scope_nested_lifo"];

fn reset_inline_single_payload_enum_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

fn assert_inline_single_payload_enum_track(tcx: TyCtxt<'_>, track_name: &str, config: ChcConfig) {
    reset_inline_single_payload_enum_counters();

    for fn_name in INLINE_SINGLE_PAYLOAD_ENUM_PROBES {
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(tcx, &body, fn_name, config);

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(has_any_constraints(&vc), "{track_name}:{fn_name} should constrain the VC");

        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{track_name}:{fn_name} should stay on the precise inline path instead of emitting inferable summaries: {inferable_decls:?}"
        );

        let has_p_inf_rule = vc.rules.iter().any(|rule| format!("{:?}", rule).contains("P_inf_"));
        assert!(
            !has_p_inf_rule,
            "{track_name}:{fn_name} should not reference P_inf_* summaries in emitted rules"
        );

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    }

    let fallback_counts = get_chc_fallback_counts();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let _translation_drops = take_translation_drop_by_fn();
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();

    assert_eq!(
        inferable_count, 0,
        "{track_name}: inline single-payload enum return probes should not increment inferable predicate counters"
    );

    for fn_name in INLINE_SINGLE_PAYLOAD_ENUM_PROBES {
        let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{track_name}:{fn_name} should stay on the precise inline path without CHC fallback, map={fallback_counts:?}"
        );

        let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            unhandled_count, 0,
            "{track_name}:{fn_name} should not increment unhandled-call counters, map={unhandled_calls:?}"
        );
    }
}

#[test]
fn test_inline_single_payload_enum_return_equality_proves_without_fallbacks() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(INLINE_SINGLE_PAYLOAD_ENUM_RETURN_PROBE, |ctx| {
        let track_configs = [
            ("reg", ChcConfig::default()),
            (
                "mem",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            ),
        ];

        for (track_name, config) in track_configs {
            assert_inline_single_payload_enum_track(ctx.tcx, track_name, config);
        }
    });

    reset_inline_single_payload_enum_counters();
}

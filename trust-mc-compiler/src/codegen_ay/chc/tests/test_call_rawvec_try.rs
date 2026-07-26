// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_misc/rawvec_try.rs`:
//! - `codegen_call_rawvec_impl` — RawVec grow/shrink/drop/new stubs
//! - `codegen_call_try_residual_impl` — Try::branch / FromResidual stubs
//! - `codegen_call_unconstrained_stub_impl` — unconstrained destination stubs
//!
//! RawVec is Vec's internal allocation buffer. These tests verify that
//! Vec operations that internally call RawVec methods produce valid CHC
//! verification conditions.
//!
//! Part of #2921 (CHC codegen test coverage gaps).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::ChcCallContext;

// =============================================================================
// Vec push — exercises RawVecGrowOne via capacity growth
// =============================================================================

const VEC_PUSH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_push() -> Vec<u32> {
        let mut v = Vec::new();
        v.push(42);
        v
    }
"#;

#[test]
fn test_vec_push_generates_valid_vc() {
    with_test_ay_ctx_for_source(VEC_PUSH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_push", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_push", body.blocks.len());

        // Vec push involves allocation and store — should have non-trivial rules
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_push");
    });
}

// =============================================================================
// Try/? operator — exercises codegen_call_try_residual_impl
// =============================================================================

const TRY_OPERATOR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_try_operator(x: Option<u32>) -> Option<u32> {
        let val = x?;
        Some(val + 1)
    }
"#;

#[test]
fn test_try_operator_generates_valid_vc() {
    with_test_ay_ctx_for_source(TRY_OPERATOR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_try_operator");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_try_operator", ChcConfig::default());

        assert_vc_structure(&vc, "probe_try_operator", body.blocks.len());

        // The ? operator should not prevent VC generation — the function
        // should have transition rules through both Some and None paths.
        let transition_rules = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_rules >= 2,
            "probe_try_operator: expected >= 2 transition rules for Some/None branches, got {transition_rules}"
        );
    });
}

// =============================================================================
// Result try operator — exercises codegen_call_try_residual_impl with Result
// =============================================================================

const RESULT_TRY_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn inner(x: u32) -> Result<u32, u32> {
        if x > 10 { Ok(x) } else { Err(x) }
    }

    pub fn probe_result_try(a: u32) -> Result<u32, u32> {
        let val = inner(a)?;
        Ok(val + 1)
    }
"#;

#[test]
fn test_result_try_generates_valid_vc() {
    with_test_ay_ctx_for_source(RESULT_TRY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_try");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_try", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_try", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_result_try");
    });
}

// =============================================================================
// Vec with_capacity + push — exercises RawVec capacity path
// =============================================================================

const VEC_WITH_CAPACITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_with_capacity(n: u32) -> Vec<u32> {
        let mut v = Vec::with_capacity(10);
        v.push(n);
        v.push(n + 1);
        v
    }
"#;

#[test]
fn test_vec_with_capacity_generates_valid_vc() {
    with_test_ay_ctx_for_source(VEC_WITH_CAPACITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_with_capacity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_with_capacity", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_with_capacity", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_with_capacity");
    });
}

// =============================================================================
// RawVec MIR-level tests (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

/// Vec::push triggers RawVec::grow_one under the hood. Exercises codegen_call_rawvec.
#[test]
fn test_rawvec_via_vec_push() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_rawvec() -> Vec<u32> {
            let mut v = Vec::new();
            v.push(42);
            v
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_rawvec");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_vec_push_rawvec",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut rawvec_stubs = Vec::new();
        let mut rawvec_candidate_calls = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                if let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains("RawVec")
                {
                    rawvec_candidate_calls += 1;
                }
                if let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_rawvec) {
                    rawvec_stubs.push(stub);
                }
            }
        }
        assert!(
            rawvec_candidate_calls == 0 || !rawvec_stubs.is_empty(),
            "Found {rawvec_candidate_calls} RawVec-like call(s) but none classified as RawVec stubs"
        );

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_vec_push_rawvec",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_vec_push_rawvec", body.blocks.len());
        assert!(
            vc.rules.len() >= body.blocks.len(),
            "vec push should produce at least one rule per bb (got {} rules for {} bbs)",
            vc.rules.len(),
            body.blocks.len()
        );
    });
}

/// Vec with capacity triggers RawVec::with_capacity. Exercises RawVecNewIn path.
#[test]
fn test_rawvec_via_vec_with_capacity() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_capacity() -> Vec<u32> {
            Vec::with_capacity(10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_capacity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_vec_capacity",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_vec_capacity", body.blocks.len());
        assert!(
            vc.rules.len() >= body.blocks.len(),
            "Vec::with_capacity should produce >= {} rules (bb_count), got {}",
            body.blocks.len(),
            vc.rules.len()
        );
    });
}

/// Part of #1037 V1: Vec capacity stubs must mark the resolved collection local.
#[test]
fn test_rawvec_capacity_dedup_marks_vec_local_from_vec_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_for_rawvec_dedup() {
            let mut v = Vec::<u32>::new();
            v.push(7);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_for_rawvec_dedup");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_vec_push_for_rawvec_dedup", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && matches!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core),
                    Some(StubKind::VecPush)
                )
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }
        let (bb_idx, args, destination, target) = call_site.expect("expected VecPush call in MIR");
        let collection_local = chc_ctx
            .resolve_collection_local(&args)
            .expect("VecPush call should resolve collection local");
        assert!(
            !chc_ctx.collections.vec_cap_stubs_fired.contains(&collection_local),
            "precondition: Vec local should be unmarked before Vec stub handling"
        );

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
        let modified_locals = HashSet::new();
        let cx = ChcCallContext {
            stub: StubKind::VecPush,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };

        super::super::codegen_call_vec::CallVec::codegen_call_vec_core(&mut chc_ctx, &cx);

        assert!(
            chc_ctx.collections.vec_cap_stubs_fired.contains(&collection_local),
            "Vec capacity modifier should mark local {} for RawVec dedup",
            collection_local
        );
    });
}

/// Part of #1037 V1: when the Vec local is pre-marked by a Vec capacity stub,
/// RawVecGrowOne must skip Vec-slot capacity updates.
#[test]
fn test_rawvec_capacity_dedup_skips_vec_slot_update_when_marked() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_for_rawvec_skip() {
            let mut v = Vec::<u32>::new();
            v.push(11);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_for_rawvec_skip");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_vec_push_for_rawvec_skip", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && matches!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core),
                    Some(StubKind::VecPush)
                )
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }
        let (bb_idx, args, destination, target) =
            call_site.expect("expected VecPush call in MIR for RawVec dedup test");

        let collection_local = chc_ctx
            .resolve_collection_local(&args)
            .expect("VecPush args should resolve a collection local");
        let vec_idx = chc_ctx.state_idx_for_local(collection_local);
        let dest_idx = chc_ctx.state_idx_for_local(destination.local);
        assert_ne!(vec_idx, dest_idx, "test requires Vec slot and call destination slot to differ");

        let vec_in_name = chc_ctx.state_var_mgr.state_vars[vec_idx].0.clone();
        let vec_out_name = chc_ctx.state_var_mgr.output_state_vars[vec_idx].0.clone();
        let dest_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_idx].0.clone();
        chc_ctx.collections.vec_cap_stubs_fired.insert(collection_local);

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
        let modified_locals = HashSet::new();
        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::RawVecGrowOne,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_rawvec(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one RawVec transition rule");
        let rule = chc_ctx.vc.rules.last().expect("rawvec call should emit one rule");

        let vec_head_arg = rule.head.args.get(vec_idx).expect("vec slot should exist in rule head");
        assert!(
            matches!(vec_head_arg.value(), ExprValue::Var { name } if name.as_str() == &*vec_in_name),
            "dedup skip should keep Vec slot on input var {vec_in_name}, got {:?}",
            vec_head_arg.value()
        );
        assert!(
            !matches!(vec_head_arg.value(), ExprValue::Var { name } if name.as_str() == &*vec_out_name),
            "dedup skip should not rewrite Vec slot to output var {vec_out_name}"
        );

        let dest_head_arg =
            rule.head.args.get(dest_idx).expect("destination slot should exist in rule head");
        assert!(
            matches!(dest_head_arg.value(), ExprValue::Var { name } if name.as_str() == &*dest_out_name),
            "rawvec skip path should still route destination slot through output var {dest_out_name}"
        );

        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "dedup skip path should not append extra capacity constraints"
        );
    });
}

// =============================================================================
// Try/residual (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

/// Option ? operator — exercises try/residual for Option<T>.
#[test]
fn test_try_residual_option() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn maybe() -> Option<u32> {
            Some(42)
        }

        pub fn probe_option_try() -> Option<u32> {
            let x = maybe()?;
            Some(x + 1)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_try");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_try", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_try", body.blocks.len());
        let constrained_rules = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_rules >= 1,
            "Option ? should produce constrained rules for try/residual, got {constrained_rules}"
        );
    });
}

// =============================================================================
// Unconstrained stubs (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

/// BTreeMap insert exercises BTreeMap internal stubs (Entry API, node ops).
#[test]
fn test_unconstrained_stub_btreemap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeMap;

        pub fn probe_btreemap_insert() -> BTreeMap<u32, u32> {
            let mut m = BTreeMap::new();
            m.insert(1, 2);
            m
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreemap_insert");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_btreemap_insert",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let btree_stub_count = body
            .blocks
            .iter()
            .filter_map(|block| {
                if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                {
                    chc_ctx.detect_stub_matching(func, StubKind::is_btreemap_internal)
                } else {
                    None
                }
            })
            .count();
        eprintln!("btreemap_insert: detected {btree_stub_count} btree stubs");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_btreemap_insert",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_btreemap_insert", body.blocks.len());
        let constrained_rules = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_rules >= 1,
            "BTreeMap insert should produce constrained rules, got {constrained_rules}"
        );
    });
}

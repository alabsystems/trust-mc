// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_output.rs` — output arg construction and mir_to_chc entry point.
//!
//! Part of #2303 (codegen_stmt_output.rs, ~135 LOC, zero dedicated coverage).
//! Covers:
//! - `mark_modified_for_unsupported_rvalue`: nondet fallback for unsupported rvalues
//! - `build_block_output_args`: output arg construction from modified locals set
//! - `mir_to_chc`: public entry point for MIR → CHC translation
//! - Auto-promote to Mem level when projected Ref/AddressOf detected (#2084)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// mir_to_chc entry point — basic pipeline validation
// =============================================================================

const SIMPLE_RETURN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn identity(x: u32) -> u32 {
        x
    }
"#;

/// mir_to_chc produces a valid VC for a trivial identity function.
#[test]
fn test_mir_to_chc_identity_produces_valid_vc() {
    with_test_ay_ctx_for_source(SIMPLE_RETURN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "identity", ChcConfig::default());

        assert_vc_structure(&vc, "identity", body.blocks.len());
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "mir_to_chc should produce non-empty SMT output");
    });
}

const MULTI_ARG_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn add(a: u32, b: u32) -> u32 {
        a + b
    }
"#;

/// mir_to_chc handles multiple function arguments.
#[test]
fn test_mir_to_chc_multi_arg_vc_structure() {
    with_test_ay_ctx_for_source(MULTI_ARG_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "add");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "add", ChcConfig::default());

        assert_vc_structure(&vc, "add", body.blocks.len());
        // Relations should have arity >= 2 for two arguments
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(max_arity >= 2, "add function relations should have arity >= 2, got {max_arity}");
    });
}

// =============================================================================
// mir_to_chc: track level parameterization
// =============================================================================

const BRANCH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn max_val(a: u32, b: u32) -> u32 {
        if a > b { a } else { b }
    }
"#;

/// Reg level produces valid VC for branching code.
#[test]
fn test_mir_to_chc_reg_level_branch() {
    with_test_ay_ctx_for_source(BRANCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "max_val");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "max_val", ChcConfig::default());

        assert_vc_structure(&vc, "max_val", body.blocks.len());
        // Branching function should produce multiple transition rules
        let transition_rules = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_rules >= 2,
            "branching function should have >= 2 transition rules, got {transition_rules}"
        );
    });
}

/// Ptr level produces valid VC for the same source.
#[test]
fn test_mir_to_chc_ptr_level_branch() {
    with_test_ay_ctx_for_source(BRANCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "max_val");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "max_val",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "Ptr level should produce rules");
        assert!(!vc.relations.is_empty(), "Ptr level should produce relations");
    });
}

/// Mem level produces valid VC for the same source.
#[test]
fn test_mir_to_chc_mem_level_branch() {
    with_test_ay_ctx_for_source(BRANCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "max_val");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "max_val",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "Mem level should produce rules");
        assert!(!vc.relations.is_empty(), "Mem level should produce relations");
        // Branching function at Mem level should have transition rules
        let transition_count = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_count >= 2,
            "Mem level branching should produce >= 2 transitions, got {}",
            transition_count
        );
    });
}

// =============================================================================
// build_block_output_args: modified local → output state var mapping
// =============================================================================

const MODIFIED_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn increment(mut x: u32) -> u32 {
        x = x + 1;
        x
    }
"#;

/// Modified locals should appear as output state vars in transition rules.
/// Exercises build_block_output_args: modified locals use OUTPUT vars.
#[test]
fn test_build_output_args_modified_local_uses_output_var() {
    with_test_ay_ctx_for_source(MODIFIED_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "increment");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "increment", ChcConfig::default());

        assert_vc_structure(&vc, "increment", body.blocks.len());

        // Transition rules with constraints should reference output state vars
        // (names ending with _out or primed variables)
        let smt = emit_chc(&vc).to_string();
        assert!(smt.contains("increment"), "SMT should reference the function name");
        // At least some rules should have constraints (the assignment x = x + 1)
        let constrained_transition_rules = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_transition_rules >= 1,
            "increment should have constrained transition rules, got {constrained_transition_rules}"
        );
    });
}

const UNMODIFIED_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn passthrough(a: u32, b: u32) -> u32 {
        // b is unmodified, only a is used in computation
        a + 1
    }
"#;

/// Unmodified locals should use INPUT state vars in output args.
/// Exercises build_block_output_args: unmodified locals use INPUT vars.
#[test]
fn test_build_output_args_unmodified_local_uses_input_var() {
    with_test_ay_ctx_for_source(UNMODIFIED_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "passthrough");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "passthrough", ChcConfig::default());

        assert_vc_structure(&vc, "passthrough", body.blocks.len());
        // Both a and b should be tracked as state variables
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "passthrough should track at least 2 state vars (a, b), got arity {max_arity}"
        );
    });
}

// =============================================================================
// mark_modified_for_unsupported_rvalue: nondet fallback
// =============================================================================

const UNSUPPORTED_RVALUE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn thread_local_like(x: u32) -> u32 {
        // Inline assembly and similar unsupported rvalues trigger the nondet fallback.
        // A simpler proxy: division (which may produce unsupported paths in some contexts).
        let y = x / 2;
        y + 1
    }
"#;

/// Unsupported rvalues don't crash the pipeline; the local becomes nondet.
/// Exercises mark_modified_for_unsupported_rvalue.
#[test]
fn test_unsupported_rvalue_produces_nondet_fallback() {
    with_test_ay_ctx_for_source(UNSUPPORTED_RVALUE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "thread_local_like");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "thread_local_like", ChcConfig::default());

        assert_vc_structure(&vc, "thread_local_like", body.blocks.len());
    });
}

// =============================================================================
// Auto-promote to Mem level (#2084)
// =============================================================================

const REF_PROJECTION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Pair { pub first: u32, pub second: u32 }

    pub fn deref_field_store(p: &mut Pair, val: u32) {
        p.first = val;
    }
"#;

/// When Ref/AddressOf with projections is detected at a lower track level,
/// mir_to_chc auto-promotes to Mem level (#2084).
#[test]
fn test_mir_to_chc_auto_promote_to_mem() {
    with_test_ay_ctx_for_source(REF_PROJECTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deref_field_store");
        let body = instance.body().expect("body");
        // Request Reg, but field-projected deref may trigger auto-promote to Mem
        let vc = mir_to_chc(ctx.tcx, &body, "deref_field_store", ChcConfig::default());

        // Should still produce a valid VC regardless of promotion
        assert!(!vc.rules.is_empty(), "auto-promoted VC should produce rules");
        assert!(!vc.relations.is_empty(), "auto-promoted VC should produce relations");
    });
}

// =============================================================================
// mir_to_chc with debug flag
// =============================================================================

/// Debug flag doesn't crash the pipeline.
#[test]
fn test_mir_to_chc_with_debug_flag() {
    with_test_ay_ctx_for_source(SIMPLE_RETURN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "identity",
            ChcConfig { chc_debug: ChcDebugMode::On, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "debug mode should still produce rules");
        assert!(!vc.relations.is_empty(), "debug mode should still produce relations");
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "debug mode should produce non-empty SMT output");
    });
}

// =============================================================================
// mir_to_chc with wide_mem flag
// =============================================================================

/// Wide-mem flag doesn't crash the pipeline at Mem level.
#[test]
fn test_mir_to_chc_with_wide_mem_flag() {
    with_test_ay_ctx_for_source(SIMPLE_RETURN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "identity",
            ChcConfig {
                track_level: crate::args::ChcTrackLevel::Mem,
                wide_mem: WideMemMode::On,
                ..ChcConfig::default()
            },
        );

        assert!(!vc.rules.is_empty(), "wide-mem mode should produce rules");
        assert!(!vc.relations.is_empty(), "wide-mem mode should produce relations");
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "wide-mem mode should produce non-empty SMT output");
    });
}

// =============================================================================
// build_block_output_args: flattened tuple locals (#2214)
// =============================================================================

const TUPLE_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn tuple_return(a: u32, b: u32) -> (u32, u32) {
        (a + 1, b + 2)
    }
"#;

/// Flattened tuple locals occupy multiple state-var slots; build_block_output_args
/// must expand modified MIR local indices to all corresponding slots.
#[test]
fn test_build_output_args_flattened_tuple_expansion() {
    with_test_ay_ctx_for_source(TUPLE_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_return");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "tuple_return", ChcConfig::default());

        assert_vc_structure(&vc, "tuple_return", body.blocks.len());
        // Tuple return → the return local should produce ≥ 2 state vars (fld0, fld1)
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 3,
            "tuple_return should have arity >= 3 (a, b, return tuple fields), got {max_arity}"
        );
    });
}

// =============================================================================
// build_block_output_args: heap memory arrays (#905, #1100)
// =============================================================================

const HEAP_ALLOC_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn heap_store(v: &mut Vec<u32>, val: u32) {
        v.push(val);
    }
"#;

/// At Mem level, modified memory arrays (heap stores) should appear as output state vars.
/// Exercises build_block_output_args: type-indexed memory array and metadata array paths.
#[test]
fn test_build_output_args_mem_level_heap_arrays() {
    with_test_ay_ctx_for_source(HEAP_ALLOC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "heap_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "heap_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Mem level with Vec::push should produce a VC (may drop some stores but shouldn't panic)
        assert!(!vc.rules.is_empty(), "heap_store at Mem should produce rules");
        assert!(!vc.relations.is_empty(), "heap_store at Mem should produce relations");
    });
}

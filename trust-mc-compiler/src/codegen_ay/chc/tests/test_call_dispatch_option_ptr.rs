// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_dispatch_option_ptr.rs` — Option/Result + pointer
//! call dispatch orchestration.
//!
//! Part of #2303 (codegen_call_dispatch_option_ptr.rs, 159 LOC, zero dedicated coverage).
//! The individual stub detection functions (detect_option_predicate_stub,
//! detect_unwrap_or_stub, etc.) are tested in test_stubs_util.rs.
//! These tests verify the *dispatch orchestration* path:
//!   codegen_call_terminator → try_dispatch_call_option_pointer → detect_* → codegen_call_*
//!
//! Each test compiles a Rust source that exercises a specific dispatch branch,
//! runs the full CHC pipeline, and checks the resulting VC structure.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_dispatch_option_ptr::CallDispatchOptionPtr;
use super::common::*;

// =============================================================================
// Option::is_some / is_none — detect_option_predicate_stub branch
// =============================================================================

const OPTION_IS_SOME_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_is_some(x: Option<u32>) -> bool {
        x.is_some()
    }
"#;

const OPTION_AS_MUT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_as_mut(x: &mut Option<u32>) -> Option<&mut u32> {
        x.as_mut()
    }
"#;

const OPTION_AS_MUT_U64_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_u64_as_mut(x: &mut Option<u64>) -> Option<&mut u64> {
        x.as_mut()
    }
"#;

const OPTION_AS_MUT_REF_U64_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_ref_u64_as_mut<'a, 'slot>(
        x: &'slot mut Option<&'a u64>,
    ) -> Option<&'slot mut &'a u64> {
        x.as_mut()
    }
"#;

const OPTION_AS_MUT_RAW_PTR_U64_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_raw_ptr_u64_as_mut<'slot>(
        x: &'slot mut Option<*mut u64>,
    ) -> Option<&'slot mut *mut u64> {
        x.as_mut()
    }
"#;

fn assert_option_as_mut_dispatch_uses_guarded_reference_payload(
    source: &str,
    fn_name: &str,
    label: &str,
) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_option_as_mut_aggregate_gap_metadata();
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) =
                chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func))
            else {
                continue;
            };
            if !callee_path.contains("Option") || !callee_path.ends_with("::as_mut") {
                continue;
            }
            let Some(target_bb) = *target else {
                continue;
            };

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);
            let before_rules = chc_ctx.vc.rules.len();
            let before_fallbacks = chc_ctx.sound_fallback_count();
            let before_gaps = chc_ctx.diagnostics.aggregate_encoding_gap.get();

            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: Some(callee_path.clone()),
            };

            assert!(
                chc_ctx.try_dispatch_call_option_pointer(&dcx),
                "{label} should be handled by option-state fast path"
            );
            assert!(
                chc_ctx.vc.rules.len() > before_rules,
                "{label} fast path should emit a transition rule"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before_fallbacks,
                "{label} fast path should not record a sound fallback"
            );
            assert_eq!(
                chc_ctx.diagnostics.aggregate_encoding_gap.get(),
                before_gaps + 1,
                "{label} should reconstruct with a guarded fresh reference payload"
            );
            assert!(
                chc_ctx.vc.rules[before_rules..]
                    .iter()
                    .any(|rule| rule_contains_var(rule, "option_as_mut_ref")),
                "{label} transition should carry an explicit fresh as_mut payload"
            );
            found += 1;
        }
        assert!(found > 0, "expected at least one Option::as_mut call in {fn_name} MIR");
    });
    reset_option_as_mut_aggregate_gap_metadata();
}

fn reset_option_as_mut_aggregate_gap_metadata() {
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();
}

/// Option::is_some should be dispatched through try_dispatch_call_option_pointer
/// via detect_option_predicate_stub, producing a well-formed CHC VC.
#[test]
fn test_dispatch_option_is_some_vc() {
    with_test_ay_ctx_for_source(OPTION_IS_SOME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_some");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_is_some", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_is_some", body.blocks.len());
    });
}

/// Option::as_mut is not a registry stub. It should still be claimed by the
/// structural option-state fast path before generic MIR inlining.
#[test]
fn test_dispatch_option_as_mut_fast_path_claims_call() {
    with_test_ay_ctx_for_source(OPTION_AS_MUT_SOURCE, |ctx| {
        let fn_name = "probe_option_as_mut";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) =
                chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func))
            else {
                continue;
            };
            if !callee_path.contains("Option") || !callee_path.ends_with("::as_mut") {
                continue;
            }
            let Some(target_bb) = *target else {
                continue;
            };

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);
            let before_rules = chc_ctx.vc.rules.len();
            let before_fallbacks = chc_ctx.sound_fallback_count();

            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: Some(callee_path.clone()),
            };

            assert!(
                chc_ctx.try_dispatch_call_option_pointer(&dcx),
                "Option::as_mut should be handled by option-state fast path"
            );
            assert!(
                chc_ctx.vc.rules.len() > before_rules,
                "Option::as_mut fast path should emit a transition rule"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before_fallbacks,
                "Option::as_mut fast path should not record a sound fallback"
            );
            found += 1;
        }
        assert!(found > 0, "expected at least one Option::as_mut call in {fn_name} MIR");
    });
}

/// `Option<u64>::as_mut` has a BV64 owned payload and a BV64 reference result
/// payload. The fast path must not forward the receiver payload just because
/// those SMT sorts match; it should emit the guarded fresh-reference
/// reconstruction instead.
#[test]
fn test_dispatch_option_as_mut_u64_uses_guarded_reference_payload() {
    assert_option_as_mut_dispatch_uses_guarded_reference_payload(
        OPTION_AS_MUT_U64_SOURCE,
        "probe_option_u64_as_mut",
        "Option<u64>::as_mut",
    );
}

/// `Option<&u64>::as_mut` returns `Option<&mut &u64>`, i.e. a mutable reference
/// to the payload slot. It must not reuse the stored `&u64` value just because
/// both encode as BV64.
#[test]
fn test_dispatch_option_as_mut_ref_u64_uses_guarded_reference_payload() {
    assert_option_as_mut_dispatch_uses_guarded_reference_payload(
        OPTION_AS_MUT_REF_U64_SOURCE,
        "probe_option_ref_u64_as_mut",
        "Option<&u64>::as_mut",
    );
}

/// `Option<*mut u64>::as_mut` likewise returns a reference to the raw-pointer
/// slot, not the stored raw pointer value.
#[test]
fn test_dispatch_option_as_mut_raw_ptr_u64_uses_guarded_reference_payload() {
    assert_option_as_mut_dispatch_uses_guarded_reference_payload(
        OPTION_AS_MUT_RAW_PTR_U64_SOURCE,
        "probe_option_raw_ptr_u64_as_mut",
        "Option<*mut u64>::as_mut",
    );
}

// =============================================================================
// Result::is_ok / is_err — detect_result_predicate_stub branch
// =============================================================================

const RESULT_IS_OK_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_is_ok(x: Result<u32, u32>) -> bool {
        x.is_ok()
    }
"#;

/// Result::is_ok should be dispatched through detect_result_predicate_stub.
#[test]
fn test_dispatch_result_is_ok_vc() {
    with_test_ay_ctx_for_source(RESULT_IS_OK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_ok");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_is_ok", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_is_ok", body.blocks.len());
    });
}

const RESULT_IS_ERR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_is_err(x: Result<u32, u32>) -> bool {
        x.is_err()
    }
"#;

/// Result::is_err exercises the negated result predicate branch.
#[test]
fn test_dispatch_result_is_err_vc() {
    with_test_ay_ctx_for_source(RESULT_IS_ERR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_err");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_is_err", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_is_err", body.blocks.len());
    });
}

// =============================================================================
// Option::unwrap_or — detect_unwrap_or_stub branch
// =============================================================================

const OPTION_UNWRAP_OR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_unwrap_or(x: Option<u32>) -> u32 {
        x.unwrap_or(42)
    }
"#;

/// Option::unwrap_or exercises detect_unwrap_or_stub → codegen_call_unwrap_or.
#[test]
fn test_dispatch_option_unwrap_or_vc() {
    with_test_ay_ctx_for_source(OPTION_UNWRAP_OR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_or");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap_or", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap_or", body.blocks.len());
    });
}

// =============================================================================
// Option::unwrap / Option::expect — detect_unwrap_expect_stub branch
// =============================================================================

const OPTION_UNWRAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_unwrap(x: Option<u32>) -> u32 {
        x.unwrap()
    }
"#;

/// Option::unwrap exercises detect_unwrap_expect_stub → codegen_call_unwrap_expect.
#[test]
fn test_dispatch_option_unwrap_vc() {
    with_test_ay_ctx_for_source(OPTION_UNWRAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap", body.blocks.len());
    });
}

// =============================================================================
// Option::and_then — detect_combinator_stub branch
// =============================================================================

const OPTION_AND_THEN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_and_then(x: Option<u32>) -> Option<u32> {
        x.and_then(|v| if v > 0 { Some(v + 1) } else { None })
    }
"#;

/// Option::and_then exercises detect_combinator_stub → codegen_call_combinator.
#[test]
fn test_dispatch_option_and_then_vc() {
    with_test_ay_ctx_for_source(OPTION_AND_THEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_and_then");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_and_then", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_and_then", body.blocks.len());
    });
}

// =============================================================================
// Dispatch returns false for unrecognized functions
// =============================================================================

const NO_OPTION_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_plain_arithmetic(x: u32, y: u32) -> u32 {
        x + y
    }
"#;

/// Plain arithmetic should NOT be dispatched through try_dispatch_call_option_pointer.
/// Verifies the "returns false" fallthrough path by checking that no Option/ptr
/// stubs are detected.
#[test]
fn test_dispatch_plain_arithmetic_no_option_ptr_stubs() {
    with_test_ay_ctx_for_source(NO_OPTION_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_plain_arithmetic");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_plain_arithmetic", ChcConfig::default());

        // None of the option/ptr detectors should fire on plain arithmetic
        let option_stubs = collect_stubs_with_fn(&chc_ctx, &body, |c, func, _| {
            c.detect_stub_matching(func, StubKind::is_option_predicate)
        });
        let result_stubs = collect_stubs_with_fn(&chc_ctx, &body, |c, func, _| {
            c.detect_stub_matching(func, StubKind::is_result_predicate)
        });
        let ptr_stubs = collect_stubs_with_fn(&chc_ctx, &body, |c, func, _| {
            c.detect_stub_matching(func, StubKind::is_ptr_memory)
        });

        assert!(
            option_stubs.is_empty() && result_stubs.is_empty() && ptr_stubs.is_empty(),
            "plain arithmetic should not trigger option/ptr dispatch"
        );
    });
}

/// Route-table dispatch should not silently drop a recognized Option/Result call
/// when `target=None`; it must increment the per-context `diverging_call_drop` metric (#2587).
#[test]
fn test_dispatch_option_route_target_none_records_drop_count() {
    with_test_ay_ctx_for_source(OPTION_IS_SOME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_some");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_is_some", ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                    && chc_ctx.detect_stub_matching(func, StubKind::is_option_predicate).is_some()
                {
                    Some((bb_idx, func, args, destination))
                } else {
                    None
                }
            })
            .expect("expected Option predicate call terminator");

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
        let handled = chc_ctx.try_dispatch_call_option_pointer(&dcx);

        assert!(handled, "option dispatch should claim recognized Option call");
        assert_eq!(
            chc_ctx.diagnostics.diverging_call_drop.get(),
            1,
            "target=None Option dispatch should record one diverging drop"
        );
    });
}

/// Helper: collect stubs using a detection closure that receives the ChcCtx.
fn collect_stubs_with_fn<'tcx, 'body, F>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
    mut detect: F,
) -> Vec<StubKind>
where
    F: FnMut(
        &ChcCtx<'tcx, 'body>,
        &rustc_public::mir::Operand,
        &[rustc_public::mir::Operand],
    ) -> Option<StubKind>,
{
    use rustc_public::mir::TerminatorKind;
    let mut detected = Vec::new();
    for block in &body.blocks {
        if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind
            && let Some(stub_kind) = detect(chc_ctx, func, args)
        {
            detected.push(stub_kind);
        }
    }
    detected
}

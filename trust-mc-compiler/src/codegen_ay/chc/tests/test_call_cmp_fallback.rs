// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for `codegen_primitive_cmp` fallback paths in `cmp_handlers.rs`.
//!
//! Each test forces a specific fail-open path and asserts that `record_fallback()`
//! was called (via `sound_fallback_count()` field). Without these, a regression removing
//! any `record_fallback()` call is invisible to the test suite.
//!
//! Part of #2783 (cmp_handlers record_fallback test coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use rustc_public::mir::Place;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::cmp_handlers::codegen_primitive_cmp;
use super::common::*;

/// Minimal Rust source providing a call site for scaffold extraction.
const FALLBACK_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn helper(x: u32) -> u32 { x + 1 }

    pub fn probe_cmp_fallback(x: u32) -> u32 {
        helper(x)
    }
"#;

/// Minimal Rust source providing a 3-arg call site for `Ord::clamp` scaffolding.
const CLAMP_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn helper3(a: u32, b: u32, c: u32) -> u32 { a.wrapping_add(b).wrapping_add(c) }

    pub fn probe_cmp_clamp_fallback(a: u32, b: u32, c: u32) -> u32 {
        helper3(a, b, c)
    }
"#;

/// Extracts a call-site scaffold from MIR and invokes `body` with a ready-to-use
/// `ChcCtx`, destination, target, from_app, stmt_constraints, modified_locals,
/// and bb_idx.
fn with_cmp_scaffold_for_source(
    source: &str,
    fn_name: &str,
    body: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &Place,
        usize, // target
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize, // bb_idx
    ) + Send,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &mir_body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                call_site = Some((bb_idx, func.clone(), destination.clone(), *target));
                break;
            }
        }
        let (bb_idx, func, destination, target) =
            call_site.expect("expected call terminator in probe_cmp_fallback MIR");
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        body(
            &mut chc_ctx,
            &func,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
        );
    });
}

/// Extracts call-site scaffold from MIR for the standard 1-arg fallback probe.
fn with_cmp_scaffold(
    body: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &Place,
        usize, // target
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize, // bb_idx
    ) + Send,
) {
    with_cmp_scaffold_for_source(FALLBACK_PROBE_SOURCE, "probe_cmp_fallback", body);
}

/// Extracts a 3-arg call-site scaffold from MIR for clamp-specific tests.
fn with_cmp_clamp_scaffold(
    body: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &Place,
        usize, // target
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize, // bb_idx
    ) + Send,
) {
    with_cmp_scaffold_for_source(CLAMP_PROBE_SOURCE, "probe_cmp_clamp_fallback", body);
}

fn dispatch_call_context<'a>(
    bb_idx: usize,
    func: &'a Operand,
    args: &'a [Operand],
    destination: &'a Place,
    target: &'a Option<rustc_public::mir::BasicBlockIdx>,
    from_app: &'a RelationApp,
    stmt_constraints: &'a [Expr],
    modified_locals: &'a HashSet<usize>,
) -> DispatchCallContext<'a> {
    DispatchCallContext {
        bb_idx,
        func,
        args,
        destination,
        target,
        from_app,
        stmt_constraints,
        modified_locals,
        callee_path: None,
    }
}

/// Injects two state vars mapped to locals 0 and 1 with the given sort.
fn inject_local_pair(chc_ctx: &mut ChcCtx<'_, '_>, sort: ay_bindings::Sort) {
    let idx = chc_ctx.state_var_mgr.state_vars.len();
    chc_ctx.push_state_var_pair("test_lhs", "test_lhs_out", sort.clone());
    chc_ctx.state_var_mgr.local_to_state_idx.insert(0, idx);
    let idx2 = chc_ctx.state_var_mgr.state_vars.len();
    chc_ctx.push_state_var_pair("test_rhs", "test_rhs_out", sort);
    chc_ctx.state_var_mgr.local_to_state_idx.insert(1, idx2);
}

/// Operand pair referencing locals 0 and 1.
fn local_pair_operands() -> [Operand; 2] {
    [
        Operand::Copy(Place { local: 0usize, projection: vec![] }),
        Operand::Copy(Place { local: 1usize, projection: vec![] }),
    ]
}

// =============================================================================
// Test 1: Operand resolution failure (both lhs and rhs unresolvable)
// Exercises line 313-322 of cmp_handlers.rs
// =============================================================================

/// When both operands point to out-of-bounds locals that `resolve_ref_or_const_referent`
/// cannot resolve, `codegen_primitive_cmp` must record a fallback and emit a single
/// unconstrained transition rule.
#[test]
fn test_cmp_operand_resolution_failure_increments_fallback() {
    with_cmp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        let bogus_args = [
            Operand::Copy(Place { local: 998usize, projection: vec![] }),
            Operand::Copy(Place { local: 999usize, projection: vec![] }),
        ];
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx = dispatch_call_context(
            bb_idx,
            func,
            &bogus_args,
            destination,
            &target_opt,
            from_app,
            sc,
            ml,
        );
        codegen_primitive_cmp(chc_ctx, &dcx, target, "eq");

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "operand resolution failure must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 2: Unexpected method name catch-all
// Exercises line 241-248 of cmp_handlers.rs
// =============================================================================

/// When the method name is not one of the recognized comparison methods
/// (cmp/partial_cmp/eq/ne/lt/le/gt/ge), `codegen_primitive_cmp` must record
/// a fallback via the outer `_ =>` catch-all.
#[test]
fn test_cmp_unexpected_method_increments_fallback() {
    with_cmp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        inject_local_pair(chc_ctx, ay_bindings::Sort::bitvec(32));
        let args = local_pair_operands();
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx =
            dispatch_call_context(bb_idx, func, &args, destination, &target_opt, from_app, sc, ml);
        codegen_primitive_cmp(chc_ctx, &dcx, target, "totally_bogus_method");

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "unexpected method name must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 3: Unsupported sorts for eq/ne — Array sorts are not bitvec/int/bool
// Exercises line 126-140 of cmp_handlers.rs
// =============================================================================

/// When operands resolve to Array sorts (not bitvec, int, or bool), the eq/ne
/// branch must record a fallback and emit an unconstrained transition.
#[test]
fn test_cmp_eq_unsupported_sorts_increments_fallback() {
    with_cmp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        let array_sort =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));
        inject_local_pair(chc_ctx, array_sort);
        let args = local_pair_operands();
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx =
            dispatch_call_context(bb_idx, func, &args, destination, &target_opt, from_app, sc, ml);
        codegen_primitive_cmp(chc_ctx, &dcx, target, "eq");

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "eq with unsupported sorts must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 4: Unsupported sorts for cmp/partial_cmp — Array sorts
// Exercises line 86-100 of cmp_handlers.rs
// =============================================================================

/// When operands resolve to Array sorts for cmp/partial_cmp, the unsupported
/// sorts branch must record a fallback.
#[test]
fn test_cmp_partial_cmp_unsupported_sorts_increments_fallback() {
    with_cmp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        let array_sort =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));
        inject_local_pair(chc_ctx, array_sort);
        let args = local_pair_operands();
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx =
            dispatch_call_context(bb_idx, func, &args, destination, &target_opt, from_app, sc, ml);
        codegen_primitive_cmp(chc_ctx, &dcx, target, "cmp");

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "cmp with unsupported sorts must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 5: Unsupported sorts for lt/le/gt/ge ordering comparisons
// Exercises line 225-239 of cmp_handlers.rs
// =============================================================================

/// When operands resolve to Array sorts for relational ops (lt/le/gt/ge),
/// the unsupported sorts branch must record a fallback.
#[test]
fn test_cmp_lt_unsupported_sorts_increments_fallback() {
    with_cmp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        let array_sort =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));
        inject_local_pair(chc_ctx, array_sort);
        let args = local_pair_operands();
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx =
            dispatch_call_context(bb_idx, func, &args, destination, &target_opt, from_app, sc, ml);
        codegen_primitive_cmp(chc_ctx, &dcx, target, "lt");

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "lt with unsupported sorts must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 6: Clamp must preserve the min <= max panic precondition
// =============================================================================

/// `Ord::clamp` panics when `min > max`. The CHC shortcut must therefore emit
/// an `error()` edge for violating bounds and guard the normal successor with
/// the positive `min <= max` condition.
#[test]
fn test_cmp_clamp_emits_error_rule_for_invalid_bounds() {
    with_cmp_clamp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        chc_ctx.declare_error_relation();
        let args = [
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
            Operand::Copy(Place { local: 2usize, projection: vec![] }),
            Operand::Copy(Place { local: 3usize, projection: vec![] }),
        ];
        let before_rules = chc_ctx.vc.rules.len();
        let before_error_rules = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx =
            dispatch_call_context(bb_idx, func, &args, destination, &target_opt, from_app, sc, ml);
        codegen_primitive_cmp(chc_ctx, &dcx, target, "clamp");

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 2,
            "clamp should emit one error rule and one guarded successor rule"
        );
        assert_eq!(
            chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count(),
            before_error_rules + 1,
            "clamp must emit an error rule for min > max"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "well-sorted clamp should not fall back when adding the precondition"
        );

        let emitted_rules = &chc_ctx.vc.rules[before_rules..];
        let error_rule = emitted_rules
            .iter()
            .find(|r| r.head.name == "error")
            .expect("expected emitted clamp error rule");
        let error_constraints =
            error_rule.body.constraints.iter().map(ToString::to_string).collect::<Vec<_>>();
        assert!(
            error_constraints
                .iter()
                .any(|constraint| { constraint.contains("bvule") && constraint.contains("(not") }),
            "clamp error rule should negate a min <= max guard, got {error_constraints:?}"
        );

        let guarded_goto = emitted_rules
            .iter()
            .find(|r| r.head.name != "error")
            .expect("expected emitted clamp successor rule");
        let guarded_constraints =
            guarded_goto.body.constraints.iter().map(ToString::to_string).collect::<Vec<_>>();
        assert!(
            guarded_constraints
                .iter()
                .any(|constraint| { constraint.contains("bvule") && !constraint.contains("(not") }),
            "clamp successor rule should require min <= max, got {guarded_constraints:?}"
        );
    });
}

// =============================================================================
// Test 7: Sort conversion failure in destination coercion path
// Exercises line 290-301 of cmp_handlers.rs
// =============================================================================

/// When comparison result cannot be coerced into destination sort, cmp handler
/// must record fallback and leave destination unconstrained.
#[test]
fn test_cmp_sort_conversion_failure_increments_fallback() {
    with_cmp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        inject_local_pair(chc_ctx, ay_bindings::Sort::bitvec(32));
        let args = local_pair_operands();
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx =
            dispatch_call_context(bb_idx, func, &args, destination, &target_opt, from_app, sc, ml);
        codegen_primitive_cmp(chc_ctx, &dcx, target, "lt");

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "sort conversion failure must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 8: Missing output state var fail-closed path
// Exercises line 303-312 of cmp_handlers.rs
// =============================================================================

/// Corrupted output-state table should still record fallback before fail-closed panic.
#[test]
fn test_cmp_missing_output_state_var_records_fallback_before_panic() {
    with_cmp_scaffold(|chc_ctx, func, destination, target, from_app, sc, ml, bb_idx| {
        inject_local_pair(chc_ctx, ay_bindings::Sort::bitvec(32));
        let args = local_pair_operands();
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars.truncate(dest_vec_idx);
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
        let target_opt = Some(target);
        let dcx =
            dispatch_call_context(bb_idx, func, &args, destination, &target_opt, from_app, sc, ml);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            codegen_primitive_cmp(chc_ctx, &dcx, target, "eq");
        }));

        assert!(result.is_err(), "corrupted output_state_vars should fail closed with panic");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "missing output state var path must record fallback before panic"
        );
    });
}

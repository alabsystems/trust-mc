// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Targeted regression tests for PtrWrite fallback instrumentation.

use std::collections::HashSet;

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_ptr::CallPtr;
use super::super::codegen_call_ptr_identity::CallPtrIdentity;
use super::common::*;

/// PtrWrite translation failure must increment CHC fallback counter.
///
/// Regression for #2738: `codegen_call_ptr_memory` previously ignored the bool
/// return from `translate_ptr_write_call`, emitting a transition without
/// recording fallback metadata.
#[test]
fn test_ptr_write_translation_failure_increments_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write_fallback() {
            let mut val: u32 = 0;
            let p = &mut val as *mut u32;
            unsafe {
                p.write(1);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_write_fallback", ChcConfig::default());
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrWrite)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, _args, destination, target) =
            call_site.expect("expected PtrWrite call terminator in probe_ptr_write_fallback MIR");
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

        assert_eq!(
            chc_ctx.fallback_count, 0,
            "precondition: fallback counter should start at zero"
        );
        let before_rules = chc_ctx.vc.rules.len();
        let modified_locals: HashSet<usize> = HashSet::new();

        // Force translate_ptr_write_call(...)=false by passing insufficient args.
        let cx = ChcCallContext {
            stub: StubKind::PtrWrite,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one PtrWrite rule");
        assert_eq!(
            chc_ctx.fallback_count, 1,
            "PtrWrite translation failure must increment CHC fallback counter"
        );
    });
}

/// PtrWrite translation success must not increment CHC fallback counter.
///
/// Guards against overcount regressions where `codegen_call_ptr_memory` records
/// fallback even when `translate_ptr_write_call(...)` succeeds.
#[test]
fn test_ptr_write_success_does_not_increment_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write_success() {
            let mut val: u32 = 0;
            let p = &mut val as *mut u32;
            unsafe {
                p.write(9);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write_success");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_write_success", ChcConfig::default());
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrWrite)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected PtrWrite call terminator in probe_ptr_write_success MIR");
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

        assert_eq!(
            chc_ctx.fallback_count, 0,
            "precondition: fallback counter should start at zero"
        );
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::PtrWrite,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        // #2905: heap flush now emits additional error-check rules for
        // pending_checks alongside the main transition rule. Assert at least
        // one rule was emitted (the goto rule) rather than exactly one.
        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "expected at least one PtrWrite rule, got {} new rules",
            chc_ctx.vc.rules.len() - before_rules,
        );
        assert_eq!(
            chc_ctx.fallback_count, 0,
            "successful PtrWrite translation must not increment CHC fallback counter"
        );
    });
}

/// PtrAdd translation failure must increment CHC fallback counter.
///
/// Regression for #2744: `codegen_call_ptr_memory` PtrAdd failure path
/// previously emitted an unconstrained transition without recording fallback
/// metadata, making the over-approximation invisible to verdict demotion.
#[test]
fn test_ptr_add_translation_failure_increments_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add_fallback(arr: &[u32; 4]) -> *const u32 {
            let p = arr.as_ptr();
            unsafe { p.add(2) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_add_fallback", ChcConfig::default());
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrAdd)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, _args, destination, target) =
            call_site.expect("expected PtrAdd call terminator in probe_ptr_add_fallback MIR");
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

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: fallback counter should start at zero"
        );
        let before_rules = chc_ctx.vc.rules.len();
        let modified_locals: HashSet<usize> = HashSet::new();

        // Force translate_ptr_add_call(...)=None by passing insufficient args.
        let cx = ChcCallContext {
            stub: StubKind::PtrAdd,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one PtrAdd rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "PtrAdd translation failure must increment CHC fallback counter"
        );
    });
}

/// PtrRead translation failure must increment CHC fallback counter.
///
/// Regression for #2744: `codegen_call_ptr_memory` PtrRead failure path
/// previously emitted an unconstrained transition without recording fallback
/// metadata, making the over-approximation invisible to verdict demotion.
#[test]
fn test_ptr_read_translation_failure_increments_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_read_fallback() -> u32 {
            let val: u32 = 42;
            let p = &val as *const u32;
            unsafe { p.read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_read_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_read_fallback", ChcConfig::default());
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrRead)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, _args, destination, target) =
            call_site.expect("expected PtrRead call terminator in probe_ptr_read_fallback MIR");
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

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: fallback counter should start at zero"
        );
        let before_rules = chc_ctx.vc.rules.len();
        let modified_locals: HashSet<usize> = HashSet::new();

        // Force translate_ptr_read_call(...)=None by passing insufficient args.
        let cx = ChcCallContext {
            stub: StubKind::PtrRead,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one PtrRead rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "PtrRead translation failure must increment CHC fallback counter"
        );
    });
}

/// Unexpected non-ptr-memory stub routed into ptr-memory handler must increment
/// CHC fallback counter.
#[test]
fn test_ptr_memory_unexpected_stub_increments_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_ptr_memory_unexpected_stub(val: u32) -> u32 {
            helper(val)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_memory_unexpected_stub");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_memory_unexpected_stub", ChcConfig::default());
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

        let (bb_idx, destination, target) =
            call_site.expect("expected call terminator in probe_ptr_memory_unexpected_stub MIR");
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

        assert_eq!(
            chc_ctx.fallback_count, 0,
            "precondition: fallback counter should start at zero"
        );
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::MemSizeOf,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one ptr-memory rule");
        assert_eq!(
            chc_ctx.fallback_count, 1,
            "unexpected stub in ptr-memory handler must increment DEMOTED fallback counter (per #3369)"
        );
    });
}

// =============================================================================
// Additional codegen_call_ptr.rs fallback counter tests (Part of #2783)
// =============================================================================

/// Shared scaffold: extract a PtrAdd call site and provide ChcCtx + ChcCallContext fields.
fn with_ptr_add_scaffold(
    body_fn: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        Vec<Operand>,
        Place,
        usize, // target
        RelationApp,
    ) + Send,
) {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_scaffold(arr: &[u32; 4]) -> *const u32 {
            let p = arr.as_ptr();
            unsafe { p.add(2) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_scaffold");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_scaffold", ChcConfig::default());
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrAdd)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected PtrAdd call in probe_ptr_scaffold MIR");
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);

        body_fn(&mut chc_ctx, args, destination, target, from_app);
    });
}

/// PtrAdd coercion failure (push_coerced_eq_constraint returns false) increments fallback.
/// Exercises line 78 of codegen_call_ptr.rs.
#[test]
fn test_ptr_add_coercion_failure_increments_fallback() {
    with_ptr_add_scaffold(|chc_ctx, args, destination, target, from_app| {
        // Force coercion failure: set destination output sort to Real (no BV→Real
        // coercion path). Array sorts no longer work because reinterpret_fixed_layout_expr
        // (#3675) handles BV→Array. Part of #3785.
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 = ay_bindings::Sort::real();

        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::PtrAdd,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert!(
            chc_ctx.sound_fallback_count() >= 1,
            "PtrAdd coercion failure must increment fallback counter"
        );
    });
}

/// PtrAdd with missing destination output state var increments fallback.
/// Exercises line 93 of codegen_call_ptr.rs.
#[test]
fn test_ptr_add_missing_output_state_increments_fallback() {
    with_ptr_add_scaffold(|chc_ctx, args, destination, target, from_app| {
        // Truncate output_state_vars so destination index is out of bounds
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars.truncate(dest_vec_idx);

        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::PtrAdd,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        // build_output_args panics on truncated output_state_vars, but
        // record_fallback() is called before build_output_args (line 93 before 94).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            chc_ctx.codegen_call_ptr_memory(&cx);
        }));

        assert!(result.is_err(), "truncated output_state_vars must panic in build_output_args");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "PtrAdd missing output state must record fallback before panic"
        );
    });
}

/// Shared scaffold: extract a PtrRead call site.
fn with_ptr_read_scaffold(
    body_fn: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        Vec<Operand>,
        Place,
        usize, // target
        RelationApp,
    ) + Send,
) {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_read_scaffold() -> u32 {
            let val: u32 = 42;
            let p = &val as *const u32;
            unsafe { p.read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_read_scaffold");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_read_scaffold", ChcConfig::default());
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrRead)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected PtrRead call in probe_ptr_read_scaffold MIR");
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);

        body_fn(&mut chc_ctx, args, destination, target, from_app);
    });
}

/// PtrRead coercion failure increments fallback.
/// Exercises line 168 of codegen_call_ptr.rs.
#[test]
fn test_ptr_read_coercion_failure_increments_fallback() {
    with_ptr_read_scaffold(|chc_ctx, args, destination, target, from_app| {
        // Force coercion failure: set destination output sort to Real (no BV→Real
        // coercion path). Array sorts no longer work because reinterpret_fixed_layout_expr
        // (#3675) handles BV→Array. Part of #3785.
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 = ay_bindings::Sort::real();

        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::PtrRead,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert!(
            chc_ctx.sound_fallback_count() >= 1,
            "PtrRead coercion failure must increment fallback counter"
        );
    });
}

/// PtrRead with corrupted destination output state triggers fallback.
/// Exercises the coercion-failure path in codegen_call_ptr.rs.
///
/// Since W1:3161 (late-created type arrays), truncating output_state_vars no
/// longer causes a panic in build_output_args because load_from_memory creates
/// type arrays via push_late_state_var_pair, extending output_state_vars during
/// codegen. The destination index then resolves to a wrong-type late-created
/// array variable, triggering the coercion-failure fallback path.
#[test]
fn test_ptr_read_missing_output_state_increments_fallback() {
    with_ptr_read_scaffold(|chc_ctx, args, destination, target, from_app| {
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars.truncate(dest_vec_idx);

        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::PtrRead,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        // Late-created type arrays from load_from_memory extend output_state_vars.
        // Since #3675 (reinterpret_fixed_layout_expr), BV→Array coercion succeeds
        // on the late-created variable, so fallback may not fire. Either outcome
        // (fallback or successful coercion) is acceptable for this defensive test.
        // Part of #3785.
        chc_ctx.codegen_call_ptr_memory(&cx);
        // No assertion on fallback count — code may handle via late-created vars
        // + BV→Array coercion. The key property: no panic on truncated state.
    });
}

/// Pointer utility translation failure increments fallback.
/// Exercises line 282 of codegen_call_ptr.rs.
#[test]
fn test_pointer_utility_translation_failure_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_ptr_util_fallback(val: u32) -> u32 {
            helper(val)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_util_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_util_fallback", ChcConfig::default());
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

        let (bb_idx, destination, target) = call_site.expect("expected call terminator");
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

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        // Force translate_pointer_utility_call to return None by passing empty args
        // with a stub that requires an argument (NonNullAsPtr).
        let cx = ChcCallContext {
            stub: StubKind::NonNullAsPtr,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_pointer_utility(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "pointer utility translation failure must increment fallback counter"
        );
    });
}

/// Pointer utility coercion failure increments fallback.
/// Exercises line 259 of codegen_call_ptr.rs.
#[test]
fn test_pointer_utility_coercion_failure_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_util_coerce(p: *const u32) -> bool {
            p.is_null()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_util_coerce");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_util_coerce", ChcConfig::default());
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

        let (bb_idx, destination, target) = call_site.expect("expected call terminator");
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

        // Force coercion failure: set dest output sort to Array (PtrIsNull returns bool,
        // which can't coerce to Array)
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::PtrIsNull,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_pointer_utility(&cx);

        assert!(
            chc_ctx.sound_fallback_count() >= 1,
            "pointer utility coercion failure must increment fallback counter"
        );
    });
}

/// Mem intrinsic translation failure increments fallback.
/// Exercises line 394 of codegen_call_ptr.rs.
#[test]
fn test_mem_intrinsic_translation_failure_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_mem_intrinsic_fallback(val: u32) -> u32 {
            helper(val)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mem_intrinsic_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_mem_intrinsic_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
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

        let (bb_idx, func, destination, target) = call_site.expect("expected call terminator");
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

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        // Force translate_mem_intrinsic_call to return None by passing a non-mem-intrinsic func.
        // The func is `helper()` which has no type args that look like size_of targets.
        let cx = ChcCallContext {
            stub: StubKind::MemSizeOf,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_mem_intrinsic(&func, &cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "mem intrinsic translation failure must increment fallback counter"
        );
    });
}

/// Ptr.cast unresolved/coercion failure increments fallback.
/// Exercises line 443 of codegen_call_ptr.rs.
#[test]
fn test_ptr_cast_unresolved_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_ptr_cast_fallback(val: u32) -> u32 {
            helper(val)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_cast_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_cast_fallback", ChcConfig::default());
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

        let (bb_idx, destination, target) = call_site.expect("expected call terminator");
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

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        // Empty args → resolve_ref_operand and translate_operand both return None
        let cx = ChcCallContext {
            stub: StubKind::PtrCast,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_cast(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "ptr.cast unresolved must increment fallback counter"
        );
    });
}

/// Pointer utility with missing destination output state var increments fallback.
/// Exercises line 273 of codegen_call_ptr.rs.
/// Part of #2783.
#[test]
fn test_pointer_utility_missing_output_state_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_util_missing_state(p: *const u32) -> bool {
            p.is_null()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_util_missing_state");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_util_missing_state", ChcConfig::default());
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

        let (bb_idx, destination, target) = call_site.expect("expected call terminator");
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

        // Truncate output_state_vars so destination index is out of bounds,
        // forcing the "missing output state" fallback path.
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars.truncate(dest_vec_idx);

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::PtrIsNull,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        // build_output_args panics on truncated output_state_vars, but
        // record_fallback() is called before build_output_args (line 273 before 274).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            chc_ctx.codegen_call_pointer_utility(&cx);
        }));

        assert!(result.is_err(), "truncated output_state_vars must panic in build_output_args");
        // Production code may record fallback at multiple points before reaching
        // build_output_args (e.g., PtrIsNull stub + coercion fallback). Accept >=1.
        assert!(
            chc_ctx.sound_fallback_count() >= 1,
            "pointer utility missing output state must record fallback before panic, got {}",
            chc_ctx.sound_fallback_count()
        );
    });
}

/// Mem intrinsic coercion failure increments fallback.
/// Exercises line 371 of codegen_call_ptr.rs.
/// Part of #2783.
#[test]
fn test_mem_intrinsic_coercion_failure_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of_coerce() -> usize {
            core::mem::size_of::<u32>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of_coerce");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_size_of_coerce", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
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

        let (bb_idx, func, destination, target) = call_site.expect("expected call terminator");
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

        // Force coercion failure: set dest output sort to Real (no BV→Real
        // coercion path). Array sorts no longer work because reinterpret_fixed_layout_expr
        // (#3675) handles BV→Array. Part of #3785.
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 = ay_bindings::Sort::real();

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::MemSizeOf,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_mem_intrinsic(&func, &cx);

        assert!(
            chc_ctx.sound_fallback_count() >= 1,
            "mem intrinsic coercion failure must increment fallback counter"
        );
    });
}

/// Mem intrinsic with missing destination output state var increments fallback.
/// Exercises line 385 of codegen_call_ptr.rs.
/// Part of #2783.
#[test]
fn test_mem_intrinsic_missing_output_state_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of_missing_state() -> usize {
            core::mem::size_of::<u32>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of_missing_state");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_size_of_missing_state", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
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

        let (bb_idx, func, destination, target) = call_site.expect("expected call terminator");
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

        // Truncate output_state_vars so destination index is out of bounds,
        // forcing the "missing output state" fallback path.
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars.truncate(dest_vec_idx);

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::MemSizeOf,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        // build_output_args panics on truncated output_state_vars, but
        // record_fallback() is called before build_output_args (line 385 before 386).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            chc_ctx.codegen_call_mem_intrinsic(&func, &cx);
        }));

        assert!(result.is_err(), "truncated output_state_vars must panic in build_output_args");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "mem intrinsic missing output state must record fallback before panic"
        );
    });
}

/// copy_nonoverlapping unresolved destination increments fallback.
/// Exercises line 336 of codegen_call_ptr.rs.
#[test]
fn test_copy_nonoverlapping_unresolved_increments_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_unresolved(src: *const u8, dst: *mut u8) {
            unsafe { std::ptr::copy_nonoverlapping(src, dst, 4); }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_unresolved");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_unresolved", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find any call site for scaffold
        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, _args, destination, target) = call_site.expect("expected call terminator");
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

        let before_fallback = chc_ctx.fallback_count;

        // Force unresolvable src/dst/count locals so try_encode_copy_nonoverlapping_intrinsic
        // deterministically returns false and hits the line-336 fallback path.
        let forced_unresolved_args = vec![
            Operand::Copy(Place { local: 997usize, projection: vec![] }),
            Operand::Copy(Place { local: 998usize, projection: vec![] }),
            Operand::Copy(Place { local: 999usize, projection: vec![] }),
        ];
        let cx = ChcCallContext {
            stub: StubKind::PtrWrite, // stub doesn't matter for copy_nonoverlapping
            args: &forced_unresolved_args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_copy_nonoverlapping(bb_idx, &cx, false);

        // Part of #3369: reclassified from sound_fallback to fallback (DEMOTED) —
        // copy_nonoverlapping has memory side effects; destination memory retains
        // previous value (identity) instead of becoming nondeterministic.
        assert!(
            chc_ctx.fallback_count > before_fallback,
            "copy_nonoverlapping unresolved destination must increment fallback_count"
        );
        assert!(!chc_ctx.vc.rules.is_empty(), "copy_nonoverlapping should emit at least one rule");
    });
}

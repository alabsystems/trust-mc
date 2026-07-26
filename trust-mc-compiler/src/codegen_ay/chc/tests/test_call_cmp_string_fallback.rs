// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for non-primitive fallback paths in `codegen_call_cmp_string`.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;

fn with_known_stdlib_contains_dispatch(
    assertions: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::String;

        pub fn probe_known_stdlib_contains(s: &String) -> bool {
            s.contains("needle")
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_known_stdlib_contains");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_known_stdlib_contains", ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                    && let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains("::contains")
                    && path.contains("str")
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target, path))
                } else {
                    None
                }
            })
            .expect("expected known-stdlib contains call terminator");

        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        assertions(
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
            &callee_path,
        );
    });
}

fn assert_known_stdlib_shared_receiver(
    chc_ctx: &ChcCtx<'_, '_>,
    actual_args: &[Operand],
    callee_path: &str,
) {
    assert!(
        callee_path.contains("core::str::<impl str>::contains"),
        "precondition: expected str::contains known-stdlib path, got {callee_path}"
    );
    assert!(
        matches!(
            actual_args[0].ty(chc_ctx.body.locals()).expect("shared receiver arg type").kind(),
            TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Not))
        ),
        "precondition: expected a shared receiver, got {:?}",
        actual_args[0].ty(chc_ctx.body.locals())
    );
}

fn remove_shared_receiver_mapping(chc_ctx: &mut ChcCtx<'_, '_>, actual_args: &[Operand]) {
    let receiver_local = match &actual_args[0] {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        Operand::Constant(..) => panic!("expected shared receiver operand, got constant"),
    };
    let removed_idx = chc_ctx.state_var_mgr.local_to_state_idx.remove(&receiver_local);
    assert!(
        removed_idx.is_some(),
        "precondition: shared receiver local {receiver_local} must have a state-var mapping"
    );
}

fn assert_known_stdlib_counters_before(chc_ctx: &ChcCtx<'_, '_>) {
    assert_eq!(chc_ctx.fallback_count, 0, "precondition: demoted fallback count at zero");
    assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: sound fallback count at zero");
    assert_eq!(
        chc_ctx.diagnostics.known_stdlib_unconstrained.get(),
        0,
        "precondition: known-stdlib counter at zero"
    );
    assert_eq!(
        chc_ctx.diagnostics.inferable_predicate.get(),
        0,
        "precondition: inferable counter at zero"
    );
    assert_eq!(
        chc_ctx.diagnostics.unhandled_call.get(),
        0,
        "precondition: unhandled-call counter at zero"
    );
}

fn assert_known_stdlib_counters_after_shared(chc_ctx: &ChcCtx<'_, '_>, before_rules: usize) {
    assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
    assert_eq!(
        chc_ctx.diagnostics.known_stdlib_unconstrained.get(),
        1,
        "known-stdlib path must stay classified when inferable summary fails"
    );
    assert_eq!(
        chc_ctx.diagnostics.inferable_predicate.get(),
        0,
        "untranslatable operands must skip inferable summary creation"
    );
    assert_eq!(
        chc_ctx.diagnostics.unhandled_call.get(),
        0,
        "known-stdlib classification must not fall through to generic catch-all"
    );
    assert_eq!(
        chc_ctx.fallback_count, 0,
        "immutable known-stdlib non-inferable path must not record demoted fallback"
    );
    assert_eq!(
        chc_ctx.sound_fallback_count(),
        1,
        "immutable known-stdlib non-inferable path must record sound fallback"
    );
}

fn with_mut_receiver_unhandled_dispatch(
    assertions: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
    ) + Send,
) {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct Counter(pub u32);

        impl Counter {
            pub fn bump(&mut self) {
                self.0 += 1;
            }
        }

        pub fn probe_mut_receiver_unhandled(c: &mut Counter) {
            c.bump();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mut_receiver_unhandled");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_mut_receiver_unhandled", ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                    && let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains("bump")
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target))
                } else {
                    None
                }
            })
            .expect("expected Counter::bump call terminator");

        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        assertions(
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
        );
    });
}

/// Known-stdlib calls with shared (immutable) receivers and non-inferable
/// operands must take the sound over-approximation path, not the DEMOTED path.
/// Part of #3142: tail-dispatch fallback classification split.
#[test]
fn test_known_stdlib_noninferable_shared_receiver_records_sound_fallback() {
    with_known_stdlib_contains_dispatch(
        |chc_ctx,
         func,
         actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert_known_stdlib_shared_receiver(chc_ctx, actual_args, callee_path);
            remove_shared_receiver_mapping(chc_ctx, actual_args);
            let before_rules = chc_ctx.vc.rules.len();
            assert_known_stdlib_counters_before(chc_ctx);

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: actual_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);
            assert_known_stdlib_counters_after_shared(chc_ctx, before_rules);
        },
    );
}

/// Mutable-receiver calls reaching `codegen_unhandled_call` must stay DEMOTED
/// (not sound over-approximation), because receiver side effects are dropped.
/// Part of #3142: tail-dispatch fallback classification split.
#[test]
fn test_unhandled_mut_receiver_stays_demoted() {
    with_mut_receiver_unhandled_dispatch(
        |chc_ctx,
         func,
         actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx| {
            assert!(
                chc_ctx.has_mut_receiver(actual_args),
                "precondition: Counter::bump must have &mut self receiver"
            );
            let before_rules = chc_ctx.vc.rules.len();
            assert_known_stdlib_counters_before(chc_ctx);

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: actual_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);

            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
            assert_eq!(
                chc_ctx.fallback_count, 1,
                "mutable-receiver unhandled call must record demoted fallback"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                0,
                "mutable-receiver unhandled call must not record sound fallback"
            );
            assert_eq!(
                chc_ctx.diagnostics.known_stdlib_unconstrained.get(),
                0,
                "user-defined method must not match known-stdlib classifier"
            );
            assert_eq!(
                chc_ctx.diagnostics.unhandled_call.get(),
                1,
                "user-defined method must reach unhandled-call catch-all"
            );
        },
    );
}

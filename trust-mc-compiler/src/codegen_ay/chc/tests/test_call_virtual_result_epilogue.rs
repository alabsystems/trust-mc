// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Targeted regressions for the shared virtual inline-result epilogue.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::RelationApp;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call::CallTerminator;
use crate::codegen_ay::emit_chc;
use ay_bindings::Expr;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Operand, TerminatorKind};

const VIRTUAL_AGGREGATE_EQ_PROBE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy, PartialEq, Eq)]
    struct Pair {
        left: u8,
        right: u8,
    }

    trait Provider {
        fn get(&self) -> Pair;
    }

    struct OnlyPair;

    impl Provider for OnlyPair {
        fn get(&self) -> Pair {
            Pair { left: 1, right: 2 }
        }
    }

    pub fn probe_virtual_aggregate_eq() {
        let provider: &dyn Provider = &OnlyPair;
        let result = provider.get();
        assert!(result == Pair { left: 1, right: 2 });
    }
"#;

struct VirtualCallSite {
    bb_idx: usize,
    func: Operand,
    args: Vec<Operand>,
    destination: Place,
    target: usize,
    callee_path: String,
}

fn find_first_virtual_call_site(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> VirtualCallSite {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            else {
                return None;
            };
            let func_ty = func.ty(chc_ctx.body.locals()).ok()?;
            let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                return None;
            };
            let instance = Instance::resolve(def, &substs).ok()?;
            matches!(instance.kind, InstanceKind::Virtual { .. }).then(|| VirtualCallSite {
                bb_idx,
                func: func.clone(),
                args: args.clone(),
                destination: destination.clone(),
                target: *target,
                callee_path: chc_ctx
                    .resolve_callee_path(func)
                    .unwrap_or_else(|| "<virtual dispatch>".to_string()),
            })
        })
        .expect("expected virtual call terminator")
}

fn assert_virtual_probe_produces_proof(source: &str, fn_name: &str) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");
        assert!(
            !vc_error_rules_contain_var(&vc, "__vtable_disc"),
            "{fn_name} should not fall back to a fresh vtable"
        );
        assert!(
            !vc_error_rules_contain_var(&vc, "__assert_fail_inline"),
            "{fn_name} should keep the semantic assertion precise"
        );

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

#[test]
fn test_virtual_aggregate_eq_solver_produces_proof() {
    assert_virtual_probe_produces_proof(VIRTUAL_AGGREGATE_EQ_PROBE, "probe_virtual_aggregate_eq");
}

#[test]
fn test_virtual_handler_drains_pending_state() {
    with_test_ay_ctx_for_source(VIRTUAL_AGGREGATE_EQ_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_virtual_aggregate_eq");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_virtual_aggregate_eq", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let callsite = find_first_virtual_call_site(&chc_ctx, &body);
        let (stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(callsite.bb_idx);
        let from_rel =
            chc_ctx.block_relations.get(&callsite.bb_idx).expect("source relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(callsite.bb_idx));
        let target_opt = Some(callsite.target);

        chc_ctx.heap_state.pending_updates.push(Expr::bool_const(true));
        chc_ctx.heap_state.pending_checks.push(Expr::bool_const(false));
        let error_rules_before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();

        let dcx = DispatchCallContext {
            bb_idx: callsite.bb_idx,
            func: &callsite.func,
            args: &callsite.args,
            destination: &callsite.destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };
        assert!(
            chc_ctx.codegen_call_terminator(&dcx),
            "{} should be handled by call dispatch",
            callsite.callee_path
        );

        let error_rules_after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(
            error_rules_after > error_rules_before,
            "virtual dispatch must emit error rules for pending checks"
        );
        assert!(
            chc_ctx.heap_state.pending_updates.is_empty(),
            "virtual dispatch must drain pending updates through the inline-result epilogue"
        );
        assert!(
            chc_ctx.heap_state.pending_checks.is_empty(),
            "virtual dispatch must drain pending checks through the inline-result epilogue"
        );
    });
}

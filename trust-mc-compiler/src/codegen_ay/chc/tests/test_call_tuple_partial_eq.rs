// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for tuple `PartialEq` call dispatch and inline encoding.
//!
//! Part of #3786: tuple equality must avoid the primitive comparison stub path
//! and prove simple equalities without CHC fallback counters.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_fn_inline::CallDispatchFnInline;
use super::common::*;
use crate::codegen_ay::emit_chc;
use crate::codegen_ay::shared::{count_effective_blocks, inline_effective_block_limit};
use rustc_public::mir::TerminatorKind;

const TUPLE_PARTIAL_EQ_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_tuple_u8_bool_eq() {
        let t: (u8, bool) = (0, true);
        assert!(t == (0, true));
    }

    pub fn probe_tuple_u8_u8_eq() {
        let t: (u8, u8) = (0, 1);
        assert!(t == (0, 1));
    }
"#;

const PROBE_FN_NAMES: [&str; 2] = ["probe_tuple_u8_bool_eq", "probe_tuple_u8_u8_eq"];

fn reset_tuple_eq_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

fn with_tuple_partial_eq_call(
    probe_suffix: &str,
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
    with_test_ay_ctx_for_source(TUPLE_PARTIAL_EQ_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, probe_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, probe_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                    && let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains("tuple::<impl")
                    && path.ends_with("::eq")
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target, path))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                panic!("expected tuple PartialEq call terminator in {probe_suffix}")
            });

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

#[test]
fn test_tuple_partial_eq_call_is_not_detected_as_primitive_cmp_stub() {
    with_test_ay_ctx_for_source(TUPLE_PARTIAL_EQ_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());

            let primitive_cmp_paths: Vec<_> = body
                .blocks
                .iter()
                .filter_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. }
                        if chc_ctx
                            .detect_stub_matching(func, StubKind::is_primitive_cmp)
                            .is_some() =>
                    {
                        chc_ctx.resolve_callee_path(func)
                    }
                    _ => None,
                })
                .collect();

            assert!(
                primitive_cmp_paths.is_empty(),
                "{fn_name} should not route tuple PartialEq through PrimitivePartialEqEq, paths={primitive_cmp_paths:?}"
            );
        }
    });
}

#[test]
fn test_tuple_partial_eq_call_is_claimed_by_fn_inline() {
    with_tuple_partial_eq_call(
        "probe_tuple_u8_bool_eq",
        |chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let func_ty = func.ty(chc_ctx.body.locals()).expect("call callee type");
            let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                panic!("expected FnDef for tuple PartialEq call, got {func_ty:?}");
            };
            let instance = rustc_public::mir::mono::Instance::resolve(def, &substs)
                .expect("tuple eq instance");
            let inline_body = instance.body().expect("tuple eq body");
            let effective = count_effective_blocks(&inline_body);
            let limit = inline_effective_block_limit(&inline_body, effective);
            assert!(
                effective <= limit,
                "{callee_path} should fit fn_inline size gate: effective={effective}, limit={limit}"
            );

            let params: Vec<_> = args
                .iter()
                .map(|arg| chc_ctx.resolve_ref_or_const_referent(arg, modified_locals))
                .collect();
            assert!(
                params.iter().all(Option::is_some),
                "{callee_path} should translate all inline params, got {params:?}"
            );

            let before_rules = chc_ctx.vc.rules.len();
            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            assert!(
                chc_ctx.try_dispatch_call_fn_inline(&dcx),
                "{callee_path} should be handled by fn_inline"
            );
            assert_eq!(
                chc_ctx.vc.rules.len(),
                before_rules + 1,
                "{callee_path} should emit one goto rule when inlined"
            );
        },
    );
}

#[test]
fn test_tuple_partial_eq_proves_without_fallbacks() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_tuple_eq_counters();

    with_test_ay_ctx_for_source(TUPLE_PARTIAL_EQ_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

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
                "{fn_name} should inline tuple PartialEq instead of emitting inferable summaries: {inferable_decls:?}"
            );

            let has_p_inf_rule =
                vc.rules.iter().any(|rule| format!("{:?}", rule).contains("P_inf_"));
            assert!(
                !has_p_inf_rule,
                "{fn_name} should not reference P_inf_* summaries in emitted rules"
            );

            let smt = emit_chc(&vc).to_string();
            assert_z3_result(&smt, "unsat");
        }

        let fallback_counts = get_chc_fallback_counts();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        for fn_name in PROBE_FN_NAMES {
            let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should stay on the precise tuple PartialEq path, fallback map={fallback_counts:?}"
            );

            let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                unhandled_count, 0,
                "{fn_name} should not increment unhandled-call counters, map={unhandled_calls:?}"
            );
        }
    });

    reset_tuple_eq_counters();
}

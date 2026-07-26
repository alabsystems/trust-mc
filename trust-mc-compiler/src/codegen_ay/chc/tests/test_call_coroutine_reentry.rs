// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-backed regression tests for repeated coroutine re-entry dispatch.
//!
//! Part of #3993: inline `Pin::new(&mut coro).resume(...)` receiver write-back.

#![allow(clippy::panic, clippy::unwrap_used)]

use super::super::call::inline_alias_writeback::resolve_call_arg_target_local;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coroutine::CallDispatchCoroutine;
use super::common::*;
use crate::codegen_ay::emit_chc;
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlock, Body, Operand, TerminatorKind};

const INLINE_PIN_REENTRY_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_inline_pin_reentry(a: u8, b: u8) -> bool {
        let mut add_one = #[coroutine]
        |mut resume: u8| {
            loop {
                resume = yield resume.saturating_add(1);
            }
        };

        let first = Pin::new(&mut add_one).resume(a);
        let second = Pin::new(&mut add_one).resume(b);

        matches!(first, CoroutineState::Yielded(v) if v == a.saturating_add(1))
            && matches!(second, CoroutineState::Yielded(v) if v == b.saturating_add(1))
    }
"#;

const YIELD_ONLY_RESUME_ARG_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::Coroutine;
    use std::pin::Pin;

    pub fn probe_resume_arg_writeback() {
        let mut g = #[coroutine]
        |mut x: Box<u8>| {
            loop {
                drop(x);
                x = yield;
            }
        };

        let _ = Pin::new(&mut g).resume(Box::new(0));
        let _ = Pin::new(&mut g).resume(Box::new(1));
    }
"#;

const COROUTINE_DROP_ENV_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::Coroutine;
    use std::pin::Pin;

    struct DropFlag;

    impl Drop for DropFlag {
        fn drop(&mut self) {}
    }

    pub fn probe_coroutine_drop_env() {
        let flag = DropFlag;
        let mut g = #[coroutine]
        || {
            yield;
            drop(flag);
        };

        let _ = Pin::new(&mut g).resume(());
        drop(g);
    }
"#;

const COROUTINE_DROP_ENV_ATOMIC_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::Coroutine;
    use std::pin::Pin;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    struct DropFlag;

    impl Drop for DropFlag {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::SeqCst);
        }
    }

    pub fn probe_coroutine_drop_env_atomic() {
        let flag = DropFlag;
        let mut g = #[coroutine]
        || {
            yield;
            drop(flag);
        };

        let _ = Pin::new(&mut g).resume(());
        drop(g);
    }
"#;

const COROUTINE_ENV_DROP_EXACT_SOURCE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../tests/trust_mc/Coroutines/rustc-coroutine-tests/env-drop.rs"
));

#[derive(Debug)]
struct InlinePinReentryDiagnostics {
    local6_decl: Option<String>,
    bb0_statements: Vec<String>,
}

impl InlinePinReentryDiagnostics {
    fn from_body(body: &Body) -> Self {
        let local6_decl =
            body.local_decls().find_map(|(idx, decl)| (idx == 6).then_some(format!("{decl:?}")));
        let bb0_statements = body
            .blocks
            .first()
            .map(|block| block.statements.iter().map(|stmt| format!("{:?}", stmt.kind)).collect())
            .unwrap_or_default();
        Self { local6_decl, bb0_statements }
    }
}

fn init_test_tracing() {
    let _ = tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_test_writer()
        .try_init();
}

#[test]
fn test_inline_pin_new_reentry_keeps_receiver_visible_to_dispatch() {
    init_test_tracing();
    with_test_ay_ctx_for_source(INLINE_PIN_REENTRY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_inline_pin_reentry");
        let body = instance.body().expect("function body");
        let diagnostics = InlinePinReentryDiagnostics::from_body(&body);
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_inline_pin_reentry", ChcConfig::default());
        chc_ctx.declare_block_relations();
        assert_inline_pin_reentry_dispatch(&mut chc_ctx, &body, &diagnostics);
    });
}

#[test]
fn test_yield_only_resume_arg_reentry_avoids_fallback() {
    init_test_tracing();
    with_test_ay_ctx_for_source(YIELD_ONLY_RESUME_ARG_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_resume_arg_writeback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_resume_arg_writeback", ChcConfig::default());
        chc_ctx.declare_block_relations();
        assert_yield_only_resume_arg_dispatch(&mut chc_ctx, &body);
    });
}

#[test]
fn test_coroutine_drop_env_translation_avoids_inline_drop_walk_failure() {
    init_test_tracing();
    assert_coroutine_drop_env_translation_avoids_inline_drop_walk_failure(
        COROUTINE_DROP_ENV_SOURCE,
        "probe_coroutine_drop_env",
    );
}

#[test]
fn test_coroutine_drop_env_atomic_translation_avoids_inline_drop_walk_failure() {
    init_test_tracing();
    assert_coroutine_drop_env_translation_avoids_inline_drop_walk_failure(
        COROUTINE_DROP_ENV_ATOMIC_SOURCE,
        "probe_coroutine_drop_env_atomic",
    );
}

#[test]
fn test_exact_env_drop_translation_avoids_inline_drop_walk_failure() {
    init_test_tracing();
    assert_coroutine_drop_env_translation_avoids_inline_drop_walk_failure(
        COROUTINE_ENV_DROP_EXACT_SOURCE,
        "main",
    );
}

fn assert_inline_pin_reentry_dispatch(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &Body,
    diagnostics: &InlinePinReentryDiagnostics,
) {
    let mut call_summaries = Vec::new();
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if try_assert_inline_pin_reentry_call(
            chc_ctx,
            body,
            diagnostics,
            &mut call_summaries,
            bb_idx,
            block,
        ) {
            return;
        }
    }

    panic!(
        "expected an inline Pin::new repeated-resume call with a live receiver state; local6_decl={:?}; bb0_statements={:?}; calls={call_summaries:?}",
        diagnostics.local6_decl, diagnostics.bb0_statements
    );
}

fn assert_yield_only_resume_arg_dispatch(chc_ctx: &mut ChcCtx<'_, '_>, body: &Body) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if try_assert_yield_only_resume_arg_call(chc_ctx, body, bb_idx, block) {
            return;
        }
    }
    panic!("expected a yield-only repeated resume(Box<_>) call with a live receiver state");
}

fn assert_coroutine_drop_env_translation_avoids_inline_drop_walk_failure(
    source: &str,
    fn_name: &str,
) {
    let sanitized = source.replace("#[kani::proof]\n", "");
    with_test_ay_ctx_for_source(&sanitized, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.sound_fallback_detail.get("inline_drop_walk_failed").copied().unwrap_or(0),
            0,
            "{fn_name} should translate coroutine env drop without inline_drop_walk_failed, got {:?}",
            diagnostics.sound_fallback_detail
        );
    });
}

fn try_assert_inline_pin_reentry_call(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &Body,
    diagnostics: &InlinePinReentryDiagnostics,
    call_summaries: &mut Vec<String>,
    bb_idx: usize,
    block: &BasicBlock,
) -> bool {
    let Some((func, args, destination, target)) = coroutine_state_call_parts(body, block) else {
        return false;
    };

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
    let target_opt = Some(target);
    let dcx = DispatchCallContext {
        bb_idx,
        func,
        args,
        destination,
        target: &target_opt,
        from_app: &from_app,
        stmt_constraints: &stmt_constraints,
        modified_locals: &modified_locals,
        callee_path: None,
    };

    let receiver_state_idx = chc_ctx.coroutine_live_receiver_state_idx(&dcx, target);
    call_summaries.push(format_call_summary(chc_ctx, body, &dcx, bb_idx, receiver_state_idx));
    let Some(receiver_state_idx) = receiver_state_idx else {
        return false;
    };

    assert_inline_pin_reentry_result(
        chc_ctx,
        &dcx,
        receiver_state_idx,
        diagnostics,
        call_summaries,
    );
    true
}

fn try_assert_yield_only_resume_arg_call(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &Body,
    bb_idx: usize,
    block: &BasicBlock,
) -> bool {
    let Some((func, args, destination, target)) = coroutine_state_call_parts(body, block) else {
        return false;
    };

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
    let target_opt = Some(target);
    let dcx = DispatchCallContext {
        bb_idx,
        func,
        args,
        destination,
        target: &target_opt,
        from_app: &from_app,
        stmt_constraints: &stmt_constraints,
        modified_locals: &modified_locals,
        callee_path: None,
    };
    let Some(receiver_state_idx) = chc_ctx.coroutine_live_receiver_state_idx(&dcx, target) else {
        return false;
    };
    let call_summary = format_call_summary(chc_ctx, body, &dcx, bb_idx, Some(receiver_state_idx));
    assert!(
        chc_ctx
            .try_build_simple_coroutine_receiver_writeback_eq(&dcx, receiver_state_idx)
            .is_some(),
        "yield-only repeated resume(Box<_>) should build a receiver write-back constraint; {call_summary}"
    );

    let receiver_out_name = chc_ctx.state_var_mgr.output_state_vars[receiver_state_idx].0.clone();
    let before_fallback = chc_ctx.sound_fallback_count();
    let before_rules = chc_ctx.vc.rules.len();
    assert!(
        chc_ctx.try_dispatch_call_coroutine(&dcx),
        "yield-only resume(Box<_>) call should be handled by coroutine dispatch"
    );
    assert_eq!(
        chc_ctx.sound_fallback_count(),
        before_fallback,
        "yield-only repeated resume(Box<_>) should avoid sound fallback; {call_summary}; detail={:?}",
        chc_ctx.sound_fallback_detail()
    );
    assert!(
        chc_ctx.vc.rules.len() > before_rules,
        "yield-only repeated resume(Box<_>) should emit a transition rule"
    );

    let smt = emit_chc(&chc_ctx.vc).to_string();
    assert!(
        smt.contains(receiver_out_name.as_ref()),
        "precise coroutine dispatch should constrain the receiver output var {receiver_out_name}; smt={smt}"
    );
    assert!(
        smt.contains("Yielded_CoroutineState"),
        "yield-only repeated resume(Box<_>) should constrain the CoroutineState result to Yielded(...); smt={smt}"
    );
    true
}

fn coroutine_state_call_parts<'a>(
    body: &'a Body,
    block: &'a BasicBlock,
) -> Option<(&'a Operand, &'a [Operand], &'a Place, usize)> {
    let (func, args, destination, target) = match &block.terminator.kind {
        TerminatorKind::Call { func, args, destination, target: Some(target), .. } => {
            (func, args.as_slice(), destination, *target)
        }
        _ => return None,
    };
    let Ok(dest_ty) = destination.ty(body.locals()) else {
        return None;
    };
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = dest_ty.kind() else {
        return None;
    };
    (def.trimmed_name() == "CoroutineState").then_some((func, args, destination, target))
}

fn format_call_summary(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &Body,
    dcx: &DispatchCallContext<'_>,
    bb_idx: usize,
    receiver_state_idx: Option<usize>,
) -> String {
    let func_ty = dcx
        .func
        .ty(body.locals())
        .ok()
        .map(|ty| format!("{ty:?}"))
        .unwrap_or_else(|| "<ty-err>".to_string());
    let arg_summaries: Vec<_> = dcx
        .args
        .iter()
        .enumerate()
        .map(|(arg_idx, arg)| format_arg_summary(chc_ctx, body, dcx, arg_idx, arg))
        .collect();
    format!(
        "bb={bb_idx} func={:?} func_ty={func_ty} receiver_state_idx={receiver_state_idx:?} args={arg_summaries:?}",
        dcx.func
    )
}

fn format_arg_summary(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &Body,
    dcx: &DispatchCallContext<'_>,
    arg_idx: usize,
    arg: &Operand,
) -> String {
    let resolved_local = resolve_call_arg_target_local(chc_ctx, dcx, arg_idx + 1);
    let ty_name = arg
        .ty(body.locals())
        .ok()
        .map(|ty| format!("{ty:?}"))
        .unwrap_or_else(|| "<ty-err>".to_string());
    match arg {
        Operand::Copy(place) | Operand::Move(place) => format!(
            "arg{} local={} projection={:?} ty={} resolved_local={resolved_local:?}",
            arg_idx + 1,
            place.local,
            place.projection,
            ty_name
        ),
        _ => format!(
            "arg{} operand={arg:?} ty={} resolved_local={resolved_local:?}",
            arg_idx + 1,
            ty_name
        ),
    }
}

fn assert_inline_pin_reentry_result(
    chc_ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    receiver_state_idx: usize,
    diagnostics: &InlinePinReentryDiagnostics,
    call_summaries: &[String],
) {
    let receiver_name = chc_ctx.state_var_mgr.state_vars[receiver_state_idx].0.clone();
    let receiver_out_name = chc_ctx.state_var_mgr.output_state_vars[receiver_state_idx].0.clone();
    let before_fallback = chc_ctx.sound_fallback_count();
    let before_rules = chc_ctx.vc.rules.len();

    assert!(
        chc_ctx.try_dispatch_call_coroutine(dcx),
        "inline Pin::new repeated-resume call should be handled by coroutine dispatch"
    );
    assert_eq!(
        chc_ctx.sound_fallback_count(),
        before_fallback,
        "inline Pin::new repeated-resume call should stay on the precise inline/write-back path instead of falling back; local6_decl={:?}; bb0_statements={:?}; call_summaries={call_summaries:?}",
        diagnostics.local6_decl,
        diagnostics.bb0_statements
    );
    assert!(
        chc_ctx.vc.rules.len() > before_rules,
        "inline Pin::new repeated-resume call should emit at least one transition rule (got {} new rules)",
        chc_ctx.vc.rules.len() - before_rules
    );
    let new_rules = &chc_ctx.vc.rules[before_rules..];
    assert!(
        new_rules.iter().any(|rule| rule_contains_var(rule, receiver_name.as_ref())),
        "inline Pin::new repeated-resume call should keep receiver state family {receiver_name} (output slot {receiver_out_name}) visible in the newly emitted rules; local6_decl={:?}; bb0_statements={:?}; call_summaries={call_summaries:?}",
        diagnostics.local6_decl,
        diagnostics.bb0_statements
    );
}

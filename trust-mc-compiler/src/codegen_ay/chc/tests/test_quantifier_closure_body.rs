// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused tests for `quantifier_encoding/closure_body.rs`.
//!
//! Part of #2921 (CHC codegen test coverage gaps).
//! Covers:
//! - capture-by-reference closure projection handling (Field + Deref)
//! - unary `Neg` translation inside closure bodies
//! - fail-closed `None` when call-delegation target is a multi-block callee

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::{
    Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind, UnOp, mono::Instance,
};
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};

use super::super::quantifier_encoding::QuantifierEncoding;
use crate::kani_middle::kani_functions::KaniHook;

const QUANTIFIER_CLOSURE_BODY_EXTRA_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall<F>(lower: i32, upper: i32, pred: F) -> bool
    where
        F: Fn(i32) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if !pred(i) { return false; }
            i += 1;
        }
        true
    }
}

#[inline(never)]
fn non_negative_or_zero(v: i32) -> i32 {
    if v >= 0 { v } else { 0 }
}

pub fn probe_quant_capture_ref(limit: i32) -> bool {
    let limit_ref = &limit;
    kani::forall(0, 3, |x| x <= *limit_ref)
}

pub fn probe_quant_unary_neg() -> bool {
    kani::forall(0, 3, |x| {
        let y = -x;
        y <= 0
    })
}

pub fn probe_quant_multiblock_call() -> bool {
    kani::forall(0, 3, |x| non_negative_or_zero(x) >= 0)
}
"#;

fn find_quantifier_forall_call<'a>(
    chc_ctx: &ChcCtx<'_, 'a>,
    body: &'a rustc_public::mir::Body,
) -> (usize, &'a rustc_public::mir::Operand, &'a [rustc_public::mir::Operand]) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| match &block.terminator.kind {
            TerminatorKind::Call { func, args, .. }
                if matches!(chc_ctx.detect_kani_hook(func), Some(found) if found == KaniHook::Forall) =>
            {
                Some((bb_idx, func, args.as_slice()))
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("expected ForallHook call in probe body"))
}

fn resolve_quantifier_closure_body(
    call_site_body: &rustc_public::mir::Body,
    func: &rustc_public::mir::Operand,
) -> rustc_public::mir::Body {
    let func_ty = func.ty(call_site_body.locals()).expect("quantifier call type");
    let (_fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => panic!("quantifier call target should be a FnDef"),
    };

    for arg in &fn_args.0 {
        let Some(arg_ty) = arg.ty() else { continue };
        if let TyKind::RigidTy(RigidTy::Closure(def, closure_args)) = arg_ty.kind() {
            for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                if let Ok(instance) = Instance::resolve_closure(def, &closure_args, kind)
                    && let Some(body) = instance.body()
                {
                    return body;
                }
            }
        }
    }
    panic!("expected quantifier closure body to resolve");
}

fn operand_uses_capture_field(operand: &Operand) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place.local == 1
                && place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(_, _)))
        }
        Operand::Constant(_) => false,
    }
}

fn rvalue_uses_capture_field(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_uses_capture_field(lhs) || operand_uses_capture_field(rhs)
        }
        Rvalue::UnaryOp(_, operand) | Rvalue::Use(operand) => operand_uses_capture_field(operand),
        Rvalue::Ref(_, _, place) | Rvalue::CopyForDeref(place) => {
            place.local == 1
                && place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(_, _)))
        }
        _ => false,
    }
}

#[test]
fn test_quantifier_closure_body_capture_ref_projection_path() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_EXTRA_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_capture_ref");
        let body = instance.body().expect("probe body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_quant_capture_ref", ChcConfig::default());

        let (_bb_idx, func, _args) = find_quantifier_forall_call(&chc_ctx, &body);
        let closure_body = resolve_quantifier_closure_body(&body, func);

        let has_capture_projection = closure_body.blocks.iter().any(|bb| {
            bb.statements.iter().any(|stmt| {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind {
                    rvalue_uses_capture_field(rvalue)
                } else {
                    false
                }
            })
        });
        assert_mir_pattern_found(
            has_capture_projection,
            "closure capture projection via local 1 Field(...) in quantifier closure body",
        );

        // NOTE: build_quantifier_expr requires full codegen state (SSA
        // variables, environments) to translate captured operands from the
        // outer function. A bare ChcCtx::new() doesn't provide this, so we
        // only verify the MIR pattern here. End-to-end quantifier translation
        // with captures is covered by integration tests.
    });
}

#[test]
fn test_quantifier_closure_body_unary_neg_path() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_EXTRA_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_unary_neg");
        let body = instance.body().expect("probe body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_quant_unary_neg", ChcConfig::default());

        let (bb_idx, func, args) = find_quantifier_forall_call(&chc_ctx, &body);
        let closure_body = resolve_quantifier_closure_body(&body, func);
        let has_unary_neg = closure_body.blocks.iter().any(|bb| {
            bb.statements.iter().any(|stmt| {
                matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::UnaryOp(UnOp::Neg, _)))
            })
        });
        assert_mir_pattern_found(has_unary_neg, "quantifier closure unary Neg rvalue");

        let expr = chc_ctx
            .build_quantifier_expr(func, args, &HashSet::new(), bb_idx, true)
            .expect("forall quantifier expression should be generated for unary-neg closure");
        assert!(
            expr.sort().is_bool(),
            "unary-neg closure translation should produce Bool, got {}",
            expr.sort()
        );
    });
}

#[test]
fn test_quantifier_closure_body_call_delegation_multiblock_callee_fails_closed() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_EXTRA_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_multiblock_call");
        let body = instance.body().expect("probe body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_quant_multiblock_call", ChcConfig::default());

        let (bb_idx, func, args) = find_quantifier_forall_call(&chc_ctx, &body);
        let closure_body = resolve_quantifier_closure_body(&body, func);
        let has_two_block_call_delegation = closure_body.blocks.len() == 2
            && matches!(
                &closure_body.blocks[0].terminator.kind,
                TerminatorKind::Call { target: Some(1), .. }
            )
            && matches!(&closure_body.blocks[1].terminator.kind, TerminatorKind::Return);
        assert_mir_pattern_found(
            has_two_block_call_delegation,
            "quantifier closure 2-block call delegation (Call -> bb1 -> Return)",
        );

        let maybe_expr = chc_ctx.build_quantifier_expr(func, args, &HashSet::new(), bb_idx, true);
        assert!(
            maybe_expr.is_none(),
            "closure call delegation with multi-block callee must fail closed (None)"
        );
    });
}

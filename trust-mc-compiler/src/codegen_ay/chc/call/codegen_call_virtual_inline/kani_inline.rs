// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline handling for kani::any() and kani::assume() inside inlined bodies.
//!
//! Part of #3737: enables inlining of rotate-helper and similar patterns.
//! Part of #3639: Extracted from codegen_call_virtual_inline.rs.

mod assume_refinement;

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, LocalDecl, Operand};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use super::super::ChcCtx;
use super::super::inline_body::DeferredInlineCheck;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::super::quantifier_encoding::QuantifierEncoding;
use crate::codegen_ay::chc::decl::codegen_types::CodegenTypes;
use crate::codegen_ay::types::{POINTER_WIDTH, ty_to_bv_width};
use crate::kani_middle::attributes;
use crate::kani_middle::kani_functions::{
    KaniFunction, KaniHook, KaniIntrinsic, KaniModel, try_get_kani_function,
};

pub(super) use assume_refinement::refine_inline_value_from_assume;

fn fresh_inline_any_expr(ctx: &ChcCtx<'_, '_>, locals: &[LocalDecl], dest_local: usize) -> Expr {
    let dest_ty = locals[dest_local].ty;
    let sort = ChcCtx::translate_ty(ctx.resolve_body_ty(dest_ty))
        .or_else(|| ty_to_bv_width(dest_ty).map(Sort::bitvec))
        .unwrap_or_else(|| Sort::bitvec(POINTER_WIDTH));
    super::super::declare_pending_var(super::super::chc_fresh_name("__kani_any_inline"), sort)
}

pub(super) fn inline_bool_condition(cond_expr: Expr) -> Option<Expr> {
    if cond_expr.sort().is_bool() {
        Some(cond_expr)
    } else {
        cond_expr.sort().bitvec_width().map(|w| cond_expr.eq(Expr::bitvec_const(0u64, w)).not())
    }
}

fn resolve_inline_kani_callee_path(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> Option<String> {
    let func_ty = func.ty(locals).ok()?;
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };
    let instance_opt = Instance::resolve(fn_def, &fn_args).ok();
    let def_id =
        instance_opt.as_ref().map_or_else(|| fn_def.def_id(), |instance| instance.def.def_id());
    let internal_def_id = rustc_internal::internal(ctx.tcx, def_id);
    Some(ctx.tcx.def_path_str(internal_def_id))
}

fn current_inline_assume_guard(assume_guards: &[Expr]) -> Option<Expr> {
    assume_guards.iter().cloned().reduce(|a, b| a.and(b))
}

fn handle_inline_kani_assume_call(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    locals: &[LocalDecl],
    local_exprs: &mut HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    assume_guards: &mut Vec<Expr>,
    reason: &str,
) -> Option<Expr> {
    if let Some(cond_expr) = args
        .first()
        .and_then(|arg| inline_operand_to_expr(ctx, arg, local_exprs, resolver, locals))
        .and_then(inline_bool_condition)
    {
        let cond_expr = assume_refinement::normalize_inline_bool_guard(cond_expr);
        assume_refinement::apply_inline_assume_refinement(local_exprs, &cond_expr);
        assume_guards.push(cond_expr);
        debug!(reason, "inline kani assume -> path guard added");
    }
    Some(Expr::bitvec_const(0u64, POINTER_WIDTH))
}

fn handle_inline_kani_assert_call(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    locals: &[LocalDecl],
    local_exprs: &mut HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    assume_guards: &[Expr],
    assert_guards: &mut Vec<Expr>,
    deferred_checks: &mut Vec<DeferredInlineCheck>,
    reason: &str,
) -> Option<Expr> {
    if let Some(cond_expr) = args
        .first()
        .and_then(|arg| inline_operand_to_expr(ctx, arg, local_exprs, resolver, locals))
        .and_then(inline_bool_condition)
    {
        let guarded_cond = if let Some(path_guard) = current_inline_assume_guard(assume_guards) {
            path_guard.not().or(cond_expr)
        } else {
            cond_expr
        };
        // Assert-guard SIDE-CHANNEL: record the check with its property
        // description so the HOST call site emits a real per-property error
        // rule even when the return-value ITE below is later discarded (unit
        // destinations, sort coercions, constructor wrapping).
        //
        // Message extraction is restricted to `Operand::Constant`: `args` are
        // CALLEE-body operands, and the Copy/Move lanes of
        // `try_extract_const_str_bytes` trace HOST-body locals (wrong index
        // space here). Const `&str` messages are the overwhelmingly common
        // shape (`kani::assert(cond, "msg")`, contract-ensures expansion).
        let message = args.get(1).and_then(|arg| match arg {
            Operand::Constant(_) => {
                let (bytes, _) = ctx.try_extract_const_str_bytes(arg)?;
                String::from_utf8(bytes).ok()
            }
            _ => None,
        });
        deferred_checks.push(DeferredInlineCheck {
            check: guarded_cond.clone(),
            kind: PropertyKind::Assertion,
            message,
        });
        assert_guards.push(guarded_cond);
        debug!(reason, "inline kani assert/check -> fail-closed guard added");
    }
    Some(Expr::bitvec_const(0u64, POINTER_WIDTH))
}

/// Handle kani::any() and kani::assume() inside an inlined function body.
///
/// Returns `Some(result_expr)` if handled, None if not a kani intrinsic.
///
/// Part of #3737: enables inlining of rotate-helper and similar patterns.
pub(in crate::codegen_ay::chc) fn try_handle_kani_call_inline<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    args: &[Operand],
    outer_body: &Body,
    locals: &[LocalDecl],
    dest_local: usize,
    local_exprs: &mut HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    assume_guards: &mut Vec<Expr>,
    assert_guards: &mut Vec<Expr>,
    deferred_checks: &mut Vec<DeferredInlineCheck>,
    current_bb: usize,
) -> Option<Expr> {
    let func_ty = func.ty(locals).ok()?;
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };
    let instance = Instance::resolve(fn_def, &fn_args).ok();
    let fn_marker = instance
        .as_ref()
        .and_then(|inst| attributes::fn_marker(inst.def))
        .or_else(|| attributes::fn_marker(fn_def));

    if let Some(fn_marker) = fn_marker
        && let Some(kani_fn) = try_get_kani_function(&fn_marker)
    {
        match kani_fn {
            KaniFunction::Model(KaniModel::Any)
            | KaniFunction::Hook(KaniHook::AnyRaw)
            | KaniFunction::Intrinsic(KaniIntrinsic::AnyModifies) => {
                debug!(dest_local, ?kani_fn, "inline kani nondet call → fresh unconstrained var");
                return Some(fresh_inline_any_expr(ctx, locals, dest_local));
            }
            KaniFunction::Hook(KaniHook::Assume) => {
                return handle_inline_kani_assume_call(
                    ctx,
                    args,
                    locals,
                    local_exprs,
                    resolver,
                    assume_guards,
                    "kani::assume",
                );
            }
            KaniFunction::Hook(KaniHook::Assert | KaniHook::Check) => {
                return handle_inline_kani_assert_call(
                    ctx,
                    args,
                    locals,
                    local_exprs,
                    resolver,
                    assume_guards,
                    assert_guards,
                    deferred_checks,
                    "kani::assert/check",
                );
            }
            KaniFunction::Hook(KaniHook::Forall | KaniHook::Exists) => {
                let is_forall = matches!(kani_fn, KaniFunction::Hook(KaniHook::Forall));
                if let Some(quant_expr) = ctx.build_inline_quantifier_expr(
                    func,
                    args,
                    outer_body.locals(),
                    local_exprs,
                    resolver,
                    current_bb,
                    is_forall,
                ) {
                    debug!(
                        is_forall,
                        current_bb, "inline kani quantifier hook -> unrolled expression"
                    );
                    return Some(quant_expr);
                }
                debug!(is_forall, current_bb, "inline kani quantifier hook could not be encoded");
                return None;
            }
            KaniFunction::Hook(
                KaniHook::Cover
                | KaniHook::InitContracts
                | KaniHook::ValueView
                | KaniHook::UntrackedDeref,
            )
            | KaniFunction::Intrinsic(KaniIntrinsic::AutomaticHarness | KaniIntrinsic::WriteAny) => {
                debug!(?kani_fn, "inline kani noop hook -> passthrough zero-sized result");
                return Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
            }
            // Part of #3989: Intercept SizeOfVal/AlignOfVal inside inlined bodies
            // so the inline walker treats them as modeled leaves instead of re-inlining
            // the library model body (which introduces untranslatable SwitchInt/Option).
            KaniFunction::Model(KaniModel::SizeOfVal | KaniModel::AlignOfVal) => {
                let is_size = matches!(kani_fn, KaniFunction::Model(KaniModel::SizeOfVal));
                let arg_ty = args.first()?.ty(locals).ok()?;
                let pointee =
                    super::super::codegen_call_kani_model_dst::extract_pointee_from_ptr_arg(
                        arg_ty,
                    )?;
                let empty_modified = std::collections::HashSet::new();
                let value = super::super::codegen_call_kani_model_dst::compute_size_or_align_value(
                    ctx,
                    pointee,
                    args,
                    &empty_modified,
                    is_size,
                )?;
                debug!(
                    is_size,
                    "inline kani::size_of_val/align_of_val → compile-time constant (#3989)"
                );
                return Some(value);
            }
            // Part of #3989: Intercept CheckedSizeOf/CheckedAlignOf if they appear
            // as nested calls. For now, return None to fall through to body inlining —
            // the checked variants produce Option<usize> which requires flattened
            // destination handling not yet supported in the inline walker.
            KaniFunction::Intrinsic(
                KaniIntrinsic::CheckedSizeOf | KaniIntrinsic::CheckedAlignOf,
            ) => {
                debug!("inline kani checked_size_of/checked_align_of → fall through (#3989)");
                return None;
            }
            _ => {}
        }
    }

    let callee_path = resolve_inline_kani_callee_path(ctx, func, locals)?;
    let tail = callee_path.rsplit("::").next();
    if callee_path.contains("kani::")
        && matches!(
            tail,
            Some(
                "any"
                    | "any_modifies"
                    | "any_raw"
                    | "any_raw_internal"
                    | "any_raw_array"
                    | "kani_intrinsic"
            )
        )
    {
        debug!(dest_local, %callee_path, "inline unmarked kani any path → fresh var");
        return Some(fresh_inline_any_expr(ctx, locals, dest_local));
    }
    if callee_path.contains("kani::Arbitrary") && tail == Some("any") {
        debug!(dest_local, %callee_path, "inline unmarked Arbitrary::any path → fresh var");
        return Some(fresh_inline_any_expr(ctx, locals, dest_local));
    }
    if callee_path.contains("kani::") && matches!(tail, Some("assume")) {
        return handle_inline_kani_assume_call(
            ctx,
            args,
            locals,
            local_exprs,
            resolver,
            assume_guards,
            "unmarked kani::assume",
        );
    }
    if callee_path.contains("kani::") && matches!(tail, Some("assert" | "check")) {
        return handle_inline_kani_assert_call(
            ctx,
            args,
            locals,
            local_exprs,
            resolver,
            assume_guards,
            assert_guards,
            deferred_checks,
            "unmarked kani::assert/check",
        );
    }
    if callee_path.contains("kani::") && matches!(tail, Some("kani_forall" | "forall")) {
        return ctx.build_inline_quantifier_expr(
            func,
            args,
            outer_body.locals(),
            local_exprs,
            resolver,
            current_bb,
            true,
        );
    }
    if callee_path.contains("kani::") && matches!(tail, Some("kani_exists" | "exists")) {
        return ctx.build_inline_quantifier_expr(
            func,
            args,
            outer_body.locals(),
            local_exprs,
            resolver,
            current_bb,
            false,
        );
    }
    None
}

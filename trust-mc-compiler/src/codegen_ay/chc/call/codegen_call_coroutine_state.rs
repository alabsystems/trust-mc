// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CoroutineState constructor and coercion helpers shared by coroutine
//! fallback dispatch paths.

use ay_bindings::sort::SortInner;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;

use super::super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::ChcCtx;
use crate::codegen_ay::types::{
    SignExtension, bool_sort, coerce_bitvec_width_safe, flatten_datatype_to_bitvec,
    unwrap_single_field_datatype_to_sort,
};

#[derive(Clone, Copy)]
pub(super) enum CoroutineStateBranch {
    Yielded,
    Complete,
}

/// Try to construct a sound `CoroutineState` expression from the destination
/// Datatype sort.
///
/// For the `CoroutineState<Y, R>` enum, prefer an `ite(choice, Yielded(..),
/// Complete(..))` expression so the solver can explore both outcomes. If only
/// one constructor is present, fall back to that variant alone.
pub(super) fn try_construct_coroutine_state_expr(
    dest_sort: &ay_bindings::Sort,
    yield_is_zst: bool,
    complete_is_zst: bool,
    allow_complete_branch: bool,
) -> Option<Expr> {
    let SortInner::Datatype(dt) = dest_sort.inner() else {
        return None;
    };

    let yielded_ctor = dt.constructors.iter().find(|ctor| {
        let name_lower = ctor.name.to_lowercase();
        name_lower.contains("yielded") || name_lower.contains("yield")
    });
    let complete_ctor = dt.constructors.iter().find(|ctor| {
        let name_lower = ctor.name.to_lowercase();
        name_lower.contains("complete")
    });

    let build_ctor = |ctor: &ay_bindings::sort::DatatypeConstructor,
                      payload_is_zst: bool,
                      fresh_prefix: &str| {
        let field_exprs: Vec<Expr> = ctor
            .fields
            .iter()
            .map(|field| {
                if payload_is_zst && field.sort.is_bool() {
                    Expr::bool_const(true)
                } else {
                    declare_pending_var(chc_fresh_name(fresh_prefix), field.sort.clone())
                }
            })
            .collect();
        Expr::datatype_constructor(&*dt.name, &*ctor.name, field_exprs, dest_sort.clone())
    };

    if !allow_complete_branch {
        return yielded_ctor
            .map(|yielded_ctor| build_ctor(yielded_ctor, yield_is_zst, "__coroutine_yield"))
            .or_else(|| {
                complete_ctor.map(|complete_ctor| {
                    build_ctor(complete_ctor, complete_is_zst, "__coroutine_complete")
                })
            });
    }

    match (yielded_ctor, complete_ctor) {
        (Some(yielded_ctor), Some(complete_ctor)) => {
            let yielded_expr = build_ctor(yielded_ctor, yield_is_zst, "__coroutine_yield");
            let complete_expr = build_ctor(complete_ctor, complete_is_zst, "__coroutine_complete");
            let choice = declare_pending_var(chc_fresh_name("__coro_outcome"), bool_sort());
            Some(Expr::ite(choice, yielded_expr, complete_expr))
        }
        (Some(yielded_ctor), None) => {
            Some(build_ctor(yielded_ctor, yield_is_zst, "__coroutine_yield"))
        }
        (None, Some(complete_ctor)) => {
            Some(build_ctor(complete_ctor, complete_is_zst, "__coroutine_complete"))
        }
        (None, None) => None,
    }
}

pub(super) fn try_construct_coroutine_state_variant_expr(
    dest_sort: &ay_bindings::Sort,
    branch: CoroutineStateBranch,
    yield_is_zst: bool,
    complete_is_zst: bool,
) -> Option<Expr> {
    let SortInner::Datatype(dt) = dest_sort.inner() else {
        return None;
    };

    let ctor = match branch {
        CoroutineStateBranch::Yielded => dt.constructors.iter().find(|ctor| {
            let name_lower = ctor.name.to_lowercase();
            name_lower.contains("yielded") || name_lower.contains("yield")
        })?,
        CoroutineStateBranch::Complete => dt.constructors.iter().find(|ctor| {
            let name_lower = ctor.name.to_lowercase();
            name_lower.contains("complete")
        })?,
    };
    let (payload_is_zst, fresh_prefix) = match branch {
        CoroutineStateBranch::Yielded => (yield_is_zst, "__coroutine_yield"),
        CoroutineStateBranch::Complete => (complete_is_zst, "__coroutine_complete"),
    };
    let field_exprs: Vec<Expr> = ctor
        .fields
        .iter()
        .map(|field| {
            if payload_is_zst && field.sort.is_bool() {
                Expr::bool_const(true)
            } else {
                declare_pending_var(chc_fresh_name(fresh_prefix), field.sort.clone())
            }
        })
        .collect();
    Some(Expr::datatype_constructor(&*dt.name, &*ctor.name, field_exprs, dest_sort.clone()))
}

pub(super) fn coroutine_state_yield_is_zst(
    func: &rustc_public::mir::Operand,
    ctx: &ChcCtx<'_, '_>,
) -> Option<bool> {
    let Ok(func_ty) = func.ty(ctx.body.locals()) else {
        return None;
    };
    let sig = func_ty.kind().fn_sig()?;
    coroutine_state_payload_is_zst_for_ty(sig.skip_binder().output(), 0)
}

pub(super) fn coroutine_state_yield_is_zst_for_local(
    local_idx: usize,
    ctx: &ChcCtx<'_, '_>,
) -> Option<bool> {
    let local_decl = ctx.body.locals().get(local_idx)?;
    coroutine_state_payload_is_zst_for_ty(local_decl.ty, 0)
}

pub(super) fn coroutine_state_complete_is_zst(
    func: &rustc_public::mir::Operand,
    ctx: &ChcCtx<'_, '_>,
) -> Option<bool> {
    let Ok(func_ty) = func.ty(ctx.body.locals()) else {
        return None;
    };
    let sig = func_ty.kind().fn_sig()?;
    coroutine_state_payload_is_zst_for_ty(sig.skip_binder().output(), 1)
}

pub(super) fn coroutine_state_complete_is_zst_for_local(
    local_idx: usize,
    ctx: &ChcCtx<'_, '_>,
) -> Option<bool> {
    let local_decl = ctx.body.locals().get(local_idx)?;
    coroutine_state_payload_is_zst_for_ty(local_decl.ty, 1)
}

fn coroutine_state_payload_is_zst_for_ty(
    ty: rustc_public::ty::Ty,
    payload_idx: usize,
) -> Option<bool> {
    let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) = ty.kind()
    else {
        return None;
    };
    let name = def.trimmed_name();
    if name != "CoroutineState" && name != "GeneratorState" {
        return None;
    }
    let rustc_public::ty::GenericArgKind::Type(payload_ty) = args.0.get(payload_idx)? else {
        return None;
    };
    Some(super::super::codegen_call_kani_model_dst::is_zst_ty(*payload_ty))
}

pub(super) fn coerce_coroutine_result_to_sort(
    result_expr: Expr,
    target_sort: &Sort,
) -> Option<Expr> {
    if result_expr.sort() == target_sort {
        return Some(result_expr);
    }

    if let Some(unwrapped) = unwrap_single_field_datatype_to_sort(&result_expr, target_sort) {
        return Some(unwrapped);
    }

    if result_expr.sort().is_datatype()
        && target_sort.is_bitvec()
        && let Some(target_width) = target_sort.bitvec_width()
        && let Some(flattened) = flatten_datatype_to_bitvec(&result_expr, target_width)
    {
        return Some(flattened);
    }

    if result_expr.sort().is_bool()
        && target_sort.is_bitvec()
        && let Some(bits) = target_sort.bitvec_width()
    {
        return Some(Expr::ite(
            result_expr,
            Expr::bitvec_const(1u64, bits),
            Expr::bitvec_const(0u64, bits),
        ));
    }

    if result_expr.sort().is_bitvec() && target_sort.is_bool() {
        let width = result_expr.sort().bitvec_width()?;
        return Some(result_expr.ne(Expr::bitvec_const(0u64, width)));
    }

    if result_expr.sort().is_bitvec()
        && target_sort.is_bitvec()
        && let Some(target_width) = target_sort.bitvec_width()
    {
        return Some(coerce_bitvec_width_safe(
            result_expr,
            target_width,
            SignExtension::ZeroExtend,
        ));
    }

    None
}

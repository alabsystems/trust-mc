// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_bindings::{Expr, Sort};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::InlineReturn;
use crate::codegen_ay::chc::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;

pub(super) fn inline_formatting_call_placeholder<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    if !ChcCtx::is_formatting_path(callee_path) {
        return None;
    }

    let dest_ty = ctx
        .resolve_inline_local_ty(outer_body, destination.local)
        .or_else(|| destination.ty(outer_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty)))?;
    let value = match dest_ty.kind() {
        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Tuple(tys))
            if tys.is_empty() =>
        {
            Expr::bitvec_const(0u64, POINTER_WIDTH)
        }
        _ => {
            let dest_sort =
                ChcCtx::translate_ty(dest_ty).unwrap_or_else(|| Sort::bitvec(POINTER_WIDTH));
            ctx.record_aggregate_gap("inline_fmt_nested_call_symbolic");
            super::super::declare_pending_var(
                super::super::chc_fresh_name("__fmt_inline"),
                dest_sort,
            )
        }
    };
    Some(InlineReturn::value_only(value))
}

pub(super) fn try_inline_option_unwrap_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<Expr> {
    let receiver = translated_args.first()?.clone();
    match ctx.stub_registry.lookup(callee_path)? {
        StubKind::OptionUnwrap | StubKind::OptionExpect | StubKind::OptionUnwrapUnchecked => {
            if receiver.sort().is_bitvec() || receiver.sort().is_bool() || receiver.sort().is_int()
            {
                return Some(receiver);
            }
            let is_some = ctx.option_is_some(receiver.clone());
            let inner = ctx.option_unwrap_value_on_some_path(receiver)?;
            let fallback = super::super::declare_pending_var(
                super::super::chc_fresh_name("__assert_fail_inline_option_unwrap"),
                inner.sort().clone(),
            );
            Some(Expr::ite(is_some, inner, fallback))
        }
        _ => None,
    }
}

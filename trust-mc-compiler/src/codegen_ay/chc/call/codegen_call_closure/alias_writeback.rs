// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Closure-specific alias-update target resolution.
//!
//! Closure calls use a different ABI than normal fn-inline consumers:
//! `args[0]` is the closure env reference and `args[1]` is the tuple of
//! user-visible call arguments. This module pre-resolves those alias-update
//! targets before inline translation so the shared epilogue can write back the
//! returned `alias_updates` soundly.

use std::collections::BTreeMap;

use rustc_public::mir::Operand;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_virtual_inline::receiver_base_local;
use super::super::ptr_receiver_mem::resolve_ptr_target_local;
use super::ChcCtx;

pub(in crate::codegen_ay::chc) fn pre_resolve_closure_alias_target_locals(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    closure_ref: Option<&Operand>,
) -> BTreeMap<usize, usize> {
    let mut resolved = BTreeMap::new();

    if let Some(env_local) =
        closure_ref.and_then(|closure_ref| ctx.resolve_closure_env_local(closure_ref))
    {
        resolved.insert(1, env_local);
    }

    let Some(arg_tuple) = dcx.args.get(1) else {
        return resolved;
    };

    for (field_idx, operand) in
        ctx.extract_closure_call_arg_operands(arg_tuple).into_iter().enumerate()
    {
        let callee_arg_local = field_idx + 2;
        if let Some(caller_local) =
            resolve_ptr_target_local(ctx, &operand).or_else(|| receiver_base_local(&operand))
        {
            resolved.insert(callee_arg_local, caller_local);
        }
    }

    resolved
}

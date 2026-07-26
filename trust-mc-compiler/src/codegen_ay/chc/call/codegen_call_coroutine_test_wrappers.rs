// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test-only wrappers for coroutine state construction and coercion helpers.
//!
//! Separated from codegen_call_coroutine.rs to keep the main file under 500 lines.
//! Part of #4127.

use ay_bindings::Expr;

use super::state::{
    CoroutineStateBranch, coerce_coroutine_result_to_sort, try_construct_coroutine_state_expr,
    try_construct_coroutine_state_variant_expr,
};

/// Test-only: construct a `CoroutineState` expression from a Datatype sort.
pub(in crate::codegen_ay::chc) fn test_try_construct_coroutine_state_expr(
    dest_sort: &ay_bindings::Sort,
    yield_is_zst: bool,
    complete_is_zst: bool,
    allow_complete_branch: bool,
) -> Option<Expr> {
    try_construct_coroutine_state_expr(
        dest_sort,
        yield_is_zst,
        complete_is_zst,
        allow_complete_branch,
    )
}

/// Test-only: construct a specific Yielded variant expression.
pub(in crate::codegen_ay::chc) fn test_try_construct_coroutine_state_yielded_expr(
    dest_sort: &ay_bindings::Sort,
    yield_is_zst: bool,
    complete_is_zst: bool,
) -> Option<Expr> {
    try_construct_coroutine_state_variant_expr(
        dest_sort,
        CoroutineStateBranch::Yielded,
        yield_is_zst,
        complete_is_zst,
    )
}

/// Test-only: construct a specific Complete variant expression.
pub(in crate::codegen_ay::chc) fn test_try_construct_coroutine_state_complete_expr(
    dest_sort: &ay_bindings::Sort,
    yield_is_zst: bool,
    complete_is_zst: bool,
) -> Option<Expr> {
    try_construct_coroutine_state_variant_expr(
        dest_sort,
        CoroutineStateBranch::Complete,
        yield_is_zst,
        complete_is_zst,
    )
}

/// Test-only: coerce a coroutine result expression to a target sort.
pub(in crate::codegen_ay::chc) fn test_coerce_coroutine_result_to_sort(
    result_expr: Expr,
    target_sort: &ay_bindings::Sort,
) -> Option<Expr> {
    coerce_coroutine_result_to_sort(result_expr, target_sort)
}

// ChcCtx test wrappers — delegates to support:: free functions for test access.
use super::ChcCtx;
use super::support::{
    has_coroutine_arg, has_simple_coroutine_yield_variant, returns_coroutine_state,
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn test_has_coroutine_arg(
        args: &[rustc_public::mir::Operand],
        ctx: &ChcCtx<'_, '_>,
    ) -> bool {
        has_coroutine_arg(args, ctx)
    }

    pub(in crate::codegen_ay::chc) fn test_returns_coroutine_state(
        func: &rustc_public::mir::Operand,
        ctx: &ChcCtx<'_, '_>,
    ) -> bool {
        returns_coroutine_state(func, ctx)
    }

    pub(in crate::codegen_ay::chc) fn test_has_simple_coroutine_yield_variant(
        func: &rustc_public::mir::Operand,
        ctx: &ChcCtx<'_, '_>,
    ) -> bool {
        has_simple_coroutine_yield_variant(func, ctx)
    }
}

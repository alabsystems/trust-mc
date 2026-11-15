// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native iterator queries over the model's logical carrier. Walking the
//! library implementation's raw ptr/end fields cannot recover that carrier.

use std::collections::HashMap;

use ay_bindings::Expr;
use rustc_public::mir::{Body, Operand};

use super::super::ChcCtx;
use super::super::inline_shared::PlaceResolver;
use super::InlineReturn;
use super::pointer_wrapper::resolve_nested_ref_arg_referent;

pub(super) fn try_inline_native_iterator_query(
    ctx: &mut ChcCtx<'_, '_>,
    func: &Operand,
    args: &[Operand],
    translated_args: &[Expr],
    body: &Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<InlineReturn> {
    let [receiver] = args else { return None };
    let instance = ctx.native_iterator_query_instance(func, body.locals())?;
    let value = resolve_nested_ref_arg_referent(ctx, receiver, body, local_exprs, resolver)
        .and_then(|value| ctx.native_iterator_query_expr(&instance, &value))
        .or_else(|| {
            translated_args
                .first()
                .and_then(|value| ctx.native_iterator_query_expr(&instance, value))
        })?;
    ctx.declare_datatype_sort_if_needed(value.sort());
    // Authenticated native queries are pure over these admitted carriers.
    // An unsupported/custom inner never produces a guessed result or alias.
    Some(InlineReturn::value_only(value))
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;

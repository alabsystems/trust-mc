// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise nested-call fast path for `Vec::pop()`.

use std::collections::{BTreeMap, HashMap};

use crate::codegen_ay::names;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;

use super::super::ChcCtx;
use super::super::codegen_call_vec::ChcVecFields;
use super::super::inline_shared::PlaceResolver;
use super::InlineReturn;
use super::pointer_wrapper::resolve_nested_ref_arg_referent;

/// Part of #4050: internal `Vec::pop()` calls inside inline bodies need both
/// the `Option<T>` result and the mutated receiver state. The generic nested
/// inline path can recover the return value, but it does not reliably bridge
/// the decremented `Vec` back through struct-field receivers, which leaves the
/// caller walking stale lengths and reintroduces SwitchInt over-approximation.
pub(super) fn try_inline_vec_pop_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<InlineReturn> {
    if !matches!(ctx.stub_registry.lookup(callee_path)?, StubKind::VecPop) {
        return None;
    }
    if translated_args.len() != 1 {
        return None;
    }

    let receiver = args
        .first()
        .and_then(|arg| {
            resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver)
        })
        .or_else(|| translated_args.first().cloned())?;
    let ChcVecFields { vec_sort, ptr, len, cap, data } = ChcVecFields::extract(receiver)?;

    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let is_nonempty = len.clone().ne(zero.clone());
    let new_len = Expr::ite(is_nonempty.clone(), len.bvsub(one), zero);
    let elem_sort = data
        .sort()
        .array_sort()
        .map_or_else(crate::codegen_ay::types::ptr_sort, |arr| arr.element_sort.clone());
    let option_result =
        ctx.build_vec_pop_option_result(data.clone(), elem_sort, is_nonempty, new_len.clone())?;

    let dt_name = vec_sort.datatype_name()?.to_owned();
    let updated_receiver = Expr::datatype_constructor(
        &dt_name,
        names::cons_name(&dt_name),
        vec![ptr, new_len, cap, data],
        vec_sort,
    );
    let alias_updates = BTreeMap::from([(1usize, updated_receiver)]);
    Some(InlineReturn {
        value: option_result,
        vtable: None,
        alloc_id: None,
        alias_updates,
        deferred_checks: Vec::new(),
    })
}

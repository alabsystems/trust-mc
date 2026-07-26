// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise nested-call fast path for `Vec::push()`.
//!
//! Part of #4050: mirrors `nested_vec_pop.rs` — Vec::push inside inline bodies
//! needs both the `()` result and the mutated receiver state. The generic
//! nested inline path cannot reliably bridge the incremented Vec back through
//! struct-field receivers, leaving the caller walking stale lengths.

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

/// Part of #4050: internal `Vec::push(value)` calls inside inline bodies need
/// the mutated receiver state bridged back. Semantics: `data[old_len] = value`,
/// `len += 1`. Returns `()` (Bool true in CHC encoding).
pub(super) fn try_inline_vec_push_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<InlineReturn> {
    if !matches!(ctx.stub_registry.lookup(callee_path)?, StubKind::VecPush) {
        return None;
    }
    // Vec::push takes (&mut self, value) → 2 args.
    if translated_args.len() != 2 {
        return None;
    }

    let receiver = args
        .first()
        .and_then(|arg| {
            resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver)
        })
        .or_else(|| translated_args.first().cloned())?;
    let ChcVecFields { vec_sort, ptr, len, cap, data } = ChcVecFields::extract(receiver)?;

    let value = &translated_args[1];
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let new_len = len.clone().bvadd(one);
    // Store value at data[old_len].
    let value = ChcCtx::coerce_store_value(data.sort(), value.clone(), false, &ctx.diagnostics);
    let new_data = data.store(len, value);

    let dt_name = vec_sort.datatype_name()?.to_owned();
    let updated_receiver = Expr::datatype_constructor(
        &dt_name,
        names::cons_name(&dt_name),
        vec![ptr, new_len, cap, new_data],
        vec_sort,
    );
    let alias_updates = BTreeMap::from([(1usize, updated_receiver)]);
    // Vec::push returns () which is Bool(true) in CHC encoding.
    Some(InlineReturn {
        value: Expr::bool_const(true),
        vtable: None,
        alloc_id: None,
        alias_updates,
        deferred_checks: Vec::new(),
    })
}

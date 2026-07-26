// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise nested-call fast path for slice/Vec iterator `next()`.
//!
//! When `fn_inline` walks a function body that calls `<Iter as Iterator>::next()`,
//! the generic `translate_inline_body_with_metadata` fallback recursively inlines
//! `next()`'s complex MIR body. This produces a partial result (element value
//! without the `is_some` discriminant), causing downstream `SwitchInt` on the
//! `Option` discriminant to read an unconstrained Bool. Constant propagation
//! then eliminates the loop body rules, producing a spurious CTREX.
//!
//! This handler intercepts `IntoIterNext` in the inline walker and produces a
//! correct `Option<T>` DT result with both discriminant and element value.

use std::collections::{BTreeMap, HashMap};

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_shared::PlaceResolver;
use super::super::stubs_option_helpers::OptionHelpers;
use super::InlineReturn;
use super::pointer_wrapper::resolve_nested_ref_arg_referent;

#[derive(Clone)]
struct WrapperFrame {
    outer: Expr,
    field_name: String,
}

struct IterCarrier {
    iter: Expr,
    wrappers: Vec<WrapperFrame>,
}

/// Part of #1739: Intercepts `IntoIterNext` (slice/Vec iterator next()) inside
/// inline walker bodies and produces a correct `Option<T>` DT result with both
/// discriminant and payload. Also produces an alias update for the iterator
/// receiver with incremented position.
pub(super) fn try_inline_iter_next_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<InlineReturn> {
    if is_next_code_point_call(callee_path) {
        return try_inline_next_code_point_call(
            ctx,
            args,
            translated_args,
            outer_body,
            local_exprs,
            resolver,
        );
    }

    // Only match IntoIterNext (covers slice::Iter::next, Vec IntoIter::next).
    if !matches!(ctx.stub_registry.lookup(callee_path)?, StubKind::IntoIterNext) {
        return None;
    }
    if translated_args.is_empty() {
        return None;
    }

    // Resolve the iterator: either through &mut ref resolution or from
    // the translated arg directly.
    let iter = args
        .first()
        .and_then(|arg| {
            resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver)
        })
        .or_else(|| translated_args.first().cloned())?;

    // Guard: must be a datatype (iterator struct).
    if !iter.sort().is_datatype() {
        debug!(
            sort = %iter.sort(),
            "nested iter_next: non-datatype iterator sort, bailing"
        );
        return None;
    }

    let carrier = resolve_iter_next_carrier(iter)?;
    let iter = carrier.iter;
    let dt_name = iter.sort().datatype_name()?.to_owned();

    // Extract fld_pos from the iterator.
    let pos = iter.clone().field_select(&dt_name, "fld_pos", Sort::bitvec(POINTER_WIDTH));

    // Extract the nested vec/slice from the iterator (fld_vec field).
    let vec_sort = ChcCtx::get_dt_field_sort(&iter, "fld_vec")?;
    let vec = iter.clone().field_select(&dt_name, "fld_vec", vec_sort.clone());

    // Extract len and data from the vec/slice. The vec/slice DT has fld_len and
    // fld_data (or for Vec: nested fld_len on the inner struct).
    let vec_dt_name = vec.sort().datatype_name()?.to_owned();
    let len = vec.clone().field_select(&vec_dt_name, "fld_len", Sort::bitvec(POINTER_WIDTH));
    let data_sort = ChcCtx::get_dt_field_sort(&vec, "fld_data")?;
    let data = vec.clone().field_select(&vec_dt_name, "fld_data", data_sort);

    // Derive element sort from data array.
    let elem_sort = data.sort().array_sort().map(|arr| arr.element_sort.clone())?;

    // Compute bounds check and element.
    let in_bounds = pos.clone().bvult(len);
    let element = data.select(pos.clone());
    let is_chars_next = is_str_chars_next_call(callee_path)
        || carrier.wrappers.iter().any(|frame| {
            frame.outer.sort().datatype_name().is_some_and(|name| name.contains("Chars"))
        });
    let payload = if is_chars_next && element.sort().is_bitvec() {
        match element.sort().bitvec_width()? {
            width if width < 32 => element.zero_extend(32 - width),
            32 => element,
            _ => return None,
        }
    } else {
        element
    };
    let payload_sort = payload.sort().clone();

    debug!(
        %callee_path,
        %dt_name,
        elem_sort = %elem_sort,
        payload_sort = %payload_sort,
        "nested iter_next: producing Option<T> result with is_some discriminant"
    );

    // Build Option<T> result: ite(in_bounds, Some(element), None).
    let opt_sort = super::super::stubs_option_helpers::make_option_sort(&payload_sort);
    let some_expr = ctx.make_some_expr_for_option(payload, &opt_sort)?;
    let none_expr = ctx.make_none_expr(&payload_sort);
    let option_result = Expr::ite(in_bounds.clone(), some_expr, none_expr);

    // Increment position: new_pos = ite(in_bounds, pos + 1, pos).
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let new_pos = Expr::ite(in_bounds, pos.clone().bvadd(one), pos);

    let updated_iter =
        reconstruct_datatype_replacing_fields(&iter, &[("fld_vec", vec), ("fld_pos", new_pos)])?;
    let updated_iter = rebuild_wrappers(updated_iter, &carrier.wrappers)?;

    // Arg 1 is &mut self (the iterator). Return the updated iterator as alias.
    let alias_updates = BTreeMap::from([(1usize, updated_iter)]);
    Some(InlineReturn {
        value: option_result,
        vtable: None,
        alloc_id: None,
        alias_updates,
        deferred_checks: Vec::new(),
    })
}

fn try_inline_next_code_point_call(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<InlineReturn> {
    debug!(
        args_len = args.len(),
        translated_args_len = translated_args.len(),
        "nested next_code_point: attempting precise inline"
    );
    let iter = args
        .first()
        .and_then(|arg| {
            resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver)
        })
        .or_else(|| translated_args.first().cloned());
    let Some(iter) = iter else {
        debug!("nested next_code_point: receiver resolution failed");
        return None;
    };
    if !iter.sort().is_datatype() {
        debug!(
            sort = %iter.sort(),
            "nested next_code_point: receiver is not a datatype"
        );
        return None;
    }

    let Some(carrier) = resolve_iter_next_carrier(iter.clone()) else {
        debug!(
            sort = %iter.sort(),
            "nested next_code_point: receiver lacks iterator carrier fields"
        );
        return None;
    };
    let iter = carrier.iter;
    let Some(dt_name) = iter.sort().datatype_name().map(str::to_owned) else {
        debug!(sort = %iter.sort(), "nested next_code_point: iterator sort has no datatype name");
        return None;
    };
    let pos = iter.clone().field_select(&dt_name, "fld_pos", Sort::bitvec(POINTER_WIDTH));
    let Some(vec_sort) = ChcCtx::get_dt_field_sort(&iter, "fld_vec") else {
        debug!(sort = %iter.sort(), "nested next_code_point: iterator has no fld_vec");
        return None;
    };
    let vec = iter.clone().field_select(&dt_name, "fld_vec", vec_sort.clone());
    let Some(vec_dt_name) = vec.sort().datatype_name().map(str::to_owned) else {
        debug!(sort = %vec.sort(), "nested next_code_point: fld_vec sort has no datatype name");
        return None;
    };
    let len = vec.clone().field_select(&vec_dt_name, "fld_len", Sort::bitvec(POINTER_WIDTH));
    let Some(data_sort) = ChcCtx::get_dt_field_sort(&vec, "fld_data") else {
        debug!(sort = %vec.sort(), "nested next_code_point: fld_vec has no fld_data");
        return None;
    };
    let data = vec.clone().field_select(&vec_dt_name, "fld_data", data_sort);
    let Some(elem_sort) = data.sort().array_sort().map(|arr| arr.element_sort.clone()) else {
        debug!(sort = %data.sort(), "nested next_code_point: fld_data is not an array");
        return None;
    };
    let Some(elem_width) = elem_sort.bitvec_width() else {
        debug!(sort = %elem_sort, "nested next_code_point: array element is not a bitvector");
        return None;
    };
    if elem_width > 32 {
        debug!(elem_width, "nested next_code_point: array element width is too wide");
        return None;
    }

    let in_bounds = pos.clone().bvult(len);
    let byte = data.select(pos.clone());
    let ascii = byte.clone().bvult(Expr::bitvec_const(0x80u64, elem_width));
    let payload = if elem_width < 32 { byte.zero_extend(32 - elem_width) } else { byte };
    let payload_sort = Sort::bitvec(32);
    let opt_sort = super::super::stubs_option_helpers::make_option_sort(&payload_sort);
    let Some(some_ascii) = ctx.make_some_expr_for_option(payload, &opt_sort) else {
        debug!("nested next_code_point: failed to build Some(payload)");
        return None;
    };
    let none_expr = ctx.make_none_expr(&payload_sort);
    let fallback_result = super::super::declare_pending_var(
        super::super::chc_fresh_name("__next_code_point_nonascii"),
        opt_sort.clone(),
    );
    let option_result = Expr::ite(
        in_bounds.clone(),
        Expr::ite(ascii.clone(), some_ascii, fallback_result),
        none_expr,
    );

    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let new_pos = pos.clone().bvadd(one);
    let Some(updated_ascii) =
        reconstruct_datatype_replacing_fields(&iter, &[("fld_vec", vec), ("fld_pos", new_pos)])
    else {
        debug!("nested next_code_point: failed to rebuild ASCII iterator");
        return None;
    };
    let fallback_iter = super::super::declare_pending_var(
        super::super::chc_fresh_name("__next_code_point_iter_nonascii"),
        updated_ascii.sort().clone(),
    );
    let updated_iter =
        Expr::ite(in_bounds, Expr::ite(ascii, updated_ascii, fallback_iter), iter.clone());
    let Some(updated_iter) = rebuild_wrappers(updated_iter, &carrier.wrappers) else {
        debug!("nested next_code_point: failed to rebuild iterator wrappers");
        return None;
    };
    let alias_updates = BTreeMap::from([(1usize, updated_iter)]);

    debug!("nested next_code_point: exact ASCII path with non-ASCII overapprox");
    Some(InlineReturn {
        value: option_result,
        vtable: None,
        alloc_id: None,
        alias_updates,
        deferred_checks: Vec::new(),
    })
}

fn has_iter_next_core_fields(expr: &Expr) -> bool {
    ChcCtx::get_dt_field_sort(expr, "fld_pos").is_some()
        && ChcCtx::get_dt_field_sort(expr, "fld_vec").is_some()
}

fn is_str_chars_next_call(callee_path: &str) -> bool {
    callee_path.contains("str::iter::Chars")
        || callee_path.contains("str::Chars")
        || (callee_path.contains("Iterator for")
            && callee_path.contains("Chars")
            && callee_path.contains("str"))
}

fn is_next_code_point_call(callee_path: &str) -> bool {
    callee_path.ends_with("str::validations::next_code_point")
        || callee_path.ends_with("core::str::validations::next_code_point")
}

fn resolve_iter_next_carrier(iter: Expr) -> Option<IterCarrier> {
    resolve_iter_next_carrier_rec(iter, 0)
}

fn resolve_iter_next_carrier_rec(iter: Expr, depth: usize) -> Option<IterCarrier> {
    if has_iter_next_core_fields(&iter) {
        return Some(IterCarrier { iter, wrappers: Vec::new() });
    }
    if depth >= 4 {
        return None;
    }
    let sort = iter.sort().clone();
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let ctor = dt.constructors.first()?;
    for field in &ctor.fields {
        if !field.sort.is_datatype() {
            continue;
        }
        let child = iter.clone().field_select(&dt.name, &field.name, field.sort.clone());
        if let Some(mut carrier) = resolve_iter_next_carrier_rec(child, depth + 1) {
            carrier.wrappers.insert(
                0,
                WrapperFrame { outer: iter.clone(), field_name: field.name.to_string() },
            );
            return Some(carrier);
        }
    }
    None
}

fn rebuild_wrappers(mut inner: Expr, wrappers: &[WrapperFrame]) -> Option<Expr> {
    for frame in wrappers.iter().rev() {
        inner = reconstruct_datatype_replacing_fields(&frame.outer, &[(&frame.field_name, inner)])?;
    }
    Some(inner)
}

fn reconstruct_datatype_replacing_fields(
    base: &Expr,
    replacements: &[(&str, Expr)],
) -> Option<Expr> {
    let sort = base.sort().clone();
    let dt = sort.datatype_sort()?;
    let ctor = dt.constructors.first()?;
    let mut fields = Vec::with_capacity(ctor.fields.len());
    for field in &ctor.fields {
        if let Some((_, replacement)) =
            replacements.iter().find(|(name, _)| *name == field.name.as_str())
        {
            fields.push(replacement.clone());
        } else {
            fields.push(base.clone().field_select(&dt.name, &field.name, field.sort.clone()));
        }
    }
    Some(Expr::datatype_constructor(&dt.name, &ctor.name, fields, sort.clone()))
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Thin inline adapter for `kani_str_bytes_nth` / `kani_str_chars_nth`.
//!
//! Part of #4161: reuses the shared `try_build_str_nth_result_expr` helper
//! from `codegen_call_string_nth` instead of duplicating `heap_select +
//! Option<T>` semantics in the inline walker.

use std::collections::HashMap;

use ay_bindings::Expr;
use rustc_public::mir::Operand;

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::InlineReturn;
use super::pointer_wrapper::{
    resolve_inline_ref_local_target_place, resolve_nested_ref_arg_referent,
};
use super::terminator_exec::resolve_inline_callee_path;

fn is_str_passthrough_callee(callee: &str) -> bool {
    callee.contains("Deref>::deref")
        || callee.contains("ToString>::to_string")
        || callee.contains("ToString::to_string")
        || (callee.contains("String") && callee.contains("::from"))
}

fn resolve_inline_str_source_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    arg: &Operand,
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<Expr> {
    if let Some(source) =
        resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver)
    {
        return Some(source);
    }

    let mut current = match arg {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    };
    for _ in 0..8 {
        let local = current?;
        let mut next = None;
        for block in &outer_body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, destination, .. } =
                &block.terminator.kind
                && destination.local == local
                && !args.is_empty()
                && resolve_inline_callee_path(ctx, func, outer_body.locals())
                    .as_deref()
                    .is_some_and(is_str_passthrough_callee)
            {
                if let Some(source) = resolve_nested_ref_arg_referent(
                    ctx,
                    &args[0],
                    outer_body,
                    local_exprs,
                    resolver,
                ) {
                    return Some(source);
                }
                next = match &args[0] {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        Some(place.local)
                    }
                    _ => None,
                };
                break;
            }
        }
        current = next;
    }

    inline_operand_to_expr(ctx, arg, local_exprs, resolver, outer_body.locals())
}

/// Part of #4161: inline fast path for `kani_str_bytes_nth` /
/// `kani_str_chars_nth` calls encountered inside inline body translation.
pub(super) fn try_inline_str_nth_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    let stub = ctx.stub_registry.lookup(callee_path)?;
    let is_chars = match stub {
        StubKind::StrCharsNth => true,
        StubKind::StrBytesNth => false,
        _ => return None,
    };

    // str_nth takes (source, index) → 2 args.
    if translated_args.len() != 2 {
        return None;
    }

    // Recover the string source: try referent resolution first, fall back to
    // the translated arg directly.
    let source = args
        .first()
        .and_then(|arg| resolve_inline_str_source_expr(ctx, arg, outer_body, local_exprs, resolver))
        .or_else(|| translated_args.first().cloned())?;

    let index_expr = translated_args[1].clone();
    let zero_offset = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let (len_hint, metadata_offset) = args
        .first()
        .and_then(super::receiver_base_local)
        .map(|local| {
            let target_local = resolve_inline_ref_local_target_place(outer_body, local, 8)
                .map(|place| place.local);
            let target_metadata = target_local.and_then(|target_local| {
                let metadata = ctx.string_backing_metadata_for_local(target_local);
                (metadata.0.is_some() || metadata.1.is_some()).then_some(metadata)
            });
            target_metadata.unwrap_or_else(|| ctx.string_backing_metadata_for_local(local))
        })
        .unwrap_or((None, None));
    let offset = metadata_offset.unwrap_or(zero_offset);

    // Build StringBacking from the resolved source expression, reusing the
    // caller's side-table metadata when the referent itself is the raw data
    // array and the length/offset stayed attached to the fat-pointer local.
    let backing = ChcCtx::string_backing_from_expr(source, len_hint, offset)?;

    // Resolve dest sort from the destination place type.
    let dest_ty = destination.ty(outer_body.locals()).ok()?;
    let dest_sort = ChcCtx::translate_ty(ctx.resolve_body_ty(dest_ty))?;

    let result = ctx.try_build_str_nth_result_expr(&backing, index_expr, &dest_sort, is_chars)?;
    Some(InlineReturn::value_only(result))
}

/// Part of #4161: const-fold fallback for `kani_str_*_nth` calls in inline
/// context. When the symbolic backing resolution path fails (e.g., because
/// `String::from("literal").chars().nth(i)` traces through passthrough
/// callees that the inline walker cannot resolve to an Array expression),
/// fall back to the MIR-level const-fold path which traces through
/// assignments and passthrough calls in the inlined body to extract
/// concrete string bytes.
pub(super) fn try_inline_str_nth_const_fold<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    destination: &rustc_public::mir::Place,
    outer_body: &rustc_public::mir::Body,
) -> Option<InlineReturn> {
    let stub = ctx.stub_registry.lookup(callee_path)?;
    let is_chars = match stub {
        StubKind::StrCharsNth => true,
        StubKind::StrBytesNth => false,
        _ => return None,
    };

    if args.len() != 2 {
        return None;
    }

    let dest_ty = destination.ty(outer_body.locals()).ok()?;
    let dest_sort = ChcCtx::translate_ty(ctx.resolve_body_ty(dest_ty))?;

    // Use an empty modified_locals set for const-fold — the inlined body's
    // locals have not been modified by the enclosing function at this point.
    let modified_locals = std::collections::HashSet::new();
    let result =
        ctx.try_const_fold_str_nth(&args[0], &args[1], &modified_locals, &dest_sort, is_chars)?;
    Some(InlineReturn::value_only(result))
}

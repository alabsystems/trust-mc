// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The real `str::chars` constructor, without walking `as_bytes().iter()`.
//!
//! Keep the complete backing array and its offset. The iterator starts at
//! `offset`, ends at `offset + len`, and its pointer names backing index zero.
//! Construction preserves bytes without a bounded copy or wrapper search.
//! Advancement decodes the next UTF-8 scalar and updates the same owner.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};
use std::collections::BTreeMap;
use trust_mc_core::violation::PropertyKind;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_fallback_emit::emit_sound_fallback_goto;
use super::codegen_types::CodegenTypes;
use super::inline_result_shared::{
    InlineResultEpilogueSpec, emit_prepared_inline_result, prepare_inline_result_epilogue,
};
use super::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::POINTER_WIDTH;

fn authenticated_output_ty(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> Option<Ty> {
    if crate::kani_middle::transform::unit_has_stubs() {
        return None;
    }
    let ty = ctx.resolve_body_ty(func.ty(locals).ok()?);
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return None };
    let instance = Instance::resolve(def, &args).ok()?;
    if !crate::kani_middle::std_abstraction::is_core_str_chars(ctx.tcx, &instance) {
        return None;
    }
    let output = ctx.resolve_body_ty(ty.kind().fn_sig()?.skip_binder().output());
    let TyKind::RigidTy(RigidTy::Adt(adt, _)) = output.kind() else { return None };
    crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
        ctx.tcx,
        rustc_internal::internal(ctx.tcx, adt.def_id()),
        &["str", "iter", "Chars"],
    )
    .then_some(output)
}

pub(super) fn try_codegen_str_chars(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let Some(target) = *dcx.target else { return false };
    let [receiver] = dcx.args else { return false };
    if !dcx.destination.projection.is_empty() {
        return false;
    }
    let Some(output) = authenticated_output_ty(ctx, dcx.func, ctx.body.locals()) else {
        return false;
    };
    let Some(sort) = ChcCtx::translate_ty(output) else { return false };
    let (data, len, offset) = if is_const_empty_str(ctx, receiver) {
        // A zero-length MIR &str constant can carry a dangling data pointer,
        // with no allocation to recover. No byte is observable through this
        // empty view. Its actual data pointer is still translated below.
        (
            Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u8, 8)),
            Expr::bitvec_const(0u64, POINTER_WIDTH),
            Expr::bitvec_const(0u64, POINTER_WIDTH),
        )
    } else {
        let Some(backing) = ctx.resolve_string_backing(receiver, dcx.modified_locals) else {
            return false;
        };
        (backing.data, backing.len, backing.offset)
    };
    let Some(pointer) = ctx.translate_operand_with_modified(receiver, dcx.modified_locals) else {
        return false;
    };
    let Some(repr) = PtrRepr::classify(&pointer) else { return false };
    // Length comes from independently resolved storage, not a decoded high
    // word. This also admits a known empty str whose packed pointer folded
    // to a zero high word (PtrRepr conservatively calls that WidenedThin).
    let Some((value, valid_range)) =
        build_chars_value(ctx, &sort, data, len, offset, repr.data().as_expr().clone())
    else {
        return false;
    };
    ctx.declare_datatype_sort_if_needed(&sort);
    ctx.emit_error_rule_for_condition_with_kind(
        dcx.from_app,
        valid_range.clone(),
        dcx.stmt_constraints,
        dcx.bb_idx,
        PropertyKind::PointerOverflow,
        Some("str::chars backing range exceeds its index domain".to_string()),
    );
    let aliases = BTreeMap::new();
    let args = BTreeMap::new();
    let prepared = prepare_inline_result_epilogue(
        ctx,
        InlineResultEpilogueSpec {
            dcx,
            target,
            dest_local: dcx.destination.local,
            result_expr: value,
            inline_vtable: None,
            fallback_vtable: None,
            alias_updates: &aliases,
            pre_resolved_args: &args,
            eq_reason: "str_chars_constructor",
            alias_reason: "str_chars_constructor",
            extra_constraints: vec![valid_range],
            extra_dests: Vec::new(),
            drain_pending_updates: true,
            drain_pending_checks: true,
        },
    );
    if emit_prepared_inline_result(ctx, prepared).is_err() {
        ctx.record_sound_fallback_reason("str_chars_destination_unresolved");
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dcx.destination.local],
            dcx.stmt_constraints,
        );
    }
    true
}

/// Read only the length word of an actual MIR &str constant. A widened thin
/// SMT pointer's zero high bits are not evidence of an empty string.
fn is_const_empty_str(ctx: &ChcCtx<'_, '_>, receiver: &Operand) -> bool {
    super::inline_const_origin::unaliased_origin(
        ctx,
        receiver,
        super::inline_const_origin::literal_str_byte_len,
    ) == Some(0)
}

/// Advance an owned Chars local through its checked mutable borrow. Other
/// aliases/projected receivers retain the general body path.
pub(super) fn try_codegen_chars_next(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let Some(target) = *dcx.target else { return false };
    let [receiver] = dcx.args else { return false };
    if !dcx.destination.projection.is_empty() || crate::kani_middle::transform::unit_has_stubs() {
        return false;
    }
    let Ok(function_ty) = dcx.func.ty(ctx.body.locals()) else { return false };
    let function_ty = ctx.resolve_body_ty(function_ty);
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = function_ty.kind() else { return false };
    let Ok(instance) = Instance::resolve(def, &args) else { return false };
    if !crate::kani_middle::std_abstraction::is_core_chars_next(ctx.tcx, &instance) {
        return false;
    }
    let (Operand::Copy(place) | Operand::Move(place)) = receiver else { return false };
    if !place.projection.is_empty() {
        return false;
    }
    let Some(alias) = ctx.ref_resolution.ref_targets.get(&place.local) else { return false };
    if !alias.projections.is_empty() {
        return false;
    }
    let owner = alias.local;
    let Some(owner_ty) = ctx.body.locals().get(owner).map(|decl| decl.ty) else { return false };
    let Some(chars_sort) = ChcCtx::translate_ty(owner_ty) else { return false };
    let Some(chars) = ctx.get_collection_arg(receiver, dcx.modified_locals) else { return false };
    if chars.sort() != &chars_sort {
        return false;
    }
    let Some(signature) = function_ty.kind().fn_sig() else { return false };
    let output_ty = ctx.resolve_body_ty(signature.skip_binder().output());
    let Some(output_sort) = ChcCtx::translate_ty(output_ty) else { return false };
    let Some((value, updated, valid)) = build_chars_next(ctx, chars, &output_sort) else {
        return false;
    };
    ctx.declare_datatype_sort_if_needed(&output_sort);
    ctx.emit_error_rule_for_condition_with_kind(
        dcx.from_app,
        valid.clone(),
        dcx.stmt_constraints,
        dcx.bb_idx,
        PropertyKind::UndefinedBehavior,
        Some("Chars::next requires a valid UTF-8 suffix".to_string()),
    );
    let aliases = BTreeMap::from([(1, updated)]);
    let owners = BTreeMap::from([(1, owner)]);
    let prepared = prepare_inline_result_epilogue(
        ctx,
        InlineResultEpilogueSpec {
            dcx,
            target,
            dest_local: dcx.destination.local,
            result_expr: value,
            inline_vtable: None,
            fallback_vtable: None,
            alias_updates: &aliases,
            pre_resolved_args: &owners,
            eq_reason: "chars_next",
            alias_reason: "chars_next_alias",
            extra_constraints: vec![valid],
            extra_dests: Vec::new(),
            drain_pending_updates: true,
            drain_pending_checks: true,
        },
    );
    if emit_prepared_inline_result(ctx, prepared).is_err() {
        ctx.record_sound_fallback_reason("chars_next_destination_unresolved");
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dcx.destination.local, owner],
            dcx.stmt_constraints,
        );
    }
    true
}

pub(super) fn build_chars_next(
    ctx: &ChcCtx<'_, '_>,
    chars: Expr,
    output_sort: &Sort,
) -> Option<(Expr, Expr, Expr)> {
    let iter = field_value(&chars, "fld_iter")?;
    let storage = field_value(&iter, "fld_vec")?;
    let pos = field_value(&iter, "fld_pos")?;
    let end = field_value(&storage, "fld_len")?;
    let data = field_value(&storage, "fld_data")?;
    let (payload, step, valid_utf8) = decode_utf8_scalar(&data, &pos, &end)?;
    let in_bounds = pos.clone().bvult(end.clone());
    let value = Expr::ite(
        in_bounds.clone(),
        ctx.make_some_expr_for_option(payload, output_sort)?,
        ctx.make_none_expr_for_option(output_sort)?,
    );
    let new_pos = Expr::ite(in_bounds.clone(), pos.clone().bvadd(step), pos.clone());
    let updated_iter = structure(iter.sort(), vec![("fld_vec", storage), ("fld_pos", new_pos)])?;
    let updated = structure(chars.sort(), vec![("fld_iter", updated_iter)])?;
    let valid = pos.bvule(end).and(in_bounds.implies(valid_utf8));
    Some((value, updated, valid))
}

/// Exact UTF-8 scalar decoding, including the shortest-form, surrogate and
/// U+10FFFF restrictions. All speculative array reads are total SMT selects;
/// only the selected, sufficiently long byte sequence affects the result.
fn decode_utf8_scalar(data: &Expr, pos: &Expr, end: &Expr) -> Option<(Expr, Expr, Expr)> {
    let index = Sort::bitvec(POINTER_WIDTH);
    let array = data.sort().array_sort()?;
    if pos.sort() != &index
        || end.sort() != &index
        || array.index_sort != index
        || array.element_sort != Sort::bitvec(8)
    {
        return None;
    }
    let bv = |n: u64| Expr::bitvec_const(n, POINTER_WIDTH);
    let byte = |n| data.clone().select(pos.clone().bvadd(bv(n)));
    let [a, b, c, d] = [byte(0), byte(1), byte(2), byte(3)];
    let between = |value: &Expr, lo: u8, hi: u8| {
        value
            .clone()
            .bvuge(Expr::bitvec_const(lo, 8))
            .and(value.clone().bvule(Expr::bitvec_const(hi, 8)))
    };
    let cont = |value: &Expr| between(value, 0x80, 0xbf);
    let available = |n| end.clone().bvsub(pos.clone()).bvuge(bv(n));
    let ascii = a.clone().bvult(Expr::bitvec_const(0x80u8, 8));
    let two = between(&a, 0xc2, 0xdf).and(cont(&b)).and(available(2));
    let three = between(&a, 0xe0, 0xef)
        .and(cont(&b))
        .and(cont(&c))
        .and(
            a.clone()
                .ne(Expr::bitvec_const(0xe0u8, 8))
                .or(b.clone().bvuge(Expr::bitvec_const(0xa0u8, 8))),
        )
        .and(
            a.clone()
                .ne(Expr::bitvec_const(0xedu8, 8))
                .or(b.clone().bvule(Expr::bitvec_const(0x9fu8, 8))),
        )
        .and(available(3));
    let four = between(&a, 0xf0, 0xf4)
        .and(cont(&b))
        .and(cont(&c))
        .and(cont(&d))
        .and(
            a.clone()
                .ne(Expr::bitvec_const(0xf0u8, 8))
                .or(b.clone().bvuge(Expr::bitvec_const(0x90u8, 8))),
        )
        .and(
            a.clone()
                .ne(Expr::bitvec_const(0xf4u8, 8))
                .or(b.clone().bvule(Expr::bitvec_const(0x8fu8, 8))),
        )
        .and(available(4));
    let piece = |value: &Expr, mask: u8, shift: u32| {
        value
            .clone()
            .bvand(Expr::bitvec_const(mask, 8))
            .zero_extend(24)
            .bvshl(Expr::bitvec_const(shift, 32))
    };
    let p2 = piece(&a, 0x1f, 6).bvor(piece(&b, 0x3f, 0));
    let p3 = piece(&a, 0x0f, 12).bvor(piece(&b, 0x3f, 6)).bvor(piece(&c, 0x3f, 0));
    let p4 = piece(&a, 0x07, 18)
        .bvor(piece(&b, 0x3f, 12))
        .bvor(piece(&c, 0x3f, 6))
        .bvor(piece(&d, 0x3f, 0));
    let payload = Expr::ite(
        ascii.clone(),
        a.zero_extend(24),
        Expr::ite(two.clone(), p2, Expr::ite(three.clone(), p3, p4)),
    );
    let step = Expr::ite(
        ascii.clone(),
        bv(1),
        Expr::ite(two.clone(), bv(2), Expr::ite(three.clone(), bv(3), bv(4))),
    );
    Some((payload, step, ascii.or(two).or(three).or(four)))
}

fn field_value(value: &Expr, name: &str) -> Option<Expr> {
    value
        .clone()
        .try_field_select(value.sort().datatype_name()?, name, field_sort(value.sort(), name)?)
        .ok()
}

fn build_chars_value(
    ctx: &ChcCtx<'_, '_>,
    chars_sort: &Sort,
    data: Expr,
    len: Expr,
    offset: Expr,
    data_pointer: Expr,
) -> Option<(Expr, Expr)> {
    let index = Sort::bitvec(POINTER_WIDTH);
    let array = data.sort().array_sort()?;
    if array.index_sort != index
        || array.element_sort != Sort::bitvec(8)
        || offset.sort() != &index
        || len.sort() != &index
        || data_pointer.sort() != &index
    {
        return None;
    }
    let iter_sort = field_sort(chars_sort, "fld_iter")?;
    let slice_sort = field_sort(&iter_sort, "fld_vec")?;
    let (end, valid) = match (ChcCtx::try_eval_const_bv(&offset), ChcCtx::try_eval_const_bv(&len)) {
        (Some(offset), Some(len)) => {
            let (end, overflow) = offset.overflowing_add(len);
            (Expr::bitvec_const(end, POINTER_WIDTH), Expr::bool_const(!overflow))
        }
        _ => {
            let end = offset.clone().bvadd(len);
            let valid = end.clone().bvuge(offset.clone());
            (end, valid)
        }
    };
    let base = ctx.step_wrapping_address(data_pointer, offset.clone(), true);
    let slice =
        structure(&slice_sort, vec![("fld_ptr", base), ("fld_len", end), ("fld_data", data)])?;
    let iter = structure(&iter_sort, vec![("fld_vec", slice), ("fld_pos", offset)])?;
    Some((structure(chars_sort, vec![("fld_iter", iter)])?, valid))
}

fn field_sort(sort: &Sort, name: &str) -> Option<Sort> {
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    Some(dt.constructors[0].fields.iter().find(|field| field.name == name)?.sort.clone())
}

fn structure(sort: &Sort, fields: Vec<(&str, Expr)>) -> Option<Expr> {
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() != 1 || dt.constructors[0].fields.len() != fields.len() {
        return None;
    }
    let ctor = &dt.constructors[0];
    let mut values = Vec::with_capacity(fields.len());
    for field in &ctor.fields {
        let value = fields.iter().find(|(name, _)| *name == field.name)?.1.clone();
        if value.sort() != &field.sort {
            return None;
        }
        values.push(value);
    }
    Expr::try_datatype_constructor(&dt.name, &ctor.name, values, sort.clone()).ok()
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;
